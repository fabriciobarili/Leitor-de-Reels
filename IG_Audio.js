// ==UserScript==
// @name         Instagram Audio Transcriber
// @namespace    https://github.com/fabriciobarili
// @version      3.8.0
// @description  Transcreve áudio do Instagram: modo lote round-robin, controle de URLs visitadas, data do reel, salvamento automático via GM_download
// @author       Fabricio Barili
// @match        https://www.instagram.com/*
// @match        https://instagram.com/*
// @run-at       document-end
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_xmlhttpRequest
// @grant        GM_download
// @connect      api.openai.com
// ==/UserScript==

/* globals GM_setValue, GM_getValue, GM_xmlhttpRequest, GM_download */
(function () {
  'use strict';

  console.log('[IAT v3.8] Script carregado.');

  /* ── Constantes ─────────────────────────────────────────── */
  const CHUNK_MS   = 60000;
  const UTC_OFFSET = 3;
  const TZ_LABEL   = 'UTC +3';

  /* ── Estado ─────────────────────────────────────────────── */
  const S = {
    recording        : false,
    stream           : null,
    recorder         : null,
    session          : null,
    pendingUrl       : null,
    profile          : '',
    inFlight         : 0,
    // Modo lote
    batch            : [],
    batchIdx         : -1,
    batchDurMs       : 300000,
    batchTimer       : null,
    batchMode        : false,
    batchRound       : 0,
    consecutiveSkips : 0,
    // Controle de URLs já mapeadas
    visitedUrls      : {},
  };

  /* ── Utilitários ─────────────────────────────────────────── */
  const pad = n => String(n).padStart(2, '0');

  function fmtDate(date, offsetH) {
    const d = new Date(date.getTime() + offsetH * 3600000);
    return pad(d.getUTCDate()) + '/' + pad(d.getUTCMonth()+1) + '/' + d.getUTCFullYear()
         + ' ' + pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes()) + ':' + pad(d.getUTCSeconds());
  }

  function fmtReelDate(isoStr) {
    var d = new Date(isoStr);
    if (isNaN(d.getTime())) return isoStr;
    return pad(d.getUTCDate()) + '-' + pad(d.getUTCMonth()+1) + '-' + d.getUTCFullYear()
         + ' ' + pad(d.getUTCHours()) + ':' + pad(d.getUTCMinutes());
  }

  function fmtVidTime(sec) {
    const h = Math.floor(sec / 3600);
    const m = Math.floor((sec % 3600) / 60);
    const s = Math.floor(sec % 60);
    return h ? pad(h)+':'+pad(m)+':'+pad(s) : pad(m)+':'+pad(s);
  }

  function tsFilename() {
    const d = new Date(Date.now() + UTC_OFFSET * 3600000);
    return d.getUTCFullYear()+''+pad(d.getUTCMonth()+1)+''+pad(d.getUTCDate())
         +'_'+pad(d.getUTCHours())+''+pad(d.getUTCMinutes())+''+pad(d.getUTCSeconds());
  }

  function videoId(url) {
    try {
      const p = new URL(url).pathname;
      const m = p.match(/\/(reel|reels|p|tv|stories\/[^/]+)\/([^/]+)/);
      return m ? m[2] : p.replace(/\//g, '_').replace(/^_|_$/g, '') || 'video';
    } catch(e) { return 'video'; }
  }

  function shortPath(url) {
    try { return new URL(url).pathname.replace(/\/$/, ''); } catch(e) { return url; }
  }

  function isMeaningfulChange(a, b) {
    return videoId(a) !== videoId(b);
  }

  function getVideoTime() {
    var v = document.querySelector('video');
    return v ? (v.currentTime || 0) : 0;
  }

  function autoDetectProfile() {
    var m = location.pathname.match(/\/stories\/([^/]+)/);
    return m ? m[1] : '';
  }

  /* ── Reel específico (tem ID, não é só listagem) ─────────── */
  function isSpecificReel(url) {
    try {
      return /\/(reel|p|tv)\/[A-Za-z0-9_-]{5,}/.test(new URL(url).pathname);
    } catch(e) { return false; }
  }

  /* ── Data do Reel (elemento <time datetime="…">) ─────────── *
   *  Numa página de reel há vários <time>: 1 é a data do post    *
   *  e os demais são timestamps de comentários. Como comentários *
   *  sempre vêm DEPOIS do post, a data do post é a MAIS ANTIGA.  *
   *  Isso é robusto a mudanças de classe/ordem no DOM.           *
   * ─────────────────────────────────────────────────────────── */
  function getReelDate() {
    var times = document.querySelectorAll('time[datetime]');
    var best = null;
    for (var i = 0; i < times.length; i++) {
      var dt = times[i].getAttribute('datetime');
      if (!dt) continue;
      var ms = Date.parse(dt);
      if (isNaN(ms)) continue;
      if (best === null || ms < best.ms) best = { ms: ms, raw: dt };
    }
    return best ? best.raw : null;
  }

  /* O <time> carrega com atraso após abrir o reel; faz polling   *
   * por alguns segundos e grava a data na sessão quando aparece. */
  function captureReelDateInto(session, tries) {
    if (!session) return;
    var d = getReelDate();
    if (d) {
      session.reelDate = d;
      updateRecordingInfo();
      addLog('📅 ' + d.substring(0, 10));
      return;
    }
    if (tries >= 16) return; // ~8s
    setTimeout(function() { captureReelDateInto(session, tries + 1); }, 500);
  }

  /* ── Avança para o próximo reel (seta pra direita) ───────── */
  function pressNextReel() {
    var opts = { key: 'ArrowRight', code: 'ArrowRight', keyCode: 39, which: 39,
                 bubbles: true, cancelable: true };
    var targets = [document, document.body, window];
    var v = document.querySelector('video');
    if (v) targets.unshift(v);
    targets.forEach(function(t) {
      try {
        t.dispatchEvent(new KeyboardEvent('keydown', opts));
        t.dispatchEvent(new KeyboardEvent('keyup', opts));
      } catch (e) {}
    });
  }

  /* ── Controle de URLs visitadas ──────────────────────────── */
  function loadVisited() {
    try { S.visitedUrls = JSON.parse(GM_getValue('iat_visited', '{}')); }
    catch(e) { S.visitedUrls = {}; }
  }

  function isVisited(url) {
    if (!isSpecificReel(url)) return false;
    return !!S.visitedUrls[videoId(url)];
  }

  function markVisited(url) {
    if (!isSpecificReel(url)) return;
    var id = videoId(url);
    S.visitedUrls[id] = Date.now();
    try { GM_setValue('iat_visited', JSON.stringify(S.visitedUrls)); } catch(e) {}
    addLog('🔖 ' + id);
  }

  function clearVisited() {
    S.visitedUrls = {};
    try { GM_setValue('iat_visited', '{}'); } catch(e) {}
    addLog('🗑️ Histórico limpo.');
  }

  /* ── CSV ─────────────────────────────────────────────────── */
  function parseCsv(text) {
    return text.split('\n').map(function(line) {
      var parts   = line.trim().split(',');
      var profile = (parts[0] || '').trim().replace(/^@/, '');
      if (!profile || profile.charAt(0) === '#') return null;
      var path    = (parts[1] || '').trim() || ('/' + profile + '/reels/');
      if (path.charAt(0) !== '/') path = '/' + path;
      return { profile: profile, path: path };
    }).filter(Boolean);
  }

  /* ── CSS ─────────────────────────────────────────────────── */
  function injectStyles() {
    var style = document.createElement('style');
    style.id  = 'iat-styles';
    style.textContent = [
      '#iat-panel { all: initial !important; display: block !important; position: fixed !important;',
      '  top: 20px !important; right: 20px !important; z-index: 2147483647 !important;',
      '  width: 330px !important; font-family: monospace !important; font-size: 13px !important;',
      '  background: #1a1a2e !important; color: #eee !important; border-radius: 12px !important;',
      '  box-shadow: 0 4px 24px rgba(0,0,0,.75) !important; border: 1px solid #3a3a5c !important;',
      '  overflow: visible !important; user-select: none !important; box-sizing: border-box !important; }',
      '#iat-panel * { font-family: monospace !important; box-sizing: border-box !important;',
      '  visibility: visible !important; opacity: 1 !important; }',
      '#iat-panel div { display: block !important; }',
      '#iat-panel span { display: inline !important; }',
      '#iat-panel button { display: inline-block !important; cursor: pointer !important;',
      '  border: none !important; border-radius: 6px !important; color: #fff !important;',
      '  font-size: 12px !important; font-family: monospace !important; }',
      '#iat-panel input, #iat-panel textarea { display: inline-block !important; color: #eee !important;',
      '  background: #0d0d1a !important; border: 1px solid #3a3a5c !important;',
      '  border-radius: 6px !important; padding: 5px 8px !important; font-size: 12px !important; }',
    ].join('\n');
    document.head.appendChild(style);
  }

  /* ── Captura de áudio ───────────────────────────────────── */
  function requestTabAudio() {
    return navigator.mediaDevices.getDisplayMedia({
      video: { displaySurface: 'browser' },
      audio: { suppressLocalAudioPlayback: false, echoCancellation: false,
               noiseSuppression: false, autoGainControl: false },
      preferCurrentTab: true,
      selfBrowserSurface: 'include',
    }).then(function(ms) {
      var audioTracks = ms.getAudioTracks();
      if (audioTracks.length === 0) {
        ms.getTracks().forEach(function(t) { t.stop(); });
        return Promise.reject(new Error('Nenhum áudio capturado. Ative "Compartilhar áudio da aba".'));
      }
      ms.getVideoTracks().forEach(function(t) { t.stop(); });
      return new MediaStream(audioTracks);
    });
  }

  /* ── Monitoramento de URL ───────────────────────────────── */
  function initUrlWatcher() {
    var lastUrl = location.href;

    function check() {
      var cur = location.href;
      if (cur !== lastUrl && isMeaningfulChange(lastUrl, cur)) onUrlChange(lastUrl, cur);
      lastUrl = cur;
    }

    ['pushState', 'replaceState'].forEach(function(method) {
      var orig = history[method].bind(history);
      history[method] = function() { orig.apply(history, arguments); check(); };
    });

    window.addEventListener('popstate', check);
  }

  function onUrlChange(prevUrl, newUrl) {
    if (!S.recording) return;

    // Em modo lote: verifica se o novo reel já foi mapeado ANTES de qualquer transcrição
    if (S.batchMode && isSpecificReel(newUrl)) {
      if (isVisited(newUrl)) {
        addLog('⏭ Já mapeado → pulando reel');
        pressNextReel();
        return; // não cria nova sessão para este reel
      }
      var d = getReelDate();
      if (d) addLog('📅 ' + d);
      markVisited(newUrl); // marca ANTES de transcrever
    }

    addLog('⚡ URL → ' + shortPath(newUrl));
    S.pendingUrl = newUrl;
    if (S.recorder && S.recorder.state === 'recording') S.recorder.stop();
  }

  /* ── Gravação paralela ───────────────────────────────────── */
  function scheduleChunk() {
    if (!S.recording) return;

    var mime = MediaRecorder.isTypeSupported('audio/webm;codecs=opus')
      ? 'audio/webm;codecs=opus' : 'audio/webm';

    var localChunks  = [];
    var localOffset  = getVideoTime();
    var localSession = S.session;

    var rec = new MediaRecorder(S.stream, { mimeType: mime });
    S.recorder = rec;

    rec.ondataavailable = function(e) {
      if (e.data && e.data.size > 0) localChunks.push(e.data);
    };

    rec.onstop = function() {
      var capturedPendingUrl = S.pendingUrl;

      if (capturedPendingUrl) {
        S.pendingUrl = null;
        var oldSession = localSession;
        oldSession.tEnd = new Date();
        // Em modo lote, a nova sessão herda a data do reel se disponível
        startSession(capturedPendingUrl, S.batchMode ? getReelDate() : null);
        scheduleChunk();
        dispatchTranscription(localChunks, mime, localOffset, oldSession, function() {
          finishSession(oldSession);
        });

      } else if (S.recording) {
        scheduleChunk();
        dispatchTranscription(localChunks, mime, localOffset, localSession, null);

      } else {
        dispatchTranscription(localChunks, mime, localOffset, localSession, checkFinished);
      }
    };

    rec.start();
    setTimeout(function() {
      if (rec.state === 'recording') rec.stop();
    }, CHUNK_MS);
  }

  function dispatchTranscription(chunks, mime, offset, session, cb) {
    if (!chunks.length) { if (cb) cb(); return; }
    S.inFlight++;
    transcribeBlob(new Blob(chunks, { type: mime }), offset, session)
      .then(function() { S.inFlight--; if (cb) cb(); });
  }

  function checkFinished() {
    if (!S.recording && S.inFlight === 0 && S.session) {
      finishSession(S.session);
      S.session = null;
      onRecordingFinished();
    }
  }

  /* ── Detector de loop do vídeo ──────────────────────────── *
   *  Quando o reel termina, o Instagram reinicia do zero.       *
   *  O Instagram pré-carrega o próximo reel, então pode haver    *
   *  vários <video> no DOM — a maioria pausada em currentTime 0. *
   *  Fazemos polling sobre TODOS os vídeos e só rastreamos os    *
   *  que estão de fato tocando (não pausados, tempo avançando).  *
   *  Loop = tempo caiu de um valor alto para ~0.                 *
   * ─────────────────────────────────────────────────────────── */
  var _loopTimer = null;
  var _loopTimes = null;      // Map<videoEl, lastCurrentTime>
  var _loopArmedAt = 0;       // evita disparo no seek inicial

  function attachVideoLoopDetector() {
    detachVideoLoopDetector();
    _loopTimes = new Map();
    _loopArmedAt = Date.now();
    _loopTimer = setInterval(scanVideosForLoop, 300);
  }

  function scanVideosForLoop() {
    if (!S.recording) return;
    var vids = document.querySelectorAll('video');
    for (var i = 0; i < vids.length; i++) {
      var v = vids[i];
      // Só nos importam vídeos que estão realmente tocando.
      var playing = !v.paused && !v.ended && v.readyState >= 2;
      var cur = v.currentTime || 0;
      var prev = _loopTimes.has(v) ? _loopTimes.get(v) : null;

      if (prev !== null && prev > 1.0 && cur < 0.5 &&
          Date.now() - _loopArmedAt > 2500) {
        addLog('🔁 Reel reiniciou (' + prev.toFixed(1) + 's → 0) → ArrowRight');
        advanceToNextReel();
        return;
      }

      // Atualiza o tempo rastreado apenas enquanto o vídeo está tocando,
      // para que vídeos pré-carregados (parados em 0) nunca disparem.
      if (playing) _loopTimes.set(v, cur);
      else if (prev === null) _loopTimes.set(v, cur);
    }
  }

  /* Dispara o avanço para o próximo reel e re-arma o detector,   *
   * com cooldown de ~2.5s para o novo reel começar a tocar.      */
  function advanceToNextReel() {
    pressNextReel();
    _loopArmedAt = Date.now();
    if (_loopTimes) _loopTimes.clear();
  }

  function detachVideoLoopDetector() {
    if (_loopTimer) { clearInterval(_loopTimer); _loopTimer = null; }
    _loopTimes = null;
  }

  /* ── Modo Lote Round-Robin ───────────────────────────────── *
   *  Rotação: X → Y → Z → X → Y → Z → …                       *
   *  Termina quando todos os perfis ficam sem novos reels.      *
   * ─────────────────────────────────────────────────────────── */
  function startBatch(items, durMs) {
    S.batch            = items;
    S.batchIdx         = -1;
    S.batchDurMs       = durMs;
    S.batchMode        = true;
    S.batchRound       = 0;
    S.consecutiveSkips = 0;
    setStatus('🔐 Aguardando permissão…');
    requestTabAudio().then(function(stream) {
      S.stream = stream;
      S.stream.getAudioTracks()[0].addEventListener('ended', function() {
        if (S.recording) { addLog('⚠️ Captura encerrada pelo Chrome.'); stopRecording(); }
      });
      showRecordingPanel();
      advanceBatch();
    }).catch(function(e) { setStatus('❌ ' + e.message); S.batchMode = false; });
  }

  function advanceBatch() {
    // Round-robin circular
    S.batchIdx = (S.batchIdx + 1) % S.batch.length;

    if (S.batchIdx === 0) {
      S.batchRound++;
      addLog('🔄 Rodada ' + S.batchRound);
    }

    var item = S.batch[S.batchIdx];
    S.profile = item.profile;
    updateBatchProgress();
    addLog('📋 [' + (S.batchIdx+1) + '/' + S.batch.length + '] @' + item.profile);

    history.pushState(null, '', item.path);
    waitForNewReel(0);
  }

  /* Aguarda um reel não visitado no perfil atual.
   * - Se a URL for um reel específico e visitado → pula e retry.
   * - Caso contrário → inicia gravação.                          */
  function waitForNewReel(retries) {
    setTimeout(function() {
      var curUrl = location.href;

      // Reel específico e visitado → pula
      if (isSpecificReel(curUrl) && isVisited(curUrl)) {
        if (retries >= 25) { skipProfile(); return; }
        addLog('⏭ Já mapeado (' + videoId(curUrl) + ') → próximo');
        pressNextReel();
        waitForNewReel(retries + 1);
        return;
      }

      // Novo reel (ou página de listagem) → grava
      S.consecutiveSkips = 0;

      if (isSpecificReel(curUrl)) {
        var d = getReelDate();
        if (d) addLog('📅 ' + d);
        markVisited(curUrl); // marca ANTES de qualquer transcrição
      }

      S.recording = true;
      S.inFlight  = 0;
      startSession(curUrl, getReelDate());
      scheduleChunk();
      setStatus('🔴 Gravando @' + S.profile + '…');
      setTimeout(attachVideoLoopDetector, 800);

      if (S.batchTimer) clearTimeout(S.batchTimer);
      S.batchTimer = setTimeout(function() {
        if (S.recording) { addLog('⏱ Tempo esgotado'); stopRecording(); }
      }, S.batchDurMs);

    }, retries === 0 ? 2500 : 1200);
  }

  function skipProfile() {
    S.consecutiveSkips++;
    addLog('⏭ @' + S.profile + ' — sem novos reels');
    if (S.consecutiveSkips >= S.batch.length) {
      // Todos os perfis sem novos reels → fim
      S.batchMode = false;
      setStatus('✅ Lote concluído! ' + S.batchRound + ' rodada(s).');
      disableStopBtn();
      var btnNew = btn('↩ Nova transcrição', '#27ae60', showSetupPanel);
      css(btnNew, { width: '100%', marginTop: '10px', fontSize: '13px' });
      elBody.appendChild(btnNew);
      return;
    }
    advanceBatch();
  }

  /* ── Sessões ─────────────────────────────────────────────── */
  function startSession(url, reelDate) {
    S.session = {
      url      : url,
      profile  : S.profile,
      segments : [],
      tStart   : new Date(),
      tEnd     : null,
      reelDate : reelDate || null,
    };
    updateRecordingInfo();
    addLog('▶ Sessão: ' + shortPath(url));
    if (isSpecificReel(url)) captureReelDateInto(S.session, 0);
  }

  function finishSession(sess) {
    if (!sess) return;
    if (!sess.tEnd) sess.tEnd = new Date();
    sess.segments.sort(function(a, b) { return a.t - b.t; });
    if (sess.segments.length > 0) saveTranscription(sess);
    else addLog('⚠️ Nenhum segmento — arquivo não salvo.');
  }

  /* ── Iniciar / Parar ─────────────────────────────────────── */
  function startRecording() {
    setStatus('🔐 Aguardando permissão…');
    requestTabAudio().then(function(stream) {
      S.stream = stream;
      S.stream.getAudioTracks()[0].addEventListener('ended', function() {
        if (S.recording) { addLog('⚠️ Captura encerrada pelo Chrome.'); stopRecording(); }
      });
      S.recording = true;
      S.inFlight  = 0;
      showRecordingPanel();
      startSession(location.href, getReelDate());
      scheduleChunk();
      setTimeout(attachVideoLoopDetector, 800);
    }).catch(function(e) { setStatus('❌ ' + e.message); });
  }

  function stopRecording() {
    detachVideoLoopDetector();
    if (S.batchTimer) { clearTimeout(S.batchTimer); S.batchTimer = null; }
    S.recording = false;
    setStatus('⏹ Finalizando…');
    disableStopBtn();
    if (S.recorder && S.recorder.state === 'recording') S.recorder.stop();
  }

  function stopBatch() {
    S.batchMode = false;
    stopRecording();
  }

  /* ── API Whisper ─────────────────────────────────────────── */
  function transcribeBlob(blob, videoOffset, session) {
    var key = GM_getValue('openai_key', '');
    if (!key) { addLog('⚠️ Chave OpenAI não configurada — abra ⚙️'); return Promise.resolve(); }

    setStatus('🔄 Transcrevendo [' + fmtVidTime(videoOffset) + '…]  (' + S.inFlight + ' em fila)');

    var fd = new FormData();
    fd.append('file', blob, 'audio.webm');
    fd.append('model', 'whisper-1');
    fd.append('response_format', 'verbose_json');
    fd.append('timestamp_granularities[]', 'segment');
    fd.append('language', 'pt');

    return new Promise(function(resolve) {
      GM_xmlhttpRequest({
        method  : 'POST',
        url     : 'https://api.openai.com/v1/audio/transcriptions',
        headers : { 'Authorization': 'Bearer ' + key },
        data    : fd,
        onload  : function(r) {
          if (r.status === 200) {
            try {
              var res  = JSON.parse(r.responseText);
              var segs = res.segments || (res.text ? [{ start: 0, text: res.text }] : []);
              segs.forEach(function(seg) {
                var text = seg.text ? seg.text.trim() : '';
                if (text && session) session.segments.push({ t: videoOffset + (seg.start || 0), text: text });
              });
              refreshPreview();
              if (S.recording) setStatus('🔴 Gravando…');
            } catch(ex) { addLog('❌ Erro ao parsear resposta Whisper.'); }
          } else {
            addLog('❌ Whisper API: HTTP ' + r.status);
          }
          resolve();
        },
        onerror : function() { addLog('❌ Erro de rede.'); resolve(); },
      });
    });
  }

  /* ── Exportar TXT ───────────────────────────────────────── */
  function saveTranscription(sess) {
    var profile  = sess.profile || 'unknown';
    var filename = 'instagram_' + profile + '_' + videoId(sess.url) + '_' + tsFilename() + '.txt';

    var header = ['==== EXTRAÇÃO DO ÁUDIO DA URL: ' + sess.url + ' ===='];
    if (sess.reelDate) header.push('DATA_POSTAGEM = ' + fmtReelDate(sess.reelDate));
    header.push('==== INÍCIO DA TRANSCRIÇÃO ' + fmtDate(sess.tStart, UTC_OFFSET) + ' ' + TZ_LABEL + ' ====');
    header.push('');

    var lines = header
      .concat(sess.segments.map(function(s) { return '[' + fmtVidTime(s.t) + '] ' + s.text; }))
      .concat(['', '==== FIM DA TRANSCRIÇÃO ' + fmtDate(sess.tEnd, UTC_OFFSET) + ' ' + TZ_LABEL + ' ====']);

    var blob = new Blob([lines.join('\n')], { type: 'text/plain;charset=utf-8' });
    var bUrl = URL.createObjectURL(blob);

    GM_download({
      url: bUrl,
      name: filename,
      saveAs: false,
      onload: function() {
        setTimeout(function() { URL.revokeObjectURL(bUrl); }, 1000);
        addLog('✅ Salvo: ' + filename);
      },
      onerror: function(err) {
        addLog('⚠️ GM_download falhou (' + (err && err.error) + '), usando fallback');
        var a = document.createElement('a');
        a.href = bUrl; a.download = filename;
        document.body.appendChild(a); a.click();
        setTimeout(function() { a.remove(); URL.revokeObjectURL(bUrl); }, 500);
        addLog('✅ Salvo (fallback): ' + filename);
      },
    });
  }

  /* ── UI ─────────────────────────────────────────────────── */
  var panel, elBody, elStatus, elRecInfo, elBatchProgress, elLog, elPreview, elStopBtn;
  var dragging = false, dragOX = 0, dragOY = 0;

  function css(el, styles) {
    Object.keys(styles).forEach(function(k) { el.style[k] = styles[k]; });
    return el;
  }
  function div(styles) { return css(document.createElement('div'), styles || {}); }
  function span()      { return document.createElement('span'); }
  function btn(label, bg, onClick) {
    var b = document.createElement('button');
    b.textContent = label;
    css(b, { background: bg, padding: '10px 12px', flex: '1', fontSize: '12px' });
    b.addEventListener('click', onClick);
    return b;
  }

  function buildPanel() {
    injectStyles();
    panel = document.createElement('div');
    panel.id = 'iat-panel';

    var hdr = div({ background: '#16213e', padding: '9px 12px', cursor: 'move',
                    display: 'flex', justifyContent: 'space-between', alignItems: 'center',
                    borderBottom: '1px solid #3a3a5c', borderRadius: '12px 12px 0 0' });
    var hdrLabel  = span(); hdrLabel.textContent  = '🎙️ Instagram Transcriber';
    var hdrToggle = span(); hdrToggle.textContent = '▼';
    hdrToggle.style.cursor = 'pointer';
    hdr.append(hdrLabel, hdrToggle);

    var collapsed = false;
    hdrToggle.addEventListener('click', function(e) {
      e.stopPropagation();
      collapsed = !collapsed;
      elBody.style.setProperty('display', collapsed ? 'none' : 'block', 'important');
      hdrToggle.textContent = collapsed ? '▶' : '▼';
    });

    hdr.addEventListener('mousedown', function(e) {
      if (e.target === hdrToggle) return;
      e.preventDefault(); dragging = true;
      var r = panel.getBoundingClientRect();
      dragOX = e.clientX - r.left; dragOY = e.clientY - r.top;
    });

    elBody = div({ padding: '12px' });
    panel.append(hdr, elBody);
    document.body.appendChild(panel);
    showSetupPanel();
  }

  /* ── Painel Setup ────────────────────────────────────────── */
  function showSetupPanel() {
    elBody.innerHTML = '';

    elStatus = div({ color: '#7ec8e3', fontSize: '12px', minHeight: '18px', marginBottom: '10px' });
    elStatus.textContent = '⏸ Configure e inicie a transcrição.';

    var lbProf = div({ color: '#888', fontSize: '11px', marginBottom: '4px' });
    lbProf.textContent = 'Perfil do criador do vídeo:';

    var rowProf = div({ display: 'flex', alignItems: 'center', gap: '4px', marginBottom: '12px' });
    var atSign  = span(); atSign.textContent = '@'; atSign.style.color = '#7ec8e3';
    var inpProf = document.createElement('input');
    css(inpProf, { flex: '1' });
    inpProf.type = 'text'; inpProf.placeholder = 'nome_do_perfil';
    inpProf.value = autoDetectProfile() || S.profile;
    rowProf.append(atSign, inpProf);

    var noteBox = div({ background: '#1e1e0a', border: '1px solid #555520', borderRadius: '6px',
                        padding: '7px 10px', fontSize: '11px', color: '#ffd',
                        marginBottom: '12px', lineHeight: '1.5' });
    noteBox.innerHTML = '⚠️ Na janela do Chrome:<br>&nbsp;&nbsp;1. Selecione <b>esta aba</b><br>&nbsp;&nbsp;2. Ative <b>"Compartilhar áudio da aba"</b>';

    var rowBtns  = div({ display: 'flex', gap: '8px', marginBottom: '10px' });
    var btnStart = btn('▶ Iniciar Escuta', '#27ae60', function() {
      var prof = inpProf.value.trim().replace(/^@/, '');
      if (!prof) { elStatus.textContent = '⚠️ Digite o nome do perfil.'; return; }
      S.profile = prof; startRecording();
    });
    css(btnStart, { fontSize: '13px' });

    var batchPanel = buildBatchPanel(elStatus);
    var btnLote    = btn('📋 Lote', '#1a4a6e', function() {
      batchPanel.style.setProperty('display',
        batchPanel.style.display === 'none' ? 'block' : 'none', 'important');
    });
    css(btnLote, { flex: '0 0 auto', fontSize: '12px' });

    var cfgPanel = buildConfigPanel();
    var btnCfg   = btn('⚙️', '#3a3a5c', function() {
      cfgPanel.style.setProperty('display',
        cfgPanel.style.display === 'none' ? 'block' : 'none', 'important');
    });
    css(btnCfg, { flex: '0 0 auto' });

    rowBtns.append(btnStart, btnLote, btnCfg);
    elBody.append(elStatus, lbProf, rowProf, noteBox, rowBtns, batchPanel, cfgPanel);
  }

  /* ── Painel Lote ─────────────────────────────────────────── */
  function buildBatchPanel(elStatusRef) {
    var p = div({ background: '#0d1a0d', border: '1px solid #2a5c2a',
                  borderRadius: '6px', padding: '10px', marginBottom: '8px' });
    p.style.setProperty('display', 'none', 'important');

    var lbCsv = div({ color: '#7dff7d', fontSize: '11px', marginBottom: '4px' });
    lbCsv.textContent = 'Perfis (um por linha: nome  ou  nome,/caminho):';

    var txCsv = document.createElement('textarea');
    css(txCsv, { width: '100%', height: '80px', resize: 'vertical',
                  fontFamily: 'monospace', fontSize: '11px' });
    txCsv.placeholder = 'joao\nmaria,/maria/reels/\n# comentário ignorado';

    var rowDur = div({ display: 'flex', alignItems: 'center', gap: '6px', margin: '8px 0' });
    var lbDur  = span(); lbDur.textContent = 'Duração por reel (min):';
    css(lbDur, { color: '#aaa', fontSize: '11px' });
    var inpDur = document.createElement('input');
    css(inpDur, { width: '50px', textAlign: 'center' });
    inpDur.type = 'number'; inpDur.min = '1'; inpDur.max = '60'; inpDur.value = '5';
    rowDur.append(lbDur, inpDur);

    var lbVis = div({ color: '#5a8c5a', fontSize: '10px', marginBottom: '6px' });
    lbVis.textContent = Object.keys(S.visitedUrls).length + ' reels já mapeados no histórico';

    var btnGo = btn('▶ Iniciar Lote (Round-Robin)', '#27ae60', function() {
      var items = parseCsv(txCsv.value);
      if (!items.length) { elStatusRef.textContent = '⚠️ Nenhum perfil válido no CSV.'; return; }
      var dur = Math.max(1, parseInt(inpDur.value, 10) || 5) * 60000;
      startBatch(items, dur);
    });
    css(btnGo, { width: '100%', fontSize: '13px', marginTop: '2px' });

    p.append(lbCsv, txCsv, rowDur, lbVis, btnGo);
    return p;
  }

  /* ── Painel Gravação ─────────────────────────────────────── */
  function showRecordingPanel() {
    elBody.innerHTML = '';

    elStatus = div({ color: '#7ec8e3', fontSize: '12px', minHeight: '18px', marginBottom: '6px' });
    elStatus.textContent = '🔴 Gravando…';

    elRecInfo = div({ background: '#0d0d1a', border: '1px solid #3a3a5c', borderRadius: '6px',
                      padding: '6px 10px', fontSize: '11px', color: '#888', marginBottom: '6px' });

    elBatchProgress = div({ background: '#0d1a0d', border: '1px solid #2a5c2a', borderRadius: '6px',
                            padding: '6px 10px', fontSize: '11px', color: '#7dff7d', marginBottom: '6px' });

    var lbLog = div({ color: '#888', fontSize: '10px', marginBottom: '3px' });
    lbLog.textContent = 'Eventos:';

    elLog = div({ maxHeight: '65px', overflowY: 'auto', fontSize: '10px', color: '#aaa',
                  background: '#0d0d1a', padding: '5px 8px', borderRadius: '6px',
                  marginBottom: '8px', lineHeight: '1.5' });

    var lbPrev = div({ color: '#888', fontSize: '10px', marginBottom: '3px' });
    lbPrev.textContent = 'Transcrição atual:';

    elPreview = div({ maxHeight: '100px', overflowY: 'auto', fontSize: '11px', color: '#ccc',
                      background: '#0d0d1a', padding: '7px 9px', borderRadius: '6px',
                      whiteSpace: 'pre-wrap', wordBreak: 'break-word', marginBottom: '10px' });
    elPreview.textContent = '(aguardando primeiro chunk…)';

    var rowBtns = div({ display: 'flex', gap: '8px' });

    if (S.batchMode) {
      var btnSkip = btn('⏭ Pular Perfil', '#e67e22', function() {
        addLog('⏭ Pulado manualmente');
        stopRecording();
      });
      elStopBtn = btn('⏹ Parar Tudo', '#e74c3c', stopBatch);
      rowBtns.append(btnSkip, elStopBtn);
    } else {
      var btnInd = btn('🔴 Gravando…', '#8e44ad', function() {});
      btnInd.disabled = true;
      elStopBtn = btn('⏹ Parar', '#e74c3c', stopRecording);
      rowBtns.append(btnInd, elStopBtn);
    }

    var cfgPanel = buildConfigPanel();
    css(cfgPanel, { marginTop: '8px' });
    var btnCfg = btn('⚙️', '#3a3a5c', function() {
      cfgPanel.style.setProperty('display',
        cfgPanel.style.display === 'none' ? 'block' : 'none', 'important');
    });
    css(btnCfg, { flex: '0 0 auto' }); rowBtns.appendChild(btnCfg);

    elBody.append(elStatus, elRecInfo);
    if (S.batchMode) elBody.appendChild(elBatchProgress);
    elBody.append(lbLog, elLog, lbPrev, elPreview, rowBtns, cfgPanel);
    updateRecordingInfo();
  }

  function onRecordingFinished() {
    if (S.batchMode) { advanceBatch(); return; }
    setStatus('✅ Concluído. Arquivo salvo.');
    disableStopBtn();
    var btnNew = btn('↩ Nova transcrição', '#27ae60', showSetupPanel);
    css(btnNew, { width: '100%', marginTop: '10px', fontSize: '13px' });
    elBody.appendChild(btnNew);
  }

  function disableStopBtn() {
    if (elStopBtn) { elStopBtn.disabled = true; elStopBtn.style.opacity = '0.4'; }
  }

  /* ── Painel Config ───────────────────────────────────────── */
  function buildConfigPanel() {
    var p = div({ background: '#0d0d1a', border: '1px solid #3a3a5c', borderRadius: '6px', padding: '10px' });
    p.style.setProperty('display', 'none', 'important');

    var lbKey = div({ color: '#888', fontSize: '11px', marginBottom: '4px' });
    lbKey.textContent = 'Chave OpenAI (Whisper-1):';
    var inpKey = document.createElement('input');
    css(inpKey, { width: '100%', marginBottom: '8px' });
    inpKey.type = 'password'; inpKey.placeholder = 'sk-…';
    inpKey.value = GM_getValue('openai_key', '');
    inpKey.addEventListener('change', function() { GM_setValue('openai_key', inpKey.value.trim()); });

    var lbVis = div({ color: '#888', fontSize: '11px', marginBottom: '4px' });
    lbVis.textContent = Object.keys(S.visitedUrls).length + ' reels no histórico';

    var btnClear = btn('🗑️ Limpar histórico de URLs', '#5a3a3a', function() {
      clearVisited();
      lbVis.textContent = '0 reels no histórico';
    });
    css(btnClear, { width: '100%', fontSize: '11px', padding: '6px' });

    p.append(lbKey, inpKey, lbVis, btnClear);
    return p;
  }

  /* ── Atualização de UI ───────────────────────────────────── */
  function setStatus(msg) { if (elStatus) elStatus.textContent = msg; }

  function updateRecordingInfo() {
    if (!elRecInfo || !S.session) return;
    var n = S.session.segments.length;
    var date = S.session.reelDate ? ' | 📅 ' + S.session.reelDate.substring(0, 10) : '';
    elRecInfo.textContent = '@' + S.session.profile + '  |  ' + shortPath(S.session.url) + date + '  |  ' + n + ' seg.';
  }

  function updateBatchProgress() {
    if (!elBatchProgress) return;
    elBatchProgress.textContent = '📋 [' + (S.batchIdx+1) + '/' + S.batch.length + ']'
      + ' @' + S.profile
      + '  Rodada ' + (S.batchRound || 1)
      + '  |  ' + Object.keys(S.visitedUrls).length + ' mapeados';
  }

  function addLog(msg) {
    console.log('[IAT]', msg);
    if (!elLog) return;
    var ts   = new Date().toLocaleTimeString('pt-BR', { hour12: false });
    var line = div({ lineHeight: '1.4' });
    line.textContent = '[' + ts + '] ' + msg;
    if (msg.indexOf('📋') >= 0 || msg.indexOf('🔄') >= 0) line.style.color = '#e67e22';
    else if (msg.indexOf('✅') === 0) line.style.color = '#7dff7d';
    else if (msg.indexOf('❌') === 0) line.style.color = '#e74c3c';
    else if (msg.indexOf('⏭') === 0) line.style.color = '#f39c12';
    elLog.appendChild(line);
    elLog.scrollTop = elLog.scrollHeight;
  }

  function refreshPreview() {
    if (!elPreview || !S.session) return;
    var sorted = S.session.segments.slice().sort(function(a, b) { return a.t - b.t; });
    var lines  = sorted.slice(-20).map(function(s) { return '[' + fmtVidTime(s.t) + '] ' + s.text; });
    elPreview.textContent = lines.length ? lines.join('\n') : '(aguardando…)';
    elPreview.scrollTop   = elPreview.scrollHeight;
    updateRecordingInfo();
  }

  /* ── Drag ─────────────────────────────────────────────────── */
  window.addEventListener('mousemove', function(e) {
    if (!dragging) return;
    panel.style.right = 'auto'; panel.style.bottom = 'auto';
    panel.style.left  = (e.clientX - dragOX) + 'px';
    panel.style.top   = (e.clientY - dragOY) + 'px';
  });
  window.addEventListener('mouseup', function() { dragging = false; });

  /* ── Init ─────────────────────────────────────────────────── */
  loadVisited();
  initUrlWatcher();
  buildPanel();

  console.log('[IAT v3.8] Pronto. Reels no histórico:', Object.keys(S.visitedUrls).length);

})();
