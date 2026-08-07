/* ── WeatherValet branding kit JS (Aug 1, 2026) ──
   Rebuilds each editor's .footer into the branded band while preserving
   every element that carries an id (moved to a hidden holding pen, so
   sidebar input bindings never break). Editors without a .footer are
   left alone except for the palette and date banner from wv-brand.css. */
(function () {
  function brand() {
    var canvas = document.getElementById('canvas');
    if (!canvas) return;
    var footer = canvas.querySelector('.footer');
    if (!footer || footer.classList.contains('wv-branded')) return;

    // Preserve the current "updated" time text if the editor has one.
    var updatedEl = footer.querySelector('#updated');
    var updatedText = updatedEl ? updatedEl.textContent.trim() : '';

    // Move every id-carrying element into a hidden pen so input bindings
    // still find their targets after the rebuild.
    var pen = document.createElement('div');
    pen.className = 'wv-orphans';
    footer.querySelectorAll('[id]').forEach(function (el) { pen.appendChild(el); });
    canvas.appendChild(pen);

    footer.innerHTML =
      '<div class="wv-feat"><div class="ic">&#127919;</div><div>' +
      '<div class="l1">Local Experts.</div><div class="l2">Precise Forecasts.</div></div></div>' +
      '<div class="wv-feat"><div class="ic">&#128737;&#65039;</div><div>' +
      '<div class="l1">Stay Aware.</div><div class="l2">Stay Prepared.</div></div></div>' +
      '<div class="wv-feat"><div class="ic">&#128172;</div><div>' +
      '<div class="l1">Real-Time Updates</div><div class="l2">24/7 Coverage</div></div></div>' +
      '<div class="wv-sitebox"><div class="site">WEATHERVALET.COM</div>' +
      '<div class="upd">Last Updated: <span class="wv-updated-mirror"></span></div></div>';
    footer.classList.add('wv-branded');

    // Mirror the (hidden) updated field live so edits still show on canvas.
    var mirror = footer.querySelector('.wv-updated-mirror');
    function sync() {
      var src = document.getElementById('updated');
      mirror.textContent = (src && src.textContent.trim()) || updatedText ||
        new Date().toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' });
    }
    sync();
    var src = document.getElementById('updated');
    if (src) new MutationObserver(sync).observe(src, { childList: true, characterData: true, subtree: true });
  }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', brand);
  } else { brand(); }
})();


/* ── Spellcheck for editor fields (Aug 2, 2026, Mets' request) ──
   Native browser spellcheck on prose fields; endpoint/coordinate-style
   inputs excluded by keyword. Covers all 29 editors via this shared kit. */
(function () {
  var SKIP = /endpoint|url|email|gps|coord|token|slug/i;
  function apply(el) {
    if (el.tagName === 'TEXTAREA' || el.isContentEditable) {
      el.setAttribute('spellcheck', 'true');
    } else if (el.tagName === 'INPUT') {
      var type = (el.getAttribute('type') || 'text').toLowerCase();
      if (type !== 'text' && type !== '') return;
      if (SKIP.test((el.id || '') + (el.name || '') + (el.placeholder || ''))) return;
      el.setAttribute('spellcheck', 'true');
    }
  }
  function boot() {
    var els = document.querySelectorAll('textarea, input, [contenteditable]');
    for (var i = 0; i < els.length; i++) apply(els[i]);
  }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else { boot(); }
})();
