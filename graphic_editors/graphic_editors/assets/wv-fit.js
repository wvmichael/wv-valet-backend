/* WeatherValet graphic auto-fit (July 24, 2026).
   Keeps every graphic inside its 1600x900 canvas no matter what a
   Meteorologist types. Three passes:
   1. Grid and flex children get min-width 0 so long text cannot force
      a card row past the canvas edge.
   2. Any big text wider than its own box shrinks until it fits, and
      never breaks mid-word.
   3. Any block still crossing the canvas edge (right or bottom) has all
      text inside it shrunk step by step until the block fits.
   Runs on load and after every edit. */
(function () {
  function findStage() {
    var all = document.querySelectorAll("*");
    for (var i = 0; i < all.length; i++) {
      var cs = getComputedStyle(all[i]);
      if (cs.width === "1600px" && cs.height === "900px") return all[i];
    }
    return null;
  }

  function leaves(root) {
    var out = [];
    var els = root.querySelectorAll("*");
    for (var i = 0; i < els.length; i++) {
      var el = els[i];
      if (el.children.length) continue;
      if (!el.textContent || !el.textContent.trim()) continue;
      out.push(el);
    }
    if (!out.length && root.textContent && root.textContent.trim()) out.push(root);
    return out;
  }

  function currentSize(el) {
    return parseFloat(el.style.fontSize) ||
           parseFloat(getComputedStyle(el).fontSize);
  }

  function fitAll() {
    var st = findStage();
    if (!st) return;
    var sr = st.getBoundingClientRect();
    var sx = sr.width / 1600, sy = sr.height / 900;
    var els = st.querySelectorAll("*");
    var i, el;

    /* pass 1: stop grid and flex blowouts */
    for (i = 0; i < els.length; i++) {
      el = els[i];
      var pd = el.parentElement ? getComputedStyle(el.parentElement).display : "";
      if (pd === "grid" || pd === "flex" || pd === "inline-grid" || pd === "inline-flex") {
        el.style.minWidth = "0";
      }
    }

    /* pass 2: per-element horizontal fit, restore first so text can grow back */
    for (i = 0; i < els.length; i++) {
      el = els[i];
      if (el.children.length) continue;
      if (!el.textContent || !el.textContent.trim()) continue;
      if (el.clientWidth === 0) continue;
      var base = parseFloat(el.dataset.wvFs || "0");
      if (!base) {
        base = parseFloat(getComputedStyle(el).fontSize);
        if (base < 26) continue;
        el.dataset.wvFs = base;
      }
      el.style.wordBreak = "normal";
      el.style.overflowWrap = "normal";
      var size = base;
      el.style.fontSize = size + "px";
      var guard = 0;
      while (el.scrollWidth > el.clientWidth + 2 && size > 16 && guard < 60) {
        size -= 2;
        el.style.fontSize = size + "px";
        guard++;
      }
    }

    /* pass 3: shrink whole blocks that still cross the canvas edge */
    var blocks = [];
    for (i = 0; i < st.children.length; i++) blocks.push(st.children[i]);
    for (i = 0; i < els.length; i++) {
      el = els[i];
      var cs = getComputedStyle(el);
      if ((cs.position === "absolute" || cs.position === "fixed") &&
          blocks.indexOf(el) === -1) blocks.push(el);
    }
    for (i = 0; i < blocks.length; i++) {
      var block = blocks[i];
      var guard2 = 0;
      while (guard2 < 45) {
        var r = block.getBoundingClientRect();
        if (r.width === 0 || r.height === 0) break;
        var right = (r.right - sr.left) / sx;
        var bottom = (r.bottom - sr.top) / sy;
        if (right <= 1602 && bottom <= 902) break;
        var lv = leaves(block), shrunk = false, j;
        for (j = 0; j < lv.length; j++) {
          var s2 = currentSize(lv[j]);
          if (s2 > 13) {
            lv[j].style.fontSize = (s2 - 1) + "px";
            shrunk = true;
          }
        }
        if (!shrunk) {
          block.style.overflow = "hidden";
          break;
        }
        guard2++;
      }
    }
  }

  document.addEventListener("input", function () {
    requestAnimationFrame(fitAll);
  });
  window.addEventListener("load", fitAll);
  setTimeout(fitAll, 400);
  window.wvFitAll = fitAll;
})();
