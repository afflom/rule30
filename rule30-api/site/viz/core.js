/* The shared core of the visualizations (tools/r30/vizmodel.py declares
   them as panels of Presentation.lex.tex): Rule 30 computed in the browser
   from the one rule on BigInt rows, the notions of the register replicated
   from rule30-core-lean's definitions (center, rdiag and the tower, the
   exposed masks and their Lucas weights, trailingParity, rulerBackground,
   the carry ledgers, the row terms), the cross-check against the verified
   vectors (core-vectors.json, when the view carries them: the verified data
   wins), and the SVG and control helpers every panel uses. Plain
   JavaScript, no dependency, no network except the view's own vectors. */
(function () {
  "use strict";

  /* ---- the automaton: row t as a BigInt with bits 0..2t, bit i is the cell at position t - i ---- */
  var ROWS = [1n];
  var BITS = [];
  function rows(n) {
    // rows 0..n-1: row (t+1) = phi (row t), phi y = y XOR ((y << 1) OR (y << 2)) (Rule30UOR.Core.phi)
    while (ROWS.length < n) { var y = ROWS[ROWS.length - 1]; ROWS.push(y ^ ((y << 1n) | (y << 2n))); }
    return ROWS;
  }
  function bit(y, i) { return i < 0 ? 0 : Number((y >> BigInt(i)) & 1n); }
  function rowBits(t) {
    // row t as a byte array over positions -t..t (index p + t), cached
    if (BITS[t]) return BITS[t];
    var y = rows(t + 1)[t], s = y.toString(2), L = 2 * t + 1, out = new Uint8Array(L), off = L - s.length;
    // s is most significant first: bit i of y sits at s[s.length-1-i]; position p = t - i, index p + t = 2t - i
    for (var k = 0; k < s.length; k++) if (s.charCodeAt(k) === 49) out[off + k] = 1;
    BITS[t] = out;
    return out;
  }
  function cell(t, p) { if (t < 0 || p < -t || p > t) return 0; return rowBits(t)[p + t]; }
  function center(t) { return cell(t, 0); }
  // Rule30UOR.Core.rdiag j t = cell t (t - j): bit j of row t
  function rdiag(j, t) { return cell(t, t - j); }
  // the length the tower draws word j at: its period divides 2^(j-1) for j >= 2 (diagonal-halving); words 0 and 1 have periods 1 and 2
  function wordLength(j) { return j === 0 ? 1 : j === 1 ? 2 : Math.pow(2, j - 1); }
  function towerWord(j, s) { return rdiag(j, s % Math.pow(2, j)); } // towerWord j s = rdiag j (s mod twopow j)
  function word(j, len) { var L = len || wordLength(j), out = []; rows(L); for (var s = 0; s < L; s++) out.push(rdiag(j, s)); return out; }
  function cyclicPeriod(w) {
    for (var P = 1; P <= w.length; P++) {
      if (w.length % P) continue;
      var ok = true;
      for (var s = P; s < w.length && ok; s++) if (w[s] !== w[s - P]) ok = false;
      if (ok) return P;
    }
    return w.length;
  }
  // the tower rebuilt by its own recursion, rows j = 0..J over s < L, without the automaton:
  // rdiag 0 s = 1, rdiag 1 s = timeParity s, rdiag (j+1) 0 = 0,
  // rdiag (k+2) (s+1) = rdiag (k+2) s XOR (rdiag (k+1) s OR rdiag k s)
  function towerByRecursion(J, L) {
    var T = [];
    for (var j = 0; j <= J; j++) T.push(new Uint8Array(L));
    for (var s = 0; s < L; s++) { T[0][s] = 1; if (J >= 1) T[1][s] = s % 2; }
    for (j = 2; j <= J; j++) for (s = 0; s + 1 < L; s++) T[j][s + 1] = T[j][s] ^ (T[j - 1][s] | T[j - 2][s]);
    return T;
  }
  // the exposed mask (Rule30UOR.Antidiagonal.exposed): word k showing through word k+1, a black cell whose left neighbour is white
  function exposed(k, i) { return rdiag(k, i) & (1 - rdiag(k + 1, i)); }
  // C(n, k) mod 2 by Lucas: odd exactly when the binary digits of k are under those of n
  function pascal(n, k) { return n >= 0 && k >= 0 && (n & k) === k ? 1 : 0; }
  // the Lucas frame of the center (center_eq_lucas): center t = not lucasSum (t-2) t,
  // lucasSum (t-2) t = XOR over i <= t-2, j < t of C(t-1-j, t-2-i) AND exposed i j
  function lucasFrame(t) {
    var cells = [], x = 0;
    if (t < 2) return { cells: cells, sum: 0, center: center(t) };
    rows(t + 1);
    for (var i = 0; i <= t - 2; i++) for (var j = 0; j < t; j++) {
      var w = pascal(t - 1 - j, t - 2 - i), e = exposed(i, j);
      if (w && e) { cells.push([i, j]); x ^= 1; }
    }
    return { cells: cells, sum: x, center: 1 - x };
  }
  // the mask transport (maskTransport k s), by its recursion, for k <= K and s <= S
  function maskTransport(K, S) {
    rows(S + 2);
    var M = [], k, s;
    for (k = 0; k <= K; k++) {
      var row = new Uint8Array(S + 1), prev = M[k - 1];
      var a = 0, b = 0;
      for (s = 0; s <= S; s++) {
        row[s] = (k === 0 ? 0 : a) ^ b;
        if (k > 0) a ^= prev[s];
        b ^= exposed(k, s);
      }
      M.push(row);
    }
    return M;
  }

  /* ---- the rulers (Rule30UOR.Ledger.trailingParity, EdgeParity.timeParity, LeftBand.rulerBackground) ---- */
  function trailingParity(t) { var c = 0; while (t % 2 === 1) { c++; t = Math.floor(t / 2); } return c % 2; }
  function timeParity(t) { return t % 2 === 1 ? 1 : 0; }
  function nsub(a, b) { return a > b ? a - b : 0; } // Nat subtraction truncates
  function rulerTerms(t) {
    // the four rulers of rulerBackground t, in the order of its definition
    return [trailingParity(nsub(t, 2)), 1 - timeParity(t), trailingParity(nsub(t, 4)), trailingParity(Math.floor(nsub(t, 4) / 2))];
  }
  function rulerBackground(t) { var r = rulerTerms(t); return r[0] ^ r[1] ^ r[2] ^ r[3]; }

  /* ---- the carry ledgers (Rule30UOR.Core.carry/phiLinear, EdgeSplit.interior, Band, LeftBand) ---- */
  function carry(y) { return y & (y << 1n); }
  function phiLinear(y) { return y ^ (y << 1n) ^ (y << 2n); }
  function phiLinearPow(n, y) { for (var i = 0; i < n; i++) y = phiLinear(y); return y; }
  function edgeSource(t) { return (1n << BigInt(2 * t)) ^ (rdiag(1, t) ? 2n : 0n); }
  function interior(m) { return carry(rows(m + 1)[m]) ^ edgeSource(m); }
  function lowSource(m) { return m === 0 ? 1n : (m >= 2 && m % 2 === 1) ? 4n : 0n; }
  function leftBandSource(m) { return m === 3 ? 8n : (m >= 5 && m % 2 === 1) ? (7n << BigInt(2 * m - 5)) : 0n; }
  function interiorThree(m) { return interior(m) ^ lowSource(m); }
  function interiorEight(m) { return interiorThree(m) ^ leftBandSource(m); }
  function ledgerDiagonal(source, n) {
    // L 0 = 0, L (t+1) = phiLinear (L t) XOR (source t << 1); the diagonal is bit t of L t, for t < n
    var L = 0n, out = [];
    for (var t = 0; t < n; t++) { out.push(bit(L, t)); L = phiLinear(L) ^ (source(t) << 1n); }
    return out;
  }
  function ledger(source, n) {
    var L = 0n;
    for (var t = 0; t < n; t++) L = phiLinear(L) ^ (source(t) << 1n);
    return L;
  }
  function rowTerm(t, m) { return bit(phiLinearPow(t - 1 - m, interior(m) << 1n), t); } // DyadicRow.rowTerm
  function xorBelow(f, n) { var x = 0; for (var i = 0; i < n; i++) x ^= f(i); return x; }

  /* ---- the cross-check ---- */
  // the verified vectors: core-vectors.json (centers, towerWords, rulerBackground) carried by the
  // view data, or fetched beside the page when the view lists the artifact; null when absent
  var VECTORS = null;
  function vectors(d) {
    if (VECTORS) return Promise.resolve(VECTORS);
    var v = d && (d.coreVectors || d["core-vectors"] || d.vectors);
    if (v && v.centers) { VECTORS = v; return Promise.resolve(v); }
    var a = ((d && d.artifacts) || []).filter(function (x) { return x.id === "core-vectors"; })[0];
    if (!a || typeof fetch !== "function" || location.protocol === "file:") return Promise.resolve(null);
    return fetch(a.path).then(function (r) { return r.ok ? r.json() : null; }).then(function (j) { VECTORS = j && j.centers ? j : null; return VECTORS; })
      .catch(function () { return null; });
  }
  // compare the browser's values with the verified ones; the mismatches name the cells
  function compare(v) {
    var bad = [];
    (v.centers || []).forEach(function (b, t) { if (center(t) !== +b) bad.push("center " + t); });
    (v.towerWords || []).forEach(function (w, j) { w.forEach(function (b, s) { if (rdiag(j, s) !== +b) bad.push("towerWord " + j + " " + s); }); });
    (v.rulerBackground || []).forEach(function (b, t) { if (rulerBackground(t) !== +b) bad.push("rulerBackground " + t); });
    return bad;
  }
  // the independent replay always available: the tower by its recursion against the rows
  function selfCheck() {
    var J = 10, L = 512, T = towerByRecursion(J, L), bad = [];
    rows(L);
    for (var j = 0; j <= J; j++) for (var s = 0; s < L; s++) if (T[j][s] !== rdiag(j, s)) { bad.push("rdiag " + j + " " + s); if (bad.length > 8) return bad; }
    return bad;
  }
  // the verified value of a center, when the vectors carry it (it wins over the browser's)
  function verifiedCenter(t) { return VECTORS && VECTORS.centers && t < VECTORS.centers.length ? +VECTORS.centers[t] : null; }
  function checkNotice(d, onVectors) {
    var p = el("p", { "class": "viz-check", role: "status" });
    var own = selfCheck();
    var base = own.length ? "The tower rebuilt by its recursion disagrees with the rows at " + own.slice(0, 6).join(", ") + "."
                          : "Replayed: words 0 to 10 of the tower rebuilt by their recursion equal the rows' diagonals for the first 512 times.";
    p.textContent = base + " Looking for the verified vectors (core-vectors.json)…";
    if (own.length) p.className += " bad";
    vectors(d).then(function (v) {
      if (!v) { p.textContent = base + " This view carries no verified vectors, so the values shown are computed in the browser only."; return; }
      var bad = compare(v);
      if (bad.length) {
        p.className = "viz-check bad";
        p.textContent = base + " The browser's computation disagrees with the verified vectors at " + bad.slice(0, 8).join(", ") + (bad.length > 8 ? " and " + (bad.length - 8) + " more" : "") + "; where they are shown the verified values win.";
      } else {
        p.textContent = base + " Cross-checked against the verified vectors: " + (v.centers || []).length + " centers, " + (v.towerWords || []).length + " tower words and " + (v.rulerBackground || []).length + " ruler values agree" + (v.module ? " (" + v.module + ")" : "") + ".";
      }
      if (onVectors) onVectors(v, bad);
    });
    return p;
  }

  /* ---- DOM and SVG helpers ---- */
  var SVGNS = "http://www.w3.org/2000/svg";
  function el(tag, attrs, children) {
    var e = document.createElement(tag);
    Object.keys(attrs || {}).forEach(function (k) { if (k === "text") e.textContent = attrs[k]; else if (k === "html") e.innerHTML = attrs[k]; else e.setAttribute(k, attrs[k]); });
    (children || []).forEach(function (c) { e.appendChild(typeof c === "string" ? document.createTextNode(c) : c); });
    return e;
  }
  function svg(tag, attrs) {
    var e = document.createElementNS(SVGNS, tag);
    Object.keys(attrs || {}).forEach(function (k) { if (k === "text") e.textContent = attrs[k]; else e.setAttribute(k, attrs[k]); });
    return e;
  }
  function uid() { uid.n = (uid.n || 0) + 1; return "viz" + uid.n; }
  // an SVG graphics document (WAI-ARIA Graphics) with its title and description as its name and description
  // maxPx caps the drawn width of a small picture, so a few cells are not blown up to the page's width
  function picture(id, w, h, title, desc, maxPx) {
    var u = id + "-" + uid();
    var s = svg("svg", { viewBox: "0 0 " + w + " " + h, role: "graphics-document", "aria-roledescription": "visualization",
                         "aria-labelledby": u + "-t", "aria-describedby": u + "-d", "shape-rendering": "crispEdges", preserveAspectRatio: "xMidYMin meet" });
    s.appendChild(svg("title", { id: u + "-t", text: title }));
    s.appendChild(svg("desc", { id: u + "-d", text: desc }));
    if (maxPx) s.style.maxWidth = Math.round(maxPx) + "px";
    s.uid = u;
    return s;
  }
  // a mark the description names (WAI-ARIA Graphics: graphics-symbol with a label)
  function symbol(node, label) { node.setAttribute("role", "graphics-symbol"); node.setAttribute("aria-label", label); return node; }
  function runsPath(cells) {
    // cells: [x, y] unit squares; one path of horizontal runs per row
    var byRow = {};
    cells.forEach(function (c) { (byRow[c[1]] = byRow[c[1]] || []).push(c[0]); });
    var d = "";
    Object.keys(byRow).forEach(function (y) {
      var xs = byRow[y].sort(function (a, b) { return a - b; });
      var i = 0;
      while (i < xs.length) { var j = i; while (j + 1 < xs.length && xs[j + 1] === xs[j] + 1) j++; d += "M" + xs[i] + " " + y + "h" + (xs[j] - xs[i] + 1) + "v1h-" + (xs[j] - xs[i] + 1) + "z"; i = j + 1; }
    });
    return d;
  }
  function reducedMotion() { try { return matchMedia("(prefers-reduced-motion: reduce)").matches; } catch (e) { return false; } }

  /* colour plus pattern: every categorical colour comes with its own hatch, so no reading depends on colour alone */
  var PALETTE = ["#d6604d", "#4393c3", "#5aae61", "#e08214", "#8073ac", "#35978f", "#c51b7d", "#878787", "#b8860b", "#1b9e77", "#9e0142", "#3288bd"];
  function colour(i) { return "var(--viz-" + ((i % PALETTE.length) + 1) + ", " + PALETTE[i % PALETTE.length] + ")"; }
  var HATCH = ["M0 4L4 0", "M0 0L4 4", "M0 2H4", "M2 0V4", "M0 4L4 0M0 0L4 4", "M0 2H4M2 0V4", "M1 1h1v1h-1z", "M0 3L3 0M1 4L4 1"];
  function patterns(s, count) {
    // <pattern> per index: the colour as a ground, the hatch over it in the ink; returns url(#…) fills
    var defs = svg("defs", {}), out = [];
    for (var i = 0; i < count; i++) {
      var id = s.uid + "-p" + i, p = svg("pattern", { id: id, width: 4, height: 4, patternUnits: "userSpaceOnUse", patternTransform: "scale(0.25)" });
      p.appendChild(svg("rect", { width: 4, height: 4, fill: colour(i) }));
      p.appendChild(svg("path", { d: HATCH[i % HATCH.length], stroke: "var(--viz-hatch, rgba(20,22,26,.55))", "stroke-width": 0.7, fill: "none" }));
      defs.appendChild(p);
      out.push("url(#" + id + ")");
    }
    s.appendChild(defs);
    return out;
  }
  function swatch(i) {
    // a legend swatch: the colour and the same hatch, as a small inline SVG
    var s = svg("svg", { "class": "sw", viewBox: "0 0 4 4", width: 14, height: 14, "aria-hidden": "true", focusable: "false" });
    s.appendChild(svg("rect", { width: 4, height: 4, fill: colour(i) }));
    s.appendChild(svg("path", { d: HATCH[i % HATCH.length], stroke: "rgba(20,22,26,.55)", "stroke-width": 0.5, fill: "none" }));
    return s;
  }
  function solid(fill) { return el("span", { "class": "sw", style: "background:" + fill, "aria-hidden": "true" }); }

  /* controls: a labelled range paired with a number field, a toggle button with aria-pressed */
  function range(label, min, max, value, step, onChange) {
    var id = uid(), st = step || 1;
    var input = el("input", { type: "range", id: id, min: min, max: max, value: value, step: st });
    var num = el("input", { type: "number", min: min, max: max, value: value, step: st, "aria-label": label + " (exact value)" });
    var wrap = el("span", { "class": "viz-range" }, [el("label", { "for": id, text: label }), input, num]);
    var fire = function (v) {
      var lo = Number(input.min), hi = Number(input.max);
      v = Math.max(lo, Math.min(hi, Math.round(Number(v) / st) * st)); if (isNaN(v)) v = lo;
      input.value = v; num.value = v; onChange(v);
    };
    input.addEventListener("input", function () { fire(input.value); });
    num.addEventListener("change", function () { fire(num.value); });
    wrap.set = function (v) { input.value = v; num.value = v; };
    wrap.setMax = function (m) { input.max = m; num.max = m; };
    return wrap;
  }
  function toggle(label, pressed, onChange, extra) {
    var b = el("button", { type: "button", "class": "viz-toggle", "aria-pressed": String(!!pressed) });
    if (label) b.appendChild(document.createTextNode(label));
    Object.keys(extra || {}).forEach(function (k) { b.setAttribute(k, extra[k]); });
    b.addEventListener("click", function () { var on = b.getAttribute("aria-pressed") !== "true"; b.setAttribute("aria-pressed", String(on)); onChange(on); });
    return b;
  }
  function button(label, onClick, extra) {
    var b = el("button", { type: "button", "class": "viz-toggle", text: label });
    Object.keys(extra || {}).forEach(function (k) { b.setAttribute(k, extra[k]); });
    b.addEventListener("click", onClick);
    return b;
  }
  function group(label, children) {
    var id = uid();
    return el("span", { "class": "viz-group", role: "group", "aria-labelledby": id }, [el("span", { "class": "viz-label", id: id, text: label })].concat(children || []));
  }
  // a focusable stage: arrow keys move a cursor, the readout (a polite live region) says what is under it
  function stage(label) { return el("div", { "class": "viz-stage", tabindex: "0", role: "group", "aria-roledescription": "explorable picture", "aria-label": label }); }
  function keys(node, moves) {
    node.addEventListener("keydown", function (e) {
      var f = moves[e.key];
      if (!f || e.altKey || e.ctrlKey || e.metaKey) return;
      e.preventDefault(); e.stopPropagation();
      f(e);
    });
  }
  function bits(xs) { return Array.prototype.map.call(xs, function (b) { return b ? "1" : "0"; }).join(""); }
  // a <details> with the numbers a picture shows, for every reader who prefers them
  function dataTable(caption, head, rowsData) {
    var t = el("table", {}, [el("caption", { text: caption })]);
    var tr = el("tr");
    head.forEach(function (h) { tr.appendChild(el("th", { scope: "col", text: h })); });
    t.appendChild(el("thead", {}, [tr]));
    var tb = el("tbody");
    rowsData.forEach(function (r) { var row = el("tr"); r.forEach(function (c, i) { row.appendChild(el(i === 0 ? "th" : "td", i === 0 ? { scope: "row", text: String(c) } : { text: String(c) })); }); tb.appendChild(row); });
    t.appendChild(tb);
    return el("div", { "class": "viz-table" }, [t]);
  }

  var STYLE = [
    ".viz{margin:0 0 6px;--viz-ink:var(--ink,#14161a);--viz-bg:var(--panel,#fbfaf6);--viz-line:var(--line,#d9d4c7);--viz-soft:var(--soft,#ebe7dc);--viz-accent:var(--accent,#b97d0c);--viz-focus:var(--focus,#1f5f8b);--viz-muted:var(--muted,#5c6066)}",
    ".viz svg[role=graphics-document]{display:block;width:100%;height:auto;max-height:78vh;background:var(--viz-bg);border:1px solid var(--viz-line);border-radius:var(--radius,12px)}",
    ".viz-controls{display:flex;gap:10px 18px;flex-wrap:wrap;align-items:center;margin:0 0 12px;font-size:.9rem}",
    ".viz-range{display:inline-flex;gap:8px;align-items:center}.viz-range label{font-weight:600}.viz-range input[type=range]{width:160px;max-width:40vw;accent-color:var(--viz-accent)}",
    ".viz-range input[type=number]{width:5.5em;border:1px solid var(--viz-line);background:var(--viz-bg);color:var(--viz-ink);border-radius:6px;padding:3px 6px;font:inherit}",
    ".viz-toggle{background:var(--viz-bg);border:1px solid var(--viz-line);color:var(--viz-ink);border-radius:999px;padding:4px 12px;min-height:28px;font:inherit;font-size:.84rem;cursor:pointer;display:inline-flex;align-items:center;gap:.35em}",
    ".viz-toggle[aria-pressed=true]{border-color:var(--viz-accent);background:var(--open-bg,#fbefd3);box-shadow:inset 0 0 0 1px var(--viz-accent)}.viz-toggle:hover{border-color:var(--viz-accent)}",
    ".viz .sw{display:inline-block;width:.9em;height:.9em;border-radius:2px;vertical-align:-.1em;border:1px solid var(--viz-line);flex:none}",
    ".viz-group{display:inline-flex;gap:6px;flex-wrap:wrap;align-items:center}.viz-label{font-weight:600}",
    ".viz-readout{font-family:var(--mono,ui-monospace,monospace);font-size:.86rem;min-height:1.5em;margin:10px 0 0;color:var(--viz-ink);background:var(--viz-soft);border-radius:8px;padding:6px 10px}",
    ".viz-summary{color:var(--viz-muted);font-size:.9rem;margin:10px 0 0;max-width:72ch;line-height:1.5}",
    ".viz-check{border-radius:10px;padding:8px 12px;margin:10px 0 0;font-size:.86rem;background:var(--proved-bg,#ddf1e3);color:var(--proved,#256a41)}.viz-check.bad{background:var(--refuted-bg,#f9dfdc);color:var(--refuted,#a8302a)}",
    ".viz-stage{outline:none;border-radius:var(--radius,12px)}.viz-stage:focus-visible{outline:3px solid var(--viz-focus);outline-offset:3px}",
    ".viz button:focus-visible,.viz input:focus-visible,.viz summary:focus-visible{outline:3px solid var(--viz-focus);outline-offset:2px}",
    ".viz-table{overflow-x:auto;margin:10px 0 0}.viz table{font-size:.84rem;border-collapse:collapse}.viz caption{text-align:left;color:var(--viz-muted);padding:0 0 4px}",
    ".viz th,.viz td{padding:3px 8px;border-bottom:1px solid var(--viz-line);font-family:var(--mono,ui-monospace,monospace);text-align:center;white-space:nowrap}.viz td.strip{text-align:left}",
    ".viz td.ok{color:var(--proved,#256a41)}.viz td.no{color:var(--refuted,#a8302a);font-weight:700}.viz tr.hl{background:var(--open-bg,#fbefd3)}",
    ".viz .strip{font-family:var(--mono,ui-monospace,monospace);font-size:.8rem;word-break:break-all;letter-spacing:.04em}.viz .strip b{color:var(--viz-accent)}",
    ".viz-legend{display:flex;gap:6px 14px;flex-wrap:wrap;color:var(--viz-muted);font-size:.82rem;margin:8px 0 0;padding:0;list-style:none}.viz-legend li{display:inline-flex;gap:.35em;align-items:center}",
    ".viz details{margin:10px 0 0}.viz summary{cursor:pointer;color:var(--link,#1f5f8b);font-size:.9rem}",
    "@media (prefers-reduced-motion:reduce){.viz *{transition:none!important;animation:none!important}}",
    "@media (forced-colors:active){.viz-toggle[aria-pressed=true]{outline:2px solid CanvasText}}"
  ].join("\n");
  function ensureStyle() {
    if (document.getElementById("viz-style")) return;
    var s = document.createElement("style"); s.id = "viz-style"; s.textContent = STYLE; document.head.appendChild(s);
  }
  function legend(items) {
    // items: [swatch node, text]
    var ul = el("ul", { "class": "viz-legend", "aria-label": "Legend" });
    items.forEach(function (it) { ul.appendChild(el("li", {}, [it[0], it[1]])); });
    return ul;
  }
  // the frame every panel uses: controls, stage, readout, legend, summary, table, notice
  function frame(slot) {
    ensureStyle();
    slot.innerHTML = "";
    var root = el("div", { "class": "viz" });
    slot.appendChild(root);
    return root;
  }

  window.r30core = {
    rows: rows, bit: bit, rowBits: rowBits, cell: cell, center: center, rdiag: rdiag, wordLength: wordLength, towerWord: towerWord,
    word: word, cyclicPeriod: cyclicPeriod, towerByRecursion: towerByRecursion, exposed: exposed, pascal: pascal, lucasFrame: lucasFrame,
    maskTransport: maskTransport,
    trailingParity: trailingParity, timeParity: timeParity, nsub: nsub, rulerTerms: rulerTerms, rulerBackground: rulerBackground,
    carry: carry, phiLinear: phiLinear, phiLinearPow: phiLinearPow, edgeSource: edgeSource, interior: interior, lowSource: lowSource,
    leftBandSource: leftBandSource, interiorThree: interiorThree, interiorEight: interiorEight, ledgerDiagonal: ledgerDiagonal, ledger: ledger,
    rowTerm: rowTerm, xorBelow: xorBelow,
    vectors: vectors, compare: compare, selfCheck: selfCheck, verifiedCenter: verifiedCenter, checkNotice: checkNotice,
    el: el, svg: svg, picture: picture, symbol: symbol, runsPath: runsPath, uid: uid, reducedMotion: reducedMotion,
    colour: colour, patterns: patterns, swatch: swatch, solid: solid, range: range, toggle: toggle, button: button, group: group,
    stage: stage, keys: keys, bits: bits, dataTable: dataTable, legend: legend, frame: frame, ensureStyle: ensureStyle
  };
  window.r30viz = window.r30viz || {};
})();
