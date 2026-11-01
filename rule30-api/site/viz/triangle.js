/* viz-triangle: Rule 30 from a single black cell, rows 0..N-1 (N up to
   256), computed in the browser. The keyboard moves a cursor and the
   readout says (t, position, bit); the center column is highlighted; the
   right diagonals rdiag j (the cells at position t - j) are switched on one
   by one, each filled with the colour and hatch of its measured period,
   which divides 2^(j-1) (diagonal-halving). The center cell of row t is
   the cell of diagonal t at time t (antidiagonal), and diagonal 1 is the
   time parity the edge carries contribute (edge-parity). */
(function () {
  "use strict";
  var C = window.r30core;
  var MAX_DIAG = 12;

  window.r30viz["viz-triangle"] = function (slot, d) {
    var root = C.frame(slot);
    var state = { n: 64, center: true, diags: { 1: true, 2: true, 3: true }, cursor: { t: 12, p: 0 } };
    var periods = {}, bound = {};
    for (var j = 1; j <= MAX_DIAG; j++) { periods[j] = C.cyclicPeriod(C.word(j, Math.pow(2, j))); bound[j] = C.wordLength(j); }
    function periodClass(j) { return Math.round(Math.log2(periods[j])); }

    var controls = C.el("div", { "class": "viz-controls" });
    var stage = C.stage("Rule 30 triangle. Arrow keys move the cursor one cell; Page Up and Page Down move sixteen rows; Home and End go to the first and the last row; C jumps to the center column. The readout below says what the cursor is on.");
    var readout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var legendSlot = C.el("div");
    var summary = C.el("p", { "class": "viz-summary" });
    var details = C.el("details");
    var svgEl = null;

    controls.appendChild(C.range("Rows N", 8, 256, state.n, 8, function (v) { state.n = v; clampCursor(); draw(); }));
    controls.appendChild(C.toggle("Center column", true, function (on) { state.center = on; draw(); }));
    var buttons = [];
    for (j = 1; j <= MAX_DIAG; j++) {
      (function (jj) {
        var b = C.toggle("", !!state.diags[jj], function (on) { state.diags[jj] = on; draw(); },
                         { "aria-label": "Diagonal rdiag " + jj + ", period " + periods[jj] + " (divides 2^" + (jj - 1) + " = " + bound[jj] + ")" });
        b.appendChild(C.swatch(periodClass(jj)));
        b.appendChild(document.createTextNode("j=" + jj));
        buttons.push(b);
      })(j);
    }
    controls.appendChild(C.group("Right diagonals:", buttons));
    controls.appendChild(C.button("All diagonals", function () { for (var k = 1; k <= MAX_DIAG; k++) { state.diags[k] = true; buttons[k - 1].setAttribute("aria-pressed", "true"); } draw(); }));
    controls.appendChild(C.button("None", function () { for (var k = 1; k <= MAX_DIAG; k++) { state.diags[k] = false; buttons[k - 1].setAttribute("aria-pressed", "false"); } draw(); }));

    function clampCursor() {
      var c = state.cursor;
      c.t = Math.max(0, Math.min(state.n - 1, c.t));
      c.p = Math.max(-c.t, Math.min(c.t, c.p));
    }
    function shown() { return Object.keys(state.diags).filter(function (k) { return state.diags[k]; }).map(Number).sort(function (a, b) { return a - b; }); }
    function describe() {
      var c = state.cursor, b = C.cell(c.t, c.p), j = c.t - c.p;
      var s = "t = " + c.t + ", position " + (c.p > 0 ? "+" : "") + c.p + ", bit " + b + (b ? " (black)" : " (white)");
      s += "; on the right diagonal rdiag " + j + (j >= 1 && j <= MAX_DIAG ? " (period " + periods[j] + ")" : "");
      if (c.p === 0) {
        var v = C.verifiedCenter(c.t);
        s += "; the center column: center " + c.t + " = rdiag " + c.t + " at time " + c.t + " (the anti-diagonal)";
        if (v !== null) s += v === b ? ", agreeing with the verified vectors" : ", but the verified value is " + v + " and it wins";
      }
      readout.textContent = s;
    }
    function draw() {
      var n = state.n, W = 2 * n - 1, H = n;
      C.rows(n);
      var ink = [], amber = [], black = 0;
      for (var t = 0; t < n; t++) {
        var off = n - 1 - t, r = C.rowBits(t);
        for (var i = 0; i <= 2 * t; i++) {
          if (!r[i]) continue;
          black++;
          if (state.center && i === t) amber.push([off + i, t]); else ink.push([off + i, t]);
        }
      }
      var js = shown();
      var title = "Rule 30, rows 0 to " + (n - 1);
      var desc = "Rows 0 to " + (n - 1) + " of Rule 30 from a single black cell: " + black + " black cells. " +
        (state.center ? "The center column is highlighted; its first bits read " + C.bits(Array.from({ length: Math.min(n, 48) }, function (_, k) { return C.center(k); })) + ". " : "") +
        (js.length ? "Coloured right diagonals: " + js.map(function (k) { return "rdiag " + k + " with period " + periods[k]; }).join(", ") + "." : "No diagonal is coloured.");
      var s = C.picture("tri", W, H, title, desc);
      var fills = C.patterns(s, 8);
      if (state.center) s.appendChild(C.symbol(C.svg("rect", { x: n - 1, y: 0, width: 1, height: H, fill: "var(--viz-accent)", opacity: "0.18" }), "the center column"));
      s.appendChild(C.svg("path", { d: C.runsPath(ink), fill: "var(--viz-ink)" }));
      if (amber.length) s.appendChild(C.svg("path", { d: C.runsPath(amber), fill: "var(--viz-accent)" }));
      // the diagonals over the cells: a black cell shows dark through its diagonal's colour and hatch
      js.forEach(function (k) {
        var cells = [];
        for (var tt = Math.ceil(k / 2); tt < n; tt++) cells.push([n - 1 + tt - k, tt]);
        var path = C.svg("path", { d: C.runsPath(cells), fill: fills[periodClass(k)], opacity: "0.62" });
        s.appendChild(C.symbol(path, "rdiag " + k + ", period " + periods[k]));
      });
      var c = state.cursor;
      var cur = C.svg("rect", { "data-cursor": "1", x: n - 1 + c.p, y: c.t, width: 1, height: 1, fill: "none", stroke: "var(--viz-focus)", "stroke-width": Math.max(0.25, n / 160), "pointer-events": "none" });
      s.appendChild(C.symbol(cur, "cursor"));
      s.addEventListener("pointermove", function (e) {
        var r = s.getBoundingClientRect();
        if (!r.width) return;
        var tt = Math.floor((e.clientY - r.top) / r.height * H), pp = Math.floor((e.clientX - r.left) / r.width * W) - (n - 1);
        if (tt < 0 || tt >= n || Math.abs(pp) > tt || (tt === state.cursor.t && pp === state.cursor.p)) return;
        state.cursor = { t: tt, p: pp };
        moveCursor();
      });
      if (svgEl) stage.replaceChild(s, svgEl); else stage.appendChild(s);
      svgEl = s;
      var items = [[C.solid("var(--viz-ink)"), "black cell"]];
      if (state.center) items.push([C.solid("var(--viz-accent)"), "center column: the cell where row t meets diagonal t"]);
      var classes = {};
      js.forEach(function (k) { (classes[periodClass(k)] = classes[periodClass(k)] || []).push(k); });
      Object.keys(classes).forEach(function (pc) { items.push([C.swatch(+pc), "period " + Math.pow(2, +pc) + ": rdiag " + classes[pc].join(", ")]); });
      legendSlot.innerHTML = "";
      legendSlot.appendChild(C.legend(items));
      summary.textContent = "Each row is made from the one above by left XOR (center OR right). Read along a diagonal parallel to the right edge and the bits repeat: rdiag j has period " +
        js.map(function (k) { return periods[k] + " (j=" + k + ")"; }).join(", ") + (js.length ? "" : "1, 2, 2, 4, 8, 8, 16, 32 for j = 0 to 7") +
        ", each dividing 2^(j-1). The center column meets diagonal t only at time t, inside the stretch before that diagonal has shown its period, so the regular right half says nothing directly about the center: Problem 1 asks whether this one diagonal read across all of them ever repeats.";
      details.innerHTML = "";
      details.appendChild(C.el("summary", { text: "The diagonals as numbers" }));
      details.appendChild(C.dataTable("Right diagonals rdiag j: the first bits, the measured period and the bound 2^(j-1)", ["j", "first 32 bits", "period", "2^(j-1)", "divides"],
        Array.from({ length: MAX_DIAG }, function (_, k) { var jj = k + 1, w = C.word(jj, Math.pow(2, jj)); return [jj, C.bits(w.slice(0, 32)), periods[jj], bound[jj], bound[jj] % periods[jj] === 0 ? "yes" : "no"]; })));
      describe();
    }
    function moveCursor() {
      clampCursor();
      var c = state.cursor, cur = svgEl && svgEl.querySelector("[data-cursor]");
      if (cur) { cur.setAttribute("x", state.n - 1 + c.p); cur.setAttribute("y", c.t); }
      describe();
    }
    function mv(dt, dp) { return function () { state.cursor.t += dt; state.cursor.p += dp; moveCursor(); }; }
    C.keys(stage, { ArrowLeft: mv(0, -1), ArrowRight: mv(0, 1), ArrowUp: mv(-1, 0), ArrowDown: mv(1, 0), PageUp: mv(-16, 0), PageDown: mv(16, 0),
                    Home: function () { state.cursor.t = 0; moveCursor(); }, End: function () { state.cursor.t = state.n - 1; moveCursor(); },
                    c: function () { state.cursor.p = 0; moveCursor(); }, C: function () { state.cursor.p = 0; moveCursor(); } });

    root.appendChild(controls);
    root.appendChild(stage);
    root.appendChild(readout);
    root.appendChild(legendSlot);
    root.appendChild(summary);
    root.appendChild(details);
    root.appendChild(C.checkNotice(d, function () { describe(); }));
    draw();
  };
})();
