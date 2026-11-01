/* viz-defects: the lag-P defect field. Choose a lag P (1 to 64): the cells
   where row t and row t+P differ (defect P t p = cell (t+P) p XOR cell t p)
   in the cone |p| <= t for t up to 256; the center column, the gated column
   -1 and column +1 highlighted (colour and hatch); the collisions
     collision P t x = (cell t x AND cell (t+P) (x+1)) XOR (cell t (x+1) AND cell (t+P) x)
   marked with a cross, those in the central band |x| <= 2P off column -1
   counted (recurrent-central-collision); and the coupling law
     leftDefect P (t+1) 0 = leftDefect P t 1 XOR (not center t AND rightDefect P t 1), the next center defect,
   checked at every t where the center agrees at lag P (coupling-law); every
   left defect has a column +1 source within its depth (left-defect-sourcing). */
(function () {
  "use strict";
  var C = window.r30core;

  window.r30viz["viz-defects"] = function (slot, d) {
    var root = C.frame(slot);
    var state = { P: 8, n: 128, band: true, collisions: true, cursor: { t: 20, p: 0 } };
    var controls = C.el("div", { "class": "viz-controls" });
    var stage = C.stage("The defect field. Arrow keys move the cursor one cell, Page Up and Page Down sixteen rows, Home and End to the first and the last row, C to the center column.");
    var readout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var result = C.el("p", { "class": "viz-check", role: "status" });
    var legendSlot = C.el("div");
    var summary = C.el("p", { "class": "viz-summary" });
    var details = C.el("details");
    var svgEl = null, data = null;

    controls.appendChild(C.range("Lag P", 1, 64, state.P, 1, function (v) { state.P = v; compute(); draw(); }));
    controls.appendChild(C.range("Rows t up to", 64, 256, state.n, 32, function (v) { state.n = v; clampCursor(); compute(); draw(); }));
    controls.appendChild(C.toggle("Central band |x| <= 2P", true, function (on) { state.band = on; draw(); }));
    controls.appendChild(C.toggle("Collisions", true, function (on) { state.collisions = on; draw(); }));

    function defect(t, p) { return C.cell(t + state.P, p) ^ C.cell(t, p); }
    function collision(t, x) { var P = state.P; return (C.cell(t, x) & C.cell(t + P, x + 1)) ^ (C.cell(t, x + 1) & C.cell(t + P, x)); }
    function compute() {
      var n = state.n, P = state.P;
      C.rows(n + P + 2);
      var cells = [], colls = [], centerDefects = 0, checked = 0, failed = [], bandColls = 0, agree = [];
      for (var t = 0; t < n; t++) {
        for (var p = -t; p <= t; p++) {
          if (defect(t, p)) { cells.push([n - 1 + p, t]); if (p === 0) centerDefects++; }
          if (p < t && collision(t, p)) { colls.push([n - 1 + p, t]); if (Math.abs(p) <= 2 * P && p !== -1) bandColls++; }
        }
        agree.push(defect(t, 0) === 0);
        if (t + 1 < n && defect(t, 0) === 0) {
          checked++;
          if (defect(t + 1, 0) !== (defect(t, -1) ^ ((1 - C.center(t)) & defect(t, 1)))) failed.push(t);
        }
      }
      data = { cells: cells, colls: colls, centerDefects: centerDefects, checked: checked, failed: failed, bandColls: bandColls, agree: agree };
    }
    function clampCursor() { var c = state.cursor; c.t = Math.max(0, Math.min(state.n - 1, c.t)); c.p = Math.max(-c.t, Math.min(c.t, c.p)); }
    function resultText() {
      return "The coupling law (the next center defect is the column -1 defect XOR (not center AND the column +1 defect)) checked at the " + data.checked + " times t < " + (state.n - 1) +
        " where the center agrees at lag " + state.P + ": " + (data.failed.length ? "fails at t = " + data.failed.slice(0, 6).join(", ") : "holds at every one") + ".";
    }
    function describe() {
      var c = state.cursor, P = state.P, a = C.cell(c.t, c.p), b = C.cell(c.t + P, c.p);
      var s = "t = " + c.t + ", position " + (c.p > 0 ? "+" : "") + c.p + ": row t has " + a + ", row t+" + P + " has " + b + ", defect " + (a ^ b);
      if (c.p < c.t) s += "; collision at (t, " + c.p + ") " + collision(c.t, c.p);
      if (c.p === 0) s += "; the center column, which " + (a === b ? "agrees" : "differs") + " at lag " + P + " here";
      if (c.p === -1) s += "; the gated column -1"; if (c.p === 1) s += "; column +1, where left defects are sourced";
      if (Math.abs(c.p) <= 2 * P) s += "; inside the central band";
      readout.textContent = s;
    }
    function draw() {
      var n = state.n, P = state.P, W = 2 * n - 1, H = n;
      var title = "The lag-" + P + " defect field, rows 0 to " + (n - 1);
      var desc = "Cells where row t and row t+" + P + " differ, in the cone of row t: " + data.cells.length + " defects, " + data.centerDefects + " on the center column; " +
        data.colls.length + " collisions, " + data.bandColls + " of them in the central band |x| <= " + 2 * P + " off column -1. " + resultText();
      var s = C.picture("defects", W, H, title, desc);
      var fills = C.patterns(s, 3);
      if (state.band) s.appendChild(C.symbol(C.svg("rect", { x: n - 1 - 2 * P, y: 0, width: 4 * P + 1, height: H, fill: "var(--open-bg, #fbefd3)", opacity: "0.7" }), "central band |x| <= 2P"));
      s.appendChild(C.symbol(C.svg("rect", { x: n - 2, y: 0, width: 1, height: H, fill: fills[1], opacity: "0.6" }), "column -1, gated"));
      s.appendChild(C.symbol(C.svg("rect", { x: n, y: 0, width: 1, height: H, fill: fills[2], opacity: "0.6" }), "column +1"));
      s.appendChild(C.symbol(C.svg("rect", { x: n - 1, y: 0, width: 1, height: H, fill: "var(--viz-accent)", opacity: "0.4" }), "center column"));
      s.appendChild(C.svg("path", { d: C.runsPath(data.cells), fill: "var(--viz-ink)", opacity: "0.85" }));
      // the times the center agrees at lag P: a tick in the margin of the center column
      var ag = "";
      data.agree.forEach(function (ok, t) { if (ok) ag += "M" + (n - 1) + " " + t + "h1v1h-1z"; });
      if (state.collisions) {
        var marks = "";
        data.colls.forEach(function (c) { marks += "M" + (c[0] + 0.15) + " " + (c[1] + 0.15) + "l0.7 0.7M" + (c[0] + 0.85) + " " + (c[1] + 0.15) + "l-0.7 0.7"; });
        s.appendChild(C.symbol(C.svg("path", { d: marks, stroke: C.colour(0), "stroke-width": Math.max(0.22, n / 600), fill: "none" }), "collisions"));
      }
      var c = state.cursor;
      s.appendChild(C.symbol(C.svg("rect", { "data-cursor": "1", x: n - 1 + c.p, y: c.t, width: 1, height: 1, fill: "none", stroke: "var(--viz-focus)", "stroke-width": Math.max(0.25, n / 160), "pointer-events": "none" }), "cursor"));
      s.addEventListener("pointermove", function (e) {
        var r = s.getBoundingClientRect();
        if (!r.width) return;
        var tt = Math.floor((e.clientY - r.top) / r.height * H), pp = Math.floor((e.clientX - r.left) / r.width * W) - (n - 1);
        if (tt < 0 || tt >= n || Math.abs(pp) > tt || (tt === state.cursor.t && pp === state.cursor.p)) return;
        state.cursor = { t: tt, p: pp }; moveCursor();
      });
      if (svgEl) stage.replaceChild(s, svgEl); else stage.appendChild(s);
      svgEl = s;
      result.textContent = resultText();
      result.className = "viz-check" + (data.failed.length ? " bad" : "");
      legendSlot.innerHTML = "";
      legendSlot.appendChild(C.legend([[C.solid("var(--viz-ink)"), "defect: rows t and t+P differ"], [C.solid("var(--viz-accent)"), "center column"],
        [C.swatch(1), "column -1, the gated column"], [C.swatch(2), "column +1, where left defects are sourced"], [C.solid("var(--open-bg, #fbefd3)"), "central band |x| <= 2P"],
        [C.solid(C.colour(0)), "collision, marked with a cross"]]));
      details.innerHTML = "";
      details.appendChild(C.el("summary", { text: "The central columns as numbers" }));
      details.appendChild(C.dataTable("The first 48 times at lag " + P + ": the defects at columns -1, 0, +1 and the coupling law where the center agrees",
        ["t", "center", "defect -1", "defect 0", "defect +1", "next center defect: law"],
        Array.from({ length: Math.min(48, n - 1) }, function (_, t) {
          var law = defect(t, 0) === 0 ? (defect(t + 1, 0) === (defect(t, -1) ^ ((1 - C.center(t)) & defect(t, 1))) ? "holds" : "FAILS") : "-";
          return [t, C.center(t), defect(t, -1), defect(t, 0), defect(t, 1), law];
        })));
      summary.textContent = "A center period P from some time on would mean no defect on the center column from then on. The coupling law says what that requires: at every later time the column -1 defect must equal (not center AND the column +1 defect), every left defect comes from column +1, and Problem 1 is the statement that no period lets the collisions keep recurring in the band |x| <= 2P. The field drawn here is finite evidence, not a proof.";
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
    root.appendChild(result);
    root.appendChild(legendSlot);
    root.appendChild(summary);
    root.appendChild(details);
    root.appendChild(C.checkNotice(d));
    compute();
    draw();
  };
})();
