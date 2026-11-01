/* viz-ledger: the center as rulers plus deep bulk. Aligned bit rows for t
   up to 512: the center column, the ruler background with its four rulers
   separable (trailingParity (t-2), not timeParity t, trailingParity (t-4),
   trailingParity ((t-4)/2)), and the deep bulk interiorEightDiagonal t,
   computed from its own carry ledger; checked at every t:
     center t = rulerBackground t XOR interiorEightDiagonal t   (t >= 6, left-band)
     center t = trailingParity (t-2) XOR interiorThreeDiagonal t (t >= 2, three-diagonal-band)
     center t = not (timeParity t XOR interiorDiagonal t)       (edge-parity) */
(function () {
  "use strict";
  var C = window.r30core;
  var SH = 7, SG = 3, GUT = 96;
  var RULERS = ["trailingParity (t-2)", "not timeParity t", "trailingParity (t-4)", "trailingParity ((t-4)/2)"];

  window.r30viz["viz-ledger"] = function (slot, d) {
    var root = C.frame(slot);
    var state = { n: 256, rulers: [false, false, false, false], three: false, edge: false, t: 6 };
    var controls = C.el("div", { "class": "viz-controls" });
    var stage = C.stage("Aligned bit rows over time. Left and Right move the cursor one time step, Page Up and Page Down by 32, Home and End to the first and the last time. The readout below gives every row at the cursor.");
    var readout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var result = C.el("p", { "class": "viz-check", role: "status" });
    var legendSlot = C.el("div");
    var summary = C.el("p", { "class": "viz-summary" });
    var details = C.el("details");
    var svgEl = null, data = null;

    controls.appendChild(C.range("Times t up to", 64, 512, state.n, 64, function (v) { state.n = v; state.t = Math.min(state.t, v - 1); compute(); draw(); }));
    controls.appendChild(C.group("Rulers, one by one:", RULERS.map(function (name, i) {
      var b = C.toggle("", false, function (on) { state.rulers[i] = on; draw(); }, { "aria-label": "Show the ruler " + name + " on its own row" });
      b.appendChild(C.swatch(i)); b.appendChild(document.createTextNode(name));
      return b;
    })));
    controls.appendChild(C.toggle("Three-diagonal form", false, function (on) { state.three = on; draw(); }));
    controls.appendChild(C.toggle("Edge form", false, function (on) { state.edge = on; draw(); }));

    function compute() {
      var n = state.n;
      C.rows(n + 1);
      var centers = [], rb = [], terms = [];
      for (var t = 0; t < n; t++) { centers.push(C.center(t)); terms.push(C.rulerTerms(t)); rb.push(C.rulerBackground(t)); }
      var eight = C.ledgerDiagonal(C.interiorEight, n), three = C.ledgerDiagonal(C.interiorThree, n), inner = C.ledgerDiagonal(C.interior, n);
      var bad8 = [], bad3 = [], badE = [];
      for (t = 6; t < n; t++) if (centers[t] !== (rb[t] ^ eight[t])) bad8.push(t);
      for (t = 2; t < n; t++) if (centers[t] !== (C.trailingParity(C.nsub(t, 2)) ^ three[t])) bad3.push(t);
      for (t = 0; t < n; t++) if (centers[t] !== 1 - (C.timeParity(t) ^ inner[t])) badE.push(t);
      data = { centers: centers, rb: rb, terms: terms, eight: eight, three: three, inner: inner, bad8: bad8, bad3: bad3, badE: badE };
    }
    function stripRows() {
      var rows = [{ name: "center t", bits: data.centers, fill: "var(--viz-accent)" }, { name: "rulerBackground t", bits: data.rb, fill: "var(--viz-ink)" }];
      state.rulers.forEach(function (on, i) { if (on) rows.push({ name: RULERS[i], bits: data.terms.map(function (r) { return r[i]; }), pattern: i, indent: true }); });
      rows.push({ name: "interiorEightDiagonal t", bits: data.eight, fill: "var(--viz-ink)", bulk: true });
      if (state.three) rows.push({ name: "interiorThreeDiagonal t", bits: data.three, fill: "var(--viz-muted)" });
      if (state.edge) rows.push({ name: "interiorDiagonal t", bits: data.inner, fill: "var(--viz-muted)" });
      return rows;
    }
    function resultText() {
      var n = state.n, f = function (bad, from) { return bad.length ? "fails at t = " + bad.slice(0, 6).join(", ") : "holds at all " + (n - from) + " times"; };
      return "center t = rulerBackground t XOR interiorEightDiagonal t for 6 <= t < " + n + ": " + f(data.bad8, 6) +
        ". center t = trailingParity (t-2) XOR interiorThreeDiagonal t for 2 <= t < " + n + ": " + f(data.bad3, 2) +
        ". center t = not (timeParity t XOR interiorDiagonal t) for t < " + n + ": " + f(data.badE, 0) + ".";
    }
    function draw() {
      var n = state.n, rows = stripRows(), W = GUT + n, H = rows.length * (SH + SG) + 12;
      var title = "The center against the rulers, t < " + n;
      var desc = rows.map(function (r) { return r.name + ": " + C.bits(r.bits.slice(0, 40)) + (n > 40 ? "…" : ""); }).join("; ") + ". " + resultText();
      var s = C.picture("ledger", W, H, title, desc);
      var fills = C.patterns(s, 4);
      rows.forEach(function (r, i) {
        var y = i * (SH + SG), path = "";
        for (var t = 0; t < n; t++) if (r.bits[t]) path += "M" + (GUT + t) + " " + y + "h1v" + SH + "h-1z";
        s.appendChild(C.svg("rect", { x: GUT, y: y, width: n, height: SH, fill: "var(--viz-soft)" }));
        s.appendChild(C.symbol(C.svg("path", { d: path, fill: r.pattern !== undefined ? fills[r.pattern] : r.fill }), r.name));
        s.appendChild(C.svg("text", { x: r.indent ? 8 : 2, y: y + SH - 1, "font-size": 5.2, fill: "var(--viz-ink)", "font-family": "var(--mono, monospace)", text: r.name }));
        if (r.bulk) s.appendChild(C.svg("line", { x1: GUT, x2: GUT + n, y1: y - SG / 2, y2: y - SG / 2, stroke: "var(--viz-line)", "stroke-width": 0.5 }));
      });
      for (var t = 0; t < n; t += 64) s.appendChild(C.svg("text", { x: GUT + t, y: H - 2, "font-size": 5, fill: "var(--viz-muted)", text: String(t) }));
      var cur = C.svg("rect", { "data-cursor": "1", x: GUT + state.t - 0.2, y: -0.5, width: 1.4, height: rows.length * (SH + SG) - SG + 1, fill: "none", stroke: "var(--viz-focus)", "stroke-width": 0.7, "pointer-events": "none" });
      s.appendChild(C.symbol(cur, "cursor"));
      s.addEventListener("pointermove", function (e) {
        var r = s.getBoundingClientRect();
        if (!r.width) return;
        var x = Math.floor((e.clientX - r.left) / r.width * W) - GUT;
        if (x < 0 || x >= n || x === state.t) return;
        state.t = x; moveCursor();
      });
      if (svgEl) stage.replaceChild(s, svgEl); else stage.appendChild(s);
      svgEl = s;
      result.textContent = resultText();
      result.className = "viz-check" + (data.bad8.length || data.bad3.length || data.badE.length ? " bad" : "");
      var items = [[C.solid("var(--viz-accent)"), "center column"], [C.solid("var(--viz-ink)"), "ruler background and deep bulk"]];
      state.rulers.forEach(function (on, i) { if (on) items.push([C.swatch(i), RULERS[i]]); });
      legendSlot.innerHTML = ""; legendSlot.appendChild(C.legend(items));
      details.innerHTML = "";
      details.appendChild(C.el("summary", { text: "The rows as numbers" }));
      details.appendChild(C.dataTable("The first 64 times: the center, the four rulers, the background and the deep bulk",
        ["t", "center", "r1", "r2", "r3", "r4", "background", "deep bulk", "XOR"],
        Array.from({ length: Math.min(64, n) }, function (_, k) { var r = data.terms[k]; return [k, data.centers[k], r[0], r[1], r[2], r[3], data.rb[k], data.eight[k], k >= 6 ? (data.rb[k] ^ data.eight[k]) : "-"]; })));
      summary.textContent = "Top: the center column. Below it the ruler background, the XOR of four rulers; switch each on to see it alone, a rhythm that doubles its spacing as it goes. Below the line: the deep bulk, the diagonal of the ledger of the carries on the right diagonals from 3 and the left diagonals from 8, computed from the rows and not from the identity. The page checks that the top row is the XOR of the other two. Whether the bottom row is ever the ruler background plus a repeating pattern is the open obligation; nothing here decides it.";
      describe();
    }
    function describe() {
      var t = state.t, r = data.terms[t], v = C.verifiedCenter(t);
      readout.textContent = "t = " + t + ": center " + data.centers[t] + " = background " + data.rb[t] + " XOR deep bulk " + data.eight[t] + (t < 6 ? " (stated from t = 6)" : "") +
        "; rulers " + RULERS.map(function (name, i) { return name + " = " + r[i]; }).join(", ") +
        (state.three ? "; three-diagonal bulk " + data.three[t] : "") + (state.edge ? "; interior diagonal " + data.inner[t] : "") +
        (v !== null ? (v === data.centers[t] ? "; verified center agrees" : "; the verified center is " + v + " and it wins") : "");
    }
    function moveCursor() {
      state.t = Math.max(0, Math.min(state.n - 1, state.t));
      var cur = svgEl && svgEl.querySelector("[data-cursor]");
      if (cur) cur.setAttribute("x", GUT + state.t - 0.2);
      describe();
    }
    function mv(dt) { return function () { state.t += dt; moveCursor(); }; }
    C.keys(stage, { ArrowLeft: mv(-1), ArrowRight: mv(1), PageUp: mv(-32), PageDown: mv(32),
                    Home: function () { state.t = 0; moveCursor(); }, End: function () { state.t = state.n - 1; moveCursor(); } });

    root.appendChild(controls);
    root.appendChild(stage);
    root.appendChild(readout);
    root.appendChild(legendSlot);
    root.appendChild(result);
    root.appendChild(summary);
    root.appendChild(details);
    root.appendChild(C.checkNotice(d, function () { describe(); }));
    compute();
    draw();
  };
})();
