/* viz-rays: the kernel law on a dyadic ray. Choose a scale k and a residue
   r < 2^k: the times t = 2^k u + r, the frozen prefix frozenPrefix k r, the
   second table secondPrefix k r' over every residue r', the late tail
   lateTail k r u, and the law
     center (2^k u + r) = not (timeParity r XOR frozenPrefix k r XOR (trailingParity (u-1) AND secondPrefix k r) XOR lateTail k r u)
   checked at every u shown (kernel-law); the second table reads 0, 0, 0, 1
   on the first four residues at every scale (second-table); and the ruler
   background depends on u only on residues 1 and 2, through
   trailingParity (u-1) (residue-dichotomy, k >= 3), which the residue
   strip highlights. The prefix sums are read off the interior ledger, the
   per-row bits from the row terms. */
(function () {
  "use strict";
  var C = window.r30core;
  var TAIL_LIMIT = 400, CELL = 12;

  window.r30viz["viz-rays"] = function (slot, d) {
    var root = C.frame(slot);
    var state = { k: 3, r: 1, U: 16, u: 1 };
    var controls = C.el("div", { "class": "viz-controls" });
    var resStage = C.stage("The residues r of scale k. Left and Right choose the residue; the readout says what the second table and the ruler background do on it.");
    var resReadout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var stage = C.stage("The ray: one column per index u. Left and Right choose the index u; the table below shows its late tail.");
    var result = C.el("p", { "class": "viz-check", role: "status" });
    var legendSlot = C.el("div");
    var tables = C.el("div");
    var summary = C.el("p", { "class": "viz-summary" });
    var resSvg = null, svgEl = null, data = null;

    var rRange = C.range("Residue r", 0, (1 << state.k) - 1, state.r, 1, function (v) { state.r = v; recompute(); });
    controls.appendChild(C.range("Scale k", 1, 6, state.k, 1, function (v) {
      state.k = v; var top = (1 << v) - 1; if (state.r > top) state.r = top;
      rRange.setMax(top); rRange.set(state.r); recompute();
    }));
    controls.appendChild(rRange);
    controls.appendChild(C.range("Indices u up to", 4, 32, state.U, 4, function (v) { state.U = v; if (state.u > v) state.u = v; recompute(); }));

    function compute() {
      var k = state.k, r = state.r, U = state.U, T = 1 << k, tmax = T * U + r;
      C.rows(tmax + 2);
      var LT = C.ledger(C.interior, T), Lr = C.phiLinearPow(r, LT);
      var frozenPrefix = C.bit(Lr, T + r);
      var secondTable = [];
      for (var rr = 0; rr < T; rr++) { var L = C.phiLinearPow(rr, LT); secondTable.push(C.bit(L, 2 * T + rr) ^ C.bit(L, rr)); }
      var secondPrefix = secondTable[r];
      var frozen = [], second = [];
      for (var m = 0; m < T; m++) {
        var Y = C.phiLinearPow(T + r - 1 - m, C.interior(m) << 1n);
        frozen.push(C.bit(Y, T + r)); second.push(C.bit(Y, 2 * T + r) ^ C.bit(Y, r));
      }
      // one pass of the interior ledger up to tmax, reading the diagonal and the frozen part at each ray time
      var out = [], Lt = 0n, want = {};
      for (var u = 1; u <= U; u++) want[T * u + r] = u;
      for (var t = 0; t <= tmax; t++) {
        if (want[t]) {
          u = want[t];
          var diag = C.bit(Lt, t), prefix = C.bit(C.phiLinearPow(t - T, LT), t), tail = diag ^ prefix;
          var tp = C.trailingParity(u - 1), rulerTerm = tp & secondPrefix;
          var law = 1 - (C.timeParity(r) ^ frozenPrefix ^ rulerTerm ^ tail);
          var c = C.center(t), rb = C.rulerBackground(t);
          var rbLaw = C.rulerBackground(T + r) ^ (tp & ((r === 1 || r === 2) ? 1 : 0));
          out.push({ u: u, t: t, center: c, tp: tp, rulerTerm: rulerTerm, tail: tail, law: law, ok: law === c, rb: rb, rbLaw: rbLaw, rbOk: rbLaw === rb });
        }
        Lt = C.phiLinear(Lt) ^ (C.interior(t) << 1n);
      }
      // does the ruler background move with u on each residue (over the indices shown)?
      var moves = [];
      for (rr = 0; rr < T; rr++) {
        var first = C.rulerBackground(T + rr), mv = false;
        for (u = 2; u <= U && !mv; u++) if (C.rulerBackground(T * u + rr) !== first) mv = true;
        moves.push(mv);
      }
      data = { T: T, frozenPrefix: frozenPrefix, secondPrefix: secondPrefix, secondTable: secondTable, frozen: frozen, second: second, rows: out, moves: moves };
    }
    function recompute() { compute(); draw(); }
    function resultText() {
      var bad = data.rows.filter(function (x) { return !x.ok; }), badRb = data.rows.filter(function (x) { return !x.rbOk; });
      return "The kernel law at u = 1 to " + data.rows.length + ": " + (bad.length ? "fails at u = " + bad.map(function (x) { return x.u; }).join(", ") : "holds at every u") +
        (state.k >= 3 ? ". rulerBackground (2^k u + r) = rulerBackground (2^k + r) XOR (trailingParity (u-1) AND [r is 1 or 2]): " + (badRb.length ? "fails at u = " + badRb.map(function (x) { return x.u; }).join(", ") : "holds at every u")
                      : ". The residue dichotomy is stated for k >= 3") + ".";
    }
    function drawResidues() {
      var T = data.T, G = 74, W = G + T * CELL + 4, H = 2 * CELL + 14;
      var desc = "The " + T + " residues of scale " + state.k + ": the second table reads " + C.bits(data.secondTable) + "; the ruler background moves with u on residues " +
        data.moves.map(function (m, i) { return m ? i : null; }).filter(function (x) { return x !== null; }).join(", ") + (state.k >= 3 ? " (the dichotomy says exactly 1 and 2)" : "") + "; residue " + state.r + " selected.";
      var s = C.picture("residues", W, H, "The residues of scale " + state.k, desc, W * 2.6);
      s.appendChild(C.svg("text", { x: 2, y: CELL - 1, "font-size": 7, fill: "var(--viz-ink)", text: "second table" }));
      s.appendChild(C.svg("text", { x: 2, y: 2 * CELL - 1, "font-size": 7, fill: "var(--viz-ink)", text: "ruler moves with u" }));
      var fills = C.patterns(s, 3);
      for (var rr = 0; rr < T; rr++) {
        var x = G + rr * CELL;
        s.appendChild(C.svg("rect", { x: x, y: 2, width: CELL - 1, height: CELL - 1, fill: data.secondTable[rr] ? "var(--viz-ink)" : "var(--viz-soft)" }));
        if (data.moves[rr]) s.appendChild(C.symbol(C.svg("rect", { x: x, y: 2 + CELL, width: CELL - 1, height: CELL - 1, fill: fills[0] }), "residue " + rr + ": the ruler background moves with u"));
        else s.appendChild(C.svg("rect", { x: x, y: 2 + CELL, width: CELL - 1, height: CELL - 1, fill: "var(--viz-soft)" }));
        if (rr === state.r) s.appendChild(C.svg("rect", { "data-cursor": "1", x: x - 1, y: 1, width: CELL + 1, height: 2 * CELL + 1, fill: "none", stroke: "var(--viz-focus)", "stroke-width": 1.5 }));
        if (T <= 16 || rr % 4 === 0) s.appendChild(C.svg("text", { x: x + 1, y: 2 * CELL + 11, "font-size": 7, fill: "var(--viz-muted)", text: String(rr) }));
      }
      if (resSvg) resStage.replaceChild(s, resSvg); else resStage.appendChild(s);
      resSvg = s;
      var r = state.r, sp = data.secondTable[r];
      resReadout.textContent = "Residue " + r + ": secondPrefix " + state.k + " " + r + " = " + sp + "; the ruler background " + (data.moves[r] ? "moves with u" : "is constant along the ray") + ". " +
        (state.k >= 3 && (r === 1 || r === 2) ? "Here the frozen rows carry no ruler, so the late tail must supply it." : state.k >= 3 && r === 3 ? "Here the frozen rows carry the ruler (secondPrefix = 1), so the late tail must cancel it." : "");
    }
    function draw() {
      drawResidues();
      var k = state.k, r = state.r, T = data.T, U = data.rows.length;
      var names = ["center t", "frozenPrefix k r", "trailingParity (u-1) AND secondPrefix", "lateTail k r u", "the law's value"];
      var W = 190 + U * CELL, H = 5 * CELL + 16;
      var desc = "Columns u = 1 to " + U + " (times t = " + T + " u + " + r + "), rows: " + names.join(", ") + ". " + resultText();
      var s = C.picture("rays", W, H, "The kernel law on the ray 2^" + k + " u + " + r, desc, W * 2.6);
      names.forEach(function (nm, i) { s.appendChild(C.svg("text", { x: 2, y: i * CELL + CELL - 3, "font-size": 7.5, fill: "var(--viz-ink)", "font-family": "var(--mono, monospace)", text: nm })); });
      data.rows.forEach(function (x, j) {
        [x.center, data.frozenPrefix, x.rulerTerm, x.tail, x.law].forEach(function (v, i) {
          var rect = C.svg("rect", { x: 190 + j * CELL, y: i * CELL, width: CELL - 1, height: CELL - 1, fill: v ? (i === 0 ? "var(--viz-accent)" : "var(--viz-ink)") : "var(--viz-soft)" });
          if (i === 4) { rect.setAttribute("stroke", x.ok ? "var(--proved, #256a41)" : "var(--refuted, #a8302a)"); rect.setAttribute("stroke-width", 1.2); }
          s.appendChild(rect);
        });
        if (U <= 16 || x.u % 4 === 0) s.appendChild(C.svg("text", { x: 190 + j * CELL + 1, y: H - 3, "font-size": 7, fill: "var(--viz-muted)", text: String(x.u) }));
      });
      var sel = data.rows.findIndex(function (x) { return x.u === state.u; });
      if (sel >= 0) s.appendChild(C.symbol(C.svg("rect", { x: 190 + sel * CELL - 1, y: -1, width: CELL + 1, height: 5 * CELL + 1, fill: "none", stroke: "var(--viz-focus)", "stroke-width": 1.5 }), "selected index u = " + state.u));
      if (svgEl) stage.replaceChild(s, svgEl); else stage.appendChild(s);
      svgEl = s;
      result.textContent = resultText();
      result.className = "viz-check" + (data.rows.some(function (x) { return !x.ok || (state.k >= 3 && !x.rbOk); }) ? " bad" : "");
      legendSlot.innerHTML = "";
      legendSlot.appendChild(C.legend([[C.solid("var(--viz-accent)"), "center bit 1"], [C.solid("var(--viz-ink)"), "term bit 1 (in the residue strip: second table 1)"],
                                       [C.swatch(0), "residue where the ruler background moves with u"], [C.solid("var(--proved, #256a41)"), "the law agrees with the center"]]));
      tables.innerHTML = "";
      tables.appendChild(C.dataTable("The ray 2^" + k + " u + " + r + ", index by index", ["u", "t", "center", "frozen", "tp(u-1)", "second", "tail", "law", "agrees", "ruler bg", "by residue"],
        data.rows.map(function (x) { return [x.u, x.t, x.center, data.frozenPrefix, x.tp, data.secondPrefix, x.tail, x.law, x.ok ? "yes" : "NO", x.rb, k >= 3 ? (x.rbOk ? "yes" : "NO") : "k < 3"]; })));
      tables.appendChild(C.el("p", { "class": "strip", text: "frozen " + k + " " + r + " m for m < 2^" + k + ": " + C.bits(data.frozen) + " (XOR = frozenPrefix = " + data.frozenPrefix + ")" }));
      tables.appendChild(C.el("p", { "class": "strip", text: "second " + k + " " + r + " m for m < 2^" + k + ": " + C.bits(data.second) + " (XOR = secondPrefix = " + data.secondPrefix + ")" }));
      var x = data.rows[sel];
      if (x) {
        if (x.t <= TAIL_LIMIT) {
          var tb = [], xr = 0;
          for (var i = 0; i < x.t - T; i++) { var b = C.rowTerm(x.t, T + i); tb.push(b); xr ^= b; }
          tables.appendChild(C.el("p", { "class": "strip", text: "late tail at u = " + x.u + " (t = " + x.t + "): rowTerm t m for m = 2^" + k + " to " + (x.t - 1) + ": " + C.bits(tb) + " (XOR = " + xr + (xr === x.tail ? ", as the ledger says)" : ", but the ledger says " + x.tail + ")") }));
        } else {
          tables.appendChild(C.el("p", { "class": "strip", text: "late tail at u = " + x.u + ": t = " + x.t + " is beyond " + TAIL_LIMIT + "; only its XOR (" + x.tail + ") is read, from the ledger." }));
        }
      }
      summary.textContent = "Every subsequence center (2^k u + r) is explicit up to the rows at or above the scale: the frozen prefix is the same at every u, the ruler term is the period-doubling sequence trailingParity (u-1) switched on by the second table at r, and the late tail is what the rows from 2^k on add. The second table reads 0, 0, 0, 1 on the first four residues at every scale; the ruler background moves with u only on residues 1 and 2. There the late tail must carry the ruler; on residue 3 it must cancel the one the frozen rows carry.";
    }
    C.keys(resStage, { ArrowLeft: function () { state.r = Math.max(0, state.r - 1); rRange.set(state.r); recompute(); },
                       ArrowRight: function () { state.r = Math.min(data.T - 1, state.r + 1); rRange.set(state.r); recompute(); } });
    C.keys(stage, { ArrowLeft: function () { state.u = Math.max(1, state.u - 1); draw(); }, ArrowRight: function () { state.u = Math.min(state.U, state.u + 1); draw(); },
                    Home: function () { state.u = 1; draw(); }, End: function () { state.u = state.U; draw(); } });

    root.appendChild(controls);
    root.appendChild(resStage);
    root.appendChild(resReadout);
    root.appendChild(stage);
    root.appendChild(result);
    root.appendChild(legendSlot);
    root.appendChild(tables);
    root.appendChild(summary);
    root.appendChild(C.checkNotice(d));
    recompute();
  };
})();
