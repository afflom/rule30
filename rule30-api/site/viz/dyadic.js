/* viz-dyadic: the dyadic column center (2^j) and the block parities of the
   scale-free sequence dyadicRow m = rowTerm (2^(m+1)) m, which equals
   rowTerm (2^J) m for every 2^J > m (scale-free-rows; that is how it is
   computed here): the sequence as a strip with its blocks [2^j, 2^(j+1))
   and their parities blockParity j, the column, and the identities
     center (2^j) = not (XOR of dyadicRow m for m < 2^j)
     center (2^(j+1)) = center (2^j) XOR blockParity j
   checked at every scale shown; the open leaf dyadic-column-aperiodic says
   this column is not eventually periodic (dyadic-response-reduction carries
   it to Problem 1); the panel shows it, it does not decide it. */
(function () {
  "use strict";
  var C = window.r30core;
  var SH = 12;

  window.r30viz["viz-dyadic"] = function (slot, d) {
    var root = C.frame(slot);
    var state = { J: 7, m: 5 };
    var controls = C.el("div", { "class": "viz-controls" });
    var stage = C.stage("The sequence dyadicRow as a strip under its blocks and the dyadic column. Left and Right move the cursor one index, Page Up and Page Down by 16, Home and End to the first and the last.");
    var readout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var result = C.el("p", { "class": "viz-check", role: "status" });
    var legendSlot = C.el("div");
    var tableSlot = C.el("div");
    var summary = C.el("p", { "class": "viz-summary" });
    var svgEl = null, data = null;

    controls.appendChild(C.range("Scales j up to", 3, 9, state.J, 1, function (v) { state.J = v; state.m = Math.min(state.m, (1 << v) - 1); compute(); draw(); }));

    function compute() {
      var J = state.J, N = 1 << J;
      C.rows(N + 2);
      var dr = [];
      for (var m = 0; m < N; m++) dr.push(C.rowTerm(N, m));
      var column = [], blocks = [], badStep = [], badPrefix = [], badFree = [];
      for (var j = 0; j <= J; j++) column.push(C.center(1 << j));
      for (j = 0; j < J; j++) {
        var x = 0, L = 1 << j;
        for (var i = 0; i < L; i++) x ^= dr[L + i];
        blocks.push(x);
        if (j >= 1 && column[j + 1] !== (column[j] ^ x)) badStep.push(j);
      }
      for (j = 1; j <= J; j++) { var y = 0; for (m = 0; m < (1 << j); m++) y ^= dr[m]; if (column[j] !== 1 - y) badPrefix.push(j); }
      // scale-free: row m's term is the same bit at the dyadic time 2^(m+1) (checked where that time is small enough)
      for (m = 0; m < Math.min(N, 9); m++) if (C.rowTerm(1 << (m + 1), m) !== dr[m]) badFree.push(m);
      data = { dr: dr, column: column, blocks: blocks, badStep: badStep, badPrefix: badPrefix, badFree: badFree };
    }
    function blockOf(m) { return m === 0 ? -1 : Math.floor(Math.log2(m)); }
    function resultText() {
      var J = state.J;
      return "center (2^(j+1)) = center (2^j) XOR blockParity j for 1 <= j < " + J + ": " + (data.badStep.length ? "fails at j = " + data.badStep.join(", ") : "holds at every scale") +
        ". center (2^j) = not (XOR of dyadicRow m, m < 2^j) for 1 <= j <= " + J + ": " + (data.badPrefix.length ? "fails at j = " + data.badPrefix.join(", ") : "holds at every scale") +
        ". dyadicRow m read at 2^(m+1) and at 2^" + J + " agree for m < 9: " + (data.badFree.length ? "not at m = " + data.badFree.join(", ") : "yes") + ".";
    }
    function draw() {
      var J = state.J, N = 1 << J, U = Math.max(1, 512 / N), W = N * U, H = 3 * SH + 22;
      var desc = "The strip dyadicRow m for m < " + N + ": " + C.bits(data.dr.slice(0, 64)) + (N > 64 ? "…" : "") + "; the block parities for j = 0 to " + (J - 1) + ": " + C.bits(data.blocks) +
        "; the column center (2^j) for j = 0 to " + J + ": " + C.bits(data.column) + ". " + resultText();
      var s = C.picture("dyadic", W, H, "The dyadic column and the blocks of dyadicRow, j up to " + J, desc);
      var fills = C.patterns(s, Math.max(1, J));
      var yStrip = 2 * SH + 6, yBlocks = SH + 3;
      s.appendChild(C.svg("rect", { x: 0, y: yStrip, width: W, height: SH, fill: "var(--viz-soft)" }));
      var path = "";
      data.dr.forEach(function (b, m) { if (b) path += "M" + m * U + " " + yStrip + "h" + U + "v" + SH + "h-" + U + "z"; });
      s.appendChild(C.symbol(C.svg("path", { d: path, fill: "var(--viz-ink)" }), "dyadicRow"));
      for (var j = 0; j < J; j++) {
        var L = 1 << j;
        var blk = C.svg("rect", { x: L * U, y: yBlocks, width: L * U, height: SH, fill: data.blocks[j] ? fills[j] : "var(--viz-soft)", stroke: "var(--viz-line)", "stroke-width": 0.5 });
        s.appendChild(C.symbol(blk, "block " + j + ", from " + L + " to " + (2 * L - 1) + ", parity " + data.blocks[j]));
        if (L * U >= 14) s.appendChild(C.svg("text", { x: L * U + 2, y: yBlocks + SH - 3, "font-size": 8, fill: "var(--viz-ink)", "paint-order": "stroke", stroke: "var(--viz-bg)", "stroke-width": 2, text: "b" + j + "=" + data.blocks[j] }));
        s.appendChild(C.svg("line", { x1: L * U, y1: 0, x2: L * U, y2: yStrip + SH, stroke: "var(--viz-muted)", "stroke-width": 0.5, "stroke-dasharray": "2 2" }));
      }
      for (j = 0; j <= J; j++) {
        var x = Math.min(1 << j, N - 1) * U;
        s.appendChild(C.symbol(C.svg("rect", { x: x, y: 0, width: Math.max(U, 3), height: SH, fill: data.column[j] ? "var(--viz-accent)" : "var(--viz-soft)", stroke: "var(--viz-accent)", "stroke-width": 0.8 }),
                               "center (2^" + j + ") = " + data.column[j]));
      }
      s.appendChild(C.svg("text", { x: 2, y: H - 3, "font-size": 8, fill: "var(--viz-muted)", text: "m = 0" }));
      s.appendChild(C.svg("text", { x: W - 40, y: H - 3, "font-size": 8, fill: "var(--viz-muted)", text: "m = " + (N - 1) }));
      s.appendChild(C.symbol(C.svg("rect", { "data-cursor": "1", x: state.m * U, y: yStrip - 1, width: U, height: SH + 2, fill: "none", stroke: "var(--viz-focus)", "stroke-width": 1.5, "pointer-events": "none" }), "cursor"));
      s.addEventListener("pointermove", function (e) {
        var r = s.getBoundingClientRect();
        if (!r.width) return;
        var m = Math.floor((e.clientX - r.left) / r.width * N);
        if (m < 0 || m >= N || m === state.m) return;
        state.m = m; moveCursor();
      });
      if (svgEl) stage.replaceChild(s, svgEl); else stage.appendChild(s);
      svgEl = s;
      svgEl.U = U;
      result.textContent = resultText();
      result.className = "viz-check" + (data.badStep.length || data.badPrefix.length || data.badFree.length ? " bad" : "");
      legendSlot.innerHTML = "";
      legendSlot.appendChild(C.legend([[C.solid("var(--viz-accent)"), "center (2^j), top row, at m = 2^j"], [C.swatch(0), "a block of odd parity (each block its own hatch)"], [C.solid("var(--viz-ink)"), "dyadicRow m = 1, bottom row"]]));
      tableSlot.innerHTML = "";
      tableSlot.appendChild(C.dataTable("The dyadic column, scale by scale", ["j", "2^j", "center (2^j)", "XOR of dyadicRow below 2^j", "blockParity j", "next = this XOR block"],
        Array.from({ length: J + 1 }, function (_, jj) {
          var y = 0; for (var m = 0; m < (1 << jj); m++) y ^= data.dr[m];
          var stepOk = jj >= 1 && jj < J ? (data.column[jj + 1] === (data.column[jj] ^ data.blocks[jj]) ? "holds" : "FAILS") : "-";
          return [jj, 1 << jj, data.column[jj], y, jj < J ? data.blocks[jj] : "-", stepOk];
        })));
      summary.textContent = "Read only at the times 1, 2, 4, 8, ..., the center column is the running parity of one fixed sequence: row m adds the same bit at every dyadic time beyond m, so the column steps from one scale to the next by the parity of one block. If the center were eventually periodic this sparse column would be too; the open leaf says it is not, and this panel shows the column without deciding it.";
      describe();
    }
    function describe() {
      var m = state.m, j = blockOf(m);
      readout.textContent = "m = " + m + ": dyadicRow m = " + data.dr[m] + (j >= 0 ? ", in block " + j + " = [" + (1 << j) + ", " + (2 << j) + ") of parity " + data.blocks[j] : ", before the first block") +
        ((m & (m - 1)) === 0 && m > 0 ? "; center (" + m + ") = " + C.center(m) : "");
    }
    function moveCursor() {
      state.m = Math.max(0, Math.min((1 << state.J) - 1, state.m));
      var cur = svgEl && svgEl.querySelector("[data-cursor]");
      if (cur) cur.setAttribute("x", state.m * svgEl.U);
      describe();
    }
    function mv(dm) { return function () { state.m += dm; moveCursor(); }; }
    C.keys(stage, { ArrowLeft: mv(-1), ArrowRight: mv(1), PageUp: mv(-16), PageDown: mv(16),
                    Home: function () { state.m = 0; moveCursor(); }, End: function () { state.m = (1 << state.J) - 1; moveCursor(); } });

    root.appendChild(controls);
    root.appendChild(stage);
    root.appendChild(readout);
    root.appendChild(result);
    root.appendChild(legendSlot);
    root.appendChild(summary);
    root.appendChild(tableSlot);
    root.appendChild(C.checkNotice(d));
    compute();
    draw();
  };
})();
