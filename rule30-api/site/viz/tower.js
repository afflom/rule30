/* viz-tower: the tower of words. rdiag j t = cell t (t - j) is bit j of row
   t, periodic from time 0 with period dividing 2^(j-1) for j >= 2
   (diagonal-halving), so each right diagonal is one word, drawn here as a
   row of length 2^(j-1) (j up to 10) scaled to a common width. The
   anti-diagonal cell towerWord t t = center t is outlined in every row
   (antidiagonal: Problem 1 is that this diagonal is not eventually
   periodic). The recursion towerWord (k+2) (s+1) = towerWord (k+2) s XOR
   (towerWord (k+1) s OR towerWord k s) rebuilds a word on demand; the
   exposed masks exposed k s = towerWord k s AND NOT towerWord (k+1) s (the
   left ends of black runs) are toggled; and the Lucas frame recomputes
   center t = not lucasSum (t-2) t from the masks with the weights
   C(t-1-j, t-2-i) mod 2 (mask-transport, lucas-frame). */
(function () {
  "use strict";
  var C = window.r30core;
  var ROWH = 22, GAP = 5, GUT = 64;

  window.r30viz["viz-tower"] = function (slot, d) {
    var root = C.frame(slot);
    var state = { J: 8, full: false, masks: false, k: 5, s: -1, timer: null, t: 12 };
    var controls = C.el("div", { "class": "viz-controls" });
    var anim = C.el("div", { "class": "viz-controls" });
    var stage = C.el("div", { "class": "viz-stage-static" });
    var readout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var legendSlot = C.el("div");
    var lucasTitle = C.el("h4", { "class": "viz-subhead", text: "The center as a weighted sum of the masks" });
    var lucasControls = C.el("div", { "class": "viz-controls" });
    var lucasStage = C.stage("The Lucas frame of center t: rows are the diagonals i, columns the times j. Left and Right change t; the readout gives the parity.");
    var lucasReadout = C.el("p", { "class": "viz-readout", "aria-live": "polite" });
    var summary = C.el("p", { "class": "viz-summary" });
    var details = C.el("details");
    var svgEl = null, lucasSvg = null, T = null;

    controls.appendChild(C.range("Words j up to", 2, 10, state.J, 1, function (v) {
      state.J = v; if (state.k > v) state.k = v; kRange.setMax(v); kRange.set(state.k); stop(); state.s = -1; draw();
    }));
    controls.appendChild(C.toggle("Show Jen's length 2^j (both halves)", false, function (on) { state.full = on; draw(); }));
    controls.appendChild(C.toggle("Exposed masks (left run-ends)", false, function (on) { state.masks = on; draw(); }));
    var kRange = C.range("Rebuild word j =", 2, state.J, state.k, 1, function (v) { state.k = v; stop(); state.s = -1; draw(); });
    var stepBtn = C.button("Step", function () { stop(); step(); });
    var playBtn = C.toggle("Play", false, function (on) { if (on) play(); else stop(); });
    var resetBtn = C.button("Reset", function () { stop(); state.s = -1; draw(); });
    anim.appendChild(C.group("The recursion:", [kRange, stepBtn, playBtn, resetBtn]));

    function len(j) { return state.full && j >= 1 ? Math.pow(2, j) : C.wordLength(j); }
    function stop() { if (state.timer) { clearInterval(state.timer); state.timer = null; } playBtn.setAttribute("aria-pressed", "false"); playBtn.firstChild.nodeValue = "Play"; }
    function step() {
      if (state.s + 1 >= len(state.k)) { stop(); return false; }
      state.s++;
      draw();
      return true;
    }
    function play() {
      if (C.reducedMotion()) {
        // reduced motion: the whole word at once, the steps still available one by one
        state.s = len(state.k) - 1; draw(); playBtn.setAttribute("aria-pressed", "false");
        readout.textContent = "Reduced motion is on, so word " + state.k + " was rebuilt in one step; use Step to walk it cell by cell. " + readout.textContent;
        return;
      }
      if (state.s + 1 >= len(state.k)) state.s = -1;
      playBtn.firstChild.nodeValue = "Pause";
      state.timer = setInterval(function () { if (!step()) stop(); }, 160);
    }

    function draw() {
      var J = state.J, W = 512, H = (J + 1) * (ROWH + GAP) + 6; // every word spans the same width
      T = C.towerByRecursion(J, Math.pow(2, J) + 1);
      C.rows(Math.pow(2, J) + J + 2);
      var words = [];
      for (var j = 0; j <= J; j++) words.push(C.word(j, len(j)));
      var rebuilding = state.s >= 0, k0 = state.k, s0 = state.s;
      var title = "The tower of words, rdiag 0 to rdiag " + J;
      var desc = "Rows j = 0 to " + J + ": the word of the right diagonal rdiag j, " + (state.full ? "at its full length 2^j, its two halves equal" : "of length 2^(j-1)") +
        ", drawn across the full width; the anti-diagonal cell (time j, the center at time j) outlined. " +
        words.map(function (w, jj) { return "j=" + jj + ": " + (w.length <= 32 ? C.bits(w) : "length " + w.length) + ", period " + C.cyclicPeriod(w); }).join("; ") + ".";
      var s = C.picture("tower", GUT + W, H, title, desc);
      var fills = C.patterns(s, 4);
      words.forEach(function (w, jj) {
        var L = w.length, cw = W / L, y = jj * (ROWH + GAP);
        var dim = rebuilding && jj === k0;
        s.appendChild(C.svg("rect", { x: GUT, y: y, width: W, height: ROWH, fill: "var(--viz-soft)" }));
        var path = "";
        for (var ss = 0; ss < L; ss++) if (w[ss] && !(dim && ss > s0)) path += "M" + (GUT + ss * cw) + " " + y + "h" + cw + "v" + ROWH + "h-" + cw + "z";
        s.appendChild(C.svg("path", { d: path, fill: "var(--viz-ink)" }));
        if (state.full && jj >= 2) {
          // the second half equals the first (diagonal-halving): hatched over
          s.appendChild(C.symbol(C.svg("rect", { x: GUT + W / 2, y: y, width: W / 2, height: ROWH, fill: fills[1], opacity: "0.35" }), "second half of word " + jj + ", equal to the first"));
        }
        if (state.masks) {
          var mp = "";
          for (ss = 0; ss < L; ss++) if (C.exposed(jj, ss)) mp += "M" + (GUT + ss * cw) + " " + (y + ROWH * 0.55) + "h" + cw + "v" + ROWH * 0.45 + "h-" + cw + "z";
          if (mp) s.appendChild(C.symbol(C.svg("path", { d: mp, fill: fills[0] }), "exposed mask of word " + jj));
        }
        if (dim && s0 + 1 < L) {
          // the three sources of the next cell and the target
          [[k0, s0, 3], [k0 - 1, s0, 2], [k0 - 2, s0, 2]].forEach(function (m) {
            var Lm = words[m[0]].length, cwm = W / Lm, sm = m[1] % Lm;
            s.appendChild(C.svg("rect", { x: GUT + sm * cwm, y: m[0] * (ROWH + GAP), width: cwm, height: ROWH, fill: "none", stroke: C.colour(m[2]), "stroke-width": 2.5, "vector-effect": "non-scaling-stroke" }));
          });
          s.appendChild(C.svg("rect", { x: GUT + (s0 + 1) * cw, y: y, width: cw, height: ROWH, fill: "none", stroke: C.colour(3), "stroke-width": 2.5, "stroke-dasharray": "4 2", "vector-effect": "non-scaling-stroke" }));
        }
        var a = jj % L;
        s.appendChild(C.symbol(C.svg("rect", { x: GUT + a * cw, y: y - 1, width: cw, height: ROWH + 2, fill: "none", stroke: "var(--viz-accent)", "stroke-width": 2.5, "vector-effect": "non-scaling-stroke" }),
                               "anti-diagonal cell of word " + jj + ": center " + jj + " = " + C.center(jj)));
        s.appendChild(C.svg("text", { x: 4, y: y + ROWH - 7, "font-size": 12, fill: "var(--viz-ink)", "font-family": "var(--mono, monospace)", text: "j=" + jj }));
        s.appendChild(C.svg("text", { x: 30, y: y + ROWH - 7, "font-size": 9, fill: "var(--viz-muted)", "font-family": "var(--mono, monospace)", text: "×" + L }));
      });
      if (state.full) s.appendChild(C.svg("line", { x1: GUT + W / 2, y1: 0, x2: GUT + W / 2, y2: H, stroke: "var(--viz-muted)", "stroke-dasharray": "4 4", "vector-effect": "non-scaling-stroke" }));
      if (svgEl) stage.replaceChild(s, svgEl); else stage.appendChild(s);
      svgEl = s;
      var items = [[C.solid("var(--viz-ink)"), "bit 1 of the word"], [C.solid("var(--viz-accent)"), "anti-diagonal: word t at time t is center t"]];
      if (state.masks) items.push([C.swatch(0), "exposed mask: word j is 1 where word j+1 is 0 (a black cell with a white left neighbour)"]);
      if (state.full) items.push([C.swatch(1), "second half, equal to the first: the period divides 2^(j-1)"]);
      if (rebuilding) items.push([C.solid(C.colour(3)), "the cell being rebuilt and its own previous value"], [C.solid(C.colour(2)), "the two words above at the same time"]);
      legendSlot.innerHTML = ""; legendSlot.appendChild(C.legend(items));
      if (rebuilding) {
        var w0 = words[k0], L0 = w0.length;
        if (s0 + 1 < L0) {
          var a0 = T[k0][s0], b0 = T[k0 - 1][s0], c0 = T[k0 - 2][s0], next = a0 ^ (b0 | c0);
          readout.textContent = "towerWord " + k0 + " " + (s0 + 1) + " = towerWord " + k0 + " " + s0 + " XOR (towerWord " + (k0 - 1) + " " + s0 + " OR towerWord " + (k0 - 2) + " " + s0 + ") = " +
            a0 + " XOR (" + b0 + " OR " + c0 + ") = " + next + (w0[s0 + 1] === next ? ", which is bit " + k0 + " of row " + (s0 + 1) + "." : "; the row says " + w0[s0 + 1] + " (they disagree).");
        } else {
          readout.textContent = "Word " + k0 + " rebuilt from towerWord " + k0 + " 0 = 0 by the recursion alone: " + C.bits(w0.slice(0, 64)) + (L0 > 64 ? "…" : "") + ", period " + C.cyclicPeriod(w0) + ".";
        }
      } else {
        readout.textContent = "Press Step or Play to rebuild word " + state.k + " cell by cell from towerWord " + state.k + " 0 = 0 and the two words above it.";
      }
      details.innerHTML = "";
      details.appendChild(C.el("summary", { text: "The words as numbers" }));
      details.appendChild(C.dataTable("The words of the tower: first bits, length drawn, measured period, the anti-diagonal", ["j", "word (first 32 bits)", "length", "period", "towerWord j j", "center j"],
        words.map(function (w, jj) { return [jj, C.bits(w.slice(0, 32)) + (w.length > 32 ? "…" : ""), w.length, C.cyclicPeriod(w), C.towerWord(jj, jj), C.center(jj)]; })));
      summary.textContent = "Two constant words start the tower: word 0 is all ones (the right edge) and word 1 alternates (the time parity, which is all the edge carries contribute to the center). Every later word follows from the two above it by one local rule, and the halving is visible when both halves are shown. The center column is the outlined diagonal: one cell from each word, word t at time t. Problem 1 is exactly the statement that this diagonal is not eventually periodic.";
      drawLucas();
    }

    lucasControls.appendChild(C.range("Center time t", 2, 64, state.t, 1, function (v) { state.t = v; drawLucas(); }));
    function drawLucas() {
      var t = state.t, F = C.lucasFrame(t), rowsN = t - 1, colsN = t, cs = 10;
      var W = colsN * cs + 40, H = rowsN * cs + 24;
      var desc = "The grid of diagonals i = 0 to " + (t - 2) + " (rows) by times j = 0 to " + (t - 1) + " (columns): exposed masks hatched, the cells whose Lucas weight C(" + (t - 1) + " - j, " + (t - 2) + " - i) is odd tinted, " +
        F.cells.length + " cells carrying both. Their parity is " + F.sum + ", so center " + t + " = not " + F.sum + " = " + F.center + "; the rows give center " + t + " = " + C.center(t) + ".";
      var s = C.picture("lucas", W, H, "The Lucas frame of center " + t, desc, W * 2.4);
      var fills = C.patterns(s, 3);
      var wp = "", ep = "", bp = "";
      for (var i = 0; i <= t - 2; i++) for (var j = 0; j < t; j++) {
        var x = 40 + j * cs, y = i * cs, w = C.pascal(t - 1 - j, t - 2 - i), e = C.exposed(i, j);
        var r = "M" + x + " " + y + "h" + cs + "v" + cs + "h-" + cs + "z";
        if (w && e) bp += r; else if (e) ep += r; else if (w) wp += r;
      }
      s.appendChild(C.svg("rect", { x: 40, y: 0, width: colsN * cs, height: rowsN * cs, fill: "var(--viz-soft)" }));
      if (wp) s.appendChild(C.symbol(C.svg("path", { d: wp, fill: "var(--viz-accent)", opacity: "0.28" }), "odd Lucas weight"));
      if (ep) s.appendChild(C.symbol(C.svg("path", { d: ep, fill: fills[0], opacity: "0.6" }), "exposed mask"));
      if (bp) s.appendChild(C.symbol(C.svg("path", { d: bp, fill: "var(--viz-ink)" }), "mask with odd weight: counted"));
      for (i = 0; i <= t - 2; i += Math.max(1, Math.ceil(t / 12))) s.appendChild(C.svg("text", { x: 2, y: i * cs + cs - 2, "font-size": 8, fill: "var(--viz-muted)", text: "i=" + i }));
      for (j = 0; j < t; j += Math.max(2, Math.ceil(t / 8))) s.appendChild(C.svg("text", { x: 40 + j * cs, y: H - 4, "font-size": 8, fill: "var(--viz-muted)", text: "j=" + j }));
      if (lucasSvg) lucasStage.replaceChild(s, lucasSvg); else lucasStage.appendChild(s);
      lucasSvg = s;
      var ok = F.center === C.center(t);
      lucasReadout.textContent = "t = " + t + ": " + F.cells.length + " exposed masks carry an odd weight, parity " + F.sum + ", so not lucasSum (" + (t - 2) + ") " + t + " = " + F.center +
        (ok ? ", which is center " + t + "." : "; the rows give center " + t + " = " + C.center(t) + " (they disagree).");
    }
    C.keys(lucasStage, { ArrowLeft: function () { state.t = Math.max(2, state.t - 1); syncT(); }, ArrowRight: function () { state.t = Math.min(64, state.t + 1); syncT(); },
                         Home: function () { state.t = 2; syncT(); }, End: function () { state.t = 64; syncT(); } });
    function syncT() { lucasControls.firstChild.set(state.t); drawLucas(); }

    root.appendChild(controls);
    root.appendChild(anim);
    root.appendChild(stage);
    root.appendChild(readout);
    root.appendChild(legendSlot);
    root.appendChild(summary);
    root.appendChild(lucasTitle);
    root.appendChild(lucasControls);
    root.appendChild(lucasStage);
    root.appendChild(lucasReadout);
    root.appendChild(C.legend([[C.solid("var(--viz-ink)"), "exposed mask with odd weight: counted"], [C.swatch(0), "exposed mask, even weight"], [C.solid("color-mix(in srgb, var(--viz-accent) 30%, transparent)"), "odd weight, no mask"]]));
    root.appendChild(details);
    root.appendChild(C.checkNotice(d));
    draw();
  };
})();
