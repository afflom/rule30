// The visualizations' core, checked in Node (scripts/tests/test_r30.py runs
// it when node is installed): loads rule30-api/site/viz/core.js with a
// window shim and prints, as JSON, what it computes (the first centers, the
// tower words at their drawn lengths, the measured periods) and the
// mismatches of every identity the panels check, over the ranges the panels
// show. Usage: node viz_check.js <path to core.js>
"use strict";
const fs = require("fs"), vm = require("vm");
const ctx = { window: {}, document: { getElementById: () => null, createElement: () => ({ setAttribute() {}, appendChild() {} }), head: { appendChild() {} } },
              matchMedia: () => ({ matches: false }), location: { protocol: "file:" } };
ctx.window.document = ctx.document;
vm.createContext(ctx);
vm.runInContext(fs.readFileSync(process.argv[2], "utf8"), ctx);
const C = ctx.window.r30core;
const out = {};
out.centers = Array.from({ length: 256 }, (_, t) => C.center(t)).join("");
out.words = Array.from({ length: 11 }, (_, j) => C.word(j).join(""));
out.periods = Array.from({ length: 13 }, (_, j) => C.cyclicPeriod(C.word(j, Math.pow(2, j))));
out.selfCheck = C.selfCheck();
// diagonal-halving: the second half of the 2^j word repeats the first, j >= 2
out.badHalving = [];
for (let j = 2; j <= 12; j++) { const w = C.word(j, Math.pow(2, j)), h = w.length / 2; for (let s = 0; s < h; s++) if (w[s] !== w[s + h]) { out.badHalving.push(j); break; } }
// antidiagonal: center t = towerWord t t, for t < 256
out.badAntidiagonal = [];
for (let t = 0; t < 256; t++) if (C.center(t) !== C.towerWord(t, t)) out.badAntidiagonal.push(t);
// mask-transport and lucas-frame: center t = not maskTransport (t-2) t = not lucasSum (t-2) t, for 2 <= t < 128
const M = C.maskTransport(126, 128);
out.badMask = []; out.badLucas = [];
for (let t = 2; t < 128; t++) {
  if (C.center(t) !== 1 - M[t - 2][t]) out.badMask.push(t);
  if (C.center(t) !== C.lucasFrame(t).center) out.badLucas.push(t);
}
// exposed masks are left run-ends: exposed k i = cell i (i-k) AND NOT cell i (i-k-1)
out.badExposed = [];
for (let i = 0; i < 64; i++) for (let k = 0; k < 64; k++) if (C.exposed(k, i) !== (C.cell(i, i - k) & (1 - C.cell(i, i - k - 1)))) out.badExposed.push([k, i]);
// viz-ledger: the left-band and three-band identities to 512
C.rows(520);
const eight = C.ledgerDiagonal(C.interiorEight, 512), three = C.ledgerDiagonal(C.interiorThree, 512);
out.badEight = []; out.badThree = [];
for (let t = 6; t < 512; t++) if (C.center(t) !== (C.rulerBackground(t) ^ eight[t])) out.badEight.push(t);
for (let t = 2; t < 512; t++) if (C.center(t) !== (C.trailingParity(C.nsub(t, 2)) ^ three[t])) out.badThree.push(t);
out.ruler = Array.from({ length: 64 }, (_, t) => C.rulerBackground(t)).join("");
// the interior diagonal is the XOR of the row terms
out.badRowTerm = [];
for (let t = 1; t < 40; t++) { const L = C.ledger(C.interior, t); if (C.bit(L, t) !== C.xorBelow(m => C.rowTerm(t, m), t)) out.badRowTerm.push(t); }
// viz-rays: the second table, the kernel law, the frozen prefix two ways, the residue dichotomy
function secondTable(k) { const T = 1 << k, LT = C.ledger(C.interior, T); const o = []; for (let r = 0; r < T; r++) { const L = C.phiLinearPow(r, LT); o.push(C.bit(L, 2 * T + r) ^ C.bit(L, r)); } return o.join(""); }
out.secondTable4 = secondTable(4); out.secondTable5 = secondTable(5);
out.badLaw = [];
for (let k = 1; k <= 5; k++) {
  const T = 1 << k, LT = C.ledger(C.interior, T);
  for (let r = 0; r < T; r++) {
    const Lr = C.phiLinearPow(r, LT), F = C.bit(Lr, T + r), S = C.bit(Lr, 2 * T + r) ^ C.bit(Lr, r);
    for (let u = 1; u <= 8; u++) {
      const t = T * u + r; C.rows(t + 1);
      const Lt = C.ledger(C.interior, t), tail = C.bit(Lt, t) ^ C.bit(C.phiLinearPow(t - T, LT), t);
      const law = 1 - (C.timeParity(r) ^ F ^ (C.trailingParity(u - 1) & S) ^ tail);
      if (law !== C.center(t)) out.badLaw.push([k, r, u]);
    }
  }
}
{ const k = 3, r = 2, T = 8, LT = C.ledger(C.interior, T); let F = 0;
  for (let m = 0; m < T; m++) F ^= C.bit(C.phiLinearPow(T + r - 1 - m, C.interior(m) << 1n), T + r);
  out.frozenAgree = F === C.bit(C.phiLinearPow(r, LT), T + r); }
out.badRuler = [];
for (let k = 3; k <= 5; k++) { const T = 1 << k; for (let r = 0; r < T; r++) for (let u = 1; u <= 16; u++) {
  const t = T * u + r; if (C.rulerBackground(t) !== (C.rulerBackground(T + r) ^ (C.trailingParity(u - 1) & ((r === 1 || r === 2) ? 1 : 0)))) out.badRuler.push([k, r, u]); } }
// viz-dyadic: the block step and the scale-free rows
{ const J = 7, N = 1 << J, dr = []; for (let m = 0; m < N; m++) dr.push(C.rowTerm(N, m));
  out.badDyadic = []; out.badDyadicRow = [];
  for (let j = 1; j < J; j++) { let x = 0; for (let i = 0; i < (1 << j); i++) x ^= dr[(1 << j) + i]; if (C.center(1 << (j + 1)) !== (C.center(1 << j) ^ x)) out.badDyadic.push(j); }
  for (let m = 0; m < 16; m++) if (C.rowTerm(1 << (m + 1), m) !== dr[m]) out.badDyadicRow.push(m); }
// viz-defects: the coupling law
out.badCoupling = [];
for (let P = 1; P <= 8; P++) for (let t = 0; t < 100; t++) {
  const dfc = (tt, p) => C.cell(tt + P, p) ^ C.cell(tt, p);
  if (dfc(t, 0) === 0 && dfc(t + 1, 0) !== (dfc(t, -1) ^ ((1 - C.center(t)) & dfc(t, 1)))) out.badCoupling.push([P, t]);
}
// the cross-check against vectors: agreement, and a planted disagreement is named
out.compareOk = C.compare({ centers: out.centers.split("").map(Number), towerWords: out.words.slice(0, 6).map(w => w.split("").map(Number)), rulerBackground: out.ruler.split("").map(Number) });
out.comparePlanted = C.compare({ centers: [1, 1, 1] });
console.log(JSON.stringify(out));
