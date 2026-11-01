"""The automaton's computational core as a LexLean semantic module.

`rule30-api/src/Rule30Core.lex.tex` declares Rule 30 as executable
definitions the kernel evaluates: the rule on three cells, the row step on a
list of booleans, the rows from a single black cell, the center column, the
right diagonals `rdiag` (both as a cell of a row and as the host's recursion
from the right edge, `rightRecursion`, which the kernel decides agree), the
tower of words `towerWord`, and the ruler background (`trailingParity`,
`timeParity`, `rulerBackground`). The decided theorems pin the first 32
centers and ruler values to literals, decide that diagonal 1 is the time
parity on the first 64 times, that the center is the anti-diagonal of the
tower, that the first words have their period `2^j` and every diagonal
`j >= 2` its half period `2^(j-1)` (`rdiag_period_half` of the paper), and
that the tower recursion `towerWord (k+2) (s+1) = towerWord (k+2) s XOR
(towerWord (k+1) s OR towerWord k s)` holds on the first four words.

Two products come from the one module:

- `lexlean production` exports the production roots (`rows`, `center`,
  `rdiag`, `towerWord`, `rulerBackground`, `centersFrom`, `rulerFrom`) to
  certified Rust (`bin/r30 api production`, with the roots of `Api`). The
  pinned compiler's targets are `rust-core` and `rust-std` only (`bin/r30 api
  production --targets`): it has no Wasm or browser target, so the page does
  not run the module (PrismPM's SDK, not this binary, carries the
  Core-Wasm route);
- `rule30-api/production/core-vectors.json` (the view artifact
  `core-vectors`): the first 256 centers, the first 12 tower words and the
  ruler background for `t < 512`, computed by the Python replica below from
  the host's own row arithmetic (`row`, `phi`, `bit` of `Core.lex.tex`),
  cross-checked against the module: the decided literals `knownCenters` and
  `knownRuler` are read back from the generated text and must be prefixes of
  the vectors, and every decided identity is re-checked by the replica over
  the whole vector range, before the file is written.

`sync` writes the module and the vectors; `check` refuses drift of either;
the tests keep the replica, the literals and the known centers in
agreement."""

import json
import re

from . import repo, semantic
from .semantic import (BOOL, NAT, add, b, beq, blt, call, definition, holds, if_, list_t, lst, match_list, n, var)

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Rule30Core.lex.tex"
NAME = "Rule30Core"
LEAN_MODULE = "Rule30Api.Rule30Core"

# What the kernel decides (the sizes of the finite checks), and what the
# vectors carry; `theorems` below states each in words for the site.
DECIDED_CENTERS = 32
DECIDED_RULER = 32
DECIDED_TIME_PARITY = 64
DECIDED_ANTIDIAGONAL = 32
DECIDED_TOWER_WORDS = 4      # the recursion on words 2..5 (k = 0..3), every position
DECIDED_PERIODS = 5          # words 0..4, every position
DECIDED_HALF_PERIODS = 6     # diagonals 2..5, every t < 2^j (two half periods)
DECIDED_AGREEMENT = 10       # rightRecursion against rdiag for t < 10, j <= t
DECIDED_WIDTHS = 32
VECTOR_CENTERS = 256
VECTOR_WORDS = 12
VECTOR_RULER = 512
VECTORS = API / "production" / "core-vectors.json"

# The production roots (SPEC §17.13), as `apimodel.PRODUCTION_ROOTS`: rows
# and words allocate lists, Nat arithmetic may overflow the target's 64-bit
# naturals, and the definitions recurse; only `rust-std` realizes them.
EFFECTS = {"effects": ["allocation", "overflow", "recursion"], "targets": ["rust-std"]}
PRODUCTION_ROOTS = {name: EFFECTS for name in ("rows", "center", "rdiag", "towerWord", "rulerBackground", "centersFrom", "rulerFrom")}

KNOWN_CENTERS = [1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0]


# ---------------------------------------------------------------- the replica

class Replica:
    """The module's definitions in Python, on the host's row arithmetic: row
    `t` as the natural `row t` of `Core.lex.tex` (`row 0 = 1`, `row (t+1) =
    phi (row t)` with `phi y = y XOR ((y << 1) OR (y << 2))`: bit `i` of the
    next row is `y_i XOR (y_{i-1} OR y_{i-2})`, the rule read with bit `i`
    as the left neighbour, so bit indices grow leftward). Bit `i` of `row t`
    is the cell at position `t - i`: the center is bit `t`, the right
    diagonal `j` is bit `j`, and the module's list `rows t` (positions `-t..t`
    left to right) is the bits `2t, 2t-1, ..., 0`, so `nth (rows t) i` is
    `bit (row t) (2t - i)`."""

    def __init__(self):
        self._rows = [1]

    def row(self, t):
        while len(self._rows) <= t:
            y = self._rows[-1]
            self._rows.append(y ^ ((y << 1) | (y << 2)))
        return self._rows[t]

    def rows(self, t):
        y = self.row(t)
        return [(y >> (2 * t - i)) & 1 for i in range(2 * t + 1)]

    def center(self, t):
        return (self.row(t) >> t) & 1

    def rdiag(self, j, t):
        return (self.row(t) >> j) & 1

    def right_recursion(self, j, t):
        memo = {}

        def rec(j, t):
            key = (j, t)
            if key not in memo:
                if t == 0:
                    memo[key] = 1 if j == 0 else 0
                elif j == 0:
                    memo[key] = 1
                elif j == 1:
                    memo[key] = 1 - rec(1, t - 1)
                else:
                    k = j - 2
                    memo[key] = rec(k + 2, t - 1) ^ (rec(k + 1, t - 1) | rec(k, t - 1))
            return memo[key]
        return rec(j, t)

    @staticmethod
    def twopow(k):
        return 1 << k

    def tower_word(self, j, s):
        return self.rdiag(j, s % self.twopow(j))

    @staticmethod
    def time_parity(t):
        return 1 if t % 2 == 1 else 0

    @staticmethod
    def trailing_parity(t):
        fuel, value = t, 0
        while fuel > 0:
            if t % 2 == 0:
                return value
            value ^= 1
            t //= 2
            fuel -= 1
        return value

    def ruler_background(self, t):
        sub = lambda a, c: a - c if a >= c else 0
        return (self.trailing_parity(sub(t, 2)) ^ (1 - self.time_parity(t))
                ^ self.trailing_parity(sub(t, 4)) ^ self.trailing_parity(sub(t, 4) // 2))

    def centers(self, count):
        return [self.center(t) for t in range(count)]

    def ruler(self, count):
        return [self.ruler_background(t) for t in range(count)]

    def word(self, j):
        return [self.tower_word(j, s) for s in range(self.twopow(j))]


REPLICA = Replica()


# -------------------------------------------------------------- the data form

def _bools(bits):
    return lst([b(x) for x in bits], BOOL)


def _prim(op, args, result):
    return {"kind": "primitive", "operation": op, "result": result, "arguments": list(args)}


def _sub(a, c):
    return _prim("subtract", [a, c], NAT)


def _rem(a, c):
    return _prim("remainder", [a, c, n(0)], NAT)


def _quo(a, c):
    return _prim("quotient", [a, c, n(0)], NAT)


def _eqb(a, c):
    return _prim("equal", [a, c], BOOL)


def _and(a, c):
    return {"kind": "and", "left": a, "right": c}


def _or(a, c):
    return {"kind": "or", "left": a, "right": c}


def _not(a):
    return {"kind": "not", "value": a}


def _cons(h, t):
    return {"kind": "cons", "head": h, "tail": t}


NIL_B = {"kind": "nil", "element": BOOL}
LB = list_t(BOOL)


def match_nat(scrutinee, zero_body, binder, succ_body):
    return {"kind": "match", "scrutinee": scrutinee, "branches": [
        {"constructor": {"name": "Nat.zero"}, "binders": [], "body": zero_body},
        {"constructor": {"name": "Nat.succ"}, "binders": [binder], "body": succ_body}]}


def _def(name, result, body, parameters=(), recursive=None):
    return definition(name, result, body, parameters=parameters, recursive=recursive,
                      production=PRODUCTION_ROOTS.get(name), executable=True)


def _counting(name, params, condition, step_args, extra_recursive=None):
    """`name <params> n`: `condition` holds at every step of a count `n`,
    the parameters advanced by `step_args` each step (the finite checks the
    kernel decides)."""
    return _def(name, BOOL,
                match_nat(var("n"), b(True), "m", _and(condition, call(name, *step_args, var("m")))),
                parameters=list(params) + [("n", NAT)], recursive="n")


def declarations(replica=REPLICA):
    t, j, k, s, i = var("t"), var("j"), var("k"), var("s"), var("i")
    known_centers = replica.centers(DECIDED_CENTERS)
    known_ruler = replica.ruler(DECIDED_RULER)
    return [
        # the rule and the rows
        _def("bxor", BOOL, if_(var("a"), _not(var("c")), var("c")), parameters=[("a", BOOL), ("c", BOOL)]),
        _def("rule", BOOL, call("bxor", var("a"), _or(var("c"), var("r"))), parameters=[("a", BOOL), ("c", BOOL), ("r", BOOL)]),
        _def("walk", LB,
             match_list(var("rest"), NIL_B, "r", "tail",
                        _cons(call("rule", var("l"), var("c"), var("r")), call("walk", var("c"), var("r"), var("tail")))),
             parameters=[("l", BOOL), ("c", BOOL), ("rest", LB)], recursive="rest"),
        _def("step", LB, call("walk", b(False), b(False), _prim("append", [var("row"), _bools([0, 0])], LB)),
             parameters=[("row", LB)]),
        _def("rows", LB, match_nat(t, _bools([1]), "s", call("step", call("rows", s))), parameters=[("t", NAT)], recursive="t"),
        _def("nth", BOOL,
             match_list(var("xs"), b(False), "h", "tl", if_(beq(i, n(0)), var("h"), call("nth", var("tl"), _sub(i, n(1))))),
             parameters=[("xs", LB), ("i", NAT)], recursive="xs"),
        _def("rowWidth", NAT, _prim("length", [call("rows", t)], NAT), parameters=[("t", NAT)]),
        # the center and the right diagonals
        _def("center", BOOL, call("nth", call("rows", t), t), parameters=[("t", NAT)]),
        _def("rdiag", BOOL, if_(blt(add(t, t), j), b(False), call("nth", call("rows", t), _sub(add(t, t), j))),
             parameters=[("j", NAT), ("t", NAT)]),
        _def("rightRecursion", BOOL,
             match_nat(t, match_nat(j, b(True), "i", b(False)), "s",
                       match_nat(j, b(True), "i",
                                 match_nat(i, _not(call("rightRecursion", add(i, n(1)), s)), "k",
                                           call("bxor", call("rightRecursion", add(k, n(2)), s),
                                                _or(call("rightRecursion", add(k, n(1)), s), call("rightRecursion", k, s)))))),
             parameters=[("j", NAT), ("t", NAT)], recursive="t"),
        # the tower of words
        _def("twopow", NAT, match_nat(k, n(1), "p", add(call("twopow", var("p")), call("twopow", var("p")))),
             parameters=[("k", NAT)], recursive="k"),
        _def("towerWord", BOOL, call("rdiag", j, _rem(s, call("twopow", j))), parameters=[("j", NAT), ("s", NAT)]),
        # the ruler background
        _def("timeParity", BOOL, beq(_rem(t, n(2)), n(1)), parameters=[("t", NAT)]),
        _def("trailingParityFuel", BOOL,
             match_nat(var("f"), b(False), "g",
                       if_(beq(_rem(t, n(2)), n(0)), b(False), _not(call("trailingParityFuel", var("g"), _quo(t, n(2)))))),
             parameters=[("f", NAT), ("t", NAT)], recursive="f"),
        _def("trailingParity", BOOL, call("trailingParityFuel", t, t), parameters=[("t", NAT)]),
        _def("rulerBackground", BOOL,
             call("bxor", call("trailingParity", _sub(t, n(2))),
                  call("bxor", _not(call("timeParity", t)),
                       call("bxor", call("trailingParity", _sub(t, n(4))), call("trailingParity", _quo(_sub(t, n(4)), n(2)))))),
             parameters=[("t", NAT)]),
        # the finite checks the kernel decides
        _def("sameBools", BOOL,
             match_list(var("xs"), beq(_prim("length", [var("ys")], NAT), n(0)), "h", "tl",
                        match_list(var("ys"), b(False), "h2", "tl2", _and(_eqb(var("h"), var("h2")), call("sameBools", var("tl"), var("tl2"))))),
             parameters=[("xs", LB), ("ys", LB)], recursive="xs"),
        _def("centersFrom", LB, match_nat(var("n"), NIL_B, "m", _cons(call("center", t), call("centersFrom", add(t, n(1)), var("m")))),
             parameters=[("t", NAT), ("n", NAT)], recursive="n"),
        _def("rulerFrom", LB, match_nat(var("n"), NIL_B, "m", _cons(call("rulerBackground", t), call("rulerFrom", add(t, n(1)), var("m")))),
             parameters=[("t", NAT), ("n", NAT)], recursive="n"),
        _def("knownCenters", LB, _bools(known_centers)),
        _def("knownRuler", LB, _bools(known_ruler)),
        _counting("rowWidthsFrom", [("t", NAT)], beq(call("rowWidth", t), add(add(t, t), n(1))), [add(t, n(1))]),
        _counting("timeParityFrom", [("t", NAT)], _eqb(call("rdiag", n(1), t), call("timeParity", t)), [add(t, n(1))]),
        _counting("antidiagonalFrom", [("t", NAT)], _eqb(call("center", t), call("towerWord", t, t)), [add(t, n(1))]),
        _def("towerStep", BOOL,
             _eqb(call("towerWord", add(k, n(2)), add(s, n(1))),
                  call("bxor", call("towerWord", add(k, n(2)), s), _or(call("towerWord", add(k, n(1)), s), call("towerWord", k, s)))),
             parameters=[("k", NAT), ("s", NAT)]),
        _counting("towerStepsFrom", [("k", NAT), ("s", NAT)], call("towerStep", k, s), [k, add(s, n(1))]),
        _counting("towerWordsFrom", [("k", NAT)], call("towerStepsFrom", k, n(0), call("twopow", add(k, n(2)))), [add(k, n(1))]),
        _counting("periodFrom", [("j", NAT), ("t", NAT)], _eqb(call("rdiag", j, add(t, call("twopow", j))), call("rdiag", j, t)), [j, add(t, n(1))]),
        _counting("periodsFrom", [("j", NAT)], call("periodFrom", j, n(0), call("twopow", j)), [add(j, n(1))]),
        _counting("halfPeriodFrom", [("j", NAT), ("t", NAT)],
                  _eqb(call("rdiag", j, add(t, call("twopow", _sub(j, n(1))))), call("rdiag", j, t)), [j, add(t, n(1))]),
        _counting("halfPeriodsFrom", [("j", NAT)], call("halfPeriodFrom", j, n(0), call("twopow", j)), [add(j, n(1))]),
        _counting("agreeFrom", [("t", NAT), ("j", NAT)], _eqb(call("rightRecursion", j, t), call("rdiag", j, t)), [t, add(j, n(1))]),
        _counting("agreementFrom", [("t", NAT)], call("agreeFrom", t, n(0), add(t, n(1))), [add(t, n(1))]),
        holds("rowWidths", call("rowWidthsFrom", n(0), n(DECIDED_WIDTHS))),
        holds("centersAreKnown", call("sameBools", call("centersFrom", n(0), n(DECIDED_CENTERS)), call("knownCenters"))),
        holds("rulerBackgroundIsKnown", call("sameBools", call("rulerFrom", n(0), n(DECIDED_RULER)), call("knownRuler"))),
        holds("rdiagOneIsTimeParity", call("timeParityFrom", n(0), n(DECIDED_TIME_PARITY))),
        holds("centerIsAntidiagonal", call("antidiagonalFrom", n(0), n(DECIDED_ANTIDIAGONAL))),
        holds("towerRecursionOnFirstWords", call("towerWordsFrom", n(0), n(DECIDED_TOWER_WORDS))),
        holds("wordsArePeriodic", call("periodsFrom", n(0), n(DECIDED_PERIODS))),
        holds("diagonalsHaveHalfPeriod", call("halfPeriodsFrom", n(2), n(DECIDED_HALF_PERIODS - 2))),
        holds("rightRecursionAgrees", call("agreementFrom", n(0), n(DECIDED_AGREEMENT))),
    ]


# What each decided theorem says, for the site and the README.
THEOREMS = [
    {"name": "rowWidths", "statement": f"row t has 2t+1 cells for t < {DECIDED_WIDTHS}"},
    {"name": "centersAreKnown", "statement": f"the first {DECIDED_CENTERS} centers are the literal knownCenters"},
    {"name": "rulerBackgroundIsKnown", "statement": f"the first {DECIDED_RULER} values of rulerBackground are the literal knownRuler"},
    {"name": "rdiagOneIsTimeParity", "statement": f"rdiag 1 t = timeParity t for t < {DECIDED_TIME_PARITY}"},
    {"name": "centerIsAntidiagonal", "statement": f"center t = towerWord t t for t < {DECIDED_ANTIDIAGONAL}"},
    {"name": "towerRecursionOnFirstWords",
     "statement": f"towerWord (k+2) (s+1) = towerWord (k+2) s XOR (towerWord (k+1) s OR towerWord k s) for k < {DECIDED_TOWER_WORDS} and every s < 2^(k+2)"},
    {"name": "wordsArePeriodic", "statement": f"rdiag j (t + 2^j) = rdiag j t for j < {DECIDED_PERIODS} and every t < 2^j"},
    {"name": "diagonalsHaveHalfPeriod",
     "statement": f"rdiag j (t + 2^(j-1)) = rdiag j t for 2 <= j < {DECIDED_HALF_PERIODS} and every t < 2^j (rdiag_period_half)"},
    {"name": "rightRecursionAgrees", "statement": f"the right-edge recursion of Core.lex.tex and the cell of the row agree for t < {DECIDED_AGREEMENT}, j <= t"},
]


def render(replica=REPLICA):
    from . import lexmod
    return lexmod.module(NAME, declarations(replica))


def sync():
    """Write the module and the vectors (the vectors only after they pass the
    cross-check against the module)."""
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    text = render()
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    data = vectors_json(text)
    VECTORS.parent.mkdir(parents=True, exist_ok=True)
    vchanged = not VECTORS.exists() or VECTORS.read_text() != data
    if vchanged:
        VECTORS.write_text(data)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "theorems": len(THEOREMS),
            "vectors": str(VECTORS.relative_to(repo.ROOT)), "changed": changed or vchanged}


def check():
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Rule30Core.lex.tex is missing; run `bin/r30 api sync`"}
    text = render()
    if MODULE.read_text() != text:
        return {"ok": False, "reason": "Rule30Core.lex.tex drifted from coremodel.py; run `bin/r30 api sync`"}
    try:
        data = vectors_json(text)
    except ValueError as e:
        return {"ok": False, "reason": f"core-vectors.json does not agree with Rule30Core.lex.tex: {e}"}
    if not VECTORS.exists() or VECTORS.read_text() != data:
        return {"ok": False, "reason": "rule30-api/production/core-vectors.json drifted from coremodel.py; run `bin/r30 api sync`"}
    return {"ok": True, "reason": None}


# ---------------------------------------------------------------- the vectors

def decided_literal(name, text=None):
    """The bits of the Boolean list literal `name` as the generated module
    states it (what the kernel decided the first values are)."""
    text = MODULE.read_text() if text is None else text
    m = re.search(r"definition\{\n  name: " + re.escape(name) + r",.*?\n\}", text, re.S)
    if not m:
        raise ValueError(f"{name} is not declared in Rule30Core.lex.tex")
    body = m.group(0).split("\n  body: ", 1)[1].split(",\n  axioms:", 1)[0]
    bits = re.findall(r"\b(?:true|false)\b", body)
    return [1 if "true" in x else 0 for x in bits]


def cross_check(v, text=None, replica=REPLICA):
    """What the module decides, re-checked on the vectors: the decided
    literals are prefixes of the vectors, and every decided identity holds
    over the whole published range. Returns the record the file carries;
    raises ValueError on the first disagreement."""
    centers, words, ruler = v["centers"], v["towerWords"], v["rulerBackground"]
    if decided_literal("knownCenters", text) != centers[:DECIDED_CENTERS]:
        raise ValueError("knownCenters is not the prefix of the published centers")
    if decided_literal("knownRuler", text) != ruler[:DECIDED_RULER]:
        raise ValueError("knownRuler is not the prefix of the published ruler background")
    if centers[:len(KNOWN_CENTERS)] != KNOWN_CENTERS:
        raise ValueError("the centers disagree with the known first 32")
    tw = lambda j, s: words[j][s % (1 << j)]
    checks = {
        "centersAreKnown": centers[:DECIDED_CENTERS] == decided_literal("knownCenters", text),
        "rulerBackgroundIsKnown": ruler[:DECIDED_RULER] == decided_literal("knownRuler", text),
        "rdiagOneIsTimeParity": all(tw(1, t) == t % 2 for t in range(VECTOR_CENTERS)),
        "centerIsAntidiagonal": all(centers[t] == replica.tower_word(t, t) for t in range(VECTOR_CENTERS)),
        "towerRecursionOnFirstWords": all(tw(k + 2, s + 1) == tw(k + 2, s) ^ (tw(k + 1, s) | tw(k, s))
                                          for k in range(VECTOR_WORDS - 2) for s in range(1 << (k + 2))),
        "wordsArePeriodic": all(replica.rdiag(j, t + (1 << j)) == words[j][t] for j in range(VECTOR_WORDS) for t in range(1 << j)),
        "diagonalsHaveHalfPeriod": all(words[j][t + (1 << (j - 1))] == words[j][t]
                                       for j in range(2, VECTOR_WORDS) for t in range(1 << (j - 1))),
        "rightRecursionAgrees": all(replica.right_recursion(j, t) == replica.rdiag(j, t) for t in range(12) for j in range(t + 1)),
        "rowWidths": all(len(replica.rows(t)) == 2 * t + 1 for t in range(64)),
        "rulerBackgroundFormula": all(ruler[t] == replica.ruler_background(t) for t in range(VECTOR_RULER)),
    }
    failed = [k for k, ok in checks.items() if not ok]
    if failed:
        raise ValueError("the vectors refute " + ", ".join(failed))
    return {"decidedLiterals": ["knownCenters", "knownRuler"],
            "recheckedOnVectors": [t["name"] for t in THEOREMS],
            "statement": "the decided literals are prefixes of these vectors, and each decided identity holds on the whole published range"}


def vectors(replica=REPLICA, text=None):
    """`core-vectors.json`: the first values of the core, computed by the
    replica and cross-checked against the module's decided theorems."""
    v = {
        "spec": "r30/core-vectors/1",
        "module": str(MODULE.relative_to(repo.ROOT)),
        "leanModule": LEAN_MODULE,
        "encoding": "bits as 0 and 1; centers[t] = center t; towerWords[j][s] = towerWord j s for s < 2^j; rulerBackground[t] = rulerBackground t",
        "decided": {"centers": DECIDED_CENTERS, "rulerBackground": DECIDED_RULER, "timeParity": DECIDED_TIME_PARITY,
                    "antidiagonal": DECIDED_ANTIDIAGONAL, "towerWords": DECIDED_TOWER_WORDS, "periods": DECIDED_PERIODS,
                    "halfPeriods": DECIDED_HALF_PERIODS, "agreement": DECIDED_AGREEMENT, "widths": DECIDED_WIDTHS},
        "theorems": THEOREMS,
        "productionRoots": sorted(PRODUCTION_ROOTS),
        "browserTarget": None,
        "centers": replica.centers(VECTOR_CENTERS),
        "towerWords": [replica.word(j) for j in range(VECTOR_WORDS)],
        "rulerBackground": replica.ruler(VECTOR_RULER),
    }
    v["crossCheck"] = cross_check(v, render(replica) if text is None else text, replica)
    return v


def vectors_json(text=None):
    """The committed form: one line per vector so a diff reads."""
    v = vectors(text=text)
    big = ("centers", "towerWords", "rulerBackground")
    head = {k: x for k, x in v.items() if k not in big}
    body = json.dumps(head, indent=2, sort_keys=True)[:-2]
    lines = [body + ","]
    lines.append('  "centers": ' + json.dumps(v["centers"], separators=(",", ":")) + ",")
    lines.append('  "rulerBackground": ' + json.dumps(v["rulerBackground"], separators=(",", ":")) + ",")
    lines.append('  "towerWords": [\n' + ",\n".join("    " + json.dumps(w, separators=(",", ":")) for w in v["towerWords"]) + "\n  ]")
    return "\n".join(lines) + "\n}\n"


def theorem_names(text=None):
    """The theorem names of the committed module, in order."""
    text = MODULE.read_text() if text is None else text
    return re.findall(r"theorem\{\n  name: ([A-Za-z0-9_]+),", text)
