"""The basis of the map: the sequences of the paper's notions, as data.

`rule30-api/src/Sequences.lex.tex` declares every sequence the discovery
engines read (`Discovery.lex.tex`): each entry is a lexeme of the glossary
(the paper's notion), the Lean constant it denotes, the parameters that make
it a sequence `Nat -> Bool` (a cell column `t -> cell t p`, a right or left
diagonal, a word of the tower, a run-end mask, ...), its κ-label, and its
window, the values for `t < N`. The kernel decides that the ids and the
κ-labels are distinct, that every window has `N / 32` words and that every
word is below `2^32`.

The κ-label of a sequence is the SHA-256 of the Rivest canonical
S-expression `(sequence <lexeme qid> <parameters...>)`
(`scripts/kappa_research.py`): it addresses what the sequence means (the
notion and where it is read), never its values, so the same notion read at the
same place has the same label in every window.

The window is the meaning, not a replica: `bin/r30 sequences --write`
generates one Lean file in which every entry is `#eval`uated from the host
definitions of `rule30-core-lean` (`lake env lean`, the built research
library), and stores the bits as 32-bit words. Where a host definition is
exponential as written (the cells recurse three ways, `Core.cell`), the file
evaluates it through its rows and proves, in the same file, that the
evaluated form is the host constant (`cell_memo` from `Ledger.cell_eq_rdiag`
and `Interfaces.row_testBit`; `ldiag_memo` from
`Interfaces.ldiag_eq_cell_neg`; the cones, the masked column, the tower words
and the exposed masks by unfolding to those): Lean refuses the file, and the
command writes nothing, when one of these equalities fails. Notions that do not
evaluate in reasonable time are excluded and say why (`EXCLUDED`).

The data lives in `rule30-api/model/sequences.toml`, which only the command
writes (it needs Lean); `bin/r30 api sync` renders the module from it and
`api check` refuses a module or a register that drifted from the basis
declared here, a κ-label that is not the label of its entry, and a window that
is not `N` bits in `N / 32` words."""

import importlib.util
import json
import re
import tomllib

from . import repo
from .semantic import (BOOL, NAT, STR, b, beq, blt, call, definition, field_of_each, holds, if_, list_t, lst,
                       match_list, member_string, n, proj, record, s, structure, theorem, var)

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Sequences.lex.tex"
DATA = API / "model" / "sequences.toml"
NAME = "Sequences"
LEAN_MODULE = "Rule30Api.Sequences"
CHUNK_BITS = 32
# The stored window: the discovery window is half of it, because the
# dilation transforms read s(2t+1) (Discovery.lex.tex).
WINDOW = 512
SPEC = "r30/sequences/1"


# ------------------------------------------------------------------ κ-labels

def _kappa_research():
    spec = importlib.util.spec_from_file_location("kappa_research", repo.ROOT / "scripts/kappa_research.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_KR = _kappa_research()


def kappa(value):
    """The κ-label of an S-expression value (lists of strings)."""
    return _KR.kappa(value)


def sequence_kappa(lexeme, parameters):
    return kappa(["sequence", lexeme, *[str(p) for p in parameters]])


# ------------------------------------------------------------------ the basis

# Each family: the lexeme it instantiates, the Lean constant, the parameter
# values, and the evaluation form the Lean file reads (`{p}` the parameter,
# `t` the time) with the theorem of the file that equates it with the host
# constant. Order matters: the relation engine expresses each column through
# the earlier independent ones, so the simplest notions come first.
FAMILIES = [
    {"family": "one", "lexeme": "lexlean.std.bool::true", "lean": "Bool.true", "values": [None],
     "form": "true", "by": "definition (the constant sequence)"},
    {"family": "time-parity", "lexeme": "r30.observation::time-parity", "lean": "Rule30UOR.EdgeParity.timeParity",
     "values": [None], "form": "EdgeParity.timeParity t", "by": "the host constant"},
    {"family": "trailing-parity", "lexeme": "r30.observation::trailing-parity", "lean": "Rule30UOR.Ledger.trailingParity",
     "values": [None], "form": "Ledger.trailingParity t", "by": "the host constant"},
    {"family": "ruler-background", "lexeme": "r30.observation::ruler-background", "lean": "Rule30UOR.LeftBand.rulerBackground",
     "values": [None], "form": "LeftBand.rulerBackground t", "by": "the host constant"},
    {"family": "center", "lexeme": "r30.scale::center", "lean": "Rule30UOR.Core.center", "values": [None],
     "form": "cellM t 0", "by": "R30Sequences.center_memo"},
    {"family": "cell", "lexeme": "r30.time::cell", "lean": "Rule30UOR.Core.cell", "values": [p for p in range(-8, 9) if p != 0],
     "form": "cellM t ({p})", "by": "R30Sequences.cell_memo"},
    {"family": "rdiag", "lexeme": "r30.right::rdiag", "lean": "Rule30UOR.Core.rdiag", "values": list(range(13)),
     "form": "rdiagM {p} t", "by": "R30Sequences.rdiag_memo"},
    {"family": "ldiag", "lexeme": "r30.time::ldiag", "lean": "Rule30UOR.Core.ldiag", "values": list(range(13)),
     "form": "ldiagM {p} t", "by": "R30Sequences.ldiag_memo"},
    {"family": "tower-word", "lexeme": "r30.observation::tower-word", "lean": "Rule30UOR.Antidiagonal.towerWord",
     "values": list(range(13)), "form": "towerWordM {p} t", "by": "R30Sequences.towerWord_memo"},
    {"family": "exposed", "lexeme": "r30.observation::exposed", "lean": "Rule30UOR.Antidiagonal.exposed",
     "values": list(range(9)), "form": "exposedM {p} t", "by": "R30Sequences.exposed_memo"},
    {"family": "masked-column", "lexeme": "r30.observation::masked-column", "lean": "Rule30UOR.Antidiagonal.maskedColumn",
     "values": [None], "form": "maskedColumnM t", "by": "R30Sequences.maskedColumn_memo"},
    {"family": "cone-zero", "lexeme": "r30.observation::cone-zero", "lean": "Rule30UOR.Antidiagonal.coneZero",
     "values": [None], "form": "coneZeroM t", "by": "R30Sequences.coneZero_memo"},
    {"family": "left-cone", "lexeme": "r30.observation::left-cone", "lean": "Rule30UOR.Antidiagonal.leftCone",
     "values": [None], "form": "leftConeM t", "by": "R30Sequences.leftCone_memo"},
    {"family": "edge-diagonal", "lexeme": "r30.observation::edge-diagonal", "lean": "Rule30UOR.EdgeSplit.edgeDiagonal",
     "values": [None], "form": "EdgeSplit.edgeDiagonal t", "by": "the host constant"},
    {"family": "interior-diagonal", "lexeme": "r30.observation::interior-diagonal", "lean": "Rule30UOR.EdgeSplit.interiorDiagonal",
     "values": [None], "form": "EdgeSplit.interiorDiagonal t", "by": "the host constant"},
    {"family": "low-diagonal", "lexeme": "r30.observation::low-diagonal", "lean": "Rule30UOR.Band.lowDiagonal",
     "values": [None], "form": "Band.lowDiagonal t", "by": "the host constant"},
    {"family": "interior-three-diagonal", "lexeme": "r30.observation::interior-three-diagonal",
     "lean": "Rule30UOR.Band.interiorThreeDiagonal", "values": [None], "form": "Band.interiorThreeDiagonal t",
     "by": "the host constant"},
    {"family": "left-band-diagonal", "lexeme": "r30.observation::left-band-diagonal", "lean": "Rule30UOR.LeftBand.leftBandDiagonal",
     "values": [None], "form": "LeftBand.leftBandDiagonal t", "by": "the host constant"},
    {"family": "interior-eight-diagonal", "lexeme": "r30.observation::interior-eight-diagonal",
     "lean": "Rule30UOR.LeftBand.interiorEightDiagonal", "values": [None], "form": "LeftBand.interiorEightDiagonal t",
     "by": "the host constant"},
    {"family": "ledger-diagonal", "lexeme": "r30.observation::ledger-diagonal", "lean": "Rule30UOR.Ledger.ledgerDiagonal",
     "values": [None], "form": "Ledger.ledgerDiagonal t", "by": "the host constant"},
]

# Notions of the paper that are `Nat -> Bool` after instantiation but are not
# in the basis, with the reason.
EXCLUDED = [
    {"id": "dyadic-row", "lexeme": "r30.observation::dyadic-row", "lean": "Rule30UOR.DyadicRow.dyadicRow",
     "reason": "dyadicRow m = rowTerm (2^(m+1)) m iterates the linear map phiLinear 2^(m+1) - 1 - m times "
               "(Core.phiLinearPow is the plain iteration), so t < 512 needs about 2^512 steps."},
    {"id": "block-parity", "lexeme": "r30.observation::block-parity", "lean": "Rule30UOR.DyadicRow.blockParity",
     "reason": "blockParity j reads dyadicRow at 2^j + i for every i < 2^j, so its window is out of reach for the "
               "reason dyadic-row is."},
    {"id": "witt-resp", "lexeme": "r30.witt::witt-resp", "lean": "Rule30UOR.Interfaces.wittRespBool",
     "reason": "wittRespBool t k is a response in two variables whose value at (t, k) runs the Witt window over "
               "2^k rows; it is a sequence in t only once k is fixed, and no k is singled out by the paper, so it is "
               "left out rather than instantiated at an arbitrary scale."},
]


def entry_id(family, value):
    return family if value is None else f"{family}({value})"


def basis():
    """Every entry of the basis, in order."""
    rows = []
    for f in FAMILIES:
        for v in f["values"]:
            params = [] if v is None else [v]
            rows.append({"id": entry_id(f["family"], v), "family": f["family"], "lexeme": f["lexeme"], "lean": f["lean"],
                         "parameters": params, "kappa": sequence_kappa(f["lexeme"], params),
                         "evaluation": f["form"].format(p=v), "justification": f["by"]})
    return rows


# --------------------------------------------------------------- evaluation

LEAN_PREAMBLE = r"""import Rule30UOR.Antidiagonal
import Rule30UOR.LeftBand

/-! Generated by `bin/r30 sequences`: the windows of the basis, evaluated from the host
definitions. Every evaluation form below is proved equal to the host constant it reads. -/

open Rule30UOR

namespace R30Sequences

/-- The rows below `bound`, computed once (`Core.row`). -/
def bound : Nat := __BOUND__

def rowTable : Array Nat := Array.ofFn (n := bound) (fun i => Core.row i.val)

theorem rowTable_size : rowTable.size = bound := by
  simp [rowTable]

def rowAt (t : Nat) : Nat :=
  if h : t < bound then rowTable[t]'(by rw [rowTable_size]; exact h) else Core.row t

theorem rowAt_eq (t : Nat) : rowAt t = Core.row t := by
  unfold rowAt
  split
  · simp [rowTable]
  · rfl

/-- A cell through its row: `Ledger.cell_eq_rdiag` and `Interfaces.row_testBit`; right of the
light cone (`t < p`, only at `t < 8` here) the host recursion itself. -/
def cellM (t : Nat) (p : Int) : Bool :=
  if p ≤ (t : Int) then (rowAt t).testBit (t - p).toNat else Core.cell t p

theorem cell_memo (t : Nat) (p : Int) : Core.cell t p = cellM t p := by
  unfold cellM
  split
  · rename_i h
    rw [rowAt_eq, Interfaces.row_testBit]
    exact Ledger.cell_eq_rdiag t (t - p).toNat p (by omega)
  · rfl

theorem center_memo (t : Nat) : Core.center t = cellM t 0 := cell_memo t 0

def rdiagM (j t : Nat) : Bool := (rowAt t).testBit j

theorem rdiag_memo (j t : Nat) : Core.rdiag j t = rdiagM j t := by
  unfold rdiagM
  rw [rowAt_eq, Interfaces.row_testBit]

/-- A left diagonal through its cell (`Interfaces.ldiag_eq_cell_neg`); before the diagonal
starts (`t < d ≤ 12`) the host recursion itself. -/
def ldiagM (d t : Nat) : Bool := if d ≤ t then cellM t ((d : Int) - (t : Int)) else Core.ldiag d t

theorem ldiag_memo (d t : Nat) : Core.ldiag d t = ldiagM d t := by
  unfold ldiagM
  split
  · rename_i h
    have e := Interfaces.ldiag_eq_cell_neg d (t - d)
    rw [Nat.add_sub_cancel' h] at e
    rw [e, cell_memo]
    congr 1
    omega
  · rfl

def towerWordM (j s : Nat) : Bool := rdiagM j (s % Core.twopow j)

theorem towerWord_memo (j s : Nat) : Antidiagonal.towerWord j s = towerWordM j s := by
  unfold Antidiagonal.towerWord towerWordM
  exact rdiag_memo j _

def exposedM (k i : Nat) : Bool := towerWordM k i && !(towerWordM (k + 1) i)

theorem exposed_memo (k i : Nat) : Antidiagonal.exposed k i = exposedM k i := by
  unfold Antidiagonal.exposed exposedM
  rw [towerWord_memo, towerWord_memo]

def maskedColumnM (t : Nat) : Bool := cellM t 1 && !(cellM t 0)

theorem maskedColumn_memo (t : Nat) : Antidiagonal.maskedColumn t = maskedColumnM t := by
  unfold Antidiagonal.maskedColumn maskedColumnM
  rw [cell_memo, center_memo]

def runEndM (j : Nat) (p : Int) : Bool := cellM j p && !(cellM j (p - 1))

theorem runEnd_memo (j : Nat) (p : Int) : Antidiagonal.runEnd j p = runEndM j p := by
  unfold Antidiagonal.runEnd runEndM
  rw [cell_memo, cell_memo]

def coneZeroM (t : Nat) : Bool :=
  EdgeSplit.xorBelow (fun j => EdgeSplit.xorBelow
    (fun q => Antidiagonal.pascalParity (t - 1 - j) q && runEndM j (-(q : Int))) (t - j)) t

theorem coneZero_memo (t : Nat) : Antidiagonal.coneZero t = coneZeroM t := by
  unfold Antidiagonal.coneZero coneZeroM
  congr 1
  funext j
  unfold Antidiagonal.coneZeroRow
  congr 1
  funext q
  unfold Antidiagonal.coneZeroTerm
  rw [runEnd_memo]

def leftConeM (t : Nat) : Bool :=
  EdgeSplit.xorBelow (fun j => EdgeSplit.xorBelow
    (fun q => Antidiagonal.pascalParity (t - 1 - j) q && runEndM j (1 - (q : Int))) (t - j)) t

theorem leftCone_memo (t : Nat) : Antidiagonal.leftCone t = leftConeM t := by
  unfold Antidiagonal.leftCone leftConeM
  congr 1
  funext j
  unfold Antidiagonal.coneRow
  congr 1
  funext q
  unfold Antidiagonal.coneTerm Antidiagonal.leftEnd
  rw [runEnd_memo]

def emit (name : String) (f : Nat → Bool) (n : Nat) : IO Unit :=
  IO.println ("SEQ " ++ name ++ " " ++ String.ofList ((List.range n).map (fun t => if f t then '1' else '0')))

end R30Sequences

open R30Sequences
"""


def lean_program(window=WINDOW, entries=None):
    """The Lean file that evaluates every entry for `t < window`."""
    entries = basis() if entries is None else entries
    lines = [LEAN_PREAMBLE.replace("__BOUND__", str(window + 2))]
    for e in entries:
        binder = "t" if re.search(r"\bt\b", e["evaluation"]) else "_"
        lines.append(f"-- {e['lean']} {' '.join(map(str, e['parameters']))}: {e['justification']}")
        lines.append(f'#eval emit "{e["id"]}" (fun {binder} => {e["evaluation"]}) {window}')
    return "\n".join(lines) + "\n"


def lean_package():
    """The Lean package whose built library the program reads: the checkout's
    `rule30-core-lean`, or `R30_CORE_LEAN` (a worktree reading the main
    checkout's build, read-only)."""
    import os
    from pathlib import Path
    return Path(os.environ.get("R30_CORE_LEAN") or repo.CORE_LEAN)


def evaluate(window=WINDOW, timeout=7200):
    """Run the program once; {id: [bits]} or raise RuntimeError with Lean's errors."""
    text = lean_program(window)
    path = repo.scratch_dir() / f"sequences-{window}.lean"
    path.write_text(text)
    code, out, err = repo.run(["lake", "env", "lean", str(path)], cwd=lean_package(), timeout=timeout)
    errors = [l for l in (out + err).splitlines() if ": error" in l or l.startswith("error")]
    if code != 0 or errors:
        raise RuntimeError("\n".join(errors[:12]) or (err or out)[-1200:])
    values = {}
    for line in out.splitlines():
        if line.startswith("SEQ "):
            _, name, bits = line.split(" ", 2)
            values[name] = [1 if c == "1" else 0 for c in bits.strip()]
    missing = [e["id"] for e in basis() if len(values.get(e["id"], [])) != window]
    if missing:
        raise RuntimeError("Lean printed no window of the right length for " + ", ".join(missing))
    return values


def chunks(bits):
    """Bits t = 0.. as little-endian 32-bit words: word i holds t in [32i, 32i+32), bit t-32i."""
    out = []
    for i in range(0, len(bits), CHUNK_BITS):
        out.append(sum(bit << k for k, bit in enumerate(bits[i:i + CHUNK_BITS])))
    return out


def unchunk(words, window):
    return [(words[t // CHUNK_BITS] >> (t % CHUNK_BITS)) & 1 for t in range(window)]


# ------------------------------------------------------------------ the data

def _q(v):
    return json.dumps(v, ensure_ascii=False)


def data_toml(values, window):
    lines = [f'spec = "{SPEC}"', f"window = {window}", f"chunk_bits = {CHUNK_BITS}",
             'evaluated_by = "bin/r30 sequences --write (lake env lean in rule30-core-lean)"', ""]
    for e in basis():
        lines += ["[[sequence]]"]
        for k in ("id", "family", "lexeme", "lean"):
            lines.append(f"{k} = {_q(e[k])}")
        lines.append(f"parameters = [{', '.join(str(p) for p in e['parameters'])}]")
        for k in ("kappa", "evaluation", "justification"):
            lines.append(f"{k} = {_q(e[k])}")
        lines.append("window = [" + ", ".join(str(w) for w in chunks(values[e["id"]])) + "]")
        lines.append("")
    for x in EXCLUDED:
        lines += ["[[excluded]]"] + [f"{k} = {_q(x[k])}" for k in ("id", "lexeme", "lean", "reason")] + [""]
    return "\n".join(lines)


def load(path=None):
    path = DATA if path is None else path
    if not path.exists():
        return None
    return tomllib.loads(path.read_text())


def problems(data):
    """What `api check` refuses in the committed data: entries that are not the
    basis, κ-labels that are not the labels of their entries, windows that are
    not `window` bits in 32-bit words."""
    if data is None:
        return ["rule30-api/model/sequences.toml is missing; run `bin/r30 sequences --write`"]
    out = []
    window = data.get("window")
    if not isinstance(window, int) or window <= 0 or window % CHUNK_BITS:
        return [f"the window {window!r} is not a positive multiple of {CHUNK_BITS}"]
    rows = data.get("sequence", [])
    declared = basis()
    if [r["id"] for r in rows] != [e["id"] for e in declared]:
        out.append("the sequences of the data are not the basis sequencemodel declares; run `bin/r30 sequences --write`")
    for r, e in zip(rows, declared):
        for k in ("family", "lexeme", "lean", "parameters", "evaluation", "justification"):
            if r.get(k) != e[k]:
                out.append(f"{r['id']}: {k} drifted from the basis; run `bin/r30 sequences --write`")
        if r.get("kappa") != sequence_kappa(r.get("lexeme"), r.get("parameters", [])):
            out.append(f"{r['id']}: the κ-label is not the label of (sequence {r.get('lexeme')} ...)")
        words = r.get("window", [])
        if len(words) != window // CHUNK_BITS or any(not (0 <= w < 1 << CHUNK_BITS) for w in words):
            out.append(f"{r['id']}: the window is not {window // CHUNK_BITS} words below 2^{CHUNK_BITS}")
    if len({r["kappa"] for r in rows}) != len(rows):
        out.append("two sequences have one κ-label")
    if [x["id"] for x in data.get("excluded", [])] != [x["id"] for x in EXCLUDED]:
        out.append("the excluded notions drifted from sequencemodel.EXCLUDED; run `bin/r30 sequences --write`")
    return out


def windows(data=None):
    """{id: [bits]} of the committed data."""
    data = load() if data is None else data
    return {r["id"]: unchunk(r["window"], data["window"]) for r in data["sequence"]}


# ---------------------------------------------------------------- the module

SEQ_T = {"kind": "named", "member": {"name": "Sequence"}, "arguments": []}
LN = list_t(NAT)
LLN = list_t(LN)


def _record(r):
    return record("Sequence", id=s(r["id"]), lexeme=s(r["lexeme"]), kappa=s(r["kappa"]),
                  window=lst([n(w) for w in r["window"]], NAT))


def declarations(data):
    rows = data["sequence"]
    window = data["window"]
    count = window // CHUNK_BITS
    prim_len = lambda x: {"kind": "primitive", "operation": "length", "result": NAT, "arguments": [x]}
    and_ = lambda a, c: {"kind": "and", "left": a, "right": c}
    not_ = lambda a: {"kind": "not", "value": a}
    return [
        structure("Sequence", [("id", STR), ("lexeme", STR), ("kappa", STR), ("window", LN)]),
        definition("windowLength", NAT, n(window), executable=True),
        definition("chunkCount", NAT, n(count), executable=True),
        definition("sequences", list_t(SEQ_T), lst([_record(r) for r in rows], SEQ_T), executable=True),
        definition("windowsOf", LLN,
                   match_list(var("xs"), {"kind": "nil", "element": LN}, "head", "tail",
                              {"kind": "cons", "head": proj(var("head"), "window"), "tail": call("windowsOf", var("tail"))}),
                   parameters=[("xs", list_t(SEQ_T))], recursive="xs", executable=True),
        definition("windows", LLN, call("windowsOf", call("sequences")), executable=True),
        field_of_each("idsOf", SEQ_T, "id"),
        field_of_each("kappasOf", SEQ_T, "kappa"),
        member_string(),
        definition("distinctStrings", BOOL,
                   match_list(var("values"), b(True), "head", "tail",
                              and_(not_(call("memberString", var("head"), var("tail"))), call("distinctStrings", var("tail")))),
                   parameters=[("values", list_t(STR))], recursive="values"),
        definition("allWordCounts", BOOL,
                   match_list(var("ws"), b(True), "head", "tail",
                              and_(beq(prim_len(var("head")), var("k")), call("allWordCounts", var("tail"), var("k")))),
                   parameters=[("ws", LLN), ("k", NAT)], recursive="ws"),
        definition("wordBelow", BOOL,
                   match_list(var("w"), b(True), "head", "tail",
                              and_(blt(var("head"), n(1 << CHUNK_BITS)), call("wordBelow", var("tail")))),
                   parameters=[("w", LN)], recursive="w"),
        definition("allWordsBelow", BOOL,
                   match_list(var("ws"), b(True), "head", "tail",
                              and_(call("wordBelow", var("head")), call("allWordsBelow", var("tail")))),
                   parameters=[("ws", LLN)], recursive="ws"),
        theorem("sequenceCountIs", prim_len(call("sequences")), n(len(rows))),
        holds("sequenceIdsDistinct", call("distinctStrings", call("idsOf", call("sequences")))),
        holds("sequenceKappasDistinct", call("distinctStrings", call("kappasOf", call("sequences")))),
        holds("windowsHaveLength", call("allWordCounts", call("windows"), call("chunkCount"))),
        holds("windowsAreBounded", call("allWordsBelow", call("windows"))),
    ]


THEOREMS = [
    {"name": "sequenceCountIs", "statement": "the basis has exactly the declared number of sequences"},
    {"name": "sequenceIdsDistinct", "statement": "the ids of the sequences are distinct"},
    {"name": "sequenceKappasDistinct", "statement": "the κ-labels of the sequences are distinct"},
    {"name": "windowsHaveLength", "statement": "every window has windowLength / 32 words"},
    {"name": "windowsAreBounded", "statement": "every word of every window is below 2^32"},
]


def render(data=None):
    from . import lexmod
    data = load() if data is None else data
    return lexmod.module(NAME, declarations(data))


def sync():
    """Render the module from the committed data (no Lean)."""
    data = load()
    if data is None or problems(data):
        return {"module": str(MODULE.relative_to(repo.ROOT)), "sequences": 0, "changed": False,
                "problems": problems(data)}
    text = render(data)
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "sequences": len(data["sequence"]), "changed": changed,
            "problems": []}


def check():
    data = load()
    bad = problems(data)
    if bad:
        return {"ok": False, "reason": bad[0]}
    if not MODULE.exists() or MODULE.read_text() != render(data):
        return {"ok": False, "reason": "Sequences.lex.tex drifted from model/sequences.toml; run `bin/r30 api sync`"}
    return {"ok": True, "reason": None}


def write(window=WINDOW):
    """Evaluate the basis in Lean and write the data and the module."""
    values = evaluate(window)
    text = data_toml(values, window)
    changed = not DATA.exists() or DATA.read_text() != text
    if changed:
        DATA.write_text(text)
    module = sync()
    return {"data": str(DATA.relative_to(repo.ROOT)), "window": window, "sequences": len(values),
            "changed": changed or module["changed"], "module": module["module"]}


def report(window=WINDOW):
    """`bin/r30 sequences` without --write: the basis and the committed data, no Lean."""
    data = load()
    return {"window": data["window"] if data else None, "requested_window": window,
            "sequences": [{"id": e["id"], "lexeme": e["lexeme"], "parameters": e["parameters"], "kappa": e["kappa"]}
                          for e in basis()],
            "excluded": EXCLUDED, "problems": problems(data)}
