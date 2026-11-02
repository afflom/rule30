"""The certified runtime of the engine: the Rust packages of the production roots `learnAll` and
`schedule` of Engine.lex.tex and `mint` of Hypotheses.lex.tex (`bin/r30 api production`), driven by a
generated harness crate, as `discover_rust.py` drives the roots of Discovery.lex.tex.

The emitted packages represent a record as a one-constructor enum (`AdtN::C0` with the fields in
order) and a string as `Str`; the harness reads the package sources to find which enum is which, and
whether `run` returns through the overflow result `R`. It reads one request per line on stdin:

    learn <weights> <outcomes> (<strategy> <family> <value>)* (<strategy> <family> <0|1>)*
    schedule <weights> <family> <count> (<strategy> <family> <value>)* <strategy>*
    mint <attempts> <claims> <rows> <store> <budget> (<claim> <strategy> <failure>)* (<claim> <status> <kappa>)*
         (<theorem> <status> <count> <statement>*)* <label>*

with the byte fields of `mint` written as `x<hex>`, and prints the learned table, the scheduled ids,
the minted hypotheses (`<count> (<label> <form> <weight> <count> <source>*)*`), or `violation overflow`.
`runner` returns the harness or raises `NoRoot`: there is no other runtime of these roots."""

import json
import re
import shutil
from pathlib import Path

from . import enginemodel as em, production, repo

HARNESS = repo.ROOT / ".r30" / "engine-harness"
SOURCE = Path(__file__).with_name("harness") / "engine.rs"
CRATES = {name: production.crate_name(name, "engine") for name in em.PRODUCTION_ROOTS}
CRATES.update({name: production.crate_name(name, "hypotheses") for name in em.HYPOTHESES_ROOTS})


class NoRoot(RuntimeError):
    """A certified root cannot run: the caller fails or reports, it never computes the answer itself."""


def bundles():
    root = repo.ROOT / "rule30-api" / ".lexlean" / "production"
    if not root.exists():
        return []
    found = []
    for result in root.glob("*/result.json"):
        pkgs = result.parent / "packages" / "rust-std"
        if all((pkgs / crate / "Cargo.toml").exists() for crate in CRATES.values()):
            found.append(result.parent)
    return sorted(found, key=lambda p: p.stat().st_mtime, reverse=True)


def _shape(lib):
    """(weight enum, outcome enum, run signature) of an emitted package's source."""
    enums = dict((m.group(1), [x.strip() for x in m.group(2).split(",")])
                 for m in re.finditer(r"pub enum (Adt\d+) \{\s*C0\(([^)]*)\),\s*\}", lib))
    weight = next((k for k, v in enums.items() if v == ["Str", "Str", "u64"]), None)
    outcome = next((k for k, v in enums.items() if v == ["Str", "Str", "bool"]), None)
    sig = re.search(r"pub fn run\(([^)]*)\) -> ([^{]+)\{", lib)
    return weight, outcome, (sig.group(2).strip() if sig else "")


def harness_source(bundle):
    pkgs = bundle / "packages" / "rust-std"
    la, sc, mi = CRATES["learnAll"], CRATES["schedule"], CRATES["mint"]
    lw, lo, lret = _shape((pkgs / la / "src" / "lib.rs").read_text())
    sw, _, sret = _shape((pkgs / sc / "src" / "lib.rs").read_text())
    params, returned = re.search(r"pub fn run\(([^)]*)\) -> R<List<(Adt\d+)>>", (pkgs / mi / "src" / "lib.rs").read_text()).groups()
    records = re.findall(r"List<(Adt\d+)>", params)
    if not (lw and lo and sw) or len(records) != 4:
        raise NoRoot("the emitted packages do not carry the records as expected")
    at, cl, ro, _ = records
    unwrap = lambda ret: ("match r { Ok(v) => v, Err(_) => return \"violation overflow\".to_string() }"
                          if ret.startswith("R<") else "r")
    fill = {"LA": la, "SC": sc, "MI": mi, "LW": lw, "LO": lo, "SW": sw, "AT": at, "CL": cl, "RO": ro, "RET": returned,
            "LEARNED": unwrap(lret), "SCHEDULED": unwrap(sret)}
    return re.sub(r"@(\w+)@", lambda m: fill[m.group(1)], SOURCE.read_text())


def cargo_toml(bundle):
    pkgs = bundle / "packages" / "rust-std"
    deps = "\n".join(f'{crate} = {{ path = "{pkgs / crate}" }}' for crate in sorted(CRATES.values()))
    return ('[package]\nname = "r30_engine_harness"\nversion = "0.1.0"\nedition = "2021"\npublish = false\n\n'
            '[dependencies]\n' + deps + "\n\n[profile.release]\nopt-level = 3\n")


def _x(text):
    return "x" + text.encode().hex()


def _text(word):
    return bytes.fromhex(word[1:]).decode()


class Runner:
    def __init__(self, binary, bundle):
        self.binary, self.bundle = binary, bundle
        self.why = f"certified roots of {bundle.name[:12]} (lexlean production), harness built with cargo"

    def _ask(self, line):
        production.USED.add(f"certified {self.bundle.name[:12]}")
        code, out, err = repo.run([str(self.binary)], input=line + "\n", timeout=600)
        if code != 0:
            raise RuntimeError((err or out)[-800:])
        answer = out.strip("\n")
        if answer.startswith(("violation", "error")):
            raise RuntimeError(f"the certified root refused: {answer}")
        return answer

    def learn_all(self, table, outcomes):
        words = ["learn", str(len(table)), str(len(outcomes))]
        words += [str(x) for row in table for x in row]
        words += [x for s, f, ok in outcomes for x in (s, f, "1" if ok else "0")]
        w = self._ask(" ".join(words)).split()
        return [(w[i], w[i + 1], int(w[i + 2])) for i in range(0, len(w), 3)]

    def schedule(self, table, family, applicable):
        words = ["schedule", str(len(table)), family, str(len(applicable))]
        words += [str(x) for row in table for x in row] + list(applicable)
        return self._ask(" ".join(words)).split()

    def mint(self, attempts, claims, rows, store, budget):
        """`Hypotheses.mint` on (claim, strategy, failure), (claim, status, kappa) and (theorem, status, statements)."""
        words = ["mint", *map(str, (len(attempts), len(claims), len(rows), len(store), budget))]
        words += [_x(f) for row in attempts + claims for f in row]
        for theorem, status, statements in rows:
            words += [_x(theorem), _x(status), str(len(statements)), *map(_x, statements)]
        words += map(_x, store)
        w = self._ask(" ".join(words)).split()
        minted, i = [], 1
        for _ in range(int(w[0])):
            n = int(w[i + 3])
            minted.append({"label": _text(w[i]), "form": _text(w[i + 1]), "weight": int(w[i + 2]),
                           "sources": [_text(x) for x in w[i + 4:i + 4 + n]]})
            i += 4 + n
        return minted


_ready = {}


def runner():
    """The built harness of the newest bundle with every package; `NoRoot` when it cannot be had."""
    found = bundles()
    if not found:
        raise NoRoot("no production bundle with the engine and hypotheses packages (run bin/r30 api production)")
    bundle = found[0]
    if bundle in _ready:
        return _ready[bundle]
    if not shutil.which("cargo"):
        raise NoRoot("cargo is not on PATH")
    binary = HARNESS / "target" / "release" / "r30_engine_harness"
    files = {HARNESS / "Cargo.toml": cargo_toml(bundle), HARNESS / "src" / "main.rs": harness_source(bundle),
             HARNESS / "bundle.json": json.dumps({"bundle": str(bundle)})}
    (HARNESS / "src").mkdir(parents=True, exist_ok=True)
    for path, text in files.items():
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
    code, out, err = repo.run(["cargo", "build", "--release", "--offline", "--quiet"], cwd=HARNESS, timeout=1800)
    if code != 0 or not binary.exists():
        raise NoRoot("the harness did not build against the emitted packages: " + (err or out).strip()[-300:])
    _ready[bundle] = Runner(binary, bundle)
    return _ready[bundle]
