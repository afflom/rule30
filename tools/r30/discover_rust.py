"""The certified runtime of `bin/r30 discover`: the Rust packages of the
production roots of Discovery.lex.tex (`bin/r30 api production`), driven by a
generated harness crate.

`lexlean production build` publishes one package per root under
`rule30-api/.lexlean/production/<result>/packages/rust-std/<crate>/`, each a
safe Rust library with no dependencies whose `run` is the root (its
certificates A, B and E kernel-checked). The harness (`.r30/discover-harness/`,
generated, never committed) depends on the three packages by path and reads
one request per line on stdin:

    columns <width> <base count> <spec count> <words...> <specs...>
    relations <width> <column count> <words...>
    recurrence <bit count> <bits...>

and prints one answer per line: the words of each built column, the masks of
the relations, the connection polynomial, or `violation <code>` when the
checked root refused (the contract violation's two Booleans). `runner` returns
the harness or raises `engine_rust.NoRoot`: there is no other runtime of these roots."""

import json
import re
import shutil
from pathlib import Path

from . import discoverymodel as dm, engine_rust, production, repo

HARNESS = repo.ROOT / ".r30" / "discover-harness"
CRATES = {name: production.crate_name(name, "discovery") for name in dm.PRODUCTION_ROOTS}


def bundles():
    """The published bundles that carry every discovery package, newest first."""
    root = repo.ROOT / "rule30-api" / ".lexlean" / "production"
    if not root.exists():
        return []
    found = []
    for result in root.glob("*/result.json"):
        pkgs = result.parent / "packages" / "rust-std"
        if all((pkgs / crate / "Cargo.toml").exists() for crate in CRATES.values()):
            found.append(result.parent)
    return sorted(found, key=lambda p: p.stat().st_mtime, reverse=True)


def harness_source():
    """The harness's main.rs, written against the emitted API (`run` of each package, its `List`, products as tuples)."""
    fill = {"C": CRATES["buildColumns"], "R": CRATES["findRelations"], "Q": CRATES["findRecurrence"]}
    return re.sub(r"@(\w+)@", lambda m: fill[m.group(1)], (Path(__file__).with_name("harness") / "discover.rs").read_text())


def cargo_toml(bundle):
    pkgs = bundle / "packages" / "rust-std"
    deps = "\n".join(f'{crate} = {{ path = "{pkgs / crate}" }}' for crate in sorted(CRATES.values()))
    return ('[package]\nname = "r30_discover_harness"\nversion = "0.1.0"\nedition = "2021"\npublish = false\n\n'
            '[dependencies]\n' + deps + "\n\n[profile.release]\nopt-level = 3\n")


class Runner:
    """The built harness: one process per request batch."""

    def __init__(self, binary, bundle):
        self.binary, self.bundle = binary, bundle
        self.why = f"certified roots of {bundle.name[:12]} (lexlean production), harness built with cargo"

    def _ask(self, lines, timeout=3600):
        production.USED.add(f"certified {self.bundle.name[:12]}")
        code, out, err = repo.run([str(self.binary)], input="\n".join(lines) + "\n", timeout=timeout)
        if code != 0:
            raise RuntimeError((err or out)[-800:])
        answers = out.splitlines()
        for a in answers:
            if a.startswith(("violation", "error")):
                from .discover import Refused
                raise Refused(f"the certified root refused: {a}")
        return answers

    def build_columns(self, width, bases, specs):
        per = len(bases[0])
        flat = [w for b in bases for w in b] + [x for s in specs for x in s]
        line = f"columns {width} {len(bases)} {len(specs)} " + " ".join(map(str, flat))
        (answer,) = self._ask([line])
        return [[int(x) for x in col.split(",")] if col else [] for col in answer.split(" ")] if answer else []

    def find_relations(self, width, words):
        line = f"relations {width} {len(words)} " + " ".join(str(x) for w in words for x in w)
        (answer,) = self._ask([line])
        return [[int(ch) for ch in m] for m in answer.split()] if answer else []

    def find_recurrences(self, windows):
        lines = [f"recurrence {len(bits)} " + " ".join(map(str, bits)) for bits in windows]
        return [[int(ch) for ch in a] for a in self._ask(lines)]


def runner():
    """The built harness of the newest bundle with every package; `NoRoot` when it cannot be had."""
    found = bundles()
    if not found:
        raise engine_rust.NoRoot("no production bundle with the discovery packages (run bin/r30 api production)")
    if not shutil.which("cargo"):
        raise engine_rust.NoRoot("cargo is not on PATH")
    bundle = found[0]
    (HARNESS / "src").mkdir(parents=True, exist_ok=True)
    stamp = json.dumps({"bundle": str(bundle)})
    files = {HARNESS / "Cargo.toml": cargo_toml(bundle), HARNESS / "src" / "main.rs": harness_source(),
             HARNESS / "bundle.json": stamp}
    for path, text in files.items():
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
    binary = HARNESS / "target" / "release" / "r30_discover_harness"
    code, out, err = repo.run(["cargo", "build", "--release", "--offline", "--quiet"], cwd=HARNESS, timeout=1800)
    if code != 0 or not binary.exists():
        raise engine_rust.NoRoot("the harness did not build against the emitted packages: " + (err or out).strip()[-300:])
    return Runner(binary, bundle)
