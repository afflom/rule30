"""`bin/r30 engine tick|status`: one deterministic cycle of the engine, and its record.

A tick, from a clean checkout of main (`.github/workflows/engine.yml` runs one
every thirty minutes off the hour, on dispatch, and on a push of the engine's
inputs):

1. `base`: record the commit the tick starts from;
2. `build`: build the research library as the gate's `make core` does
   (`modules.build`: `LexLeanRuntime.Laws`, which no Lake root covers, then
   `lake build`; the Lake directories restored from the cache). A build cut by
   its allowance ends the tick `cut`, and the next tick resumes it;
3. `induction`: `sequences --write` only when its inputs changed (the
   evaluation program and the κ-labels of the modules it imports), then
   `discover --write` at the committed window: new relations become
   `observed` claims;
4. `pruning`: `audit --write`, the conditional refutations of the period
   classified dead, live-discharged or open;
5. `deduction`: `deduce` within what is left of the budget (`deduce.py`);
6. `learning`: the tick's outcomes folded into the weights by the certified
   root `learnAll`, the table consolidated in `model/engine.toml` and
   `Engine.lex.tex` (`api sync`);
7. `hypotheses`: the certified root `mint` on the ledger, the register and the
   audit, its new rows appended to `model/hypotheses.toml`; its budget is the
   model's (`hypothesisBudget`), scaled like the stage shares. A row is a change,
   so a tick that minted is not idle. The store is no input of `mint` but as the
   labels to leave out and no other stage reads it, so the rows end once the
   store holds what the ledger and the audit give;
8. `gate`: with `--commit`, `bin/r30 commit --wait` in the foreground through
   the unchanged pre-commit gate; with `--push`, `git fetch` and a push only
   when `origin/main` still is the base (otherwise the work is dropped and the
   next tick redoes it from the new main; never a force push). A push the
   remote rejects while main has not moved is no race: the tick is `refused`.
   With `--push`, a tick whose base is no longer `origin/main` when it starts
   (a queued run, or main moved during the setup) ends `stale` at once.

Homeostasis: the gate's share is reserved first and never cut (its model share
scaled to the budget, or 1.25 times its last measured duration when larger),
every other stage may take its model share, and deduction takes what the
earlier stages left; a stage that overruns its allowance is cut (its
subprocess times out, deduction stops scheduling attempts and never runs one
past its deadline). Only a stage that finished is measured: a cut is a lower
bound, not a duration. When nothing changed (no new relation, every observed
claim attempted by every applicable strategy, no record other than the tick
itself) and nothing was cut or is still pending, the tick ends `idle` without
a commit; the workflow then marks the commit settled and later ticks on it
stop after the checkout, until a developer pushes a new feature. A tick that
changed nothing because a stage was cut ends `cut`, which settles nothing: the
next tick on the commit does the work. A certified root that cannot run ends the
tick `error`: there is no other runtime of the roots.

`model/engine.toml` (`r30/engine/1`) is the engine's ledger: the weights,
every attempt, and the last ticks with their stages, seconds and outcome.

`prune_evidence` (`bin/r30 engine prune --apply`, which the workflow runs
before caching) keeps of the gate's evidence only what the next run can use:
the current tools key's Lake builds, LexLean attestations (the newest per
project) and replay receipts, the current κ memo, and never a certificate."""

import hashlib
import json
import os
import re
import subprocess
import time
import tomllib
from datetime import datetime, timezone
from pathlib import Path

from . import enginemodel as em, production, repo

LEDGER = repo.ROOT / "rule30-api" / "model" / "engine.toml"
HYPOTHESES = LEDGER.with_name("hypotheses.toml")
SPEC = "r30/engine/1"
KEEP_TICKS = 12
STAGES = [s for s, _, _ in em.WORKLOAD["stages"]]


# ----------------------------------------------------------------- the ledger

def load(path=None):
    path = LEDGER if path is None else path
    data = tomllib.loads(path.read_text()) if path.exists() else {}
    data.setdefault("weight", [])
    data.setdefault("attempt", [])
    data.setdefault("tick", [])
    data.setdefault("spec", SPEC)
    return data


def _q(v):
    return json.dumps(v, ensure_ascii=False)


def _inline(d):
    return "{" + ", ".join(f"{k} = {_value(v)}" for k, v in d.items()) + "}"


def _value(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return repr(v)
    if isinstance(v, dict):
        return _inline(v)
    if isinstance(v, list):
        return "[" + ", ".join(_value(x) for x in v) + "]"
    return _q(str(v))


def dumps(data):
    lines = ["# The engine's ledger (bin/r30 engine, deduce): the consolidated weights, every attempt,",
             "# and the last ticks. Written by the engine only.", f'spec = "{SPEC}"']
    for k in ("sequences_input",):
        if data.get(k):
            lines.append(f"{k} = {_q(data[k])}")
    lines.append("")
    for w in sorted(data["weight"], key=lambda r: (r["strategy"], r["family"])):
        lines += ["[[weight]]", f"strategy = {_q(w['strategy'])}", f"family = {_q(w['family'])}", f"value = {int(w['value'])}", ""]
    for a in data["attempt"]:
        lines.append("[[attempt]]")
        for k in ("claim", "kappa", "strategy", "template", "family", "outcome", "failure", "theorem"):
            lines.append(f"{k} = {_q(a.get(k, ''))}")
        if a.get("library"):  # library-rewrite: the library its facts were read from (deduce.library_digest)
            lines.append(f"library = {_q(a['library'])}")
        lines += [f"seconds = {float(a.get('seconds', 0))}", f"tick = {int(a.get('tick', 0))}", ""]
    for t in data["tick"][-KEEP_TICKS:]:
        lines.append("[[tick]]")
        for k, v in t.items():
            lines.append(f"{k} = {_value(v)}")
        lines.append("")
    return "\n".join(lines)


def save(data, path=None):
    path = LEDGER if path is None else path
    path.parent.mkdir(parents=True, exist_ok=True)
    text = dumps(data)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def weights(data):
    """The weight rows, the initial table completed by the consolidated rows."""
    have = {(r["strategy"], r["family"]): r["value"] for r in data["weight"]}
    return [{"strategy": st, "family": f, "value": have.get((st, f), v)} for st, f, v in em.initial_table()]


def attempt_key(attempt):
    """What an attempt is never repeated for: the claim κ, the strategy, its template digest, and for
    library-rewrite the library digest (the facts it reads; empty for the other strategies)."""
    return attempt["kappa"], attempt["strategy"], attempt["template"], attempt.get("library", "")


def record_attempt(data, attempt, tick=0):
    """Append an attempt (never one already recorded). `tick` is the tick that made it (0: a `deduce`
    run outside a tick); the weights follow by `learned`, at the end of the tick or the run."""
    key = attempt_key(attempt)
    if any(attempt_key(a) == key for a in data["attempt"]):
        raise RuntimeError(f"attempt {key} is already in the ledger (the redundancy rule)")
    data["attempt"].append({**attempt, "tick": tick})


def current_tick(data):
    return (data["tick"][-1]["number"] + 1) if data["tick"] else 1


def learned(table, attempts):
    """`table` with the attempts' outcomes folded in by the certified root `learnAll`, as weight rows."""
    from . import engine_rust
    outcomes = [(a["strategy"], a["family"], a["outcome"] in em.SUCCESS) for a in attempts]
    return [{"strategy": a, "family": b, "value": c} for a, b, c in engine_rust.runner().learn_all(table, outcomes)]


def consolidate(data, tick, start):
    """Learning: the weights recomputed by `learnAll` from the table the tick started from and the tick's outcomes."""
    attempts = [a for a in data["attempt"] if a.get("tick") == tick]
    data["weight"] = learned(start, attempts)
    return {"outcomes": len(attempts), "runtime": "certified"}


# ---------------------------------------------------------------- hypotheses

def store(path=None):
    """The rows of the hypothesis store (`model/hypotheses.toml`, `r30/hypotheses/1`)."""
    path = HYPOTHESES if path is None else path
    return tomllib.loads(path.read_text()).get("hypothesis", []) if path.exists() else []


def mint(tick, budget, data=None):
    """New hypotheses by the certified root `Hypotheses.mint`, appended to the store; the rule of what is
    live and what is known is the root's. Nothing here or there reads a minted row but to leave it out."""
    from . import auditmodel, engine_rust, frontier
    data = load() if data is None else data
    record = auditmodel.load()
    if record is None:
        raise RuntimeError("no audit recorded yet; run bin/r30 audit --write")
    rows = [(r["theorem"], r["status"], [h["statement"] for h in r["hypotheses"] if h["status"] == "open"]) for r in record[0]]
    if not all(all(statements) for _, _, statements in rows):
        raise RuntimeError("the audit carries an open hypothesis without its statement; run bin/r30 audit --write")
    attempts = [(a["claim"], a["strategy"], a.get("failure", "")) for a in data["attempt"]]
    claims = [(c["id"], c["status"], c.get("kappa", "")) for c in frontier.load()["claim"]]
    minted = engine_rust.runner().mint(attempts, claims, rows, [r["label"] for r in store()], budget)
    lines = [] if HYPOTHESES.exists() else ['# The labelled hypotheses (bin/r30 engine): written by the engine only.', 'spec = "r30/hypotheses/1"', ""]
    for m in minted:
        lines += ["[[hypothesis]]", f"label = {_q(m['label'])}", f"form = {_q(m['form'])}", f"sources = {_value(m['sources'])}",
                  f"weight = {m['weight']}", f"tick = {tick}", 'status = "minted"', ""]
    with HYPOTHESES.open("a") as f:
        f.write("".join(line + "\n" for line in lines))
    return minted


# ---------------------------------------------------------------- homeostasis

def measured(data):
    """{stage: seconds} of the last tick that finished each stage (a cut stage's seconds are a lower
    bound of its duration, not a measurement)."""
    out = {}
    for t in data["tick"]:
        for st in t.get("stages", []):
            if st.get("outcome") == "ok":
                out[st["id"]] = st["seconds"]
    return out


def allowances(budget_minutes, data, elapsed=0.0, done=()):
    """The minutes each remaining stage may take: the gate's share reserved first (its model share
    scaled to the budget, or 1.25 times its measured duration when larger), every other stage its
    model share scaled to the budget, and the deduction stage what is left (recomputed when it
    starts, so the time an earlier stage did not use goes to deduction). A stage's limit is never
    its last duration: a rebuild or a re-evaluation of the basis takes what its share allows."""
    shares = {s: b for s, b, _ in em.WORKLOAD["stages"]}
    scale = budget_minutes / em.WORKLOAD["tickBudget"]
    m = {k: v / 60 for k, v in measured(data).items()}
    gate = max(shares["gate"] * scale, 1.25 * m.get("gate", 0))
    left = budget_minutes - elapsed / 60 - gate
    out = {}
    for s in STAGES:
        if s in done or s == "gate":
            continue
        out[s] = shares[s] * scale
    rest = sum(v for k, v in out.items() if k != "deduction")
    if "deduction" in out:
        out["deduction"] = max(0.0, left - rest)
    total = sum(out.values())
    if total > max(left, 0):  # overrun: everything but the gate shrinks proportionally
        f = max(left, 0) / total if total else 0
        out = {k: v * f for k, v in out.items()}
    out["gate"] = gate
    return out


# -------------------------------------------------------------------- stages

def sequences_input():
    """The inputs of `sequences --write`: the evaluation program and the κ-labels of the modules
    it imports, with their imports in the research library."""
    from . import cli, sequencemodel
    program = sequencemodel.lean_program(sequencemodel.WINDOW)
    roots = re.findall(r"^import (Rule30UOR\.\S+)", program, re.M)
    mods, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in mods:
            continue
        mods.add(m)
        path = repo.CORE_LEAN / (m.replace(".", "/") + ".lean")
        if path.exists():
            todo += re.findall(r"^(?:public )?import (Rule30UOR\.\S+)", path.read_text(), re.M)
    kr = cli._kappa_research()
    memo, read_only = kr.working_memo(repo.CORE_LEAN)
    labels = kr.memo_labels(repo.CORE_LEAN, sorted(mods), memo, read_only=read_only)
    h = hashlib.sha256(program.encode())
    for m in sorted(labels):
        h.update(f"{m} {labels[m]['kappa']}\n".encode())
    return "sha256:" + h.hexdigest()


def build_library(allow):
    """The build stage: the research library as the gate's `make core` builds it (`modules.build`:
    `LexLeanRuntime.Laws`, then `lake build Rule30UOR`) within `allow` minutes. A build its allowance
    cuts is `cut` (the Lake directories are cached either way, so the next tick resumes it); a
    failed one is `error`, with its first errors."""
    from . import modules
    try:
        ok, errors = modules.build([], timeout=int(allow * 60))
    except subprocess.TimeoutExpired:
        return "cut", f"lake build did not finish within {allow:.0f} min; the next tick resumes it"
    return ("ok" if ok else "error"), errors[:300]


def _r30(args, timeout):
    """A `bin/r30` subcommand as a stage step: (ok, output tail)."""
    try:
        p = subprocess.run([str(repo.ROOT / "bin" / "r30"), *args], cwd=repo.ROOT, capture_output=True, text=True,
                           timeout=max(30, int(timeout)))
    except subprocess.TimeoutExpired:
        return None, f"cut after {int(timeout)} s"
    return p.returncode == 0, (p.stdout + p.stderr).strip()[-1500:]


def dirty():
    _, out, _ = repo.run(["git", "status", "--porcelain"])
    return [line[3:] for line in out.splitlines() if line.strip()]


def gh_output(**kv):
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a") as f:
            for k, v in kv.items():
                f.write(f"{k}={v}\n")


def gate_tools_key(root=None, env=None):
    """The key under which the gate (`scripts/validate_git_tree.py`) keeps its Lake builds, LexLean
    attestations and replay receipts, computed as the gate computes it: the SHA-256 of the toolchain
    of HEAD, `lean --version` and `lake --version` under it, `lexlean --version`, the compiler's
    bytes and the gate script's bytes, extended by `tools`, cut to 16 hex digits (the tests run the
    gate on a fixture and compare). None when a tool cannot be run."""
    import shutil
    root = Path(repo.ROOT if root is None else root)
    env = dict(os.environ if env is None else env)

    def output(*args, environ=None):
        p = subprocess.run(args, cwd=root, env=env if environ is None else environ, capture_output=True, text=True)
        if p.returncode != 0:
            raise RuntimeError(f"{args[0]} exited {p.returncode}")
        return p.stdout.strip()
    try:
        toolchain = output("git", "show", "HEAD:rule30-core-lean/lean-toolchain")
        configured = (env.get("LEXLEAN_BIN") or env.get("LEXLEAN")
                      or subprocess.run(["git", "config", "--get", "rule30.lexlean"], cwd=root, env=env,
                                        capture_output=True, text=True).stdout.strip())
        local = root / ".local" / "bin" / "lexlean"
        compiler = shutil.which(configured or (str(local) if local.exists() else "lexlean"), path=env.get("PATH"))
        if not compiler:
            return None
        compiler = str(Path(compiler).resolve())
        version = output(compiler, "--version")
        clean = dict(env)
        for name in output("git", "rev-parse", "--local-env-vars").splitlines():
            clean.pop(name, None)
        for name in ("ELAN_TOOLCHAIN", "MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES"):
            clean.pop(name, None)
        clean.update(LEXLEAN_BIN=compiler, ELAN_TOOLCHAIN=toolchain)
        lean_version = output("lean", "--version", environ=clean)
        lake_version = output("lake", "--version", environ=clean)
        digest = hashlib.sha256()
        for item in (toolchain, lean_version, lake_version, version):
            digest.update(item.encode() + b"\0")
        digest.update(Path(compiler).read_bytes())
        digest.update((root / "scripts" / "validate_git_tree.py").read_bytes())
    except (OSError, RuntimeError):
        return None
    digest.update(b"tools")
    return digest.hexdigest()[:16]


def kappa_procedure():
    """The κ memo's current store: the digest of the labeling procedure (`kappa_research.py`)."""
    from . import cli
    try:
        return cli._kappa_research().exporter_digest(repo.CORE_LEAN)
    except (OSError, ImportError):
        return None


def evidence_dir():
    """The gate's evidence: `rule30-validation` in the Git common directory."""
    code, out, _ = repo.run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"])
    return Path(out.strip()) / "rule30-validation" if code == 0 and out.strip() else None


def _size(path):
    if path.is_symlink() or not path.is_dir():
        return path.lstat().st_size if path.exists() or path.is_symlink() else 0
    return sum(f.lstat().st_size for f in path.rglob("*") if f.is_file() or f.is_symlink())


def prune_evidence(apply=False, root=None, key=None, procedure=None):
    """What of the gate's evidence the next run can use, and what it cannot (deleted with `apply`).
    Kept: under `lake/`, `lexlean/` and `replay/` only the current tools key (`gate_tools_key`; the
    newest directory when it cannot be computed), within the LexLean attestations of that key only
    the newest complete slot of each project (`scripts/verify_lexlean.sh`: one slot per input
    digest), and of the κ memo only the current procedure's store. Dropped besides: every file of
    the top level (the `.ok` certificates, which say a tree passed and which a later run must
    establish itself, and their locks) and unfinished slots (`*.new*`)."""
    import shutil
    root = evidence_dir() if root is None else Path(root)
    report = {"root": str(root or ""), "key": None, "procedure": None, "kept": [], "dropped": [],
              "kept_bytes": 0, "dropped_bytes": 0, "applied": bool(apply)}
    if root is None or not root.is_dir():
        return report
    key = gate_tools_key() if key is None else key
    procedure = kappa_procedure() if procedure is None else procedure
    report.update(key=key, procedure=procedure)
    keep, drop = [], []
    unfinished = lambda p: p.name.endswith(".new") or ".new." in p.name

    def newest(paths):
        return max(paths, key=lambda p: p.stat().st_mtime) if paths else None
    drop += [p for p in sorted(root.iterdir()) if not p.is_dir()]
    chosen = {}
    for family, current in (("lake", key), ("lexlean", key), ("replay", key), ("kappa", procedure)):
        d = root / family
        if not d.is_dir():
            continue
        entries = sorted(d.iterdir())
        pick = d / current if current else newest([p for p in entries if p.is_dir() and not unfinished(p)])
        chosen[family] = pick if pick is not None and pick.is_dir() else None
        drop += [p for p in entries if p != chosen[family]]
    if chosen.get("lexlean"):
        for project in sorted(p for p in chosen["lexlean"].iterdir() if p.is_dir()):
            slots = [s for s in project.iterdir() if s.is_dir() and not unfinished(s) and (s / "latest-verified.json").is_file()]
            best = newest(slots)
            drop += [s for s in sorted(project.iterdir()) if s != best]
    if chosen.get("lake"):  # a package slot whose copy was interrupted (validate_git_tree.store_lake_cache)
        drop += [p for p in sorted(chosen["lake"].rglob("*.new")) if p.is_dir()]
    keep = [p for p in (chosen.get(f) for f in ("lake", "lexlean", "replay", "kappa")) if p is not None]
    for p in drop:
        report["dropped"].append(str(p.relative_to(root)))
        report["dropped_bytes"] += _size(p)
    report["kept"] = [str(p.relative_to(root)) for p in keep]
    report["kept_bytes"] = sum(_size(p) for p in keep) - sum(_size(p) for p in drop if any(p.is_relative_to(k) for k in keep))
    if apply:
        for p in drop:
            if p.is_dir() and not p.is_symlink():
                shutil.rmtree(p, ignore_errors=True)
            else:
                p.unlink(missing_ok=True)
    return report


def render_prune(r):
    if not r["root"]:
        return "no gate evidence here"
    mb = lambda n: f"{n / 2 ** 20:.1f} MB"
    head = (f"gate evidence {r['root']}: tools key {r['key'] or '(not computable: the newest kept)'}, "
            f"κ procedure {r['procedure'] or '(the newest kept)'}")
    lines = [head, f"kept {len(r['kept'])} ({mb(r['kept_bytes'])}): " + ", ".join(r["kept"]),
             f"{'dropped' if r['applied'] else 'to drop'} {len(r['dropped'])} ({mb(r['dropped_bytes'])})"
             + ("" if r["applied"] else "; --apply deletes them")]
    return "\n".join(lines)


def backfill_gate(data):
    """The gate's duration of the last committed tick, which its own record cannot carry (the record
    is part of the commit the gate validates): the commit's time (written once the hook accepted
    it) less the tick's start and the seconds before the gate. Homeostasis reads it next tick."""
    for t in reversed(data["tick"]):
        if t.get("outcome") not in ("committed", "pushed") or any(s["id"] == "gate" for s in t.get("stages", [])):
            continue
        code, out, _ = repo.run(["git", "log", "-1", "--format=%ct", "--fixed-strings", f"--grep=Engine tick {t['number']}:"])
        if code != 0 or not out.strip():
            return None
        start = datetime.strptime(t["start"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()
        seconds = round(max(0.0, int(out.strip()) - start - t["seconds"]), 1)
        t["stages"] = t.get("stages", []) + [{"id": "gate", "seconds": seconds, "allowance": 0.0, "outcome": "ok",
                                               "note": "measured by the next tick from the commit's time"}]
        return seconds
    return None


def main_moved(base):
    """origin/main after a fetch, when it is not `base`; None when it is, or when the fetch fails (a
    network error is no move)."""
    code, _, _ = repo.run(["git", "fetch", "origin", "main"], timeout=600)
    if code != 0:
        return None
    _, remote, _ = repo.run(["git", "rev-parse", "origin/main"])
    remote = remote.strip()
    return remote if remote and remote != base else None


def tick(budget_minutes=300, commit=False, push=False, log=print):
    """One cycle; returns the tick summary (also recorded in the ledger, but for a stale tick)."""
    from . import deduce, discover, frontier, sequencemodel, discoverymodel as dm
    t0 = time.time()
    data = load()
    backfill_gate(data)
    number = current_tick(data)
    start_table = [(r["strategy"], r["family"], r["value"]) for r in weights(data)]
    _, base, _ = repo.run(["git", "rev-parse", "HEAD"])
    base = base.strip()
    summary = {"number": number, "start": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "base": base,
               "budget": budget_minutes, "stages": [], "outcome": "running", "seconds": 0.0, "commit": "",
               "observed": 0, "proved": 0, "refuted": 0, "known": 0, "attempts": 0, "new_relations": 0, "minted": 0}
    ledger_rel = str(LEDGER.relative_to(repo.ROOT)) if LEDGER.is_relative_to(repo.ROOT) else None
    if [p for p in dirty() if p != ledger_rel]:  # the ledger may carry the record of an idle tick
        raise RuntimeError("the working tree is not clean; a tick starts from a clean checkout of main")
    moved = main_moved(base) if push else None
    if moved:
        # a queued run, or main moved during the setup: whatever this tick did would be dropped at the
        # push, and the run on the new main does it; nothing is recorded and nothing is settled
        summary.update(outcome="stale", seconds=round(time.time() - t0, 1))
        log(f"tick {number}: stale (main is {moved[:12]}, this run's commit {base[:12]})")
        gh_output(outcome="stale", pushed="false")
        return summary
    done = []

    def stage(name, fn):
        allow = allowances(budget_minutes, data, time.time() - t0, done)[name]
        s0 = time.time()
        production.USED.clear()
        try:
            outcome, note = fn(allow)
        except Exception as e:  # a stage error ends the tick, the record says where
            outcome, note = "error", f"{type(e).__name__}: {str(e)[:400]}"
        row = {"id": name, "seconds": round(time.time() - s0, 1), "allowance": round(allow, 1), "outcome": outcome,
               "note": note[:300], "runtime": ", ".join(sorted(production.USED)) or "no root"}
        summary["stages"].append(row)
        done.append(name)
        log(f"[{name}] {outcome} in {row['seconds']} s (allowance {row['allowance']} min){': ' + note[:200] if note else ''}")
        if outcome == "error":
            raise RuntimeError(f"stage {name}: {note}")
        return outcome

    def induction(allow):
        notes = []
        want = sequences_input()
        if want != data.get("sequences_input") or sequencemodel.load() is None:
            ok, out = _r30(["sequences", "--write"], allow * 60)
            if not ok:
                return ("cut" if ok is None else "error"), "sequences --write: " + out[-300:]
            data["sequences_input"] = want
            notes.append("sequences re-evaluated")
        window = dm.discovery_width(sequencemodel.load())
        r = discover.run(window=window, degree=2, write=True)
        summary["new_relations"] = len(r["written"])
        notes.append(f"discover: {r['counts']['new']} new, {len(r['written'])} written")
        return "ok", "; ".join(notes)

    def pruning(allow):
        ok, out = _r30(["audit", "--write"], allow * 60)
        return ("ok" if ok else "cut" if ok is None else "error"), out.splitlines()[0] if out else ""

    def deduction(allow):
        if allow <= 0.5:
            return "cut", "no budget left"
        rep = deduce.run(budget_minutes=allow, log=log, tick=number)
        for k in ("proved", "refuted", "known"):
            summary[k] = len(rep[k])
        summary["attempts"] = len(rep["attempts"])
        return ("cut" if rep["skipped"] else "ok"), deduce.render(rep).splitlines()[0]

    def learning(allow):
        info = consolidate(data, number, start_table)
        save(data)
        r = subprocess.run([str(repo.ROOT / "bin" / "r30"), "api", "sync"], cwd=repo.ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            return "error", "api sync: " + (r.stdout + r.stderr)[-300:]
        return "ok", f"{info['outcomes']} outcomes through learnAll ({info['runtime']})"

    def hypotheses(allow):
        if allow <= 0:
            return "cut", "no budget left"
        minted = mint(number, round(em.WORKLOAD["hypothesisBudget"] * budget_minutes / em.WORKLOAD["tickBudget"]), data)
        summary["minted"] = len(minted)
        return "ok", f"{len(minted)} minted through mint"

    try:
        if stage("build", build_library) == "cut":
            summary["outcome"] = "cut"  # nothing runs on an unbuilt library; the next tick resumes the build
            summary["pending"] = None
            if stalled(data, summary):
                summary["outcome"] = "stalled"
                raise RuntimeError(f"the build was cut {STALL_TICKS + 1} ticks in a row on {base[:12]} without "
                                   "finishing; its share of the budget is too small for this library")
            return summary
        stage("induction", induction)
        stage("pruning", pruning)
        save(data)  # deduction reads and writes the ledger
        stage("deduction", deduction)
        data.update({k: v for k, v in load().items() if k in ("attempt", "weight")})
        stage("learning", learning)
        stage("hypotheses", hypotheses)
        summary["observed"] = sum(1 for c in frontier.load()["claim"] if c["status"] == "observed")
        changed = [p for p in dirty() if p != ledger_rel]
        attempted = any(a.get("tick") == number for a in data["attempt"])
        if not changed and not attempted:
            # idle only when nothing is left: a stage that was cut, or an attempt still pending (left
            # for the budget), is the next tick's work on this commit, so this one settles nothing
            cut = any(s["outcome"] == "cut" for s in summary["stages"])
            pending = sum(len(r["pending"]) for r in deduce.plan(ledger=data))
            summary["outcome"] = "cut" if cut or pending else "idle"
            summary["pending"] = pending
            if summary["outcome"] == "cut" and stalled(data, summary):
                # homeostasis failed: the same work is cut again and again with no progress
                summary["outcome"] = "stalled"
                raise RuntimeError(f"{STALL_TICKS + 1} ticks in a row on {base[:12]} were cut with the same "
                                   f"{pending} attempts pending and nothing changed")
        elif any(p.startswith(".github/") for p in changed):
            raise RuntimeError("the tick changed a workflow file; GITHUB_TOKEN cannot push it: " + ", ".join(changed))
        elif not commit:
            summary["outcome"] = "uncommitted"
        else:
            # the record the commit carries: the outcome the gate's acceptance makes true
            summary["outcome"] = "committed"
            _record(data, summary, t0)

            def gate(allow):
                msg = (f"Engine tick {number}: {summary['proved']} proved, {summary['known']} known to the library, "
                       f"{summary['refuted']} refuted, {summary['new_relations']} new relations observed, {summary['minted']} hypotheses minted "
                       f"(base {base[:12]})")
                ok, out = _r30(["commit", "--wait", "--coauthor", "", "-m", msg], 10 ** 6)
                return ("ok" if ok else "error"), out.splitlines()[-1] if out else ""
            try:
                stage("gate", gate)
            except RuntimeError:
                summary["outcome"] = "refused"
                raise
            _, head, _ = repo.run(["git", "rev-parse", "HEAD"])
            summary["commit"] = head.strip()
            if push:
                moved = main_moved(base)
                if moved:
                    summary["outcome"] = "dropped"
                    log(f"main moved to {moved[:12]} during the tick; the work is dropped, the next tick redoes it")
                else:
                    code, out, err = repo.run(["git", "push", "origin", "HEAD:main"], timeout=1800)
                    if code != 0 and not REJECTED.search(out + err) and not main_moved(base):
                        # a transport failure (5xx, reset), not a decision of the remote: try once more
                        code, out, err = repo.run(["git", "push", "origin", "HEAD:main"], timeout=1800)
                    if code == 0:
                        summary["outcome"] = "pushed"
                    else:
                        why = (err or out).strip()[-300:]
                        fcode, _, _ = repo.run(["git", "fetch", "origin", "main"], timeout=600)
                        _, remote, _ = repo.run(["git", "rev-parse", "origin/main"])
                        if fcode == 0 and remote.strip() == base and REJECTED.search(out + err):
                            # no race: main did not move, so the remote refuses the engine's push itself
                            # (a branch rule GITHUB_TOKEN cannot pass); every tick would repeat it
                            summary["outcome"] = "refused"
                            raise RuntimeError("the remote rejected the push while main is still the base: " + why)
                        summary["outcome"] = "dropped"
                        log("the push failed and main moved (or cannot be read); the work is dropped, the next tick "
                            "redoes it: " + why)
    finally:
        if summary["outcome"] == "running":
            summary["outcome"] = "error"
        summary["seconds"] = round(time.time() - t0, 1)
        if summary["outcome"] not in ("committed", "pushed", "dropped"):
            _record(data, summary, t0)
        log(f"tick {number}: {summary['outcome']} in {summary['seconds']} s")
        if summary["outcome"] in ("idle", "refused", "error", "stalled"):
            # the workflow caches this file under the commit's key: later ticks on it stop after the checkout
            (repo.scratch_dir() / "settled").write_text(f"{base} {summary['outcome']}\n")
        gh_output(outcome=summary["outcome"], pushed="true" if summary["outcome"] == "pushed" else "false")
    return summary


STALL_TICKS = 2  # earlier ticks that, with this one, make a stall


def stalled(data, summary):
    """Whether this cut tick repeats the last STALL_TICKS ticks exactly: same base, each cut, the same
    work pending, nothing committed. Such a tick would recur every half hour with no progress, so it
    ends `stalled`: the job fails (visible) and the base is settled until a new commit arrives."""
    previous = [t for t in data.get("tick", []) if t.get("number") != summary["number"]][-STALL_TICKS:]
    return len(previous) == STALL_TICKS and all(
        t.get("base") == summary["base"] and t.get("outcome") == "cut" and t.get("pending") == summary.get("pending")
        for t in previous)


# What the remote says when it decides against a push (a rule, a protected branch, a non-fast-forward
# it will not take): only these make a tick `refused`; anything else is transport and is `dropped`.
REJECTED = re.compile(r"\[remote rejected\]|! \[rejected\]|protected branch|GH00[0-9]|GH01[0-9]")


def _record(data, summary, t0):
    """The tick summary into the ledger (the last KEEP_TICKS kept)."""
    summary["seconds"] = round(time.time() - t0, 1)
    data["tick"] = [t for t in data["tick"] if t["number"] != summary["number"]] + [dict(summary)]
    save(data)


def status(data=None):
    """The last tick, the counts of the register and the ledger, and the network (units, synapses, events)."""
    from . import frontier, sequencemodel
    data = load() if data is None else data
    claims = frontier.load()["claim"]
    basis = sequencemodel.load()
    last = data["tick"][-1] if data["tick"] else None
    synapses = {st: sum(1 for c in claims if c.get("relation") and c["status"] == st) for st in ("observed", "proved", "refuted")}
    by_outcome = {}
    for a in data["attempt"]:
        by_outcome[a["outcome"]] = by_outcome.get(a["outcome"], 0) + 1
    from . import deduce, engine_rust
    try:
        pending = sum(len(r["pending"]) for r in deduce.plan(ledger=data))
    except engine_rust.NoRoot as e:
        pending = f"unknown ({e})"
    rows = store()
    forms = {f: sum(1 for r in rows if r["form"].startswith(f"(9:{f}") or r["form"].startswith(f"(10:{f}")) for f in ("exclusion", "obligation")}
    return {"last": last, "hypotheses": {"total": len(rows), **forms}, "units": len(basis["sequence"]) if basis else 0, "synapses": synapses,
            "events": data["tick"][-1]["number"] if data["tick"] else 0,
            "attempts": by_outcome, "pending": pending,
            "weights": [w for w in weights(data) if w["value"] != em.W_INIT]}


def render_status(st):
    lines = [f"network: {st['units']} units (basis sequences), synapses "
             + ", ".join(f"{v} {k}" for k, v in st["synapses"].items()) + f", {st['events']} events (ticks)",
             "attempts: " + (", ".join(f"{v} {k}" for k, v in sorted(st["attempts"].items())) or "none")
             + f"; pending {st['pending']}"]
    h = st["hypotheses"]
    lines.append(f"hypotheses: {h['total']} labelled ({h['exclusion']} exclusions, {h['obligation']} obligations)")
    t = st["last"]
    if t:
        lines.append(f"last tick {t['number']} ({t['start']}, base {t['base'][:12]}): {t['outcome']} in {t['seconds']} s"
                     + (f", commit {t['commit'][:12]}" if t.get("commit") else ""))
        lines.append(f"  {t['proved']} proved, {t['known']} known to the library, {t['refuted']} refuted, "
                     f"{t['new_relations']} new relations, {t.get('minted', 0)} hypotheses minted, {t['observed']} observed left, {t['attempts']} attempts")
        for s in t.get("stages", []):
            lines.append(f"  {s['id']:10s} {s['outcome']:6s} {s['seconds']:8.1f} s / {s['allowance']} min  [{s.get('runtime', 'not recorded')}]  {s.get('note', '')[:100]}")
    else:
        lines.append("no tick recorded yet")
    if st["weights"]:
        lines.append("learned weights (initial " + str(em.W_INIT) + " elsewhere): "
                     + ", ".join(f"{w['strategy']}/{w['family']}={w['value']}" for w in st["weights"]))
    return "\n".join(lines)
