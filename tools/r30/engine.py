"""`bin/r30 engine tick|status`: one deterministic cycle of the engine, and its record.

A tick, from a clean checkout of main (`.github/workflows/engine.yml` runs one
every thirty minutes off the hour, on dispatch, and on a push of the engine's
inputs):

1. `base`: record the commit the tick starts from;
2. `build`: build the research library (`lake build`, the Lake directories
   restored from the cache);
3. `induction`: `sequences --write` only when its inputs changed (the
   evaluation program and the κ-labels of the modules it imports), then
   `discover --write` at the committed window: new relations become
   `observed` claims;
4. `pruning`: `audit --write`, the conditional refutations of the period
   classified dead, live-discharged or open;
5. `deduction`: `deduce` within what is left of the budget (`deduce.py`);
6. `learning`: the tick's outcomes folded into the weights by `learnAll`
   (the certified root when built, else the mirror), the table consolidated
   in `model/engine.toml` and `Engine.lex.tex` (`api sync`);
7. `gate`: with `--commit`, `bin/r30 commit --wait` in the foreground through
   the unchanged pre-commit gate; with `--push`, `git fetch` and a push only
   when `origin/main` still is the base (otherwise the work is dropped and the
   next tick redoes it from the new main; never a force push).

Homeostasis: the budget is split across the stages from their measured
durations (the ledger's last ticks; the model's shares before any were
measured), the gate's share is reserved first and never cut, and a stage
that overruns its allowance is cut (its subprocess times out, deduction stops
scheduling attempts). When nothing changed (no new relation, every observed
claim attempted by every applicable strategy, no record other than the tick
itself) the tick ends `idle` without a commit; the workflow then marks the
commit settled and later ticks on it stop after the checkout, until a
developer pushes a new feature.

`model/engine.toml` (`r30/engine/1`) is the engine's ledger: the weights,
every attempt, and the last ticks with their stages, seconds and outcome."""

import hashlib
import json
import os
import re
import subprocess
import time
import tomllib
from datetime import datetime, timezone
from pathlib import Path

from . import enginemodel as em, repo

LEDGER = repo.ROOT / "rule30-api" / "model" / "engine.toml"
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


def record_attempt(data, attempt, tick=0):
    """Append an attempt (never one already recorded) and potentiate or depress its strategy for
    the relation's family (plasticity, the mirror of `learn`). `tick` is the tick that made it
    (0: a `deduce` run outside a tick)."""
    key = (attempt["kappa"], attempt["strategy"], attempt["template"])
    if any((a["kappa"], a["strategy"], a["template"]) == key for a in data["attempt"]):
        raise RuntimeError(f"attempt {key} is already in the ledger (the redundancy rule)")
    attempt = {**attempt, "tick": tick}
    data["attempt"].append(attempt)
    table = [(r["strategy"], r["family"], r["value"]) for r in weights(data)]
    table = em.Mirror.update(table, attempt["strategy"], attempt["family"], attempt["outcome"] in em.SUCCESS)
    data["weight"] = [{"strategy": a, "family": b, "value": c} for a, b, c in table]


def current_tick(data):
    return (data["tick"][-1]["number"] + 1) if data["tick"] else 1


def consolidate(data, tick, start):
    """Learning: the weights recomputed by `learnAll` (the certified root when built, else the
    mirror) from the table the tick started from and the tick's outcomes, checked against the
    table the attempts updated one by one."""
    from . import engine_rust
    outcomes = [(a["strategy"], a["family"], a["outcome"] in em.SUCCESS) for a in data["attempt"] if a.get("tick") == tick]
    kind, runner = engine_rust.locate(build=True)
    runtime = "python"
    if kind == "rust":
        try:
            learned = runner.learn_all(start, outcomes)
            runtime = "rust"
        except RuntimeError:
            learned = em.Mirror.learn_all(start, outcomes)
    else:
        learned = em.Mirror.learn_all(start, outcomes)
    incremental = [(r["strategy"], r["family"], r["value"]) for r in weights(data)]
    by = {(a, b): c for a, b, c in learned}
    if {(a, b): c for a, b, c in incremental} != {**{(a, b): c for a, b, c in start}, **by}:
        raise RuntimeError("the weights learned during the tick differ from learnAll over its outcomes")
    data["weight"] = [{"strategy": a, "family": b, "value": c} for (a, b), c in
                      {**{(a, b): c for a, b, c in start}, **by}.items()]
    return {"outcomes": len(outcomes), "runtime": runtime}


# ---------------------------------------------------------------- homeostasis

def measured(data):
    """{stage: seconds} of the last tick that ran each stage."""
    out = {}
    for t in data["tick"]:
        for st in t.get("stages", []):
            if st.get("outcome") in ("ok", "cut"):
                out[st["id"]] = st["seconds"]
    return out


def allowances(budget_minutes, data, elapsed=0.0, done=()):
    """The minutes each remaining stage may take: the gate's share reserved first (its model share
    scaled to the budget, or 1.25 times its measured duration when larger), every other stage its
    measured duration (its model share before one was measured) within its model share, and the
    deduction stage what is left."""
    shares = {s: b for s, b, _ in em.WORKLOAD["stages"]}
    scale = budget_minutes / em.WORKLOAD["tickBudget"]
    m = {k: v / 60 for k, v in measured(data).items()}
    gate = max(shares["gate"] * scale, 1.25 * m.get("gate", 0))
    left = budget_minutes - elapsed / 60 - gate
    out = {}
    for s in STAGES:
        if s in done or s == "gate":
            continue
        want = min(shares[s] * scale, max(m.get(s, shares[s] * scale), 1))
        out[s] = want
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


def prune_evidence():
    """On a runner (GITHUB_ACTIONS), keep the gate's evidence small enough to cache: no certificate
    or lock, only the newest tools key of each family, and only the newest slot of each LexLean
    project. A local checkout keeps its evidence as it is."""
    import shutil
    if os.environ.get("GITHUB_ACTIONS") != "true":
        return
    code, out, _ = repo.run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"])
    if code != 0:
        return
    root = Path(out.strip()) / "rule30-validation"
    if not root.exists():
        return
    for p in list(root.glob("*.ok")) + list(root.glob("*.lock")):
        p.unlink(missing_ok=True)
    newest = lambda ps: sorted(ps, key=lambda p: p.stat().st_mtime, reverse=True)
    for family in ("lake", "lexlean", "replay", "kappa"):
        d = root / family
        if d.is_dir():
            for old in newest([p for p in d.iterdir() if p.is_dir()])[1:]:
                shutil.rmtree(old, ignore_errors=True)
    lex = root / "lexlean"
    if lex.is_dir():
        for key in lex.iterdir():
            for project in (key.iterdir() if key.is_dir() else []):
                if project.is_dir():
                    for old in newest([p for p in project.iterdir() if p.is_dir()])[1:]:
                        shutil.rmtree(old, ignore_errors=True)


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


def tick(budget_minutes=300, commit=False, push=False, log=print):
    """One cycle; returns the tick summary (also recorded in the ledger)."""
    from . import cli, deduce, discover, frontier, modules, sequencemodel, discoverymodel as dm
    t0 = time.time()
    data = load()
    backfill_gate(data)
    number = current_tick(data)
    start_table = [(r["strategy"], r["family"], r["value"]) for r in weights(data)]
    _, base, _ = repo.run(["git", "rev-parse", "HEAD"])
    base = base.strip()
    summary = {"number": number, "start": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "base": base,
               "budget": budget_minutes, "stages": [], "outcome": "running", "seconds": 0.0, "commit": "",
               "observed": 0, "proved": 0, "refuted": 0, "known": 0, "attempts": 0, "new_relations": 0}
    ledger_rel = str(LEDGER.relative_to(repo.ROOT)) if LEDGER.is_relative_to(repo.ROOT) else None
    if [p for p in dirty() if p != ledger_rel]:  # the ledger may carry the record of an idle tick
        raise RuntimeError("the working tree is not clean; a tick starts from a clean checkout of main")
    done = []

    def stage(name, fn):
        allow = allowances(budget_minutes, data, time.time() - t0, done)[name]
        s0 = time.time()
        try:
            outcome, note = fn(allow)
        except Exception as e:  # a stage error ends the tick, the record says where
            outcome, note = "error", f"{type(e).__name__}: {str(e)[:400]}"
        row = {"id": name, "seconds": round(time.time() - s0, 1), "allowance": round(allow, 1), "outcome": outcome,
               "note": note[:300]}
        summary["stages"].append(row)
        done.append(name)
        log(f"[{name}] {outcome} in {row['seconds']} s (allowance {row['allowance']} min){': ' + note[:200] if note else ''}")
        if outcome == "error":
            raise RuntimeError(f"stage {name}: {note}")
        return outcome

    def build(allow):
        ok, errors = modules.build([], timeout=int(allow * 60))
        return ("ok" if ok else "error"), errors[-300:]

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

    try:
        stage("build", build)
        stage("induction", induction)
        stage("pruning", pruning)
        save(data)  # deduction reads and writes the ledger
        stage("deduction", deduction)
        data.update({k: v for k, v in load().items() if k in ("attempt", "weight")})
        stage("learning", learning)
        summary["observed"] = sum(1 for c in frontier.load()["claim"] if c["status"] == "observed")
        changed = [p for p in dirty() if p != ledger_rel]
        attempted = any(a.get("tick") == number for a in data["attempt"])
        if not changed and not attempted:
            summary["outcome"] = "idle"
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
                       f"{summary['refuted']} refuted, {summary['new_relations']} new relations observed "
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
                repo.run(["git", "fetch", "origin", "main"], timeout=600)
                _, remote, _ = repo.run(["git", "rev-parse", "origin/main"])
                if remote.strip() != base:
                    summary["outcome"] = "dropped"
                    log(f"main moved to {remote.strip()[:12]} during the tick; the work is dropped, the next tick redoes it")
                else:
                    code, out, err = repo.run(["git", "push", "origin", "HEAD:main"], timeout=1800)
                    if code != 0:
                        summary["outcome"] = "dropped"
                        log("the push was refused (main moved?): " + (err or out).strip()[-300:])
                    else:
                        summary["outcome"] = "pushed"
    finally:
        if summary["outcome"] == "running":
            summary["outcome"] = "error"
        summary["seconds"] = round(time.time() - t0, 1)
        if summary["outcome"] not in ("committed", "pushed", "dropped"):
            _record(data, summary, t0)
        log(f"tick {number}: {summary['outcome']} in {summary['seconds']} s")
        if summary["outcome"] in ("idle", "refused", "error"):
            # the workflow caches this file under the commit's key: later ticks on it stop after the checkout
            (repo.scratch_dir() / "settled").write_text(f"{base} {summary['outcome']}\n")
        gh_output(outcome=summary["outcome"], pushed="true" if summary["outcome"] == "pushed" else "false")
        prune_evidence()
    return summary


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
    from . import deduce
    pending = sum(len(r["pending"]) for r in deduce.plan(ledger=data))
    return {"last": last, "units": len(basis["sequence"]) if basis else 0, "synapses": synapses,
            "events": data["tick"][-1]["number"] if data["tick"] else 0,
            "attempts": by_outcome, "pending": pending,
            "weights": [w for w in weights(data) if w["value"] != em.W_INIT]}


def render_status(st):
    lines = [f"network: {st['units']} units (basis sequences), synapses "
             + ", ".join(f"{v} {k}" for k, v in st["synapses"].items()) + f", {st['events']} events (ticks)",
             "attempts: " + (", ".join(f"{v} {k}" for k, v in sorted(st["attempts"].items())) or "none")
             + f"; pending {st['pending']}"]
    t = st["last"]
    if t:
        lines.append(f"last tick {t['number']} ({t['start']}, base {t['base'][:12]}): {t['outcome']} in {t['seconds']} s"
                     + (f", commit {t['commit'][:12]}" if t.get("commit") else ""))
        lines.append(f"  {t['proved']} proved, {t['known']} known to the library, {t['refuted']} refuted, "
                     f"{t['new_relations']} new relations, {t['observed']} observed left, {t['attempts']} attempts")
        for s in t.get("stages", []):
            lines.append(f"  {s['id']:10s} {s['outcome']:6s} {s['seconds']:8.1f} s / {s['allowance']} min  {s.get('note', '')[:100]}")
    else:
        lines.append("no tick recorded yet")
    if st["weights"]:
        lines.append("learned weights (initial " + str(em.W_INIT) + " elsewhere): "
                     + ", ".join(f"{w['strategy']}/{w['family']}={w['value']}" for w in st["weights"]))
    return "\n".join(lines)
