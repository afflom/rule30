"""`r30`: the command surface for working on this repository.

Every command prints a short, stable text report (or JSON with `--json`) so that
an agent can act on it without reading build logs.
"""

import argparse
import json
import subprocess
import sys
import time

from . import repo, checks, frontier, leansig
from .convert import Unsupported


def out(args, data, text):
    print(repo.to_json(data) if args.json else text)


def cmd_status(args):
    code, log, _ = repo.run(["git", "log", "--oneline", "-3"])
    _, st, _ = repo.run(["git", "status", "--short"])
    _, ahead, _ = repo.run(["git", "rev-list", "--count", "origin/main..main"])
    fr = frontier.summary()
    gate = gate_state()
    data = {"head": log.strip().splitlines()[:1], "dirty": len(st.strip().splitlines()),
            "ahead_of_origin": int(ahead.strip() or 0), "frontier": fr,
            "lexlean": repo.lexlean_bin(), "gate_running": bool(gate and gate["running"])}
    text = (f"HEAD {data['head'][0] if data['head'] else '?'}\n"
            f"dirty files: {data['dirty']}; ahead of origin: {data['ahead_of_origin']}"
            + ("; GATE RUNNING" if data["gate_running"] else "") + "\n"
            f"frontier: {fr['counts']}; open: {', '.join(fr['open']) or '-'}")
    out(args, data, text)


def cmd_brief(args):
    """Everything a session needs before touching the repo, in one screen."""
    from .lexicon import Lexicon
    lx = Lexicon()
    claims = frontier.load()["claim"]
    by = {s: [c for c in claims if c["status"] == s] for s in frontier.STATUSES}
    _, head, _ = repo.run(["git", "log", "--oneline", "-1"])
    gate = gate_state()
    lines = [f"HEAD {head.strip()}" + ("   [GATE RUNNING]" if gate and gate["running"] else ""),
             "", "OPEN (the only places to work):"]
    for c in by["open"]:
        lines.append(f"  {c['id']}: {c['statement']}")
        if c.get("note"):
            lines.append(f"      {c['note']}")
    lines += ["", "PROVED REDUCTIONS (equivalent forms of the goal; use them, do not re-derive them):"]
    for c in by["proved"]:
        lines.append(f"  {c['id']}: {c['statement'][:140]}")
        lines.append(f"      Lean {c.get('lean', '-')}   lexeme {c.get('lexeme', '-')}")
    lines += ["", "REFUTED ROUTES (do not walk again):"]
    for c in by["refuted"]:
        lines.append(f"  {c['id']}: {c['statement'][:120]}")
    lines += ["", "LOOP: edit Rule30UOR/*.lean -> lake build Rule30UOR.<Module> -> bin/r30 theorem add <name>",
              "      -> bin/r30 verify paper --modules src/Observations.lex.tex (seconds) -> bin/r30 frontier set/add",
              "      -> bin/r30 commit -m ... --push (gate; minutes with warm caches). Details: AGENTS.md.",
              f"VOCABULARY: {sum(1 for e in lx.entries.values() if e.project != 'builtin')} lexemes; "
              "bin/r30 lexicon search <text>; state theorems with twopow, bxor, rowBit, naturalBit, named predicates."]
    out(args, {"open": by["open"], "proved": by["proved"], "refuted": by["refuted"]}, "\n".join(lines))


def cmd_claim(args):
    """One claim in full: register entry, Lean type, published statement, dependents."""
    from .lexicon import Lexicon
    claims = frontier.load()["claim"]
    c = next((x for x in claims if x["id"] == args.id), None)
    if c is None:
        sys.exit(f"no claim {args.id}")
    lx = Lexicon()
    data = dict(c)
    data["dependents"] = [x["id"] for x in claims if args.id in x.get("depends", [])]
    if c.get("lean"):
        from . import sexpr
        sig = leansig.signatures([c["lean"]]).get(c["lean"])
        data["lean_type"] = sexpr.dumps(sig["type"]) if sig else "unknown to Lean"
        e = lx.for_lean(c["lean"])
        if e and e.category == "proof-constant":
            for f in lx.lex_tex_files(e.package):
                text = f.read_text()
                i = text.find("\\begin{theorem}{" + e.id + "}")
                if i >= 0:
                    data["published"] = text[i:text.index("\\end{theorem}", i)].splitlines()[2]
                    data["published_in"] = str(f.relative_to(repo.ROOT))
                    break
    text = "\n".join(f"{k}: {v}" for k, v in data.items())
    out(args, data, text)


def cmd_lexicon(args):
    from .lexicon import Lexicon
    lx = Lexicon()
    if args.sub == "search":
        rows = lx.search(args.query, args.limit)
        out(args, rows, "\n".join(f"{r['id']:55s} {str(r['surface']):30s} {r['frame']:6s} "
                                  f"{r['arity']}  {r['lean'] or ''}" for r in rows) or "no match")
    elif args.sub == "show":
        e = lx.get(args.id) or lx.for_lean(args.id)
        if e is None:
            sys.exit(f"no lexeme {args.id}")
        data = {**e.row(), "signature": e.signature, "path": str(e.path) if e.path else None,
                "precedence": e.precedence, "associativity": e.associativity}
        out(args, data, "\n".join(f"{k}: {v}" for k, v in data.items()))
    elif args.sub == "packages":
        rows = [{"package": p, "project": lx.lexicon_project[p], "imports": lx.imports[p],
                 "entries": sum(1 for e in lx.entries.values() if e.package == p)}
                for p in lx.packages()]
        out(args, rows, "\n".join(f"{r['package']:20s} {r['entries']:5d} entries  "
                                  f"[{r['project']}] imports {', '.join(r['imports'])}" for r in rows))


def cmd_sig(args):
    sigs = leansig.signatures(args.names)
    from . import sexpr
    data = {n: (None if s is None else {"kind": s["kind"], "type": sexpr.dumps(s["type"])})
            for n, s in sigs.items()}
    out(args, data, "\n".join(f"{n}: {d['kind'] + ' ' + d['type'] if d else 'unknown'}"
                              for n, d in data.items()))


def cmd_theorem(args):
    from . import theorem
    try:
        results = []
        for name in args.names:
            p = theorem.add(name, args.lexicon, args.slug if len(args.names) == 1 else None,
                            args.target, dry_run=(args.sub == "preview"))
            results.append(p)
    except Unsupported as e:
        sys.exit(f"refused: {e}")
    if args.json:
        print(repo.to_json([{k: (str(v) if k == "entry_path" else v) for k, v in p.items()} for p in results]))
        return
    for p in results:
        print(f"{p['qid']}  <-  {p['lean']}  [{p['category']}, args {p['args']}]")
        if p["statement"]:
            print("  " + p["statement"])
        print("  signature: " + p["signature"][:300] + ("..." if len(p["signature"]) > 300 else ""))
        print("  probe: " + p["probe_type"][:200])
        if args.sub == "add":
            print(f"  wrote {p['entry_path'].name}" + (f" and appended to {p['target']}" if p.get('target') else "")
                  + f"; lexlean check {p['check']}")


def cmd_selfcheck(args):
    from . import theorem
    r = theorem.selfcheck(args.lexicon, args.limit)
    text = (f"checked {r['checked']}; signature mismatches {len(r['signature_mismatch'])}; "
            f"statement mismatches {len(r['statement_mismatch'])}; unsupported {len(r['unsupported'])}")
    for k in ("signature_mismatch", "statement_mismatch", "unsupported"):
        for row in r[k][:args.show]:
            text += f"\n[{k}] " + "\n   | ".join(str(x) for x in row)
    out(args, r, text)


def cmd_unpublished(args):
    from . import theorem
    rows = theorem.unpublished(args.lexicon, tuple(args.prefixes))
    if args.only_ok:
        rows = [r for r in rows if r["ok"]]
    text = "\n".join((f"OK   {r['lean']}\n     {r['statement']}" if r["ok"] else f"NO   {r['lean']}: {r['reason']}")
                     for r in rows) or "everything is published"
    out(args, rows, text)


def cmd_check(args):
    results = checks.check_all() if args.project == "all" else [checks.check(args.project, args.modules or None)]
    text = "\n".join(f"{r['project']}: {'ok' if r['ok'] else 'FAILED'}" +
                     ("".join("\n  " + d for d in r["diagnostics"]) if r["diagnostics"] else "")
                     for r in results)
    out(args, results, text)
    sys.exit(0 if all(r["ok"] for r in results) else 1)


def cmd_verify(args):
    t0 = time.time()
    r = checks.verify(args.project, args.modules or None)
    r["seconds"] = round(time.time() - t0)
    text = f"{r['project']}: {'verified ' + (r['attestation'] or '')[:16] if r['ok'] else 'FAILED'} ({r['seconds']}s)"
    if r["diagnostics"]:
        text += "".join("\n  " + d for d in r["diagnostics"])
    out(args, r, text)
    sys.exit(0 if r["ok"] else 1)


def cmd_probe(args):
    from . import theorem
    try:
        prepared = [theorem.prepare(n, args.lexicon) for n in args.names]
    except Unsupported as e:
        sys.exit(f"refused: {e}")
    errs = theorem.probe(prepared)
    out(args, {"errors": errs}, "probe ok" if not errs else "probe FAILED:\n" + "\n".join(errs[:10]))
    sys.exit(0 if not errs else 1)


def cmd_axioms(args):
    data = leansig.axioms(args.names)
    bad = {n: a for n, a in data.items() if a is None or any(x not in ("propext", "Quot.sound") for x in a)}
    text = "\n".join(f"{n}: {', '.join(a) if a else ('unknown' if a is None else 'none')}" for n, a in data.items())
    out(args, data, text)
    sys.exit(1 if bad else 0)


def cmd_choice_audit(args):
    users = leansig.choice_users(tuple(args.prefixes))
    out(args, users, "\n".join(users) if users else "no theorem depends on Classical.choice")
    sys.exit(1 if users else 0)


def cmd_frontier(args):
    if args.sub == "list":
        rows = frontier.list_claims(args.status)
        out(args, rows, "\n".join(f"[{c['status']:7s}] {c['id']}: {c['statement']}"
                                  + (f"  ({c['lean']})" if c.get('lean') else "") for c in rows) or "empty")
    elif args.sub == "add":
        c = frontier.add(args.id, args.statement, args.status, args.lean, args.lexeme, args.note, args.depends)
        frontier.render_file()
        out(args, c, f"added {c['id']} [{c['status']}]")
    elif args.sub == "set":
        c = frontier.update(args.id, status=args.status, lean=args.lean, lexeme=args.lexeme, note=args.note,
                            depends=args.depends)
        frontier.render_file()
        out(args, c, f"updated {c['id']} [{c['status']}]")
    elif args.sub == "render":
        _, skipped = frontier.render_file()
        out(args, {"skipped": skipped}, f"rendered {frontier.FRONTIER_TEX.relative_to(repo.ROOT)}"
            + (f"; not restated (no published proof-constant): {', '.join(skipped)}" if skipped else ""))
    elif args.sub == "check":
        problems = frontier.check()
        out(args, problems, "frontier register is consistent with the kernel" if not problems
            else "frontier register problems:\n  " + "\n  ".join(problems))
        sys.exit(1 if problems else 0)


def _gate_process_alive():
    """A gate process has `scripts/validate_git_tree.py` or `check_ci.sh` as an
    argument of its own (not inside a shell wrapper's -c string)."""
    import os
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            argv = open(f"/proc/{pid}/cmdline", "rb").read().split(b"\0")
        except OSError:
            continue
        if any(a.endswith((b"validate_git_tree.py", b"check_ci.sh")) for a in argv[1:3]):
            return True
    return False


def gate_state():
    """The most recent gate log and whether its process is still running."""
    logs = sorted(repo.scratch_dir().glob("commit-*.log"))
    if not logs:
        return None
    log = logs[-1]
    running = _gate_process_alive()
    tail = log.read_text().splitlines()[-3:]
    if tail and tail[-1].startswith(("   ", "Everything up-to-date")) and "->" in tail[-1]:
        running = False  # the push line is the gate's last word
    stage = next((l for l in reversed(log.read_text().splitlines())
                  if l.startswith(("make", "./scripts", "python3 scripts", "Validation already", "To https"))), "")
    return {"log": str(log), "running": running, "stage": stage[:120], "tail": [t[:160] for t in tail]}


def cmd_gate(args):
    st = gate_state()
    if st is None:
        out(args, {}, "no gate has run from this checkout")
        return
    text = (f"{'RUNNING' if st['running'] else 'finished'}: {st['log']}\n"
            f"last stage: {st['stage'] or '?'}\n" + "\n".join("  " + t for t in st["tail"]))
    out(args, st, text)


def cmd_commit(args):
    """Stage the given paths (default: all tracked changes plus new entries) and
    commit through the pre-commit gate in the background; optionally push."""
    st = gate_state()
    if st and st["running"]:
        sys.exit(f"a gate is already running ({st['log']}); wait for it: bin/r30 gate")
    paths = args.paths or ["-A"]
    repo.run(["git", "add", *paths])
    log = repo.scratch_dir() / f"commit-{int(time.time())}.log"
    script = f"git commit -F - <<'MSG' && {'git push origin main' if args.push else 'true'}\n{args.message}\n\nCo-Authored-By: {args.coauthor}\nMSG"
    with open(log, "w") as f:
        subprocess.Popen(["bash", "-c", script], cwd=repo.ROOT, stdout=f, stderr=subprocess.STDOUT,
                         start_new_session=True)
    out(args, {"log": str(log)}, f"commit running through the hook; log: {log}\n"
                                  f"poll with: tail -3 {log}")


def cmd_experiment(args):
    exp = repo.ROOT / "experiments"
    if args.sub == "list":
        rows = sorted(p.name for p in exp.glob("*.py"))
        out(args, rows, "\n".join(rows))
    else:
        script = exp / (args.name if args.name.endswith(".py") else args.name + ".py")
        code, o, e = repo.run([sys.executable, "-I", str(script), *args.args], timeout=3600)
        print(o if code == 0 else o + e)
        sys.exit(code)


def main(argv=None):
    ap = argparse.ArgumentParser(prog="r30", description=__doc__)
    ap.add_argument("--json", action="store_true")
    sp = ap.add_subparsers(dest="cmd", required=True)

    sp.add_parser("status").set_defaults(fn=cmd_status)
    sp.add_parser("brief", help="the one-screen briefing to start a session").set_defaults(fn=cmd_brief)
    s = sp.add_parser("claim", help="one frontier claim in full"); s.add_argument("id"); s.set_defaults(fn=cmd_claim)
    sp.add_parser("gate", help="is the pre-commit gate running, and where is it").set_defaults(fn=cmd_gate)

    lex = sp.add_parser("lexicon").add_subparsers(dest="sub", required=True)
    s = lex.add_parser("search"); s.add_argument("query"); s.add_argument("--limit", type=int, default=40)
    s.set_defaults(fn=cmd_lexicon)
    s = lex.add_parser("show"); s.add_argument("id"); s.set_defaults(fn=cmd_lexicon)
    lex.add_parser("packages").set_defaults(fn=cmd_lexicon)

    s = sp.add_parser("sig"); s.add_argument("names", nargs="+"); s.set_defaults(fn=cmd_sig)

    th = sp.add_parser("theorem").add_subparsers(dest="sub", required=True)
    for name in ("preview", "add"):
        s = th.add_parser(name)
        s.add_argument("names", nargs="+", help="Lean declaration names")
        s.add_argument("--lexicon", default="r30.observation")
        s.add_argument("--slug", help="entry id (single name only)")
        s.add_argument("--target", help=".lex.tex file for the statement")
        s.set_defaults(fn=cmd_theorem)

    s = sp.add_parser("check"); s.add_argument("project", nargs="?", default="all")
    s.add_argument("--modules", nargs="*"); s.set_defaults(fn=cmd_check)
    s = sp.add_parser("unpublished"); s.add_argument("prefixes", nargs="*", default=["Rule30UOR"])
    s.add_argument("--lexicon", default="r30.observation"); s.add_argument("--only-ok", action="store_true")
    s.set_defaults(fn=cmd_unpublished)
    s = sp.add_parser("selfcheck"); s.add_argument("--lexicon", default="r30.observation")
    s.add_argument("--limit", type=int); s.add_argument("--show", type=int, default=8); s.set_defaults(fn=cmd_selfcheck)
    s = sp.add_parser("verify"); s.add_argument("project", nargs="?", default="paper")
    s.add_argument("--modules", nargs="*", help="module paths relative to the project (default: all)")
    s.set_defaults(fn=cmd_verify)
    s = sp.add_parser("probe"); s.add_argument("names", nargs="+"); s.add_argument("--lexicon", default="r30.observation")
    s.set_defaults(fn=cmd_probe)
    s = sp.add_parser("axioms"); s.add_argument("names", nargs="+"); s.set_defaults(fn=cmd_axioms)
    s = sp.add_parser("choice-audit"); s.add_argument("prefixes", nargs="*", default=["Rule30UOR"])
    s.set_defaults(fn=cmd_choice_audit)

    fr = sp.add_parser("frontier").add_subparsers(dest="sub", required=True)
    s = fr.add_parser("list"); s.add_argument("--status"); s.set_defaults(fn=cmd_frontier)
    s = fr.add_parser("add"); s.add_argument("id"); s.add_argument("statement")
    s.add_argument("--status", default="open"); s.add_argument("--lean"); s.add_argument("--lexeme"); s.add_argument("--note")
    s.add_argument("--depends", nargs="*"); s.set_defaults(fn=cmd_frontier)
    s = fr.add_parser("set"); s.add_argument("id"); s.add_argument("--status"); s.add_argument("--lean")
    s.add_argument("--lexeme"); s.add_argument("--note"); s.add_argument("--depends", nargs="*"); s.set_defaults(fn=cmd_frontier)
    fr.add_parser("check").set_defaults(fn=cmd_frontier)
    fr.add_parser("render", help="write src/Frontier.lex.tex from the register").set_defaults(fn=cmd_frontier)

    s = sp.add_parser("commit"); s.add_argument("-m", "--message", required=True)
    s.add_argument("--push", action="store_true"); s.add_argument("paths", nargs="*")
    s.add_argument("--coauthor", default="Claude <noreply@anthropic.com>")
    s.set_defaults(fn=cmd_commit)

    ex = sp.add_parser("experiment").add_subparsers(dest="sub", required=True)
    ex.add_parser("list").set_defaults(fn=cmd_experiment)
    s = ex.add_parser("run"); s.add_argument("name"); s.add_argument("args", nargs="*"); s.set_defaults(fn=cmd_experiment)

    args = ap.parse_args(argv)
    args.fn(args)


if __name__ == "__main__":
    main()
