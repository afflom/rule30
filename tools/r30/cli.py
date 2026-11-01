"""`r30`: the command surface for working on this repository.

Every command prints a short, stable text report (or JSON with `--json`) so that
an agent can act on it without reading build logs.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

from . import repo, checks, frontier, leansig
from .convert import Unsupported
from .errors import fail


def out(args, data, text):
    try:
        print(repo.to_json(data) if args.json else text)
    except BrokenPipeError:  # the reader (a pager, `head`) closed early
        sys.stderr.close()


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
    if by["observed"]:
        lines += ["", "OBSERVED (relations bin/r30 discover certified on a window; candidates for a Lean proof):"]
        for c in by["observed"]:
            lines.append(f"  {c['id']}: " + " + ".join(c.get("relation", [])) + f" = 0 on t < {c.get('window')}")
    lines += ["", "LOOP: edit Rule30UOR/*.lean -> lake build Rule30UOR.<Module> -> bin/r30 theorem add <name>",
              "      -> bin/r30 verify paper --modules src/Observations.lex.tex (seconds) -> bin/r30 frontier set/add",
              "      -> bin/r30 commit -m ... --push (gate; minutes with warm caches). Details: AGENTS.md.",
              f"VOCABULARY: {sum(1 for e in lx.entries.values() if e.project != 'builtin')} lexemes; "
              "bin/r30 lexicon search <text>; state theorems with twopow, bxor, rowBit, naturalBit, named predicates."]
    out(args, {"open": by["open"], "proved": by["proved"], "refuted": by["refuted"]}, "\n".join(lines))


def cmd_interface(args):
    from . import interface
    try:
        data = interface.sheet(args.id, with_related=not args.no_related)
    except ValueError as e:
        fail("R301001", str(e))
    if args.write:
        path = interface.write(args.id, data)
        print(f"wrote {path.relative_to(repo.ROOT)}")
    out(args, data, interface.render(data))


def cmd_api(args):
    """The API as a LexLean semantic module (rule30-api/src/Api.lex.tex)."""
    from . import apimodel, registermodel, archmodel, presentationmodel, observermodel, convertmodel, standardsmodel, coremodel, prismmodel, site
    from . import sequencemodel, discoverymodel
    if args.sub == "sync":
        a, r, h, p = apimodel.sync(), registermodel.sync(), archmodel.sync(), presentationmodel.sync()
        o, c, d = observermodel.sync(), convertmodel.sync(fixtures=args.fixtures), standardsmodel.sync()
        k = coremodel.sync()
        q, v = sequencemodel.sync(), discoverymodel.sync()
        m, g = prismmodel.sync(), site.sync_logo()
        if (a["changed"] or r["changed"] or h["changed"] or p["changed"] or o["changed"] or c["changed"] or d["changed"] or k["changed"]
                or q["changed"] or v["changed"]):
            locked = checks.lock("api")
        else:
            locked = {"ok": True}
        state = lambda x: " (rewritten)" if x["changed"] else " (current)"
        out(args, {"api": a, "register": r, "architecture": h, "presentation": p, "observer": o, "convert": c, "standards": d, "core": k,
                   "sequences": q, "discovery": v, "model": m, "logo": g},
            f"{a['module']}: {a['commands']} commands" + state(a) +
            f"\n{r['module']}: {r['claims']} claims" + state(r) +
            f"\n{h['module']}: {h['stakeholders']} stakeholders" + state(h) +
            f"\n{p['module']}: {p['panels']} panels" + state(p) +
            f"\n{o['module']}: {o['quadruples']} quadruples" + state(o) +
            f"\n{c['module']}: {c['fixtures']} fixtures" + state(c) +
            f"\n{d['module']}: {d['standards']} standards" + state(d) +
            f"\n{k['module']}: {k['theorems']} decided theorems, {k['vectors']}" + state(k) +
            f"\n{q['module']}: {q['sequences']} sequences" + state(q) + "".join("\n  " + x for x in q.get("problems", [])) +
            f"\n{v['module']}: {v['theorems']} decided theorems" + state(v) +
            f"\n{m['model']}: {m['claims']} claims, {m['registers']} registers" + state(m) +
            f"\n{g['logo']}" + state(g))
        if not locked["ok"]:
            fail("R303001", "lexlean lock refused api after the sync:\n" + locked["output"])
    elif args.sub == "production":
        from . import production
        if args.targets:
            t = production.targets()
            out(args, t, "\n".join(f"{k} {v}" for k, v in t["targets"].items()) or "\n".join(t["diagnostics"]))
            return
        r = production.build(replay=not args.no_replay)
        out(args, r, production.render(r))
        if not r["ok"]:
            fail("R306002" if r["stage"] == "replay" else "R306001", f"see the report above ({r['stage']})")
    else:
        results = {"api": apimodel.check(), "register": registermodel.check(), "architecture": archmodel.check(),
                   "presentation": presentationmodel.check(), "observer": observermodel.check(),
                   "convert": convertmodel.check(), "standards": standardsmodel.check(), "core": coremodel.check(),
                   "sequences": sequencemodel.check(), "discovery": discoverymodel.check(), "model": prismmodel.check(),
                   "logo": site.check_logo()}
        names = {"api": "Api.lex.tex matches the CLI", "register": "Register.lex.tex matches frontier.toml",
                 "architecture": "Architecture.lex.tex is current", "presentation": "Presentation.lex.tex and Application.lex.tex are current",
                 "observer": "Observer.lex.tex matches the register and the presentation",
                 "convert": "Convert.lex.tex matches convert.py, the glossary and the fixtures",
                 "standards": "Standards.lex.tex is current and every panel, artifact, journey and command names a standard",
                 "core": "Rule30Core.lex.tex and production/core-vectors.json match coremodel.py",
                 "sequences": "Sequences.lex.tex and model/sequences.toml are the basis, with their κ-labels",
                 "discovery": "Discovery.lex.tex matches discoverymodel.py, the basis and the register's relations",
                 "model": "model/ registers, schemas, features and CONFORMANCE.md are current", "logo": "site/logo.svg is current"}
        out(args, results, "\n".join(names[k] if v["ok"] else v["reason"] for k, v in results.items()))
        if not all(v["ok"] for v in results.values()):
            fail("R303003", ", ".join(k for k, v in results.items() if not v["ok"]))


def cmd_chain(args):
    """The reduction tree: from each root claim, the claims that rest on it
    (`depends`), with status and Lean name, so the proof plan is read as a DAG."""
    rows, text = frontier.chain()
    out(args, rows, text)


def cmd_view(args):
    """The current view for stakeholders: the artifacts `Presentation.lex.tex`
    declares (tree, register, sheets, modules, site with the data embedded)
    written into a directory; the view workflow publishes that directory."""
    from . import site
    r = site.render_view(Path(args.out))
    out(args, r, f"{r['out']}: {len(r['written'])} artifacts" + (f" at {r['commit'][:12]}" if r.get("commit") else ""))


def cmd_claim(args):
    """One claim in full: register entry, Lean type, published statement, dependents."""
    from .lexicon import Lexicon
    claims = frontier.load()["claim"]
    c = next((x for x in claims if x["id"] == args.id), None)
    if c is None:
        fail("R301001", args.id)
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
    if getattr(args, "related", False) and c.get("lean"):
        # the exact facts already proved about the claim's head constants
        sigs = leansig.signatures([c["lean"], c["lean"] + ".eq_1"])
        heads = set()
        for s in sigs.values():  # a predicate's constants are in its defining equation, a theorem's in its type
            if s:
                heads |= {n for n in _constants(s["type"]) if n.startswith("Rule30UOR.") and n != c["lean"]}
        data["related"] = {h: leansig.mentions([h]) for h in sorted(heads)}
    if getattr(args, "related", False):
        from . import auditmodel  # the conditional refutations this claim concerns, with their open hypotheses
        data["audit"] = auditmodel.related(c)
    text = "\n".join(f"{k}: {v}" for k, v in data.items() if k not in ("related", "audit"))
    for a in data.get("audit", []):
        text += f"\naudit {a['status'].upper()}: {a['theorem']}" + (f"; open: {'; '.join(a['open'])}" if a["open"] else "") \
            + (f"; refuted by {', '.join(a['refutedBy'][:3])}" if a["refutedBy"] else "")
    if data.get("related"):
        for h, rows in data["related"].items():
            text += f"\nrelated via {h} ({len(rows)}):\n  " + "\n  ".join(rows[:40]) + ("\n  ..." if len(rows) > 40 else "")
    out(args, data, text)


def _constants(node):
    """Constant names occurring in an s-expression node."""
    found = set()

    def walk(n):
        if isinstance(n, list):
            if len(n) == 2 and n[0] == "const" and isinstance(n[1], str):
                found.add(n[1])
            for x in n:
                walk(x)
    walk(node)
    return found


def cmd_audit(args):
    """The conditional refutations of the period in the research library, each
    classified dead, live-discharged or open by exact facts about theorems
    (`tools/r30/auditmodel.py`); `--write` records them in model/audit.toml and
    src/Audit.lex.tex, `--cached` reads the last record without Lean."""
    from . import auditmodel
    if args.cached:
        record = auditmodel.load()
        if record is None:
            fail("R308001", "no audit recorded yet (rule30-api/model/audit.toml); run bin/r30 audit --write")
        rep = auditmodel.report(*record)
    else:
        try:
            rep = auditmodel.run()
        except RuntimeError as e:
            fail("R308001", str(e)[:800])
    if args.write:
        bad = auditmodel.write(rep)
        if bad:
            fail("R308002", "; ".join(bad[:5]))
        checks.lock("api")
    if args.status:
        rep = {**rep, "conditionals": [e for e in rep["conditionals"] if e["status"] == args.status]}
    out(args, rep, auditmodel.render_table(rep) + (f"\nwrote {auditmodel.REGISTER.relative_to(repo.ROOT)} and "
                                                    f"{auditmodel.MODULE.relative_to(repo.ROOT)}" if args.write else ""))


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
            fail("R302001", args.id)
        data = {**e.row(), "signature": e.signature, "path": str(e.path) if e.path else None,
                "precedence": e.precedence, "associativity": e.associativity}
        out(args, data, "\n".join(f"{k}: {v}" for k, v in data.items()))
    elif args.sub == "packages":
        rows = [{"package": p, "project": lx.lexicon_project[p], "imports": lx.imports[p],
                 "entries": sum(1 for e in lx.entries.values() if e.package == p)}
                for p in lx.packages()]
        out(args, rows, "\n".join(f"{r['package']:20s} {r['entries']:5d} entries  "
                                  f"[{r['project']}] imports {', '.join(r['imports'])}" for r in rows))


def cmd_mentions(args):
    rows = leansig.mentions(args.names, tuple(args.prefixes))
    out(args, rows, "\n".join(rows) if rows else "no theorem mentions all of " + " ".join(args.names))


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
        fail("R302002", str(e))
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


def cmd_theorem_remove(args):
    from . import theorem
    rows = []
    for qid in args.qids:
        try:
            rows.append({"qid": qid, **theorem.remove(qid)})
        except Unsupported as e:
            fail("R302003", str(e))
    out(args, rows, "\n".join(f"removed {r['qid']}: entry {r['entry']}" + (f", block in {r['block']}" if r['block'] else "")
                              for r in rows))


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


def cmd_define(args):
    from . import theorem
    results, refused = theorem.define(args.names, args.lexicon, args.target)
    for p in results:
        print(f"OK   {p['qid']}: {p['statement'][:150]}")
    for name, why in refused:
        print(f"NO   {name}: {why}")
    print(f"{len(results)} defining equations published, {len(refused)} refused")


def cmd_check(args):
    results = checks.check_all() if args.project == "all" else [checks.check(args.project, args.modules or None)]
    text = "\n".join(f"{r['project']}: {'ok' if r['ok'] else 'FAILED'}" +
                     ("".join("\n  " + d for d in r["diagnostics"]) if r["diagnostics"] else "")
                     for r in results)
    out(args, results, text)
    if not all(r["ok"] for r in results):
        fail("R303001", ", ".join(r["project"] for r in results if not r["ok"]))


def cmd_verify(args):
    t0 = time.time()
    r = checks.verify(args.project, args.modules or None)
    r["seconds"] = round(time.time() - t0)
    text = f"{r['project']}: {'verified ' + (r['attestation'] or '')[:16] if r['ok'] else 'FAILED'} ({r['seconds']}s)"
    if r["diagnostics"]:
        text += "".join("\n  " + d for d in r["diagnostics"])
    out(args, r, text)
    if not r["ok"]:
        fail("R303002", r["project"])


def cmd_probe(args):
    from . import theorem
    try:
        prepared = [theorem.prepare(n, args.lexicon) for n in args.names]
    except Unsupported as e:
        fail("R302002", str(e))
    errs = theorem.probe(prepared)
    out(args, {"errors": errs}, "probe ok" if not errs else "probe FAILED:\n" + "\n".join(errs[:10]))
    if errs:
        fail("R304001", f"{len(errs)} error(s)")


def cmd_axioms(args):
    data = leansig.axioms(args.names)
    bad = {n: a for n, a in data.items() if a is None or any(x not in ("propext", "Quot.sound") for x in a)}
    text = "\n".join(f"{n}: {', '.join(a) if a else ('unknown' if a is None else 'none')}" for n, a in data.items())
    out(args, data, text)
    if bad:
        fail("R304002", ", ".join(bad))


def cmd_choice_audit(args):
    users = leansig.choice_users(tuple(args.prefixes))
    out(args, users, "\n".join(users) if users else "no theorem depends on Classical.choice")
    if users:
        fail("R304003", f"{len(users)} theorem(s)")


def _sync_register():
    """The register module follows frontier.toml (a changed plan is a changed LexLean module),
    and so does the Observer, whose real qualities are the register's proved claims."""
    from . import registermodel, observermodel, presentationmodel
    changed = registermodel.sync()["changed"]
    # every module that reads the register follows it: the Observer's real qualities are its proved
    # claims, and the Presentation's steps cite its claims (the refuted-routes step lists them all)
    changed = presentationmodel.sync()["changed"] or changed
    changed = observermodel.sync()["changed"] or changed
    if changed:
        locked = checks.lock("api")
        if not locked["ok"]:
            fail("R303001", "lexlean lock refused api after the register changed:\n" + locked["output"])
    from . import prismmodel
    prismmodel.sync()


def cmd_frontier(args):
    if args.sub == "list":
        rows = frontier.list_claims(args.status)
        out(args, rows, "\n".join(f"[{c['status']:7s}] {c['id']}: {c['statement']}"
                                  + (f"  ({c['lean']})" if c.get('lean') else "") for c in rows) or "empty")
    elif args.sub in ("add", "set"):
        try:
            if args.sub == "add":
                c = frontier.add(args.id, args.statement, args.status, args.lean, args.lexeme, args.note, args.depends,
                                 relation=args.relation, window=args.window)
            else:
                c = frontier.update(args.id, status=args.status, lean=args.lean, lexeme=args.lexeme, note=args.note,
                                    depends=args.depends, statement=args.statement, relation=args.relation,
                                    window=args.window)
        except ValueError as e:
            fail("R301003", str(e))
        # Frontier.lex.tex restates the proved and refuted claims with a Lean
        # name; a change that touches neither (an observed relation, a note)
        # leaves it as it is, and needs no Lean.
        if (c["status"] in ("proved", "refuted") if args.sub == "add" else
                any(x is not None for x in (args.status, args.lean, args.lexeme, args.statement))):
            frontier.render_file()
        _sync_register()
        out(args, c, f"{'added' if args.sub == 'add' else 'updated'} {c['id']} [{c['status']}]")
    elif args.sub == "render":
        _, skipped = frontier.render_file()
        out(args, {"skipped": skipped}, f"rendered {frontier.FRONTIER_TEX.relative_to(repo.ROOT)}"
            + (f"; not restated (no published proof-constant): {', '.join(skipped)}" if skipped else ""))
    elif args.sub == "check":
        problems = frontier.check()
        out(args, problems, "frontier register is consistent with the kernel" if not problems
            else "frontier register problems:\n  " + "\n  ".join(problems))
        if problems:
            fail("R301002", f"{len(problems)} problem(s)")


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
        fail("R305001", f"{st['log']}; wait for it: bin/r30 gate")
    paths = args.paths or ["-A"]
    # `git add` refuses a whole list when one path neither exists nor is tracked; committing the
    # rest of the index anyway once shipped a batch without its proofs, so a failed staging stops here.
    code, _, err = repo.run(["git", "add", *paths] if paths == ["-A"] else ["git", "add", "-A", "--", *paths])
    if code != 0:
        fail("R305006", "git add failed, nothing committed: " + err.strip().splitlines()[-1] if err.strip() else "git add failed")
    log = repo.scratch_dir() / f"commit-{int(time.time())}.log"
    script = f"git commit -F - <<'MSG' && {'git push origin main' if args.push else 'true'}\n{args.message}\n\nCo-Authored-By: {args.coauthor}\nMSG"
    with open(log, "w") as f:
        subprocess.Popen(["bash", "-c", script], cwd=repo.ROOT, stdout=f, stderr=subprocess.STDOUT,
                         start_new_session=True)
    out(args, {"log": str(log)}, f"commit running through the hook; log: {log}\n"
                                  f"poll with: tail -3 {log}")


def cmd_module(args):
    from . import modules
    if args.sub == "list":
        rows = modules.list_modules()
        out(args, rows, "\n".join(rows))
        return
    if args.sub == "add":
        try:
            r = modules.register(args.name)
        except (ValueError, FileNotFoundError) as e:
            fail("R305002", str(e))
        text = f"{r['module']}: " + (", ".join(r["changed"]) if r["changed"] else "already registered")
        if not args.build:
            out(args, r, text)
            return
        print(text)
        names = [r["module"]]
    else:
        names = args.names
    t0 = time.time()
    ok, errors = modules.build(names)
    report = {"ok": ok, "seconds": round(time.time() - t0, 1), "errors": errors}
    out(args, report, ("built" if ok else "build failed") + f" {' '.join(names) or 'Rule30UOR'} "
                      f"({report['seconds']}s)" + ("" if ok else "\n" + errors))
    if not ok:
        fail("R305003", " ".join(names) or "Rule30UOR")


def cmd_kappa(args):
    """The κ-label of research modules: the address of the declarations the
    kernel replays (scripts/kappa_research.py), the key of the replay receipts."""
    from . import modules
    try:
        names = [modules.qualify(n) for n in args.names]
    except ValueError as e:
        fail("R305005", str(e))
    names = names or list(modules.list_modules())
    unknown = [n for n in names if n not in modules.list_modules()]
    if unknown:
        fail("R305005", " ".join(unknown))
    kappa_research = _kappa_research()
    memo, read_only = kappa_research.working_memo(repo.CORE_LEAN)
    labels = kappa_research.memo_labels(repo.CORE_LEAN, names, memo, read_only=read_only)
    if args.duplicates:
        every = list(modules.list_modules())
        # the parents of generated names may live in modules outside the requested ones
        full = labels if set(names) == set(every) else \
            kappa_research.memo_labels(repo.CORE_LEAN, every, memo, read_only=read_only)
        groups = kappa_research.duplicates(labels, kappa_research.library_kinds(full))
        rows = [{"statement": k, "theorems": [f"{m}: {n}" for m, n in v]} for k, v in sorted(groups.items())]
        text = "\n".join(f"! {r['statement'][:19]}  " + "  =  ".join(r["theorems"]) for r in rows) \
            or "no two theorems state the same thing"
        out(args, rows, text)
        return
    data = {m: {"kappa": r["kappa"], **({"declarations": [{"name": n, "kappa": k} for n, k in r["declarations"]]}
                                        if args.declarations else {})} for m, r in labels.items()}
    out(args, data, kappa_research.render(labels, args.declarations))


def _kappa_research():
    import importlib.util
    spec = importlib.util.spec_from_file_location("kappa_research", repo.ROOT / "scripts/kappa_research.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def cmd_consolidate(args):
    """One proof per statement: plan, from the freshly built library, the consolidation of the
    theorems proved more than once (statement κ shared, `kappa --duplicates`, refused by the
    gate); with --apply, carry it out completely: remove the redundant declarations, rewrite every
    reference to the canonical theorem, add the imports, relock, rebuild, regenerate the interface
    sheets that named a removed theorem, and relabel."""
    from . import consolidate, interface, modules
    ok, errors = modules.build([])
    if not ok:
        fail("R305003", "the research library does not build; consolidation plans from the built library:\n" + errors)
    kr = _kappa_research()
    names = list(modules.list_modules())
    memo, read_only = kr.working_memo(repo.CORE_LEAN)
    labels = kr.memo_labels(repo.CORE_LEAN, names, memo, read_only=read_only)
    groups = kr.duplicates(labels)
    exact = {name: e for row in labels.values() for name, _, e in row.get("statements", [])}
    planned = consolidate.plan(groups, exact=exact)
    reason = lambda r: ("import cycle via " + ", ".join(r["cycle"]) if r.get("cycle") else
                        "binder info differs" if r.get("binders") else
                        "private, used outside its module" if r.get("hidden") else
                        "declared after a reference it would take" if r.get("early") else
                        "promoted name clashes in " + ", ".join(r["clash"]) if r.get("clash") else "wrapper")
    summary = (f"{len(groups)} redundant groups: {len(planned['keep'])} consolidable, "
               f"{len(planned['manual'])} for a person")
    lines = [f"  {r['canonical']}  <-  " + ", ".join(x["name"] for x in r["removed"])
             + (f"  (imports into {', '.join(r['imports'])})" if r["imports"] else "") for r in planned["keep"]]
    lines += [f"! {r['canonical']}  <-  " + ", ".join(x["name"] for x in r["removed"]) + f"  ({reason(r)})"
              for r in planned["manual"]]
    if not args.apply:
        out(args, planned, summary + ("\n" + "\n".join(lines) if lines else ""))
        return
    sheets = consolidate.stale_sheets(planned)
    touched = consolidate.apply(planned)
    for project, prefix in (("paper", "rule30-paper/"), ("core", "rule30-lexlean/")):
        if any(t.startswith(prefix + "glossary/") or t.startswith(prefix + "src/") for t in touched):
            locked = checks.lock(project)
            if not locked["ok"]:
                fail("R303001", f"lexlean lock refused {project} after the rewrite (git diff shows the edits):\n"
                                + locked["output"])
    ok, errors = modules.build([])
    if not ok:
        fail("R305003", "the consolidated library does not build (git diff shows the edits):\n" + errors)
    if "frontier.toml" in touched:
        # rendered from the rebuilt library, where a promoted canonical is public
        frontier.render_file()
        _sync_register()
    for claim in sheets:
        interface.write(claim)
    gone = {x["name"] for r in planned["keep"] for x in r["removed"]}
    audit_record = repo.ROOT / "rule30-api" / "model" / "audit.toml"
    if gone and audit_record.exists() and any(n in audit_record.read_text() for n in gone):
        # the audit record names a removed theorem: re-audit the rebuilt library
        rerun = subprocess.run([str(repo.ROOT / "bin" / "r30"), "audit", "--write"], cwd=repo.ROOT,
                               capture_output=True, text=True)
        if rerun.returncode != 0:
            fail("R308001", "audit --write failed after the consolidation:\n" + (rerun.stdout + rerun.stderr)[-800:])
    if any(t in ("tools/r30/convert_fixtures.json", "tools/r30/convertmodel.py") for t in touched):
        # the converter's fixtures name theorems: recapture their signatures from the rebuilt library
        sync = subprocess.run([str(repo.ROOT / "bin" / "r30"), "api", "sync", "--fixtures"], cwd=repo.ROOT,
                              capture_output=True, text=True)
        if sync.returncode != 0:
            fail("R303001", "api sync --fixtures failed after the rewrite:\n" + (sync.stdout + sync.stderr)[-800:])
    left = kr.duplicates(kr.memo_labels(repo.CORE_LEAN, names, memo, read_only=read_only))
    report = {"consolidated": len(planned["keep"]), "manual": planned["manual"], "touched": touched,
              "sheets": sheets, "remaining": len(left)}
    out(args, report, f"consolidated {len(planned['keep'])} groups across {len(touched)} files; "
                      f"{len(sheets)} interface sheets regenerated; {len(left)} redundant groups remain"
                      + ("\n" + "\n".join(lines[len(planned['keep']):]) if planned["manual"] else ""))


def cmd_sequences(args):
    """The basis of the map (Sequences.lex.tex): report it, or evaluate every
    entry in Lean and write model/sequences.toml and the module."""
    from . import sequencemodel
    if args.write:
        try:
            r = sequencemodel.write(args.window)
        except RuntimeError as e:
            fail("R307001", str(e)[:1200])
        checks.lock("api")
        out(args, r, f"{r['data']}: {r['sequences']} sequences, window {r['window']}"
            + (" (rewritten)" if r["changed"] else " (current)") + f"\n{r['module']}")
        return
    r = sequencemodel.report(args.window)
    lines = [f"{len(r['sequences'])} sequences in the basis; committed window {r['window']}"]
    lines += [f"  {x['id']}: {x['lexeme']} {x['parameters'] or ''} {x['kappa'][:19]}" for x in r["sequences"]]
    lines += ["excluded:"] + [f"  {x['id']}: {x['reason']}" for x in r["excluded"]]
    out(args, r, "\n".join(lines) + ("\nPROBLEMS:\n  " + "\n  ".join(r["problems"]) if r["problems"] else ""))
    if r["problems"]:
        fail("R307002", r["problems"][0])


def cmd_discover(args):
    """Induction mechanized: the relation and recurrence engines of
    Discovery.lex.tex on the basis (tools/r30/discover.py)."""
    from . import discover
    try:
        r = discover.run(window=args.window, degree=args.degree, write=args.write)
    except discover.BasisError as e:
        fail("R307002", str(e))
    except discover.Refused as e:
        fail("R307003", str(e)[:1200])
    out(args, r, discover.render(r))


def cmd_experiment(args):
    exp = repo.ROOT / "experiments"
    if args.sub == "list":
        rows = sorted(p.name for p in exp.glob("*.py"))
        out(args, rows, "\n".join(rows))
    else:
        script = exp / (args.name if args.name.endswith(".py") else args.name + ".py")
        code, o, e = repo.run([sys.executable, "-I", str(script), *args.args], timeout=3600)
        print(o if code == 0 else o + e)
        if code != 0:
            fail("R305004", f"{script.name} exited {code}")


def build_parser():
    """The command surface. The MCP server derives its tools from this parser,
    so a new subcommand is a new tool without further registration."""
    ap = argparse.ArgumentParser(prog="r30", description=__doc__)
    ap.add_argument("--json", action="store_true")
    sp = ap.add_subparsers(dest="cmd", required=True)

    sp.add_parser("status").set_defaults(fn=cmd_status)
    sp.add_parser("brief", help="the one-screen briefing to start a session").set_defaults(fn=cmd_brief)
    sp.add_parser("chain", help="the reduction tree of the register (depends), with status and Lean names").set_defaults(fn=cmd_chain)
    api = sp.add_parser("api", help="the API as a LexLean semantic module: sync regenerates it from the CLI, check compares").add_subparsers(dest="sub", required=True)
    s = api.add_parser("sync", help="regenerate rule30-api/src/Api.lex.tex from the CLI parser and lock")
    s.add_argument("--fixtures", action="store_true", help="re-capture the converter fixtures (Convert.lex.tex) from Lean first")
    s.set_defaults(fn=cmd_api)
    api.add_parser("check", help="refuse a CLI that drifted from Api.lex.tex").set_defaults(fn=cmd_api)
    s = api.add_parser("production", help="export the production roots of Api.lex.tex to certified Rust packages (lexlean production build) and replay the bundle")
    s.add_argument("--targets", action="store_true", help="only print the compiler's target descriptors (id and digest)")
    s.add_argument("--no-replay", action="store_true", help="do not replay the published bundle with verify-artifact")
    s.set_defaults(fn=cmd_api)
    vw = sp.add_parser("view", help="the current view for stakeholders, as Presentation.lex.tex declares it").add_subparsers(dest="sub", required=True)
    s = vw.add_parser("render", help="write the view artifacts (tree, register, sheets, modules, site) into a directory")
    s.add_argument("--out", default="view", help="the directory to write (default: view)"); s.set_defaults(fn=cmd_view)
    s = sp.add_parser("interface", help="the labeled interface sheet of a claim: chain, notions, exact facts, handles")
    s.add_argument("id"); s.add_argument("--write", action="store_true", help="also write interfaces/<id>.md")
    s.add_argument("--no-related", action="store_true"); s.set_defaults(fn=cmd_interface)
    s = sp.add_parser("claim", help="one frontier claim in full"); s.add_argument("id")
    s.add_argument("--related", action="store_true", help="also list the theorems mentioning the claim's constants")
    s.set_defaults(fn=cmd_claim)
    s = sp.add_parser("audit", help="the conditional refutations of the period, each dead, live-discharged or open by exact facts about theorems")
    s.add_argument("--write", action="store_true", help="record the audit in rule30-api/model/audit.toml and src/Audit.lex.tex")
    s.add_argument("--cached", action="store_true", help="report the last recorded audit (model/audit.toml) without running Lean")
    s.add_argument("--status", choices=["dead", "live-discharged", "open"], help="only the conditional refutations of this status")
    s.set_defaults(fn=cmd_audit)
    sp.add_parser("gate", help="is the pre-commit gate running, and where is it").set_defaults(fn=cmd_gate)

    lex = sp.add_parser("lexicon").add_subparsers(dest="sub", required=True)
    s = lex.add_parser("search"); s.add_argument("query"); s.add_argument("--limit", type=int, default=40)
    s.set_defaults(fn=cmd_lexicon)
    s = lex.add_parser("show"); s.add_argument("id"); s.set_defaults(fn=cmd_lexicon)
    lex.add_parser("packages").set_defaults(fn=cmd_lexicon)

    s = sp.add_parser("sig"); s.add_argument("names", nargs="+"); s.set_defaults(fn=cmd_sig)
    s = sp.add_parser("mentions", help="theorems whose statements mention all of the given Lean constants")
    s.add_argument("names", nargs="+"); s.add_argument("--prefixes", nargs="*", default=["Rule30UOR"])
    s.set_defaults(fn=cmd_mentions)

    th = sp.add_parser("theorem").add_subparsers(dest="sub", required=True)
    for name in ("preview", "add"):
        s = th.add_parser(name)
        s.add_argument("names", nargs="+", help="Lean declaration names")
        s.add_argument("--lexicon", default="r30.observation")
        s.add_argument("--slug", help="entry id (single name only)")
        s.add_argument("--target", help=".lex.tex file for the statement")
        s.set_defaults(fn=cmd_theorem)
    s = th.add_parser("remove", help="unpublish lexemes: delete the entry and the statement block, lock")
    s.add_argument("qids", nargs="+"); s.set_defaults(fn=cmd_theorem_remove)

    s = sp.add_parser("define", help="publish the defining equations of host definitions as lemmas")
    s.add_argument("names", nargs="+"); s.add_argument("--lexicon", default="r30.observation"); s.add_argument("--target")
    s.set_defaults(fn=cmd_define)
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
    s.add_argument("--depends", nargs="*")
    s.add_argument("--relation", nargs="*", help="the column ids of Sequences.lex.tex whose XOR vanishes (an observed claim needs one)")
    s.add_argument("--window", type=int, help="the window of the relation (default: the discovery window)")
    s.set_defaults(fn=cmd_frontier)
    s = fr.add_parser("set"); s.add_argument("id"); s.add_argument("--status"); s.add_argument("--lean")
    s.add_argument("--lexeme"); s.add_argument("--note"); s.add_argument("--depends", nargs="*")
    s.add_argument("--relation", nargs="*", help="the column ids of Sequences.lex.tex whose XOR vanishes")
    s.add_argument("--window", type=int, help="the window of the relation (default: the discovery window)")
    s.add_argument("--statement", help="restate the claim"); s.set_defaults(fn=cmd_frontier)
    fr.add_parser("check").set_defaults(fn=cmd_frontier)
    fr.add_parser("render", help="write src/Frontier.lex.tex from the register").set_defaults(fn=cmd_frontier)

    s = sp.add_parser("commit"); s.add_argument("-m", "--message", required=True)
    s.add_argument("--push", action="store_true"); s.add_argument("paths", nargs="*")
    s.add_argument("--coauthor", default="Claude <noreply@anthropic.com>")
    s.set_defaults(fn=cmd_commit)

    mo = sp.add_parser("module", help="research modules: list, add (register + skeleton), build").add_subparsers(dest="sub", required=True)
    mo.add_parser("list").set_defaults(fn=cmd_module)
    s = mo.add_parser("add", help="register a Rule30UOR module as a Lake root and audit import; create it if absent")
    s.add_argument("name"); s.add_argument("--build", action="store_true"); s.set_defaults(fn=cmd_module)
    s = mo.add_parser("build", help="lake build the given modules (all research modules when none)")
    s.add_argument("names", nargs="*"); s.set_defaults(fn=cmd_module)

    s = sp.add_parser("consolidate", help="one proof per statement: plan, or with --apply carry out, the removal of theorems proved more than once (statement κ shared, refused by the gate), rebuilding and regenerating what named them")
    s.add_argument("--apply", action="store_true", help="edit the sources, relock, rebuild, regenerate the interface sheets that named a removed theorem, and relabel")
    s.set_defaults(fn=cmd_consolidate)
    s = sp.add_parser("kappa", help="the κ-label of research modules: the address of the declarations the kernel replays (uor-addr), the key of the replay receipts")
    s.add_argument("names", nargs="*", help="Rule30UOR module names (default: every research module)"); s.add_argument("--declarations", action="store_true", help="also each declaration's κ")
    s.add_argument("--duplicates", action="store_true", help="theorems across the modules whose statements share a κ-label (the same theorem proved twice)")
    s.set_defaults(fn=cmd_kappa)

    s = sp.add_parser("sequences", help="the basis of the map (Sequences.lex.tex): every sequence with its lexeme, parameters, κ-label and window; --write evaluates the windows in Lean")
    s.add_argument("--window", type=int, default=512, help="the number of times t < N to evaluate (default 512: twice the discovery window, which the dilations read)")
    s.add_argument("--write", action="store_true", help="evaluate the basis from the host Lean definitions and write model/sequences.toml and Sequences.lex.tex")
    s.set_defaults(fn=cmd_sequences)
    s = sp.add_parser("discover", help="induction mechanized: the relations (Gaussian elimination over F2) and the recurrences (Berlekamp-Massey) of the basis, minus the register's, through the certified roots of Discovery.lex.tex")
    s.add_argument("--window", type=int, default=256, help="the discovery window W (at most half the stored window)")
    s.add_argument("--degree", type=int, choices=[1, 2], default=2, help="2 adds the pairwise ANDs of the cell columns |p| <= 3")
    s.add_argument("--write", action="store_true", help="append the new relations to the register as status observed")
    s.set_defaults(fn=cmd_discover)

    ex = sp.add_parser("experiment").add_subparsers(dest="sub", required=True)
    ex.add_parser("list").set_defaults(fn=cmd_experiment)
    s = ex.add_parser("run"); s.add_argument("name"); s.add_argument("args", nargs="*"); s.set_defaults(fn=cmd_experiment)

    return ap


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        args.fn(args)
    except RuntimeError as e:  # `leansig`: the research library did not answer
        fail("R304004", str(e)[:800])


if __name__ == "__main__":
    main()
