"""Tests for the engine (suite `engine` of ids.toml): the workload of
`.github/workflows/engine.yml` as decided data (`tools/r30/enginemodel.py`,
`rule30-api/src/Engine.lex.tex`), the tick and its record (`tools/r30/engine.py`),
deduction (`tools/r30/deduce.py`) and its portfolio of proof templates, and the
learning layer with its certified roots (`tools/r30/engine_rust.py`).

They need no Lean build: the Lean check of an attempt and the stages of a tick
are replaced by recorded answers; the templates are rendered for real relations
of the basis and their Boolean cores decided in Python, as `deduce` does before
it runs Lean. Each PrismPM id of the suite has a test whose name ends in the id."""

from pathlib import Path
import json
import random
import re
import sys
import tempfile
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.r30 import deduce, engine, enginemodel as em, frontier, repo, schema  # noqa: E402


def claim(relation, cid="observed-test"):
    from tools.r30 import discoverymodel as dm, sequencemodel
    data = sequencemodel.load()
    return {"id": cid, "status": "observed", "statement": "test", "relation": relation, "window": 256,
            "kappa": dm.relation_kappa(relation, dm.kappas_of(data))}


def needs_basis(test):
    from tools.r30 import sequencemodel
    if sequencemodel.load() is None:
        test.skipTest("model/sequences.toml is absent (bin/r30 sequences --write)")


class EngineTests(unittest.TestCase):

    # -------------------------------------------------------------- the workload

    def test_workflow_is_rendered_from_the_decided_workload_engine_workload(self):
        text = em.WORKFLOW.read_text()
        self.assertEqual(text, em.render_workflow())
        self.assertEqual(em.workflow_problems(text), [])
        self.assertIn('- cron: "17,47 * * * *"', text)
        self.assertIn("  workflow_dispatch:\n", text)
        self.assertIn("  push:\n    branches: [main]\n    paths:\n", text)
        self.assertNotIn("pull_request", text)
        self.assertIn("permissions:\n  contents: write\n  actions: write\n\n", text)
        self.assertIn("concurrency:\n  group: r30-engine\n  cancel-in-progress: false\n", text)
        self.assertIn("runs-on: ubuntu-24.04", text)
        self.assertIn("timeout-minutes: 340", text)
        self.assertIn("if: github.repository == 'afflom/rule30' && vars.R30_ENGINE != 'off'", text)
        self.assertIn("run: bin/r30 engine tick --budget-minutes 300 --commit --push", text)
        self.assertIn("make hooks", text)
        self.assertIn("gh workflow run view.yml --ref main", text)
        self.assertIn("fetch-depth: 0", text)
        # caches: the compiler, the Lake builds, the gate's evidence without certificates, the settled mark
        for key in ("r30-lexlean-", "r30-lake-", "r30-gate-", "r30-settled-"):
            self.assertIn(key, text)
        self.assertIn("-name '*.ok'", text)
        self.assertEqual(set(re.findall(r"secrets\.(\w+)", text)), set())
        self.assertEqual(set(re.findall(r"uses:\s*(\S+)", text)), set(em.WORKLOAD["actions"]))
        # the actions allowed are those the repository's other workflows and actions already use
        used = set()
        for p in list((ROOT / ".github").rglob("*.yml")):
            if p.name != "engine.yml":
                used |= set(re.findall(r"uses:\s*(\S+)", p.read_text()))
        self.assertTrue(set(em.WORKLOAD["allowedActions"]) - {"actions/cache/restore@v4", "actions/cache/save@v4",
                                                               "./.github/actions/setup-proof-tools"} <= used | {"actions/cache@v4"})
        # the drift and safety checks refuse what they should
        self.assertTrue(em.workflow_problems(text + "\n  env:\n    X: ${{ secrets.MODEL_KEY }}\n"))
        self.assertTrue(em.workflow_problems(text + "\n      - uses: some/action@v1\n"))
        self.assertTrue(em.workflow_problems(text.replace("workflow_dispatch:", "pull_request:")))
        # the module decides the facts the file rests on
        module = em.MODULE.read_text()
        for name in ("onlyGithubToken", "permissionsContentsActionsWrite", "stageBudgetsFillTheTick",
                     "stageBudgetsFitTheTimeout", "gateKeepsItsShare", "cronOffTheHour", "concurrencySingle",
                     "actionsAlreadyUsed", "portfolioIdsDistinct", "templatesPinnedByDigest"):
            self.assertIn(f"name: {name},", module)
        self.assertEqual(sum(b for _, b, _ in em.WORKLOAD["stages"]), em.WORKLOAD["tickBudget"])
        self.assertLessEqual(em.WORKLOAD["setupMinutes"] + em.WORKLOAD["tickBudget"], em.WORKLOAD["timeoutMinutes"])
        self.assertTrue(all(0 < m < 60 for m in em.WORKLOAD["cronMinutes"]))
        self.assertTrue(em.check()["ok"], em.check()["reason"])

    # -------------------------------------------------------------- the portfolio

    def test_templates_are_pinned_and_render_real_relations_strategy_portfolio(self):
        needs_basis(self)
        ids = [p["id"] for p in em.PORTFOLIO]
        self.assertEqual(len(ids), len(set(ids)))
        digests = [em.template_digest(i) for i in ids]
        self.assertEqual(len(set(digests)), len(digests))
        module = em.MODULE.read_text()
        for i, d in zip(ids, digests):
            self.assertIn(d, module)
            self.assertTrue(em.template_path(i).read_text().startswith(f"-- r30 deduce template: {i}, revision"))
        # the digest covers the template and the renderer that fills it
        import hashlib
        tmpl = em.template_path("step-induction").read_bytes()
        self.assertEqual(em.template_digest("step-induction"), "sha256:" + hashlib.sha256(
            b"template\0" + tmpl + b"\0renderer\0" + em.RENDERER.read_bytes()).hexdigest())
        # applicability and families
        apps, fam = deduce.applicable(claim(["time-parity", "rdiag(3)", "shift:rdiag(3)"]))
        self.assertEqual(fam, "right-shift")
        self.assertEqual(apps, ["library-rewrite", "step-induction", "period-reduction"])
        apps, fam = deduce.applicable(claim(["even:ldiag(2)"]))
        self.assertEqual((fam, apps), ("left-dilated", ["library-rewrite", "step-induction"]))
        apps, fam = deduce.applicable(claim(["one", "time-parity", "center", "low-diagonal", "interior-three-diagonal"]))
        self.assertEqual((fam, apps), ("open", ["library-rewrite"]))
        # the orbit decides the finite systems exactly: ldiag 7 is white forever, ldiag 3 is not
        self.assertIsNone(deduce.orbit(["ldiag(7)"])["fail"])
        self.assertEqual(deduce.orbit(["ldiag(3)"])["fail"], 3)
        self.assertEqual(deduce.applicable(claim(["ldiag(3)"]))[0], ["library-rewrite", "counterexample"])
        # every template renders a theorem of the statement, with no sorry and no tactic outside the vocabulary
        c = claim(["time-parity", "rdiag(3)", "shift:rdiag(3)"])
        name = deduce.theorem_name(c["relation"], c["kappa"])
        self.assertEqual(name, "rdiag3_succ_eq_timeParity_xor_rdiag3")
        stmt = "Core.rdiag 3 (t + 1) = Core.bxor (EdgeParity.timeParity (t)) (Core.rdiag 3 (t))"
        self.assertEqual(deduce.statement(c["relation"]), stmt)
        for sid in ("step-induction", "period-reduction"):
            body, _ = deduce.RENDER[sid](c, name, {})
            self.assertIn(f"theorem {name} (t : Nat) : {stmt} := by", body)
            self.assertIn(em.template_digest(sid)[:19], body)
            self.assertNotIn("sorry", body)
            self.assertNotRegex(body, r"\b(omega|simp|native_decide|Classical)\b")
        body, info = deduce.render_library_rewrite(claim(["rdiag(3)", "rdiag(4)", "exposed(2)", "shift:rdiag(4)"]), "x", {}, facts=[])
        self.assertIn("show Core.bxor (Core.rdiag 4 (t)) (Core.rdiag 3 (t) || Core.rdiag 2 (t)) =", body)
        self.assertIn("revert a0 a1 a2", body)
        # the Boolean core is decided before Lean: without the library's fact rdiag 2 = time parity it fails
        with self.assertRaises(deduce.Unprovable):
            deduce.render_library_rewrite(c, name, {}, facts=[])
        fact = {"lean": "Rule30UOR.Band.rdiag_two_eq_parity", "lhs": ("col", "base", "rdiag", 2),
                "rhs": ("col", "base", "time-parity", None)}
        body, info = deduce.render_library_rewrite(c, name, {}, facts=[fact])
        self.assertEqual(info["facts"], ["Rule30UOR.Band.rdiag_two_eq_parity"])
        self.assertEqual(info["imports"], ["Rule30UOR.Band"])
        self.assertIn("have h : Core.rdiag 2 (t) = EdgeParity.timeParity (t) := Rule30UOR.Band.rdiag_two_eq_parity (t)", body)
        self.assertIn("all_goals exact h", body)
        # rewriting never closes a goal by rfl before the tactics that follow it (`rewrite`, not `rw`)
        self.assertNotRegex(body.split(":= by", 1)[1].split("\n  show", 1)[0].replace("    rw [", ""), r"\n  rw \[")
        # a fact that excludes no assignment (time parity is the word 1) is not instantiated
        taut = {"lean": "Rule30UOR.Antidiagonal.towerWord_one", "lhs": ("col", "base", "tower-word", 1),
                "rhs": ("col", "base", "time-parity", None)}
        _, info = deduce.render_library_rewrite(c, name, {}, facts=[fact, taut])
        self.assertEqual(info["facts"], ["Rule30UOR.Band.rdiag_two_eq_parity"])
        # a library theorem that states the relation proves it: no new theorem
        same = {"lean": "Rule30UOR.Band.rdiag_two_eq_parity", "lhs": ("col", "base", "rdiag", 2),
                "rhs": ("col", "base", "time-parity", None)}
        stated = {"publishable": {"Rule30UOR.Band.rdiag_two_eq_parity": True}}
        self.assertEqual(deduce.render_library_rewrite(claim(["time-parity", "rdiag(2)"]), "y", stated, facts=[same]),
                         (None, {"known": "Rule30UOR.Band.rdiag_two_eq_parity"}))
        # ... unless LexLean cannot state it (it reads `decide (m % 2 = 1)`): then the fact proves a new theorem
        unstated = {"publishable": {"Rule30UOR.Band.rdiag_two_eq_parity": False}}
        body, info = deduce.render_library_rewrite(claim(["time-parity", "rdiag(2)"]), "y", unstated, facts=[same])
        self.assertIn("theorem y (t : Nat) : Core.rdiag 2 (t) = EdgeParity.timeParity (t) := by", body)
        # the counterexample: the iteration evaluated at the failing time
        body, info = deduce.render_counterexample(claim(["ldiag(3)"]), "ldiag3_eq_false_fails")
        self.assertEqual(info["counterexample"], 3)
        self.assertIn("theorem ldiag3_eq_false_fails : Core.ldiag 3 (3) = !(false) := by", body)

    def test_signatures_parse_into_library_facts_strategy_portfolio(self):
        nat = lambda k: ["app", ["const", "OfNat.ofNat"], ["const", "Nat"], ["nat", str(k)], ["app", ["const", "instOfNatNat"], ["nat", str(k)]]]
        mod2 = ["app", ["const", "HMod.hMod"], ["const", "Nat"], ["const", "Nat"], ["const", "Nat"], ["app", ["const", "instHMod"]],
                ["local", "m"], nat(2)]
        sig = {"kind": "theorem", "type": ["pi", "explicit", "m", ["const", "Nat"], [
            "app", ["const", "Eq"], ["const", "Bool"], ["app", ["const", "Rule30UOR.Core.rdiag"], nat(2), ["local", "m"]],
            ["app", ["const", "Decidable.decide"], ["app", ["const", "Eq"], ["const", "Nat"], mod2, nat(1)], ["const", "inst"]]]]}
        f = deduce.parse_fact("Rule30UOR.Band.rdiag_two_eq_parity", sig)
        self.assertEqual(deduce.fact_relation(f), ["rdiag(2)", "time-parity"])
        plus1 = ["app", ["const", "HAdd.hAdd"], ["const", "Nat"], ["const", "Nat"], ["const", "Nat"], ["const", "i"], ["local", "m"], nat(1)]
        sig2 = {"kind": "theorem", "type": ["pi", "explicit", "m", ["const", "Nat"], [
            "app", ["const", "Eq"], ["const", "Bool"], ["app", ["const", "Rule30UOR.Core.ldiag"], nat(1), plus1], ["const", "Bool.true"]]]}
        self.assertEqual(deduce.fact_relation(deduce.parse_fact("x", sig2)), ["one", "shift:ldiag(1)"])
        # the successor form states the same relation (Core.ldiag_one: ldiag 1 (Nat.succ s) = true)
        succ = ["app", ["const", "Nat.succ"], ["local", "m"]]
        sig3 = {"kind": "theorem", "type": ["pi", "explicit", "m", ["const", "Nat"], [
            "app", ["const", "Eq"], ["const", "Bool"], ["app", ["const", "Rule30UOR.Core.ldiag"], nat(1), succ], ["const", "Bool.true"]]]}
        self.assertEqual(deduce.fact_relation(deduce.parse_fact("Rule30UOR.Core.ldiag_one", sig3)), ["one", "shift:ldiag(1)"])
        self.assertIsNone(deduce.parse_fact("y", {"kind": "def", "type": sig["type"]}))

    # -------------------------------------------------------------- the learning layer

    def test_learning_rule_scheduler_and_certified_roots_strategy_learning(self):
        m = em.Mirror
        for w in range(em.W_MIN, em.W_MAX + 1):
            for ok in (True, False):
                self.assertTrue(em.W_MIN <= m.learn(w, ok) <= em.W_MAX)
        self.assertEqual(m.learn(em.W_MAX, True), em.W_MAX)
        self.assertEqual(m.learn(em.W_MIN, False), em.W_MIN)
        self.assertEqual(m.learn(8, True), 8 + em.RAISE)
        self.assertEqual(m.learn(8, False), 8 - em.LOWER)
        rnd = random.Random(30)
        ids = [p["id"] for p in em.PORTFOLIO]
        for _ in range(200):
            table = [(s, f, rnd.randint(em.W_MIN, em.W_MAX)) for s in ids for f in em.FAMILIES[:3]]
            fam = rnd.choice(em.FAMILIES[:3])
            apps = [x for x in ids if rnd.random() < 0.7]
            order = m.schedule(table, fam, apps)
            self.assertEqual(sorted(order), sorted(apps))  # a permutation
            ws = [m.weight_of(x, fam, table) for x in order]
            self.assertEqual(ws, sorted(ws, reverse=True))  # by weight
            for a, b in zip(order, order[1:]):  # ties in portfolio order
                if m.weight_of(a, fam, table) == m.weight_of(b, fam, table):
                    self.assertLess(apps.index(a), apps.index(b))
        # the module decides the mirror's fixtures and the invariants over the committed table
        module = em.MODULE.read_text()
        for name in ("learnStaysInBounds", "committedWeightsBounded", "learnAllFixture", "everyScheduleIsSound",
                     "scheduleFixture0", "scheduleFixture1", "scheduleFixture2"):
            self.assertIn(f"name: {name},", module)
        self.assertIn("production: {effects: [allocation, overflow, recursion], targets: [rust-std]}", module)
        from tools.r30 import production
        roots = {r["root"] for r in production.roots()}
        self.assertTrue({"Rule30Api.Engine.learnAll", "Rule30Api.Engine.schedule"} <= roots)
        # the certified roots agree with the mirror (when `bin/r30 api production` has built them)
        from tools.r30 import engine_rust
        kind, runner = engine_rust.locate(build=True)
        if kind != "rust":
            self.skipTest(f"no certified roots to compare: {runner}")
        start = em.initial_table()
        self.assertEqual(runner.learn_all(start, em.FIXTURE_OUTCOMES), m.learn_all(start, em.FIXTURE_OUTCOMES))
        learned = m.learn_all(start, em.FIXTURE_OUTCOMES)
        for fam, apps in em.FIXTURE_SCHEDULES:
            self.assertEqual(runner.schedule(learned, fam, apps), m.schedule(learned, fam, apps))
        for _ in range(30):  # and on random tables, outcomes and subsets
            table = [(s, f, rnd.randint(em.W_MIN, em.W_MAX)) for s in ids for f in em.FAMILIES]
            outs = [(rnd.choice(ids), rnd.choice(em.FAMILIES), rnd.random() < 0.5) for _ in range(rnd.randint(0, 20))]
            self.assertEqual(runner.learn_all(table, outs), m.learn_all(table, outs))
            fam, apps = rnd.choice(em.FAMILIES), [x for x in ids if rnd.random() < 0.7]
            self.assertEqual(runner.schedule(table, fam, apps), m.schedule(table, fam, apps))

    # -------------------------------------------------------------- the ledger

    def test_ledger_roundtrip_redundancy_and_reproducible_weights_engine_ledger(self):
        data = engine.load(Path("/nonexistent/engine.toml"))
        self.assertEqual((data["weight"], data["attempt"], data["tick"]), ([], [], []))
        a = {"claim": "observed-x", "kappa": "sha256:" + "a" * 64, "strategy": "step-induction",
             "template": em.template_digest("step-induction"), "family": "left-plain", "outcome": "proved",
             "failure": "", "seconds": 0.4, "theorem": "Rule30UOR.Deduced.x"}
        engine.record_attempt(data, a)
        with self.assertRaises(RuntimeError):
            engine.record_attempt(data, dict(a))  # the same (claim, strategy, template) twice
        engine.record_attempt(data, {**a, "strategy": "library-rewrite", "template": em.template_digest("library-rewrite"),
                                     "outcome": "failed", "failure": "(decided in Python) ..."})
        w = {(r["strategy"], r["family"]): r["value"] for r in engine.weights(data)}
        self.assertEqual(w[("step-induction", "left-plain")], em.W_INIT + em.RAISE)
        self.assertEqual(w[("library-rewrite", "left-plain")], em.W_INIT - em.LOWER)
        # the weights are reproducible from the attempts
        replay = em.Mirror.learn_all(em.initial_table(), [(x["strategy"], x["family"], x["outcome"] in em.SUCCESS)
                                                          for x in data["attempt"]])
        self.assertEqual({(s, f): v for s, f, v in replay}, w)
        data["tick"].append({"number": 1, "start": "2026-11-01T00:00:00Z", "base": "0" * 40, "budget": 300,
                             "stages": [{"id": "build", "seconds": 12.5, "allowance": 60.0, "outcome": "ok", "note": ""}],
                             "outcome": "committed", "seconds": 13.0, "commit": "", "observed": 0, "proved": 1, "refuted": 0,
                             "known": 0, "attempts": 2, "new_relations": 0})
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "engine.toml"
            engine.save(data, path)
            back = engine.load(path)
            self.assertEqual(back["attempt"][0]["template"], a["template"])
            self.assertEqual(back["tick"][0]["stages"][0]["seconds"], 12.5)
            self.assertEqual(engine.weights(back), engine.weights(data))
            self.assertEqual(tomllib.loads(path.read_text())["spec"], "r30/engine/1")
        if engine.LEDGER.exists():  # the committed ledger is well formed and in bounds
            real = engine.load()
            keys = [(x["kappa"], x["strategy"], x["template"]) for x in real["attempt"]]
            self.assertEqual(len(keys), len(set(keys)))
            self.assertTrue(all(em.W_MIN <= r["value"] <= em.W_MAX for r in real["weight"]))

    # -------------------------------------------------------------- deduction

    def test_deduce_records_attempts_once_and_settles_proofs_deduce_command(self):
        needs_basis(self)
        rel = ["time-parity", "rdiag(3)", "shift:rdiag(3)"]
        c = claim(rel, "observed-test")
        with tempfile.TemporaryDirectory() as d:
            ledger_path = Path(d) / "engine.toml"
            saved = {}
            patches = [(frontier, "load", lambda: {"claim": [c]}), (engine, "LEDGER", ledger_path),
                       (deduce, "check", lambda name, body, imports, timeout: ("proved", "", ["propext", "Quot.sound"])),
                       (deduce, "settle", lambda accepted, report, log=print: saved.setdefault("accepted", accepted)),
                       (deduce, "library_facts", lambda relation, cache: [])]
            for mod, attr, value in patches:
                old = getattr(mod, attr)
                setattr(mod, attr, value)
                self.addCleanup(setattr, mod, attr, old)
            plan = deduce.plan()
            self.assertEqual(plan[0]["pending"], ["library-rewrite", "step-induction", "period-reduction"])
            dry = deduce.run(dry_run=True, log=lambda *a: None)
            self.assertFalse(ledger_path.exists())
            self.assertTrue(all(a["outcome"] in ("dry-run", "failed") for a in dry["attempts"]))
            r = deduce.run(log=lambda *a: None)
            schema.validate(schema.document("deduce-result"), json.loads(json.dumps(r)))
            # library-rewrite fails in Python (no facts), step-induction proves: the third is never tried
            self.assertEqual([(a["strategy"], a["outcome"]) for a in r["attempts"]],
                             [("library-rewrite", "failed"), ("step-induction", "proved")])
            self.assertEqual(saved["accepted"][0]["name"], "rdiag3_succ_eq_timeParity_xor_rdiag3")
            ledger = engine.load(ledger_path)
            self.assertEqual(len(ledger["attempt"]), 2)
            # a second run attempts nothing already attempted
            self.assertEqual(deduce.plan()[0]["pending"], ["period-reduction"])
            # the learned order: step-induction proved for right-shift, so it now comes first
            self.assertEqual(deduce.plan()[0]["order"][0], "step-induction")

    def test_module_text_roundtrip_and_scratch_file_deduce_command(self):
        thms = [{"name": "a_eq_b", "body": "/-- d -/\ntheorem a_eq_b (t : Nat) : x = y := by\n  decide\n", "imports": ["Rule30UOR.Band"]},
                {"name": "c_eq_d", "body": "/-- e -/\ntheorem c_eq_d (t : Nat) : z = w := by\n  rfl\n", "imports": []}]
        text = deduce.module_text(thms)
        self.assertTrue(text.startswith("module\npublic import Rule30UOR.Antidiagonal\npublic import Rule30UOR.Band\n"))
        self.assertIn("@[expose] public section", text)
        self.assertTrue(text.rstrip().endswith("end Rule30UOR.Deduced"))
        old = deduce.DEDUCED_PATH
        with tempfile.TemporaryDirectory() as d:
            deduce.DEDUCED_PATH = Path(d) / "Deduced.lean"
            self.addCleanup(setattr, deduce, "DEDUCED_PATH", old)
            deduce.DEDUCED_PATH.write_text(text)
            back = deduce.read_module()
            self.assertEqual([t["name"] for t in back], ["a_eq_b", "c_eq_d"])
            self.assertEqual(deduce.module_text(back), text)
        scratch = deduce.scratch_file("a_eq_b", thms[0]["body"], ["Rule30UOR.Band"])
        self.assertIn("#print axioms Rule30UOR.Deduced.a_eq_b", scratch)
        self.assertTrue(scratch.startswith("module\n"))

    # -------------------------------------------------------------- the tick

    def test_budget_regulation_keeps_the_gate_share_engine_tick(self):
        data = {"tick": [], "weight": [], "attempt": []}
        a = engine.allowances(300, data)
        self.assertEqual(a["gate"], 85)
        self.assertAlmostEqual(sum(a.values()), 300)
        data["tick"] = [{"number": 1, "stages": [{"id": "build", "seconds": 600, "outcome": "ok"},
                                                 {"id": "gate", "seconds": 6000, "outcome": "ok"}]}]
        a = engine.allowances(300, data)
        self.assertEqual(a["gate"], 125)  # 1.25 times its measured 100 minutes, above its share
        self.assertEqual(a["build"], 10)  # its measured duration
        self.assertAlmostEqual(sum(a.values()), 300)
        late = engine.allowances(300, data, elapsed=250 * 60, done=("build", "induction", "pruning"))
        self.assertEqual(late["gate"], 125)  # never cut
        self.assertEqual(late["deduction"], 0)  # the stage that would overrun is cut
        self.assertEqual(engine.allowances(30, {"tick": [], "weight": [], "attempt": []})["gate"], 8.5)
        # the gate's duration of a committed tick is measured by the next tick from the commit's time
        from datetime import datetime, timezone
        start = "2026-11-01T00:17:00Z"
        epoch = int(datetime(2026, 11, 1, 0, 17, tzinfo=timezone.utc).timestamp())
        data = {"tick": [{"number": 4, "start": start, "outcome": "pushed", "seconds": 600.0,
                          "stages": [{"id": "build", "seconds": 100.0, "allowance": 60.0, "outcome": "ok", "note": ""}]}],
                "weight": [], "attempt": []}
        asked = []
        old = repo.run
        repo.run = lambda cmd, **kw: asked.append(cmd) or (0, f"{epoch + 600 + 1500}\n", "")
        self.addCleanup(setattr, repo, "run", old)
        self.assertEqual(engine.backfill_gate(data), 1500)
        self.assertIn("--grep=Engine tick 4:", asked[0])
        self.assertEqual(engine.measured(data)["gate"], 1500)
        self.assertIsNone(engine.backfill_gate(data))  # measured once

    def _tick(self, changes, push_moved=False, commit=False, push=False):
        """A tick with its stages replaced by recorded answers."""
        from tools.r30 import discover, modules, sequencemodel
        calls = []
        with tempfile.TemporaryDirectory() as d:
            ledger = Path(d) / "engine.toml"
            state = {"dirty": [], "head": "b" * 40}

            def run(cmd, cwd=None, timeout=None, env=None, input=None):
                calls.append(cmd)
                if cmd[:2] == ["git", "rev-parse"]:
                    if cmd[2] == "origin/main":
                        return 0, ("c" * 40 if push_moved else "b" * 40) + "\n", ""
                    return 0, state["head"] + "\n", ""
                return 0, "", ""

            def r30(args, timeout):
                calls.append(["r30", *args])
                if args[0] == "commit":
                    state["head"] = "d" * 40
                return True, "ok"
            patches = [(engine, "LEDGER", ledger), (engine, "dirty", engine.dirty), (repo, "run", run),
                       (repo, "SCRATCH", Path(d) / "scratch"),
                       (engine, "_r30", r30), (engine, "prune_evidence", lambda: None),
                       (engine, "sequences_input", lambda: "sha256:" + "0" * 64),
                       (modules, "build", lambda names, timeout=None: state.update(started=True) or (True, "")),
                       (sequencemodel, "load", lambda: {"window": 512, "sequence": []}),
                       (discover, "run", lambda **kw: {"written": [], "counts": {"new": 0}}),
                       (deduce, "run", lambda budget_minutes, log=print, tick=0: {"attempts": [], "proved": [], "refuted": [],
                                                                          "known": [], "skipped": [], "dry_run": False}),
                       (engine, "consolidate", lambda data, tick, start: {"outcomes": 0, "runtime": "python"}),
                       (frontier, "load", lambda: {"claim": []})]
            import subprocess as sp
            patches.append((sp, "run", lambda *a, **k: type("P", (), {"returncode": 0, "stdout": "", "stderr": ""})()))
            for mod, attr, value in patches:
                old = getattr(mod, attr)
                setattr(mod, attr, value)
                self.addCleanup(setattr, mod, attr, old)
            # clean at the start, `changes` once the stages ran
            engine.dirty = lambda: changes if state.get("started") else []
            summary = engine.tick(budget_minutes=60, commit=commit, push=push, log=lambda *a: None)
            recorded = engine.load(ledger)["tick"]
            marker = Path(d) / "scratch" / "settled"
            self.settled = marker.read_text() if marker.exists() else ""
            return summary, calls, recorded

    def test_tick_idle_commit_and_dropped_push_engine_tick(self):
        s, calls, recorded = self._tick([])
        self.assertEqual(s["outcome"], "idle")
        self.assertTrue(self.settled.startswith("b" * 40 + " idle"))  # the file the workflow caches as settled
        self.assertEqual([st["id"] for st in s["stages"]], ["build", "induction", "pruning", "deduction", "learning"])
        self.assertFalse(any(c[:2] == ["r30", "commit"] for c in calls))
        self.assertEqual(recorded[-1]["outcome"], "idle")
        schema.validate(schema.document("engine-tick-result"), json.loads(json.dumps(s)))
        s, calls, _ = self._tick(["frontier.toml"], commit=True, push=True)
        self.assertEqual(s["outcome"], "pushed")
        commit = next(c for c in calls if c[:2] == ["r30", "commit"])
        self.assertIn("--wait", commit)
        self.assertEqual(commit[commit.index("--coauthor") + 1], "")  # no model co-author on engine commits
        self.assertIn(["git", "push", "origin", "HEAD:main"], calls)
        self.assertFalse(any("--force" in c or "-f" in c for c in calls if c[:2] == ["git", "push"]))
        s, calls, _ = self._tick(["frontier.toml"], commit=True, push=True, push_moved=True)
        self.assertEqual(s["outcome"], "dropped")
        self.assertNotIn(["git", "push", "origin", "HEAD:main"], calls)
        s, _, _ = self._tick(["frontier.toml"])
        self.assertEqual(s["outcome"], "uncommitted")
        with self.assertRaises(RuntimeError):
            self._tick([".github/workflows/engine.yml"], commit=True)

    def test_status_reports_the_network_and_the_last_tick_engine_status(self):
        data = {"weight": [{"strategy": "step-induction", "family": "left-plain", "value": 10}], "attempt": [
            {"claim": "x", "kappa": "sha256:" + "b" * 64, "strategy": "step-induction", "template": "sha256:" + "c" * 64,
             "family": "left-plain", "outcome": "proved", "failure": "", "seconds": 1.0, "theorem": "T", "tick": 1}],
                "tick": [{"number": 1, "start": "2026-11-01T00:17:00Z", "base": "a" * 40, "budget": 300,
                          "stages": [{"id": "build", "seconds": 30.0, "allowance": 60.0, "outcome": "ok", "note": "built"}],
                          "outcome": "committed", "seconds": 40.0, "commit": "", "observed": 3, "proved": 1, "refuted": 0,
                          "known": 0, "attempts": 1, "new_relations": 2}]}
        st = engine.status(data)
        schema.validate(schema.document("engine-status-result"), json.loads(json.dumps(st)))
        self.assertEqual(st["events"], 1)
        self.assertEqual(st["attempts"], {"proved": 1})
        self.assertEqual(st["weights"], [{"strategy": "step-induction", "family": "left-plain", "value": 10}])
        text = engine.render_status(st)
        self.assertIn("units (basis sequences)", text)
        self.assertIn("last tick 1", text)
        self.assertIn("build", text)
        self.assertIn("step-induction/left-plain=10", text)
        self.assertIn("no tick recorded yet", engine.render_status(engine.status({"weight": [], "attempt": [], "tick": []})))

    def test_every_engine_id_has_a_test_engine_ledger(self):
        from tools.r30 import prismmodel
        ids = [x["id"] for x in prismmodel.API_IDS if x["suite"] == "engine"]
        self.assertEqual(sorted(ids), sorted(["engine-workload", "engine-tick", "engine-status", "deduce-command",
                                              "strategy-portfolio", "strategy-learning", "engine-ledger"]))
        for i in ids:
            self.assertTrue(any(n.endswith(i.replace("-", "_")) for n in dir(EngineTests)), i)
        feature = (prismmodel.FEATURES / "engine.feature").read_text()
        for i in ids:
            self.assertIn(f"@{i} @build", feature)


if __name__ == "__main__":
    unittest.main()
