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
import hashlib
import json
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


class RecordedRoots:
    """What the certified roots answer, recorded for tests that have no bundle (the gate's snapshot never
    has one); `test_learning...` compares the frozen fixtures with the real roots when a bundle exists."""
    why = "recorded"

    def schedule(self, table, fam, apps):
        w = {(s, f): v for s, f, v in table}
        return sorted(apps, key=lambda x: -w.get((x, fam), em.W_INIT))

    def learn_all(self, table, outcomes):
        t = {(s, f): v for s, f, v in table}
        for s, f, ok in outcomes:
            v = t.get((s, f), em.W_INIT)
            t[(s, f)] = min(v + em.RAISE, em.W_MAX) if ok else max(v - em.LOWER, em.W_MIN)
        return [(s, f, v) for (s, f), v in t.items()]


class EngineTests(unittest.TestCase):

    def setUp(self):
        from tools.r30 import engine_rust
        self.addCleanup(setattr, engine_rust, "runner", engine_rust.runner)
        self.real_runner = engine_rust.runner
        engine_rust.runner = RecordedRoots

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
        self.assertIn("timeout-minutes: 355", text)
        self.assertIn("if: github.repository == 'afflom/rule30' && vars.R30_ENGINE != 'off'", text)
        self.assertIn("run: bin/r30 engine tick --budget-minutes 300 --commit --push", text)
        self.assertIn("make hooks", text)
        self.assertIn("gh workflow run view.yml --ref main", text)
        self.assertIn("fetch-depth: 0", text)
        # caches: the compiler, the Lake builds, the gate's evidence without certificates, the settled mark
        for key in ("r30-lexlean-", "r30-lake-", "r30-gate-", "r30-settled-"):
            self.assertIn(key, text)
        # the evidence is pruned by the engine's own command before it is saved, never by hand
        steps = re.split(r"\n      - name: ", text)
        names = [s.split("\n", 1)[0] for s in steps[1:]]
        self.assertLess(names.index("Prune the gate's evidence before caching"), names.index("Save the gate's evidence"))
        self.assertIn("run: bin/r30 engine prune --apply", text)
        self.assertNotIn("find .git/rule30-validation", text)
        # a run whose commit is no longer main's tip (queued behind a tick that pushed) stops after the checkout:
        # every later step is conditioned on it, the settled mark included
        self.assertEqual(names[:2], ["Checkout (full history, so the tick can push)", "Is this commit still the tip of main"])
        self.assertIn('git ls-remote origin refs/heads/main | cut -f1)" = "$GITHUB_SHA"', text)
        self.assertEqual(names[2], "Is this commit settled")
        for step in steps[4:]:
            self.assertIn("steps.tip.outputs.current == 'true'", step.split("\n", 2)[1], step.split("\n", 1)[0])
        # nothing new to cache after a stale tick; only idle, refused and error settle (a cut tick is resumed)
        for name in ("Prune the gate's evidence before caching", "Save the Lake builds", "Save the gate's evidence"):
            self.assertIn("steps.tick.outputs.outcome != 'stale'", steps[names.index(name) + 1])
        self.assertIn("""contains(fromJSON('["idle", "refused", "error", "stalled"]'), steps.tick.outputs.outcome)""", text)
        # the gate's log reaches the job log, so a refusal on the runner says where
        self.assertIn('echo "::group::gate log $f"; tail -n 200 "$f"', text)
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
        # the module decides the frozen fixtures and the invariants over the committed table
        module = em.MODULE.read_text()
        for name in ("learnStaysInBounds", "committedWeightsBounded", "learnAllFixture", "everyScheduleIsSound",
                     "scheduleFixture0", "scheduleFixture1", "scheduleFixture2"):
            self.assertIn(f"name: {name},", module)
        self.assertIn("production: {effects: [allocation, overflow, recursion], targets: [rust-std]}", module)
        from tools.r30 import engine_rust, production
        roots = {r["root"] for r in production.roots()}
        self.assertTrue({"Rule30Api.Engine.learnAll", "Rule30Api.Engine.schedule", "Rule30Api.Hypotheses.mint"} <= roots)
        self.assertFalse(hasattr(em, "Mirror"))  # the roots have no other runtime
        # the certified roots answer the frozen fixtures (when `bin/r30 api production` has built them)
        try:
            runner = self.real_runner()
        except engine_rust.NoRoot as e:
            self.skipTest(f"no certified roots to compare: {e}")
        start = em.initial_table()
        learned = [(s, f, em.FIXTURE_LEARNED.get((s, f), v)) for s, f, v in start]
        self.assertEqual(runner.learn_all(start, em.FIXTURE_OUTCOMES), learned)
        for fam, apps, expected in em.FIXTURE_SCHEDULES:
            self.assertEqual(runner.schedule(learned, fam, apps), expected)
        recorded = RecordedRoots()  # and the answers the other tests record are the roots' own
        self.assertEqual(runner.learn_all(start, em.FIXTURE_OUTCOMES), recorded.learn_all(start, em.FIXTURE_OUTCOMES))
        for fam, apps, expected in em.FIXTURE_SCHEDULES:
            self.assertEqual(recorded.schedule(learned, fam, apps), expected)

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
                                     "outcome": "failed", "failure": "(decided in Python) ...", "library": "sha256:" + "1" * 64})
        with self.assertRaises(RuntimeError):  # the same library: the same attempt
            engine.record_attempt(data, {**data["attempt"][-1]})
        # a changed library is a new library-rewrite attempt (a lemma pushed since may close the claim)
        engine.record_attempt(data, {**data["attempt"][-1], "library": "sha256:" + "2" * 64})
        data["attempt"].pop()
        data["weight"] = engine.learned(em.initial_table(), data["attempt"])
        w = {(r["strategy"], r["family"]): r["value"] for r in engine.weights(data)}
        self.assertEqual(w[("step-induction", "left-plain")], em.W_INIT + em.RAISE)
        self.assertEqual(w[("library-rewrite", "left-plain")], em.W_INIT - em.LOWER)
        data["tick"].append({"number": 1, "start": "2026-11-01T00:00:00Z", "base": "0" * 40, "budget": 300,
                             "stages": [{"id": "build", "seconds": 12.5, "allowance": 60.0, "outcome": "ok", "note": ""}],
                             "outcome": "committed", "seconds": 13.0, "commit": "", "observed": 0, "proved": 1, "refuted": 0,
                             "known": 0, "attempts": 2, "new_relations": 0, "minted": 0})
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "engine.toml"
            engine.save(data, path)
            back = engine.load(path)
            self.assertEqual(back["attempt"][0]["template"], a["template"])
            self.assertEqual([x.get("library", "") for x in back["attempt"]], ["", "sha256:" + "1" * 64])
            self.assertEqual(back["tick"][0]["stages"][0]["seconds"], 12.5)
            self.assertEqual(engine.weights(back), engine.weights(data))
            self.assertEqual(tomllib.loads(path.read_text())["spec"], "r30/engine/1")
        if engine.LEDGER.exists():  # the committed ledger is well formed and in bounds
            real = engine.load()
            keys = [engine.attempt_key(x) for x in real["attempt"]]
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
            from tools.r30 import modules
            patches = [(frontier, "load", lambda: {"claim": [c]}), (engine, "LEDGER", ledger_path),
                       (deduce, "check", lambda name, body, imports, timeout: ("proved", "", ["propext", "Quot.sound"])),
                       (deduce, "settle", lambda accepted, report, log=print: saved.setdefault("accepted", accepted)),
                       (deduce, "library_facts", lambda relation, cache: []),
                       # hermetic: the build of Rule30UOR.Deduced that run() starts with is a recorded answer
                       (modules, "build", lambda names, timeout=3600: saved.setdefault("built", list(names)) and (True, ""))]
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
            self.assertEqual(saved["built"], [deduce.DEDUCED])
            # library-rewrite fails in Python (no facts), step-induction proves: the third is never tried
            self.assertEqual([(a["strategy"], a["outcome"]) for a in r["attempts"]],
                             [("library-rewrite", "failed"), ("step-induction", "proved")])
            self.assertEqual(saved["accepted"][0]["name"], "rdiag3_succ_eq_timeParity_xor_rdiag3")
            ledger = engine.load(ledger_path)
            self.assertEqual(len(ledger["attempt"]), 2)
            # library-rewrite's key holds the library it read; the other strategies' does not
            library = deduce.library_digest([c])
            self.assertEqual([a.get("library", "") for a in ledger["attempt"]], [library, ""])
            # a second run attempts nothing already attempted
            self.assertEqual(deduce.plan()[0]["pending"], ["period-reduction"])
            # the learned order: step-induction proved for right-shift, so it now comes first
            self.assertEqual(deduce.plan()[0]["order"][0], "step-induction")
            # a relation proved since is a new library: library-rewrite is pending again, nothing else is
            proved = {"id": "observed-other", "status": "proved", "lean": "Rule30UOR.Deduced.other",
                      "relation": ["ldiag(7)"], "statement": "x"}
            frontier.load = lambda: {"claim": [c, proved]}
            self.assertNotEqual(deduce.library_digest([c, proved]), library)
            self.assertEqual(sorted(deduce.plan()[0]["pending"]), ["library-rewrite", "period-reduction"])

    def _deduce(self, c, check=None, settle=None, facts=(), publishable=True, weights=()):
        """deduce.run on one claim with Lean replaced by recorded answers; returns (report, ledger path)."""
        from tools.r30 import modules
        d = tempfile.mkdtemp()
        self.addCleanup(__import__("shutil").rmtree, d, True)
        ledger_path = Path(d) / "engine.toml"
        if weights:
            engine.save({"spec": engine.SPEC, "weight": list(weights), "attempt": [], "tick": []}, ledger_path)
        patches = [(frontier, "load", lambda: {"claim": [c]}), (engine, "LEDGER", ledger_path),
                   (deduce, "check", check or (lambda name, body, imports, timeout: ("proved", "", ["propext", "Quot.sound"]))),
                   (deduce, "settle", settle or (lambda accepted, report, log=print: None)),
                   (deduce, "library_facts", lambda relation, cache: list(facts)),
                   (deduce, "publishable", lambda lean, cache=None: publishable),
                   (modules, "build", lambda names, timeout=3600: (True, ""))]
        for mod, attr, value in patches:
            old = getattr(mod, attr)
            setattr(mod, attr, value)
            self.addCleanup(setattr, mod, attr, old)
        return deduce.run(log=lambda *a: None), ledger_path

    def test_a_library_theorem_stating_the_relation_proves_it_first_deduce_command(self):
        needs_basis(self)
        c = claim(["time-parity", "rdiag(2)"])
        apps, fam = deduce.applicable(c)
        self.assertIn("step-induction", apps)
        # step-induction ranks first for this family, but the library already states the relation
        weights = [{"strategy": "step-induction", "family": fam, "value": em.W_MAX},
                   {"strategy": "library-rewrite", "family": fam, "value": em.W_MIN}]
        self.assertEqual(em.schedule(weights, fam, apps)[0], "step-induction")
        fact = {"lean": "Rule30UOR.Band.rdiag_two_eq_parity", "lhs": ("col", "base", "rdiag", 2),
                "rhs": ("col", "base", "time-parity", None)}
        checked = []
        r, path = self._deduce(c, check=lambda *a: checked.append(a) or ("proved", "", []), facts=[fact], weights=weights)
        self.assertEqual(deduce.plan(ledger=engine.load(path))[0]["order"][0], "step-induction")
        self.assertEqual(checked, [])  # no Lean ran: no second proof of a statement the library has
        self.assertEqual([(a["strategy"], a["outcome"], a["theorem"]) for a in r["attempts"]],
                         [("library-rewrite", "known", "Rule30UOR.Band.rdiag_two_eq_parity")])
        self.assertEqual(r["known"], [{"id": c["id"], "lean": "Rule30UOR.Band.rdiag_two_eq_parity"}])

    def test_an_attempt_the_deadline_cuts_stays_pending_deduce_command(self):
        needs_basis(self)
        c = claim(["time-parity", "rdiag(3)", "shift:rdiag(3)"])
        asked = []
        # the stage's deadline leaves less than an attempt's full time: the Lean check times out on it
        cut = lambda name, body, imports, timeout: asked.append(timeout) or ("timeout", f"no answer within {timeout} s", None)
        import itertools
        import types
        start = 1_800_000_000.0
        clock = itertools.chain([start], itertools.repeat(start + 3600 - 100))  # 100 s left once the run starts
        self.addCleanup(setattr, deduce, "time", deduce.time)
        deduce.time = types.SimpleNamespace(time=lambda: next(clock))  # deduce's clock only
        r, path = self._deduce(c, check=cut)
        self.assertTrue(asked and all(t < em.ATTEMPT_TIMEOUT for t in asked))
        self.assertEqual([a["strategy"] for a in r["attempts"]], ["library-rewrite"])  # decided in Python
        self.assertEqual([s["strategy"] for s in r["skipped"]], ["step-induction", "period-reduction"])
        ledger = engine.load(path)
        self.assertNotIn("timeout", [a["outcome"] for a in ledger["attempt"]])  # not the strategy's failure
        self.assertEqual(deduce.plan(ledger=ledger)[0]["pending"], ["step-induction", "period-reduction"])

    def test_a_proof_settling_did_not_record_is_not_in_the_ledger_deduce_command(self):
        needs_basis(self)
        c = claim(["time-parity", "rdiag(3)", "shift:rdiag(3)"])

        def settle(accepted, report, log=print):
            raise RuntimeError("the Deduced module did not build with the accepted theorems")
        with self.assertRaises(RuntimeError):
            self._deduce(c, settle=settle)
        ledger = engine.load(Path(engine.LEDGER))
        # the failure is recorded, the proof the register never received is not: the claim stays pending for it
        self.assertEqual([(a["strategy"], a["outcome"]) for a in ledger["attempt"]], [("library-rewrite", "failed")])
        self.assertEqual(deduce.plan(ledger=ledger)[0]["pending"], ["step-induction", "period-reduction"])

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
        # a stage's limit is its share, never its last duration: a fast warm build must not cap the rebuild
        # a pushed base module needs (10 minutes measured, 60 allowed)
        self.assertEqual(a["build"], 60)
        self.assertAlmostEqual(sum(a.values()), 300)
        data["tick"].append({"number": 2, "stages": [{"id": "build", "seconds": 20, "outcome": "ok"},
                                                     {"id": "induction", "seconds": 40, "outcome": "ok"}]})
        self.assertEqual({k: engine.allowances(300, data)[k] for k in ("build", "induction", "pruning")},
                         {"build": 60, "induction": 30, "pruning": 20})
        # what the earlier stages left goes to deduction, recomputed when it starts
        after = engine.allowances(300, data, elapsed=2 * 60, done=("build", "induction", "pruning"))
        self.assertAlmostEqual(after["deduction"], 300 - 2 - 125 - 5 - 5)
        # a cut stage is not measured (its seconds are a lower bound): the gate's reservation ignores a cut
        data["tick"].append({"number": 3, "stages": [{"id": "gate", "seconds": 60, "outcome": "cut"}]})
        self.assertEqual(engine.measured(data)["gate"], 6000)
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

    def _tick(self, changes, push_moved=False, commit=False, push=False, moved_early=False, push_rejected=False,
              build=None, deduced=None, pending=0, minted=0):
        """A tick with its stages replaced by recorded answers. `moved_early`: main is not the base when
        the tick starts; `push_moved`: main moves while the tick runs; `push_rejected`: the remote refuses
        the push; `build`: the build's answer (an exception to raise); `deduced`: deduce's report."""
        from tools.r30 import discover, modules, sequencemodel
        calls = []
        with tempfile.TemporaryDirectory() as d:
            ledger = Path(d) / "engine.toml"
            state = {"dirty": [], "head": "b" * 40}

            def run(cmd, cwd=None, timeout=None, env=None, input=None):
                calls.append(cmd)
                if cmd[:2] == ["git", "rev-parse"]:
                    if cmd[2] == "origin/main":
                        moved = moved_early or (push_moved is True and state.get("started")) \
                            or (push_moved == "after-push" and state.get("pushed"))
                        return 0, ("c" * 40 if moved else "b" * 40) + "\n", ""
                    return 0, state["head"] + "\n", ""
                if cmd[:2] == ["git", "push"]:
                    state["pushed"] = True
                    if push_rejected:
                        return 1, "", "! [remote rejected] HEAD -> main (protected branch hook declined)"
                return 0, "", ""

            def build_answer(names, timeout=None):
                state.update(started=True)
                if isinstance(build, BaseException):
                    raise build
                return build or (True, "")

            def r30(args, timeout):
                calls.append(["r30", *args])
                if args[0] == "commit":
                    state["head"] = "d" * 40
                return True, "ok"
            patches = [(engine, "LEDGER", ledger), (engine, "dirty", engine.dirty), (repo, "run", run),
                       (repo, "SCRATCH", Path(d) / "scratch"),
                       (engine, "_r30", r30), (engine, "prune_evidence", lambda: None),
                       (engine, "sequences_input", lambda: "sha256:" + "0" * 64),
                       (modules, "build", build_answer),
                       (sequencemodel, "load", lambda: {"window": 512, "sequence": []}),
                       (discover, "run", lambda **kw: {"written": [], "counts": {"new": 0}}),
                       (deduce, "run", lambda budget_minutes, log=print, tick=0: deduced or {
                           "attempts": [], "proved": [], "refuted": [], "known": [], "skipped": [], "dry_run": False}),
                       (deduce, "plan", lambda ledger=None: [{"pending": ["step-induction"] * pending}]),
                       (engine, "consolidate", lambda data, tick, start: {"outcomes": 0, "runtime": "certified"}),
                       (engine, "mint", lambda tick, budget, data=None: [{"label": "x"}] * minted),
                       (frontier, "load", lambda: {"claim": []})]
            import subprocess as sp
            patches.append((sp, "run", lambda *a, **k: type("P", (), {"returncode": 0, "stdout": "", "stderr": ""})()))
            for mod, attr, value in patches:
                old = getattr(mod, attr)
                setattr(mod, attr, value)
                self.addCleanup(setattr, mod, attr, old)
            # clean at the start, `changes` once the stages ran
            engine.dirty = lambda: changes if state.get("started") else []
            try:
                summary = engine.tick(budget_minutes=60, commit=commit, push=push, log=lambda *a: None)
            finally:
                marker = Path(d) / "scratch" / "settled"
                self.settled = marker.read_text() if marker.exists() else ""
                self.recorded = engine.load(ledger)["tick"]
            return summary, calls, self.recorded

    def test_tick_idle_commit_and_dropped_push_engine_tick(self):
        s, calls, recorded = self._tick([])
        self.assertEqual(s["outcome"], "idle")
        self.assertTrue(self.settled.startswith("b" * 40 + " idle"))  # the file the workflow caches as settled
        self.assertEqual([st["id"] for st in s["stages"]], ["build", "induction", "pruning", "deduction", "learning", "hypotheses"])
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
        self.assertEqual(self.settled, "")  # the next tick redoes it from the new main
        s, _, _ = self._tick(["frontier.toml"])
        self.assertEqual(s["outcome"], "uncommitted")
        with self.assertRaises(RuntimeError):
            self._tick([".github/workflows/engine.yml"], commit=True)

    def test_stale_cut_and_rejected_ticks_settle_only_what_needs_a_person_engine_tick(self):
        import subprocess
        # a run whose base is no longer main (queued behind a tick that pushed): it stops at once
        s, calls, recorded = self._tick(["frontier.toml"], commit=True, push=True, moved_early=True)
        self.assertEqual((s["outcome"], s["stages"]), ("stale", []))
        self.assertEqual((self.settled, recorded), ("", []))
        self.assertFalse(any(c[:2] == ["r30", "commit"] for c in calls))
        schema.validate(schema.document("engine-tick-result"), json.loads(json.dumps(s)))
        # a build its allowance cuts (a rebuild after a pushed base module, an evicted cache): nothing runs on
        # the unbuilt library, nothing is settled, and the next tick resumes the build
        s, calls, recorded = self._tick([], build=subprocess.TimeoutExpired(["lake", "build"], 3600))
        self.assertEqual(s["outcome"], "cut")
        self.assertEqual([(st["id"], st["outcome"]) for st in s["stages"]], [("build", "cut")])
        self.assertEqual(self.settled, "")
        self.assertEqual(recorded[-1]["outcome"], "cut")
        self.assertNotIn("build", engine.measured({"tick": recorded}))
        # a failed build is a person's: settled
        with self.assertRaises(RuntimeError):
            self._tick([], build=(False, "error: Rule30UOR/Core.lean:3:0: unknown module"))
        self.assertTrue(self.settled.startswith("b" * 40 + " error"))
        self.assertIn("unknown module", self.recorded[-1]["stages"][0]["note"])
        # deduction left attempts for the budget: nothing changed, but the tick is not idle
        report = {"attempts": [], "proved": [], "refuted": [], "known": [], "dry_run": False,
                  "skipped": [{"id": "observed-x", "strategy": "step-induction", "reason": "budget"}]}
        s, _, _ = self._tick([], deduced=report, pending=1)
        self.assertEqual((s["outcome"], self.settled), ("cut", ""))
        self.assertEqual(s["stages"][3]["outcome"], "cut")
        # nothing cut, but an attempt still pending: not idle either
        s, _, _ = self._tick([], pending=1)
        self.assertEqual((s["outcome"], self.settled), ("cut", ""))
        # the remote rejects the push while main has not moved: no race, so the tick is refused and settled
        with self.assertRaises(RuntimeError):
            self._tick(["frontier.toml"], commit=True, push=True, push_rejected=True)
        self.assertTrue(self.settled.startswith("b" * 40 + " refused"))
        self.assertEqual(self.recorded[-1]["outcome"], "refused")
        # ... and when main moved between the check and the push, it is the race: dropped, not settled
        s, calls, _ = self._tick(["frontier.toml"], commit=True, push=True, push_rejected=True, push_moved="after-push")
        self.assertIn(["git", "push", "origin", "HEAD:main"], calls)
        self.assertEqual((s["outcome"], self.settled), ("dropped", ""))

    def test_build_compiles_the_runtime_laws_first_engine_tick(self):
        """Rule30UOR.Core imports LexLeanRuntime.Laws, which no Lake root covers: the build compiles it as the
        Makefile's `core` recipe does, so a build from an empty .lake succeeds; and only when its inputs changed."""
        from tools.r30 import modules
        self.assertIn("lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean "
                      "-i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build",
                      (ROOT / "Makefile").read_text())
        lakefile = tomllib.loads((repo.CORE_LEAN / "lakefile.toml").read_text())
        runtime = next(lib for lib in lakefile["lean_lib"] if lib["name"] == "LexLeanRuntime")
        self.assertNotIn("LexLeanRuntime.Laws", runtime["roots"])  # why the step exists
        with tempfile.TemporaryDirectory() as d:
            core = Path(d)
            for rel in modules.LAWS_INPUTS:
                (core / rel).parent.mkdir(parents=True, exist_ok=True)
                (core / rel).write_text(f"-- {rel}\n")
            calls = []

            def run(cmd, cwd=None, timeout=None, env=None, input=None, group=False):
                calls.append(cmd)
                self.assertEqual(cwd, core)
                self.assertTrue(group)  # a cut build leaves no Lean process writing into the cached .lake
                if cmd[:3] == ["lake", "env", "lean"]:
                    for flag in ("-o", "-i"):
                        (core / cmd[cmd.index(flag) + 1]).write_bytes(b"compiled")
                return 0, "", ""
            for mod, attr, value in [(repo, "CORE_LEAN", core), (repo, "run", run)]:
                self.addCleanup(setattr, mod, attr, getattr(mod, attr))
                setattr(mod, attr, value)
            self.assertEqual(modules.build([]), (True, ""))
            self.assertEqual(calls, [["lake", "build", "LexLeanRuntime"],
                                     ["lake", "env", "lean", "-R", ".", "-o", ".lake/build/lib/lean/LexLeanRuntime/Laws.olean",
                                      "-i", ".lake/build/lib/lean/LexLeanRuntime/Laws.ilean", "LexLeanRuntime/Laws.lean"],
                                     ["lake", "build", "Rule30UOR"]])
            calls.clear()
            self.assertEqual(modules.build(["Deduced"]), (True, ""))
            self.assertEqual(calls, [["lake", "build", "Rule30UOR.Deduced"]])  # current: not compiled again
            (core / "LexLeanRuntime/Portable.lean").write_text("-- changed\n")
            calls.clear()
            modules.build([])
            self.assertEqual([c[:3] for c in calls], [["lake", "build", "LexLeanRuntime"], ["lake", "env", "lean"],
                                                      ["lake", "build", "Rule30UOR"]])
        # a failed build keeps its first error block, not Lake's progress lines around it
        out = ("✔ [24/85] Built Rule30UOR.Intent (867ms)\n✖ [26/85] Building Rule30UOR.Core\n"
               "error: Rule30UOR/Core.lean:3:0: unknown module prefix 'LexLeanRuntime'\n"
               "⚠ [25/85] Built Rule30UOR.ZeroDiagonals (2.4s)\nwarning: unused variable\n"
               "✔ [27/85] Built Rule30UOR.Fixed (1.0s)\nerror: build failed\n")
        self.assertEqual(modules.errors_of(out), "error: Rule30UOR/Core.lean:3:0: unknown module prefix 'LexLeanRuntime'\n"
                                                 "error: build failed")
        self.assertEqual(modules.errors_of("lake: killed\n"), "lake: killed")

    def test_a_timed_out_build_kills_its_whole_process_group_engine_tick(self):
        import subprocess
        import time
        with tempfile.TemporaryDirectory() as d:
            pidfile = Path(d) / "child.pid"
            # a parent (lake) that starts a child (lean) and waits: the timeout must take both
            script = f"sleep 30 & echo $! > {pidfile}; wait"
            with self.assertRaises(subprocess.TimeoutExpired):
                repo.run(["sh", "-c", script], cwd=d, timeout=1, group=True)
            child = int(pidfile.read_text())
            for _ in range(50):
                try:
                    import os
                    os.kill(child, 0)
                except ProcessLookupError:
                    break
                time.sleep(0.1)
            else:
                self.fail("the build's child process survived its timeout")

    def test_prune_keeps_what_the_next_run_can_use_engine_workload(self):
        """The gate's evidence before caching: the current tools key, the newest attestation per LexLean
        project, the current κ procedure, never a certificate."""
        import os
        import time
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "rule30-validation"

            def put(rel, text="x", age=0):
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
                stamp = time.time() - age
                for q in [path] + list(path.parents):
                    if q == root.parent:
                        break
                    os.utime(q, (stamp, stamp))
            put("a" * 64 + ".ok", "tree")
            put("a" * 64 + ".lock", "")
            put("lake/bbbbbbbbbbbbbbbb/rule30-core-lean/.lake/o", age=900)
            put("lake/cccccccccccccccc/rule30-core-lean/.lake/o")
            put("lake/cccccccccccccccc/rule30-core-lean.new/.lake/o")
            for project in ("rule30-paper", "rule30-api"):
                put(f"lexlean/cccccccccccccccc/{project}/{'1' * 64}/latest-verified.json", age=600)
                put(f"lexlean/cccccccccccccccc/{project}/{'1' * 64}/verified/i/attestation.json", age=600)
                put(f"lexlean/cccccccccccccccc/{project}/{'2' * 64}/latest-verified.json", age=60)
                put(f"lexlean/cccccccccccccccc/{project}/{'3' * 64}.new.123/latest-verified.json")
            put(f"lexlean/cccccccccccccccc/rule30-lexlean/{'4' * 64}/latest-verified.json", age=6000)
            put(f"lexlean/bbbbbbbbbbbbbbbb/rule30-paper/{'5' * 64}/latest-verified.json")
            put("replay/bbbbbbbbbbbbbbbb/k.ok")
            put("replay/cccccccccccccccc/k.ok")
            put("kappa/ffffffffffffffff/m")
            put("kappa/eeeeeeeeeeeeeeee/m")
            plan = engine.prune_evidence(root=root, key="cccccccccccccccc", procedure="eeeeeeeeeeeeeeee")
            self.assertFalse(plan["applied"])
            self.assertTrue((root / ("a" * 64 + ".ok")).exists())  # a report changes nothing
            r = engine.prune_evidence(apply=True, root=root, key="cccccccccccccccc", procedure="eeeeeeeeeeeeeeee")
            self.assertEqual(r["dropped"], plan["dropped"])
            schema.validate(schema.document("engine-prune-result"), json.loads(json.dumps(r)))
            left = sorted(str(p.relative_to(root)) for p in root.rglob("*") if p.is_file())
            self.assertEqual(left, [
                "kappa/eeeeeeeeeeeeeeee/m",
                "lake/cccccccccccccccc/rule30-core-lean/.lake/o",
                f"lexlean/cccccccccccccccc/rule30-api/{'2' * 64}/latest-verified.json",
                f"lexlean/cccccccccccccccc/rule30-lexlean/{'4' * 64}/latest-verified.json",
                f"lexlean/cccccccccccccccc/rule30-paper/{'2' * 64}/latest-verified.json",
                "replay/cccccccccccccccc/k.ok"])
            self.assertEqual(r["kept"], ["lake/cccccccccccccccc", "lexlean/cccccccccccccccc", "replay/cccccccccccccccc",
                                         "kappa/eeeeeeeeeeeeeeee"])
            self.assertNotIn(".ok", " ".join(p.name for p in root.iterdir()))
            self.assertIn("kept 4", engine.render_prune(r))
            # without a computable key, the newest directory of each family stands in for it
            put("lake/dddddddddddddddd/x")
            r = engine.prune_evidence(apply=True, root=root, key="", procedure="eeeeeeeeeeeeeeee")
            self.assertEqual(sorted(p.name for p in (root / "lake").iterdir()), ["dddddddddddddddd"])
        self.assertEqual(engine.prune_evidence(root=Path(d) / "absent")["kept"], [])

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
        self.assertIn("exclusions", text)
        self.assertIn("[not recorded]", text)  # a stage's runtime, for a tick from before it was kept

    def test_the_store_grows_by_new_labels_only_hypothesis_store(self):
        from tools.r30 import auditmodel, engine_rust
        seen = []

        class Roots(RecordedRoots):
            def mint(self, attempts, claims, rows, store, budget):
                seen.append((rows, list(store)))
                return [r for r in [{"label": "sha256:" + hashlib.sha256(b"(f)").hexdigest(), "form": "(f)", "weight": 1,
                                     "sources": ["a b"]}] if r["label"] not in store][:budget]
        engine_rust.runner = Roots
        with tempfile.TemporaryDirectory() as d:
            old = engine.HYPOTHESES, auditmodel.load, frontier.load
            self.addCleanup(lambda: (setattr(engine, "HYPOTHESES", old[0]), setattr(auditmodel, "load", old[1]), setattr(frontier, "load", old[2])))
            engine.HYPOTHESES = Path(d) / "hypotheses.toml"
            row = {"theorem": "T", "status": "open", "hypotheses": [{"status": "open", "statement": "(s)"}, {"status": "refuted", "statement": ""}]}
            auditmodel.load, frontier.load = (lambda: ([row], {})), (lambda: {"claim": [{"id": "c", "status": "observed"}]})
            data = {"attempt": [], "weight": [], "tick": []}
            self.assertEqual(len(engine.mint(3, 5, data)), 1)
            self.assertEqual(engine.mint(4, 5, data), [])  # the second run mints nothing: what the store holds is known
            self.assertEqual(seen[0][0], [("T", "open", ["(s)"])])
            self.assertEqual(len(seen[1][1]), 1)
            self.assertEqual([(r["form"], r["sources"], r["tick"], r["status"]) for r in engine.store()], [("(f)", ["a b"], 3, "minted")])
            row["hypotheses"][0]["statement"] = ""  # an audit from before the statements is refused, not read as a key
            with self.assertRaises(RuntimeError):
                engine.mint(5, 5, data)
        engine.HYPOTHESES = old[0]
        rows = engine.store()  # the committed store: every label is the digest of its form, no label twice
        self.assertEqual(len({r["label"] for r in rows}), len(rows))
        for r in rows:
            self.assertEqual(r["label"], "sha256:" + hashlib.sha256(r["form"].encode()).hexdigest())
            self.assertEqual(r["status"], "minted")
        self.assertEqual(tomllib.loads(engine.HYPOTHESES.read_text())["spec"], "r30/hypotheses/1")
        from tools.r30 import cli
        self.assertEqual(cli.build_parser().parse_args(["engine", "hypotheses"]).budget, em.WORKLOAD["hypothesisBudget"])
        self.assertFalse({r["label"] for r in rows} & {c.get("kappa") for c in frontier.load()["claim"]})

    def test_a_root_that_cannot_run_ends_the_stage_and_new_rows_are_no_idle_tick_engine_tick(self):
        from tools.r30 import engine_rust
        text = em.WORKFLOW.read_text()
        self.assertLess(text.index("run: bin/r30 api production"), text.index("run: bin/r30 engine tick"))  # the bundle, before the tick
        self.assertIn("for family in r30-bundle ", text)
        s, _, _ = self._tick(["rule30-api/model/hypotheses.toml"], minted=3)
        self.assertEqual((s["minted"], s["outcome"]), (3, "uncommitted"))
        self.assertEqual(s["stages"][-1]["id"], "hypotheses")
        self.assertEqual(s["stages"][-1]["runtime"], "no root")  # the stand-in ran no root, and says so
        s, _, _ = self._tick([], minted=0)
        self.assertEqual(s["outcome"], "idle")  # nothing new: the tick may settle

        def no_root():
            raise engine_rust.NoRoot("no production bundle")
        engine_rust.runner = no_root
        with self.assertRaises(engine_rust.NoRoot):
            em.schedule([], "open", ["library-rewrite"])
        # the record of the last tick is still printed, and says what cannot be known without the root
        self.addCleanup(setattr, deduce, "plan", deduce.plan)
        deduce.plan = lambda ledger=None: no_root()
        self.assertIn("unknown", engine.status({"weight": [], "attempt": [], "tick": []})["pending"])

    def test_every_engine_id_has_a_test_engine_ledger(self):
        from tools.r30 import prismmodel
        ids = [x["id"] for x in prismmodel.API_IDS if x["suite"] == "engine"]
        self.assertEqual(sorted(ids), sorted(["engine-workload", "engine-tick", "engine-status", "deduce-command",
                                              "strategy-portfolio", "strategy-learning", "engine-ledger", "hypothesis-store"]))
        for i in ids:
            self.assertTrue(any(n.endswith(i.replace("-", "_")) for n in dir(EngineTests)), i)
        feature = (prismmodel.FEATURES / "engine.feature").read_text()
        for i in ids:
            self.assertIn(f"@{i} @build", feature)



class EngineStallTests(unittest.TestCase):
    """A cut tick that repeats the same pending work on the same base ends stalled (visible, settled);
    a transport failure of the push is retried and never settles a base."""

    def test_three_identical_cut_ticks_stall_engine_tick(self):
        from tools.r30 import engine
        base = "a" * 40
        earlier = [{"number": n, "base": base, "outcome": "cut", "pending": 11} for n in (1, 2)]
        self.assertTrue(engine.stalled({"tick": earlier}, {"number": 3, "base": base, "pending": 11}))
        self.assertFalse(engine.stalled({"tick": earlier}, {"number": 3, "base": base, "pending": 10}))
        self.assertFalse(engine.stalled({"tick": earlier[1:]}, {"number": 3, "base": base, "pending": 11}))
        moved = [dict(t, base="b" * 40) for t in earlier]
        self.assertFalse(engine.stalled({"tick": moved}, {"number": 3, "base": base, "pending": 11}))

    def test_only_a_remote_decision_counts_as_a_rejection_engine_tick(self):
        from tools.r30 import engine
        self.assertTrue(engine.REJECTED.search(" ! [remote rejected] HEAD -> main (protected branch hook declined)"))
        self.assertTrue(engine.REJECTED.search("remote: error: GH006: Protected branch update failed"))
        self.assertFalse(engine.REJECTED.search("error: RPC failed; HTTP 502 curl 22 The requested URL returned error: 502"))
        self.assertFalse(engine.REJECTED.search("fatal: the remote end hung up unexpectedly"))


if __name__ == "__main__":
    unittest.main()
