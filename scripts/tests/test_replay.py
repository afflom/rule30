"""The kernel replay keeps a κ-addressed receipt per replayed module: keyed by
the address of the module's declarations, not by its object-file bytes."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import kappa_research  # noqa: E402


def stream(module, value, theorems=()):
    """...with, for each (name, statement value) in `theorems`, a theorem whose statement is the
    nat literal `statement value` (two theorems with one statement value state the same thing)."""
    line = lambda *parts: kappa_research.canonical(list(parts)) + b"\n"
    # an equation lemma (`.eq_1`) is a name Lean reserves: the exporter marks it
    body = b"".join(line("node", str(3 + i), "lit", "nat", str(v)) +
                    line("decl", module + "." + n, "thm", ["levels"], str(3 + i), "2",
                         *([["reserved"]] if n.endswith(".eq_1") else []))
                    for i, (n, v) in enumerate(theorems))
    plain = _stream(module, value)
    return plain.replace(line("end", module), body + line("end", module))


def _stream(module, value):
    """The canned declaration stream of a fixture module: a definition `d : Prop`
    whose value is the nat literal `value`. The stream is what the exporter
    prints for the module; the object-file bytes play no part in its κ."""
    line = lambda *parts: kappa_research.canonical(list(parts)) + b"\n"
    return (line("module", module, ["constants", "1"]) +
            line("node", "0", "lzero") + line("node", "1", "sort", "0") +
            line("node", "2", "lit", "nat", str(value)) +
            line("decl", module + ".d", "def", ["levels"], "1", "2", ["safety", "safe"]) +
            line("end", module))


class ReplayReceiptTests(unittest.TestCase):
    MODULES = ["Rule30UOR.Alpha", "Rule30UOR.Beta", "Rule30UOR.Parts.Gamma"]

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.core = self.repo / "rule30-core-lean"
        (self.repo / "scripts").mkdir(parents=True)
        for name in ("replay_research.py", "check_research_coverage.py", "kappa_research.py", "kappa_label.py"):
            shutil.copy(ROOT / "scripts" / name, self.repo / "scripts" / name)
        roots = ", ".join(f'"{m}"' for m in self.MODULES)
        (self.core / "scripts").mkdir(parents=True)
        (self.core / "lakefile.toml").write_text('[[lean_lib]]\nname = "Rule30UOR"\nroots = [' + roots + ']\n')
        (self.core / "scripts/CheckResearchAxioms.lean").write_text(
            "".join(f"import {m}\n" for m in self.MODULES) + "if (`Rule30UOR).isPrefixOf name then\n")
        (self.core / "lean-toolchain").write_text("leanprover/lean4:test\n")
        self.streams = self.base / "streams"
        self.streams.mkdir()
        for module in self.MODULES:
            source = self.core / Path(*module.split(".")).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- replay fixture\n")
            self.compile(module, "compiled " + module)
        # A toolchain prefix with a leanchecker that records its arguments, a `lean`
        # whose `--run scripts/KappaExport.lean` prints the canned streams, and a
        # `lake env` that names the prefix and runs the command it is given.
        self.prefix = self.base / "toolchain"
        (self.prefix / "bin").mkdir(parents=True)
        self.log = self.base / "leanchecker.log"
        self.leanchecker = self.prefix / "bin/leanchecker"
        self.leanchecker.write_text("#!/bin/sh\n"
                                    f'echo "$@" >> "{self.log}"\n'
                                    'exit "${LEANCHECKER_EXIT:-0}"\n')
        self.leanchecker.chmod(0o755)
        lean = self.base / "lean"
        lean.write_text("#!/bin/sh\n"
                        '[ "$1 $2" = "--run scripts/KappaExport.lean" ] || { echo "unexpected lean call: $*" >&2; exit 2; }\n'
                        'shift 2\n'
                        f'for m in "$@"; do cat "{self.streams}/$m.sexp" || exit 1; done\n')
        lean.chmod(0o755)
        lake = self.base / "lake"
        lake.write_text("#!/bin/sh\n"
                        f'if [ "$1 $2 $3" = "env lean --print-prefix" ]; then echo "{self.prefix}"; exit 0; fi\n'
                        '[ "$1" = env ] || { echo "unexpected lake call: $*" >&2; exit 2; }\n'
                        'shift\nexec "$@"\n')
        lake.chmod(0o755)
        self.cache = self.base / "receipts"
        self.env = dict(os.environ, PATH=str(self.base) + os.pathsep + os.environ["PATH"],
                        RULE30_REPLAY_CACHE=str(self.cache))
        self.env.pop("LEANCHECKER_EXIT", None)
        self.env.pop("RULE30_KAPPA_MEMO", None)

    def compile(self, module, contents, value=0, theorems=()):
        """Write the module's object file with `contents` (standing for positions,
        docstrings and extension data) and its declaration stream with `value`."""
        olean = self.core / ".lake/build/lib/lean" / Path(*module.split("."))
        olean = olean.with_name(olean.name + ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_text(contents + "\n")
        olean.with_name(olean.name + ".private").write_text("private " + contents + "\n")
        (self.streams / (module + ".sexp")).write_bytes(stream(module, value, theorems))

    def replay(self, success=True, **env):
        result = subprocess.run(["python3", "scripts/replay_research.py"], cwd=self.repo,
                                env=dict(self.env, **env), capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result.stdout.splitlines()

    def invocations(self):
        return [line.split() for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def receipts(self):
        return sorted(p.read_text().splitlines()[0] for p in self.cache.glob("*.ok"))

    def replayed(self, lines):
        return [line.split(":")[0] for line in lines if line.endswith(": replayed")]

    def receipted(self, lines):
        return [line.split(":")[0] for line in lines if ": receipt " in line]

    def kappa(self, module, value=0):
        return kappa_research.labels_from_stream(stream(module, value))[module]["kappa"]

    def test_first_run_replays_every_module_in_one_invocation(self):
        lines = self.replay()
        self.assertEqual(self.invocations(), [self.MODULES])
        self.assertEqual(self.replayed(lines), self.MODULES)
        self.assertEqual(self.receipted(lines), [])
        self.assertEqual(self.receipts(), sorted(self.MODULES))

    def test_receipt_holds_the_module_and_its_full_kappa(self):
        self.replay()
        kappa = self.kappa("Rule30UOR.Alpha")
        receipts = [p for p in self.cache.glob("*.ok") if p.read_text().startswith("Rule30UOR.Alpha\n")]
        self.assertEqual(len(receipts), 1)
        self.assertTrue(receipts[0].name.startswith(kappa[len("sha256:"):] + "."))
        lines = receipts[0].read_text().splitlines()
        self.assertEqual(lines[1], f"kappa {kappa}")
        self.assertRegex(lines[2], r"^tools [0-9a-f]{64}$")

    def test_second_run_replays_nothing(self):
        self.replay()
        lines = self.replay()
        self.assertEqual(len(self.invocations()), 1)
        self.assertEqual(self.replayed(lines), [])
        self.assertEqual(self.receipted(lines), self.MODULES)
        receipts = [line for line in lines if ": receipt " in line]
        for line in receipts:
            self.assertRegex(line, r"^Rule30UOR\.[A-Za-z.]+: receipt sha256:[0-9a-f]{12}$")
        self.assertTrue(receipts[0].endswith(self.kappa("Rule30UOR.Alpha")[:19]))

    def test_a_rebuilt_module_with_the_same_declarations_replays_nothing(self):
        # A docstring, a comment or shifted source positions change the object
        # file (both parts) and leave the declaration stream, hence the κ, alone.
        self.replay()
        self.compile("Rule30UOR.Beta", "recompiled Rule30UOR.Beta with a new docstring")
        lines = self.replay()
        self.assertEqual(len(self.invocations()), 1)
        self.assertEqual(self.replayed(lines), [])
        self.assertEqual(self.receipted(lines), self.MODULES)

    def test_a_changed_value_replays_exactly_that_module(self):
        self.replay()
        # A changed value changes the object file too, as a real compilation does.
        self.compile("Rule30UOR.Beta", "compiled Rule30UOR.Beta with value 1", value=1)
        lines = self.replay()
        self.assertEqual(self.invocations()[-1], ["Rule30UOR.Beta"])
        self.assertEqual(self.replayed(lines), ["Rule30UOR.Beta"])
        self.assertEqual(self.receipted(lines), ["Rule30UOR.Alpha", "Rule30UOR.Parts.Gamma"])
        # The receipt is addressed by meaning: the old declarations' receipt is
        # kept beside the new one, so restoring them replays nothing.
        self.compile("Rule30UOR.Beta", "compiled Rule30UOR.Beta restored", value=0)
        self.assertEqual(self.replayed(self.replay()), [])

    def test_failing_leanchecker_writes_no_receipt(self):
        self.replay(success=False, LEANCHECKER_EXIT="1")
        self.assertEqual(self.receipts(), [])
        self.assertEqual(len(self.invocations()), 1)
        # Nothing was recorded, so the next run replays everything again.
        self.assertEqual(self.replayed(self.replay()), self.MODULES)

    def test_receipts_are_keyed_by_the_proof_tools(self):
        self.replay()
        self.leanchecker.write_text(self.leanchecker.read_text() + "# another kernel\n")
        self.assertEqual(self.replayed(self.replay()), self.MODULES)
        (self.core / "lean-toolchain").write_text("leanprover/lean4:other\n")
        self.assertEqual(self.replayed(self.replay()), self.MODULES)
        self.assertEqual(self.replayed(self.replay()), [])

    def test_missing_artifact_fails_before_replaying(self):
        (self.core / ".lake/build/lib/lean/Rule30UOR/Beta.olean").unlink()
        self.replay(success=False)
        self.assertEqual(self.invocations(), [])
        self.assertEqual(self.receipts(), [])

    def test_failing_exporter_fails_before_replaying(self):
        (self.streams / "Rule30UOR.Parts.Gamma.sexp").unlink()
        self.replay(success=False)
        self.assertEqual(self.invocations(), [])
        self.assertEqual(self.receipts(), [])

    def test_default_cache_is_the_scratch_directory(self):
        env = dict(self.env)
        env.pop("RULE30_REPLAY_CACHE")
        result = subprocess.run(["python3", "scripts/replay_research.py"], cwd=self.repo,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(list((self.repo / ".r30/replay").glob("*.ok"))), len(self.MODULES))
        self.assertFalse(self.cache.exists())


    def test_labels_are_memoized_by_artifact_bytes(self):
        # A second run never calls the exporter: the stream is gone and the run still passes.
        self.replay()
        for module in self.MODULES:
            (self.streams / (module + ".sexp")).unlink()
        self.assertEqual(self.replayed(self.replay()), [])

    def test_the_memo_is_keyed_by_the_labeling_procedure(self):
        self.replay()
        (self.core / "scripts" / "KappaExport.lean").write_text("-- another exporter\n")
        for module in self.MODULES:
            (self.streams / (module + ".sexp")).unlink()
        self.replay(success=False)

    def test_a_statement_proved_twice_is_refused(self):
        self.compile("Rule30UOR.Alpha", "compiled Alpha with a theorem", theorems=[("t", 7)])
        self.compile("Rule30UOR.Beta", "compiled Beta with the same theorem", theorems=[("u", 7)])
        lines = self.replay(success=False)
        self.assertEqual(self.invocations(), [])
        self.assertEqual(self.receipts(), [])

    def test_different_statements_pass_and_generated_theorems_do_not_count(self):
        # `d` is each fixture module's definition: its equation lemmas are generated.
        self.compile("Rule30UOR.Alpha", "compiled Alpha", theorems=[("t", 7), ("d.eq_1", 8)])
        self.compile("Rule30UOR.Beta", "compiled Beta", theorems=[("u", 9), ("d.eq_1", 8)])
        self.assertEqual(self.replayed(self.replay()), self.MODULES)

    def test_a_statement_proved_twice_is_refused_also_from_the_memo(self):
        # A retried commit is judged on memo hits alone: the statements are read back from the memo.
        self.compile("Rule30UOR.Alpha", "compiled Alpha with a theorem", theorems=[("t", 7)])
        self.compile("Rule30UOR.Beta", "compiled Beta with the same theorem", theorems=[("u", 7)])
        self.replay(success=False)
        for module in self.MODULES:
            (self.streams / (module + ".sexp")).unlink()
        self.replay(success=False)
        self.assertEqual(self.invocations(), [])

    def test_the_gate_memo_is_written_only_where_the_gate_says(self):
        memo = self.base / "gate-memo"
        self.replay(RULE30_KAPPA_MEMO=str(memo))
        self.assertTrue(any(p.is_file() for p in memo.rglob("*")))
        self.assertFalse((self.cache / "kappa").exists())

    def test_the_memo_is_keyed_by_the_labeling_rule(self):
        self.replay()
        rule = self.repo / "scripts" / "kappa_label.py"
        rule.write_text(rule.read_text() + "\n# another labeling rule\n")
        for module in self.MODULES:
            (self.streams / (module + ".sexp")).unlink()
        self.replay(success=False)

    def test_reports_and_the_redundancy_test_do_not_relabel(self):
        # kappa_research.py holds no labeling rule: editing it reuses the memo.
        self.replay()
        research = self.repo / "scripts" / "kappa_research.py"
        research.write_text(research.read_text() + "\n# a report changed\n")
        for module in self.MODULES:
            (self.streams / (module + ".sexp")).unlink()
        self.assertEqual(self.replayed(self.replay()), [])

    def test_an_unreadable_memo_entry_is_a_miss(self):
        self.replay()
        for entry in (self.cache / "kappa").rglob("*"):
            if entry.is_file():
                entry.write_text("{truncated")
        self.assertEqual(self.replayed(self.replay()), [])


if __name__ == "__main__":
    unittest.main()
