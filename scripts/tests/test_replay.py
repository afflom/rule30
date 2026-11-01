"""The kernel replay keeps a content-addressed receipt per replayed artifact."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class ReplayReceiptTests(unittest.TestCase):
    MODULES = ["Rule30UOR.Alpha", "Rule30UOR.Beta", "Rule30UOR.Parts.Gamma"]

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.core = self.repo / "rule30-core-lean"
        (self.repo / "scripts").mkdir(parents=True)
        for name in ("replay_research.py", "check_research_coverage.py"):
            shutil.copy(ROOT / "scripts" / name, self.repo / "scripts" / name)
        roots = ", ".join(f'"{m}"' for m in self.MODULES)
        (self.core / "scripts").mkdir(parents=True)
        (self.core / "lakefile.toml").write_text('[[lean_lib]]\nname = "Rule30UOR"\nroots = [' + roots + ']\n')
        (self.core / "scripts/CheckResearchAxioms.lean").write_text(
            "".join(f"import {m}\n" for m in self.MODULES) + "if (`Rule30UOR).isPrefixOf name then\n")
        (self.core / "lean-toolchain").write_text("leanprover/lean4:test\n")
        for module in self.MODULES:
            source = self.core / Path(*module.split(".")).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- replay fixture\n")
            self.compile(module, "compiled " + module)
        # A toolchain prefix with a leanchecker that records its arguments, and a
        # `lake env` that names that prefix and runs the command it is given.
        self.prefix = self.base / "toolchain"
        (self.prefix / "bin").mkdir(parents=True)
        self.log = self.base / "leanchecker.log"
        self.leanchecker = self.prefix / "bin/leanchecker"
        self.leanchecker.write_text("#!/bin/sh\n"
                                    f'echo "$@" >> "{self.log}"\n'
                                    'exit "${LEANCHECKER_EXIT:-0}"\n')
        self.leanchecker.chmod(0o755)
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

    def compile(self, module, contents):
        olean = self.core / ".lake/build/lib/lean" / Path(*module.split("."))
        olean = olean.with_name(olean.name + ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.write_text(contents + "\n")
        olean.with_name(olean.name + ".private").write_text("private " + contents + "\n")

    def replay(self, success=True, **env):
        result = subprocess.run(["python3", "scripts/replay_research.py"], cwd=self.repo,
                                env=dict(self.env, **env), capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result.stdout.splitlines()

    def invocations(self):
        return [line.split() for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def receipts(self):
        return sorted(p.read_text().strip() for p in self.cache.glob("*.ok"))

    def replayed(self, lines):
        return [line.split(":")[0] for line in lines if line.endswith(": replayed")]

    def receipted(self, lines):
        return [line.split(":")[0] for line in lines if ": receipt " in line]

    def test_first_run_replays_every_module_in_one_invocation(self):
        lines = self.replay()
        self.assertEqual(self.invocations(), [self.MODULES])
        self.assertEqual(self.replayed(lines), self.MODULES)
        self.assertEqual(self.receipted(lines), [])
        self.assertEqual(self.receipts(), sorted(self.MODULES))

    def test_second_run_replays_nothing(self):
        self.replay()
        lines = self.replay()
        self.assertEqual(len(self.invocations()), 1)
        self.assertEqual(self.replayed(lines), [])
        self.assertEqual(self.receipted(lines), self.MODULES)
        for line in lines[:3]:
            self.assertRegex(line, r"^Rule30UOR\.[A-Za-z.]+: receipt [0-9a-f]{12}$")

    def test_modified_artifact_replays_exactly_that_module(self):
        self.replay()
        self.compile("Rule30UOR.Beta", "recompiled Rule30UOR.Beta")
        lines = self.replay()
        self.assertEqual(self.invocations()[-1], ["Rule30UOR.Beta"])
        self.assertEqual(self.replayed(lines), ["Rule30UOR.Beta"])
        self.assertEqual(self.receipted(lines), ["Rule30UOR.Alpha", "Rule30UOR.Parts.Gamma"])
        # The receipt is addressed by content: the old artifact's receipt is kept
        # beside the new one, so restoring the artifact replays nothing.
        self.compile("Rule30UOR.Beta", "compiled Rule30UOR.Beta")
        self.assertEqual(self.replayed(self.replay()), [])

    def test_private_part_is_part_of_the_artifact(self):
        self.replay()
        olean = self.core / ".lake/build/lib/lean/Rule30UOR/Alpha.olean.private"
        olean.write_text("other proof terms\n")
        self.assertEqual(self.replayed(self.replay()), ["Rule30UOR.Alpha"])

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

    def test_default_cache_is_the_scratch_directory(self):
        env = dict(self.env)
        env.pop("RULE30_REPLAY_CACHE")
        result = subprocess.run(["python3", "scripts/replay_research.py"], cwd=self.repo,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(list((self.repo / ".r30/replay").glob("*.ok"))), len(self.MODULES))
        self.assertFalse(self.cache.exists())


if __name__ == "__main__":
    unittest.main()
