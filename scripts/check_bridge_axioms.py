#!/usr/bin/env python3
"""Kernel axiom audit for every theorem the bridge package defines.

The import list is generated from the bridge's `lakefile.toml` roots, so a new
bridge module cannot escape the audit. Theorems from the pinned prize kit
(`Ruliology`) and from Lean itself are not audited; everything else must depend
only on `propext` and `Quot.sound`.
"""

from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

AUDIT = r'''
open Lean Elab Command

elab "#check_bridge_axioms" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let external : Array Name := #[`Ruliology, `Lean, `Init, `Std, `Lake]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    let some i := env.getModuleIdxFor? name | continue
    let m := env.header.moduleNames[i.toNat]!
    if external.any (·.isPrefixOf m) then continue
    unless info matches .thmInfo _ do continue
    for axiomName in ← liftTermElabM (Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
    checked := checked + 1
  unless checked > 0 do
    throwError "no bridge theorems were found"
  logInfo m!"Checked {checked} bridge theorems; all axioms are in propext, Quot.sound."

#check_bridge_axioms
'''


def bridge_modules(bridge):
    config = tomllib.loads((bridge / "lakefile.toml").read_text())
    modules = []
    for library in config["lean_lib"]:
        modules.extend(library.get("roots", [library["name"]]))
    return modules


def main():
    bridge = Path(__file__).resolve().parents[1] / "rule30-bridge"
    imports = "".join(f"import {m}\n" for m in bridge_modules(bridge))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("import Lean\n" + imports + AUDIT)
        path = f.name
    try:
        result = subprocess.run(["lake", "env", "lean", path], cwd=bridge,
                                capture_output=True, text=True)
    finally:
        Path(path).unlink()
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode != 0 or "error" in result.stdout:
        sys.exit(1)


if __name__ == "__main__":
    main()
