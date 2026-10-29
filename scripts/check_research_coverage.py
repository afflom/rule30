#!/usr/bin/env python3
"""Require every core Rule30UOR source to be built, audited, and kernel-replayed."""

from pathlib import Path
import re
import sys
import tomllib


def covered_modules(root):
    core = root / "rule30-core-lean"
    config = tomllib.loads((core / "lakefile.toml").read_text())
    libraries = [library for library in config["lean_lib"] if library["name"] == "Rule30UOR"]
    if len(libraries) != 1:
        raise ValueError("Expected exactly one Rule30UOR library")
    roots = set(libraries[0]["roots"])
    sources = {".".join(path.relative_to(core).with_suffix("").parts)
               for path in (core / "Rule30UOR").rglob("*.lean")}
    if not sources:
        raise ValueError("No Rule30UOR sources found")
    if sources != roots:
        raise ValueError(f"Rule30UOR build coverage mismatch: unregistered={sorted(sources - roots)}, "
                         f"missing sources={sorted(roots - sources)}")
    if any(not re.fullmatch(r"Rule30UOR(?:\.[A-Za-z_][A-Za-z_0-9]*)+", name) for name in roots):
        raise ValueError("Rule30UOR module names must use ordinary Lean identifiers")
    audit = (core / "scripts/CheckResearchAxioms.lean").read_text()
    imports = set(re.findall(r"^import (Rule30UOR(?:\.[A-Za-z_][A-Za-z_0-9]*)+)\s*$", audit, re.M))
    if not roots <= imports:
        raise ValueError(f"Modules missing from axiom audit: {sorted(roots - imports)}")
    if "if (`Rule30UOR).isPrefixOf name then" not in audit:
        raise ValueError("The axiom audit must cover the entire Rule30UOR namespace")
    return sorted(roots)


if __name__ == "__main__":
    try:
        modules = covered_modules(Path(__file__).resolve().parents[1])
        if sys.argv[1:] == ["--modules"]:
            # The kernel replay consumes this same list; no second module allowlist.
            print(" ".join(modules))
        elif sys.argv[1:]:
            raise ValueError("Usage: check_research_coverage.py [--modules]")
        else:
            print(f"All {len(modules)} Rule30UOR sources are build roots and axiom-audit imports.")
    except (OSError, ValueError, KeyError) as error:
        print(f"Research coverage failed: {error}", file=sys.stderr)
        sys.exit(1)
