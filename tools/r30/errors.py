"""Every typed failure of the `r30` command surface, in one register.

A command that refuses or fails exits through `fail(code, detail)`: the code
names a row here, the row fixes the title, the class and the exit status, and
`rule30-api/model/errors.toml` (`prismpm/errors/1`) is generated from this
table by `bin/r30 api sync`. The tests refuse a `fail` in `cli.py` whose code
is not registered and a registered code no command raises, so a public failure
cannot exist without a row (template rule R5), and the exit statuses are the
closed set {1: the check failed, 2: the request was refused}.
"""

import sys

ERRORS = [
    {"code": "R301001", "title": "Unknown claim", "class": "register", "exit": 2,
     "statement": "A command names a claim id that is not in frontier.toml.",
     "commands": ["claim", "interface"]},
    {"code": "R301002", "title": "Register inconsistent with the kernel", "class": "register", "exit": 1,
     "statement": "A proved claim lacks a kernel-checked Lean theorem under propext and Quot.sound or a published lexeme, a refuted claim names no refutation, a claim depends on an unknown claim, or the rendered Frontier module is stale.",
     "commands": ["frontier_check"]},
    {"code": "R301003", "title": "Register edit refused", "class": "register", "exit": 2,
     "statement": "frontier add or set names a status outside open, proved, refuted and retired, adds an id that exists, or sets one that does not.",
     "commands": ["frontier_add", "frontier_set"]},
    {"code": "R302001", "title": "Unknown lexeme", "class": "lexicon", "exit": 2,
     "statement": "lexicon show names neither a lexeme id nor the Lean name of a published lexeme.",
     "commands": ["lexicon_show"]},
    {"code": "R302002", "title": "Statement not expressible in LexLean", "class": "converter", "exit": 2,
     "statement": "The Lean declaration cannot be stated on the first-order surface: an implicit binder, a cast, Bool.xor instead of bxor, 2 ^ k instead of twopow k, a lexeme not visible from the target lexicon, or a function-typed argument. Fix the Lean statement, not the entry.",
     "commands": ["theorem_preview", "theorem_add", "probe"]},
    {"code": "R302003", "title": "Unpublish refused", "class": "lexicon", "exit": 2,
     "statement": "theorem remove names a lexeme that is not a published proof constant of this project or whose statement block cannot be located.",
     "commands": ["theorem_remove"]},
    {"code": "R303001", "title": "LexLean check failed", "class": "lexlean", "exit": 1,
     "statement": "lexlean check reported a diagnostic for a module of the selected project.",
     "commands": ["check"]},
    {"code": "R303002", "title": "LexLean verify failed", "class": "lexlean", "exit": 1,
     "statement": "lexlean verify produced no attestation for the selected project or modules.",
     "commands": ["verify"]},
    {"code": "R303003", "title": "API drifted from its sources", "class": "lexlean", "exit": 1,
     "statement": "A generated module, register, schema, feature, conformance document or the logo of rule30-api differs from what its sources render; run bin/r30 api sync.",
     "commands": ["api_check"]},
    {"code": "R304001", "title": "Probe failed", "class": "kernel", "exit": 1,
     "statement": "The elaboration probe of a prepared statement (the same Lean that lexlean verify runs) reported errors.",
     "commands": ["probe"]},
    {"code": "R304002", "title": "Axiom beyond propext and Quot.sound", "class": "kernel", "exit": 1,
     "statement": "A named theorem is unknown to Lean or depends on an axiom other than propext and Quot.sound.",
     "commands": ["axioms"]},
    {"code": "R304003", "title": "Theorem depends on Classical.choice", "class": "kernel", "exit": 1,
     "statement": "At least one theorem under the given prefixes depends on Classical.choice.",
     "commands": ["choice_audit"]},
    {"code": "R304004", "title": "Lean cannot answer", "class": "kernel", "exit": 1,
     "statement": "The query to the built research library failed: the library is not built, a module is missing, or Lean reported an error.",
     "commands": ["claim", "sig", "mentions", "interface", "frontier_render", "frontier_add", "frontier_set", "unpublished", "selfcheck", "define"]},
    {"code": "R305001", "title": "Gate already running", "class": "gate", "exit": 2,
     "statement": "A pre-commit gate started from this checkout is still running; wait for it (bin/r30 gate).",
     "commands": ["commit"]},
    {"code": "R305002", "title": "Module registration refused", "class": "workspace", "exit": 2,
     "statement": "module add names a module that is not a valid Rule30UOR module name or whose Lake workspace files are absent.",
     "commands": ["module_add"]},
    {"code": "R305003", "title": "Lake build failed", "class": "workspace", "exit": 1,
     "statement": "lake build of the named research modules reported errors.",
     "commands": ["module_add", "module_build"]},
    {"code": "R305004", "title": "Experiment failed", "class": "experiment", "exit": 1,
     "statement": "The experiment script exited with a nonzero status; its output precedes the failure.",
     "commands": ["experiment_run"]},
    {"code": "R306001", "title": "Production export failed", "class": "production", "exit": 1,
     "statement": "lexlean production build refused the request or the project: a malformed request, a root that is not a production root, an unregistered target digest, a stale lock, an ineligible closure, or a failed certificate.",
     "commands": ["api_production"]},
    {"code": "R306002", "title": "Production bundle replay failed", "class": "production", "exit": 1,
     "statement": "lexlean production verify-artifact found a disagreement between the published bundle's parts.",
     "commands": ["api_production"]},
]

BY_CODE = {e["code"]: e for e in ERRORS}


def fail(code, detail=""):
    """Report a registered failure on stderr and exit with its status."""
    e = BY_CODE[code]
    message = f"{code} {e['title']}" + (f": {detail}" if detail else "")
    print(message, file=sys.stderr)
    sys.exit(e["exit"])
