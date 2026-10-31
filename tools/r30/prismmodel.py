"""The PrismPM project model of the API, generated from the register, the
command surface and the architecture.

`rule30-api/model/` holds the registers PrismPM's own model uses, in the
shapes of UOR-Foundation/template and PrismPM:

- `authorities.toml`, `ids.toml`, `ledger.toml` (`template/1`): the
  conceptual model and the sources the project realizes (the Rule 30 Prize,
  Problem 1; LexLean and PrismPM as the observer facets of the proof), the
  register's claims as capabilities with a level, and the evidence of each;
- `commands.toml` (`prismpm/command-contract/1`): every leaf of the `r30`
  command surface with what it mutates and the schema of its result, so a
  command cannot exist without a row (the MCP tools and `Api.lex.tex` come
  from the same parser);
- `standards.toml` (`prismpm/standards/1`): the public standards the
  architecture is modelled on, through the vendored `prism.arch` and
  `prism.qual` facets, with exactly the entries `Architecture.lex.tex` uses;
- `projection.toml` (`prismpm/projection/1`): which declaration of which
  module projects to which collection of the view (the stdlib's model kinds
  as a catalog, the labeled entries, the claims, the commands, the panels);
- `contracts.toml` (`prismpm/contracts/1`) with `rule30-api/schemas/`: the
  JSON the project publishes (`register.json`, `--json` of `interface`).

`prismpm.toml` binds the LexLean project. No PrismPM toolchain runs here: the
gate is the pre-commit hook, and CI only renders; the model is kept so that
a pinned PrismPM can build the generated runtime and publish to the
stakeholders without any change to the sources."""

import json

from . import archmodel, frontier, repo

API = repo.ROOT / "rule30-api"
MODEL = API / "model"
SCHEMAS = API / "schemas"

LEVEL = {"proved": "build", "open": "open", "refuted": "some-true", "retired": "some-true"}

AUTHORITIES = [
    {"id": "RULE30-PRIZE", "name": "Wolfram Rule 30 Prize, Problem 1",
     "citation": "https://www.rule30prize.org",
     "statement": "The center column of Rule 30 from a single black cell is not eventually periodic.",
     "realized_by": lambda claims: [c["id"] for c in claims if c["status"] in ("proved", "open")]},
    {"id": "LEXLEAN", "name": "UOR-Foundation/LexLean",
     "citation": "https://github.com/UOR-Foundation/LexLean",
     "statement": "A closed-lexicon LaTeX-to-Lean 4 compiler; the paper, the register and the API are its modules.",
     "realized_by": lambda claims: ["api-modules"]},
    {"id": "PRISMPM", "name": "UOR-Foundation/PrismPM",
     "citation": "https://github.com/UOR-Foundation/PrismPM",
     "statement": "Model registers (authorities, ids, ledger, commands, standards, projection, contracts) and the generated runtime of LexLean application models.",
     "realized_by": lambda claims: ["api-modules", "prism-model"]},
    {"id": "PRISM-STDLIB", "name": "UOR-Foundation/PrismPM stdlib (Foundation.Arch, Foundation.Qual) 0.2.0",
     "citation": "https://github.com/UOR-Foundation/PrismPM/tree/main/stdlib",
     "statement": "The architecture and quality entities (ISO/IEC/IEEE 42010, ISO/IEC 25010) as LexLean structures, vendored under rule30-api/stdlib with their license.",
     "realized_by": lambda claims: ["api-modules"]},
]

API_IDS = [
    {"id": "api-modules", "level": "build", "suite": "api",
     "statement": "The command surface, the register, the architecture and the presentation are LexLean semantic modules on prism-stdlib, verified by the gate.",
     "feature": "rule30-api/src", "evidence": "lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check"},
    {"id": "prism-model", "level": "build", "suite": "api",
     "statement": "The model registers (authorities, ids, ledger, commands, standards, projection, contracts) are generated from the register, the parser and the architecture, and drift is refused.",
     "feature": "rule30-api/model", "evidence": "bin/r30 api check; scripts/tests/test_r30.py"},
    {"id": "current-view", "level": "build", "suite": "api",
     "statement": "The view workflow renders the artifacts Presentation.lex.tex declares, with the site, on every push to main, and runs no validation.",
     "feature": ".github/workflows/view.yml", "evidence": "bin/r30 view render; scripts/tests/test_r30.py"},
]

# What each command mutates (`never` when it only reads). A leaf of the
# parser without a row here is reported by `check`.
MUTATES = {
    "api_sync": "api-modules-and-model", "theorem_add": "paper-modules-and-glossary", "theorem_remove": "paper-modules-and-glossary",
    "define": "paper-modules-and-glossary", "frontier_add": "register", "frontier_set": "register", "frontier_render": "paper-modules",
    "module_add": "lean-workspace", "module_build": "lake-build", "commit": "repository", "verify": "lexlean-build",
    "check": "lexlean-build", "interface": "interface-sheets", "view_render": "view-directory", "experiment_run": "never",
}

STANDARDS = [
    {"id": "ISO-42010-2022", "name": "ISO/IEC/IEEE 42010:2022", "edition": "2022",
     "reference": "https://www.iso.org/standard/74393.html", "basis": "public-catalog",
     "scope": "Architecture description conceptual foundations and view/viewpoint framework",
     "provenance": "ISO/IEC/IEEE international standard catalog entry",
     "interpretation": "The architecture of the proof effort is stakeholders, concerns, viewpoints and views on Foundation.Arch; every entry carries a stdlib entity and Architecture.lex.tex decides that the indices agree with the labels.",
     "facet_package": "prism.arch", "facet_entries": ["arch-concern", "arch-model-kind", "arch-stakeholder", "arch-view", "arch-viewpoint"]},
    {"id": "ISO-25010-2023", "name": "ISO/IEC 25010:2023", "edition": "2023",
     "reference": "https://www.iso.org/standard/78176.html", "basis": "public-catalog",
     "scope": "System and software product quality model",
     "provenance": "ISO/IEC international standard catalog entry",
     "interpretation": "What an optimal implementation is here: characteristics, subcharacteristics, requirements and measures with thresholds on Foundation.Qual, each measure naming the r30 command that reports it.",
     "facet_package": "prism.qual", "facet_entries": ["qual-characteristic", "qual-measure", "qual-requirement", "qual-subcharacteristic"]},
]

PROJECTION = {
    "catalog": [{"module": "Foundation.Arch", "declaration": "ModelKind", "facet": "prism.arch@1.0.0", "target": "model_kinds"}],
    "entity": [
        {"module": "Architecture", "type_name": "StakeholderEntry", "target": "stakeholders"},
        {"module": "Architecture", "type_name": "ConcernEntry", "target": "concerns"},
        {"module": "Architecture", "type_name": "ViewpointEntry", "target": "viewpoints"},
        {"module": "Architecture", "type_name": "ViewEntry", "target": "views"},
        {"module": "Architecture", "type_name": "CharacteristicEntry", "target": "characteristics"},
        {"module": "Architecture", "type_name": "SubcharacteristicEntry", "target": "subcharacteristics"},
        {"module": "Architecture", "type_name": "RequirementEntry", "target": "requirements"},
        {"module": "Architecture", "type_name": "MeasureEntry", "target": "measures"},
        {"module": "Register", "type_name": "Claim", "target": "register"},
        {"module": "Api", "type_name": "Command", "target": "commands"},
        {"module": "Presentation", "type_name": "Artifact", "target": "artifacts"},
        {"module": "Presentation", "type_name": "Panel", "target": "panels"},
        {"module": "Presentation", "type_name": "Journey", "target": "journeys"},
        {"module": "Application", "type_name": "StatusMark", "target": "statusMarks"},
    ],
}

CONTRACTS = [
    {"schema": "r30/register/1", "path": "schemas/register.schema.json", "media_type": "application/vnd.r30.register.v1+json",
     "identity": "sha256-canonical-json", "maximum_bytes": 1048576, "maximum_items": 4096, "extension_policy": "closed",
     "compatibility": "exact-major", "produced_by": "frontier_list", "artifact": "register.json"},
    {"schema": "r30/interface-sheet/1", "path": "schemas/interface-sheet.schema.json", "media_type": "application/vnd.r30.interface-sheet.v1+json",
     "identity": "sha256-canonical-json", "maximum_bytes": 1048576, "maximum_items": 4096, "extension_policy": "closed",
     "compatibility": "exact-major", "produced_by": "interface", "artifact": "interfaces"},
]

REGISTER_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "r30/register/1",
    "title": "The claim register (frontier list --json; view/register.json)",
    "type": "array",
    "items": {
        "type": "object",
        "required": ["id", "status", "statement"],
        "additionalProperties": False,
        "properties": {
            "id": {"type": "string", "pattern": "^[a-z][a-z0-9-]*$"},
            "status": {"type": "string", "enum": list(frontier.STATUSES)},
            "statement": {"type": "string"},
            "lean": {"type": "string"},
            "lexeme": {"type": "string"},
            "since": {"type": "string"},
            "note": {"type": "string"},
            "depends": {"type": "array", "items": {"type": "string"}},
        },
    },
}

SHEET_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "$id": "r30/interface-sheet/1",
    "title": "The interface sheet of a claim (interface --json)",
    "type": "object",
    "required": ["id", "status", "statement", "chain", "notions"],
    "additionalProperties": False,
    "properties": {
        "id": {"type": "string"},
        "status": {"type": "string", "enum": list(frontier.STATUSES)},
        "statement": {"type": "string"},
        "lean": {"type": ["string", "null"]},
        "note": {"type": ["string", "null"]},
        "chain": {"type": "array", "items": {"type": "object", "required": ["id", "status"],
                                             "properties": {"id": {"type": "string"}, "status": {"type": "string"},
                                                            "lean": {"type": ["string", "null"]}}}},
        "notions": {"type": "array", "items": {"type": "object", "required": ["lean"],
                                               "properties": {"lean": {"type": "string"}, "lexeme": {"type": ["string", "null"]},
                                                              "definition": {"type": ["string", "null"]}}}},
        "related": {"type": "object", "additionalProperties": {"type": "array", "items": {"type": "string"}}},
    },
}


def _q(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def _list(xs):
    return "[" + ", ".join(_q(x) for x in xs) + "]"


def rows():
    return frontier.load()["claim"]


def authorities(claims):
    lines = ['spec = "template/1"', ""]
    for a in AUTHORITIES:
        lines += ["[[authority]]", f"id = {_q(a['id'])}", f"name = {_q(a['name'])}", f"citation = {_q(a['citation'])}",
                  f"statement = {_q(a['statement'])}", "realized_by = " + _list(a["realized_by"](claims)), ""]
    return "\n".join(lines)


def ids(claims):
    lines = ['spec = "template/1"', ""]
    for c in claims:
        lines += ["[[id]]", f"id = {_q(c['id'])}", f"level = {_q(LEVEL[c['status']])}", 'suite = "register"',
                  f"statement = {_q(c['statement'])}", ""]
    for x in API_IDS:
        lines += ["[[id]]", f"id = {_q(x['id'])}", f"level = {_q(x['level'])}", f"suite = {_q(x['suite'])}",
                  f"statement = {_q(x['statement'])}", ""]
    return "\n".join(lines)


def ledger(claims):
    lines = ['spec = "template/1"', ""]
    for c in claims:
        evidence = (f"frontier check: {c['lean']} kernel-checked under propext and Quot.sound and published"
                    if c["status"] == "proved" else
                    f"register: {c['status']}" + (f" ({c['lean']})" if c.get("lean") else ""))
        lines += ["[[claim]]", f"id = {_q(c['id'])}", f"level = {_q(LEVEL[c['status']])}",
                  f"statement = {_q(c['statement'])}", f"feature = {_q('interfaces/' + c['id'] + '.md')}",
                  f"evidence = {_q(evidence)}", ""]
    for x in API_IDS:
        lines += ["[[claim]]", f"id = {_q(x['id'])}", f"level = {_q(x['level'])}", f"statement = {_q(x['statement'])}",
                  f"feature = {_q(x['feature'])}", f"evidence = {_q(x['evidence'])}", ""]
    return "\n".join(lines)


def commands():
    from . import apimodel
    lines = ['spec = "prismpm/command-contract/1"', ""]
    for r in apimodel.surface():
        lines += ["[[command]]", f"name = {_q(r['name'])}", f"path = {_list(r['path'])}",
                  f"mutates = {_q(MUTATES.get(r['name'], 'never'))}", "requires_digest = false",
                  f"result_schema = {_q('r30/' + r['name'].replace('_', '-') + '-result/1')}", ""]
    return "\n".join(lines)


def standards():
    lines = ['spec = "prismpm/standards/1"', ""]
    for st in STANDARDS:
        lines += ["[[standard]]"]
        for k in ("id", "name", "edition", "reference", "basis", "scope", "provenance", "interpretation", "facet_package"):
            lines.append(f"{k} = {_q(st[k])}")
        lines += ["facet_entries = " + _list(st["facet_entries"]), 'coverage_state = "implemented"', "release_scope = true", ""]
    return "\n".join(lines)


def projection():
    lines = ['spec = "prismpm/projection/1"', ""]
    for c in PROJECTION["catalog"]:
        lines += ["[[catalog]]", f"module = {_q(c['module'])}", f"declaration = {_q(c['declaration'])}",
                  f"facet = {_q(c['facet'])}", f"target = {_q(c['target'])}", ""]
    for e in PROJECTION["entity"]:
        lines += ["[[entity]]", f"module = {_q(e['module'])}", f"type_name = {_q(e['type_name'])}", f"target = {_q(e['target'])}", ""]
    return "\n".join(lines)


def contracts():
    lines = ['spec = "prismpm/contracts/1"', ""]
    for c in CONTRACTS:
        lines += ["[[contract]]"]
        for k, v in c.items():
            lines.append(f"{k} = {v if isinstance(v, int) else _q(v)}")
        lines.append("")
    return "\n".join(lines)


PRISMPM = '''spec = "prismpm/project/1"
project = "Rule30Api"
lexlean_project = "lexlean.toml"
build_root = ".prism"

[limits]
max_holo_bytes = 67108864
max_entities = 100000
max_diagnostics = 256
'''


def files(claims):
    """Every generated file of the model: path -> text."""
    out = {
        MODEL / "authorities.toml": authorities(claims),
        MODEL / "ids.toml": ids(claims),
        MODEL / "ledger.toml": ledger(claims),
        MODEL / "commands.toml": commands(),
        MODEL / "standards.toml": standards(),
        MODEL / "projection.toml": projection(),
        MODEL / "contracts.toml": contracts(),
        SCHEMAS / "register.schema.json": json.dumps(REGISTER_SCHEMA, indent=1) + "\n",
        SCHEMAS / "interface-sheet.schema.json": json.dumps(SHEET_SCHEMA, indent=1) + "\n",
        API / "prismpm.toml": PRISMPM,
    }
    return out


def sync():
    MODEL.mkdir(parents=True, exist_ok=True)
    SCHEMAS.mkdir(parents=True, exist_ok=True)
    claims = rows()
    changed = False
    for path, text in files(claims).items():
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
            changed = True
    return {"model": str(MODEL.relative_to(repo.ROOT)), "claims": len(claims), "registers": 7, "changed": changed}


def check():
    claims = rows()
    for path, text in files(claims).items():
        if not path.exists() or path.read_text() != text:
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} drifted from its sources; run `bin/r30 api sync`"}
    from . import apimodel
    missing = [r["name"] for r in apimodel.surface() if r["name"] not in MUTATES and _mutating(r)]
    if missing:
        return {"ok": False, "reason": f"commands without a mutation class in prismmodel.MUTATES: {', '.join(missing)}"}
    for st in STANDARDS:
        facet = API / "language" / st["facet_package"] / "entries"
        absent = [e for e in st["facet_entries"] if not (facet / f"{e}.toml").exists()]
        if absent:
            return {"ok": False, "reason": f"{st['id']} names lexicon entries absent from rule30-api/language: {', '.join(absent)}"}
    return {"ok": True, "reason": None}


def _mutating(row):
    """A command with a `--write`-like flag or a sub-verb that is not a query
    must declare what it mutates."""
    verbs = {"add", "set", "remove", "sync", "render", "build", "run", "commit", "write"}
    return bool(set(row["path"]) & verbs) or any(a["name"] == "write" for a in row["arguments"])
