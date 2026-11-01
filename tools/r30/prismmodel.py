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
  JSON the project publishes (`register.json`, `--json` of `interface`) and
  the result schemas of the read-only commands (`schema.py`);
- `errors.toml` (`prismpm/errors/1`): every typed failure of the commands,
  from `errors.ERRORS`, the table `cli.py` exits through;
- `dependencies.toml` (`prismpm/dependencies/1`): the pinned compiler, Lean
  toolchain, builtin lexicons and the vendored prism-stdlib, with the tree
  digests `lexlean.lock` records and this module computes;
- `runtime-roots.toml` (`prismpm/runtime-roots/1`) and
  `production/request.json`: the production roots `lexlean production`
  exports to Rust (`production.py`);
- `stdlib-package.toml` (`prismpm/stdlib-package/1`): the vendored stdlib;
- `observer.toml` (`r30/observer/1`): the rows of `Observer.lex.tex` (the
  quadruple of each vantage, the overlaps, the interactions, the facets of
  the proof), from `observermodel`;
- `features/suites/<suite>.feature` and `CONFORMANCE.md`: one Gherkin
  scenario per id of `ids.toml`, worded by its level, and the conformance
  document generated from the register (template rules R1 and R3).

`prismpm.toml` binds the LexLean project. No PrismPM toolchain runs here: the
gate is the pre-commit hook, and CI only renders; the model is kept so that
a pinned PrismPM can build the generated runtime and publish to the
stakeholders without any change to the sources."""

import hashlib
import json
import tomllib

from . import archmodel, frontier, repo
from .errors import ERRORS

API = repo.ROOT / "rule30-api"
MODEL = API / "model"
SCHEMAS = API / "schemas"
FEATURES = API / "features" / "suites"
CONFORMANCE = API / "CONFORMANCE.md"

# An observed relation is measured on a window and reported, never asserted.
LEVEL = {"proved": "build", "open": "open", "refuted": "some-true", "retired": "some-true", "observed": "open"}

AUTHORITIES = [
    {"id": "RULE30-PRIZE", "name": "Wolfram Rule 30 Prize, Problem 1",
     "citation": "https://www.rule30prize.org",
     "statement": "The center column of Rule 30 from a single black cell is not eventually periodic.",
     "realized_by": lambda claims: [c["id"] for c in claims if c["status"] in ("proved", "open")]},
    {"id": "LEXLEAN", "name": "UOR-Foundation/LexLean",
     "citation": "https://github.com/UOR-Foundation/LexLean",
     "statement": "A closed-lexicon LaTeX-to-Lean 4 compiler; the paper, the register and the API are its modules.",
     "realized_by": lambda claims: ["api-modules", "verified-core", "relation-search", "recurrence-search"]},
    {"id": "PRISMPM", "name": "UOR-Foundation/PrismPM",
     "citation": "https://github.com/UOR-Foundation/PrismPM",
     "statement": "Model registers (authorities, ids, ledger, commands, standards, projection, contracts, errors, dependencies, runtime-roots, stdlib-package) and the generated runtime of LexLean application models.",
     "realized_by": lambda claims: ["api-modules", "prism-model", "rust-emission"]},
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
     "statement": "The model registers (authorities, ids, ledger, commands, standards, projection, contracts, errors, dependencies, runtime-roots, stdlib-package), the result schemas, the Gherkin suites and CONFORMANCE.md are generated from the register, the parser, the error table and the architecture, and drift is refused.",
     "feature": "rule30-api/model", "evidence": "bin/r30 api check; scripts/tests/test_r30.py"},
    {"id": "rust-emission", "level": "build", "suite": "api",
     "statement": "The production roots of Api.lex.tex (commands, commandCount) and of Rule30Core.lex.tex (rows, center, rdiag, towerWord, rulerBackground, centersFrom, rulerFrom) export to certified Rust packages through lexlean production build, kernel-checked under their stated axioms, and the published bundle replays with verify-artifact.",
     "feature": "rule30-api/production/request.json", "evidence": "bin/r30 api production; scripts/tests/test_r30.py"},
    {"id": "verified-core", "level": "build", "suite": "api",
     "statement": "Rule30Core.lex.tex declares the automaton's computational core (the rule on three cells, the row step, the rows, the center, the right diagonals rdiag, the tower of words towerWord, trailingParity, timeParity and the ruler background) as executable definitions whose production roots export to Rust; the kernel decides the first 32 centers and ruler values, rdiag 1 as the time parity on 64 times, center t = towerWord t t, the periods 2^j of the first words and the half periods 2^(j-1) of the first diagonals, the tower recursion on the first words and the agreement of the row cells with the right-edge recursion of Core.lex.tex; core-vectors.json (256 centers, 12 tower words, the ruler background below 512) is generated from the same model, cross-checked against the decided literals and identities, and published by the view. The pinned compiler has no Wasm or browser target, so the page reads the vectors rather than running the module.",
     "feature": "rule30-api/src/Rule30Core.lex.tex", "evidence": "lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check; scripts/tests/test_r30.py"},
    {"id": "observer", "level": "build", "suite": "api",
     "statement": "Observer.lex.tex records the object quadruple of every stakeholder vantage (the proof as the real object, the journey as the sensual object, the proved claims its panels render as real qualities, the panels as sensual qualities, the open claims as withdrawn) and the kernel decides withdrawal, nonempty overlap, symmetric interaction and gauge covariance over the register and the presentation.",
     "feature": "rule30-api/src/Observer.lex.tex", "evidence": "lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check"},
    {"id": "current-view", "level": "build", "suite": "api",
     "statement": "The view workflow renders the artifacts Presentation.lex.tex declares, with the site, on every push to main, deploys them to GitHub Pages at the URL Application.lex.tex names, and runs no validation; the site opens on a choice of vantage and shows one step at a time, every step a rendered panel toward a goal on declared evidence, the journeys covering the Observer's poles in order and ending in verification as the kernel decides, and the page meets WCAG AA contrast with keyboard focus and reduced motion honoured.",
     "feature": ".github/workflows/view.yml", "evidence": "bin/r30 view render; scripts/tests/test_r30.py"},
    {"id": "design-system", "level": "build", "suite": "api",
     "statement": "Presentation.lex.tex declares the design system of the site as data (colour tokens with their sRGB values in both themes, the contrast pairs the stylesheet uses, the type and spacing scales, the motion durations with their reduced-motion variant, the landing) and the kernel decides, in integer arithmetic over relative luminance, that every pair meets WCAG 2.2 AA (4.5:1 for text, 3:1 for controls and graphics) in both themes, that the scales increase, that targets are at least 24px and that reduced motion is instant; api sync writes the tokens into the site as CSS custom properties and api check refuses drift.",
     "feature": "rule30-api/src/Presentation.lex.tex", "evidence": "lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check; scripts/tests/test_r30.py DesignTests"},
    {"id": "standards-register", "level": "build", "suite": "api",
     "statement": "Standards.lex.tex names every external standard the implementation realizes (architecture, quality, accessibility, markup, graphics, metadata, provenance, schemas, API description, citation, licensing, canonical forms, attestations, the toolchains) with its authority, version, scope, realizers and check; the kernel decides that the ids are distinct, every standard has an authority and a realizer, every realizer is declared, every panel, artifact, journey, command, navigation and visualization id names a standard, and the toolchain rows carry the pinned versions; view render writes the artifacts the standards call for (openapi.json, sitemap.xml, provenance.jsonld, schema.json, attestations.intoto.json, standards.json, CITATION.cff).",
     "feature": "rule30-api/src/Standards.lex.tex", "evidence": "lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check; scripts/tests/test_r30.py"},
    # induction mechanized (Sequences.lex.tex, Discovery.lex.tex, bin/r30 sequences|discover, the observed status)
    {"id": "discovery-basis", "level": "build", "suite": "discovery",
     "statement": "Sequences.lex.tex declares the basis of the map: 79 sequences of the paper's notions (the constant, the time and trailing parities, the ruler background, the center, the cells at positions -8..8, the right and left diagonals and the tower words j <= 12, the exposed masks k <= 8, the masked column, the two cones and the seven ledger diagonals), each with its lexeme, Lean constant, parameters and κ-label (sequence <lexeme> <parameters>), and its window for t < 512 evaluated from the host Lean definitions by bin/r30 sequences --write in one Lean file that proves every evaluation form equal to its host constant; the kernel decides that the ids and the κ-labels are distinct and that every window has 16 words below 2^32, and api check refuses data that is not the basis or whose labels are not the labels of its entries. dyadicRow, blockParity and wittRespBool are excluded, with the reason recorded.",
     "feature": "rule30-api/src/Sequences.lex.tex", "evidence": "bin/r30 sequences --write; bin/r30 api check; lexlean verify rule30-api; scripts/tests/test_r30.py DiscoveryTests"},
    {"id": "relation-search", "level": "build", "suite": "discovery",
     "statement": "Discovery.lex.tex declares the contract RelationSearch (input a window of chunked Nat bit-vectors, output masks over the sequences; precondition IsWindow, postcondition AllRelationsHold, each with an executable validator and a soundness theorem), the realization RelationEngine (Gaussian elimination over F2 with a mask per pivot), the model RelationSearchModel, the transforms of the extended basis (shift, even and odd dilations, AND) as data, and the kernel decides on 64 times of the real data that the engine finds the edge parity, the left light cone, the cone identity cone-zero = cell(-1) and the increment law in the basis, and that its output passes the postcondition.",
     "feature": "rule30-api/src/Discovery.lex.tex", "evidence": "lexlean verify rule30-api; bin/r30 api check; scripts/tests/test_r30.py DiscoveryTests"},
    {"id": "recurrence-search", "level": "build", "suite": "discovery",
     "statement": "Discovery.lex.tex declares the contract RecurrenceSearch (input one window as bits, output a connection polynomial with leading 1; precondition IsSequenceWindow, postcondition SatisfiesRecurrence: the recurrence holds for every L <= t < N), the realization RecurrenceEngine (Berlekamp-Massey over F2) and the model RecurrenceSearchModel; the certificate is the recurrence on the window, not its minimality; the kernel decides s(t) = s(t-2) for the time parity and the tower word 2 and s(t) = s(t-3) for the period-3 word 100.",
     "feature": "rule30-api/src/Discovery.lex.tex", "evidence": "lexlean verify rule30-api; bin/r30 api check; scripts/tests/test_r30.py DiscoveryTests"},
    {"id": "discovery-roots", "level": "build", "suite": "discovery",
     "statement": "The production roots buildColumns, findRelations and findRecurrence of Discovery.lex.tex are executable, admit the allocation, overflow and recursion effects on rust-std, and apply their models through checked_apply with both the precondition and the postcondition checked at run time, so every output is accepted by a validator the kernel proved sound; they are requested beside the roots of Api and Rule30Core in production/request.json and runtime-roots.toml.",
     "feature": "rule30-api/production/request.json", "evidence": "bin/r30 api production; bin/r30 api check; scripts/tests/test_r30.py DiscoveryTests"},
    {"id": "discover-command", "level": "build", "suite": "discovery",
     "statement": "bin/r30 discover [--window W] [--degree 1|2] [--write] runs the engines on the basis (the certified Rust of the roots when they are built and cargo runs them, otherwise the Python mirror re-checked by the mirror of the validators, and says which), reports every relation with its columns, κ-label (relation <sorted column labels>), class (register, trivial, consequence, new) and certificate (the rank before its dependent column), and the recurrence of every base window; --write appends the new relations to the register as status observed.",
     "feature": "tools/r30/discover.py", "evidence": "scripts/tests/test_r30.py DiscoveryTests; bin/r30 discover --window 256 --degree 2"},
    {"id": "observed-status", "level": "build", "suite": "discovery",
     "statement": "The register has the status observed: a relation certified on a window (relation, window, κ-label), re-validated by frontier check against the committed windows and refused when it does not vanish; Register.lex.tex carries every claim's relation and κ-label and decides that every observed claim has both; Discovery.lex.tex decides that every relation of the register vanishes on its window; the Observer counts an observed claim as neither a real quality nor withdrawn, and the site renders its mark.",
     "feature": "frontier.toml", "evidence": "bin/r30 frontier check; scripts/tests/test_r30.py DiscoveryTests"},
    {"id": "discovery-candidates", "level": "open", "suite": "discovery",
     "statement": "The relations and recurrences bin/r30 discover --window 256 --degree 2 finds on the committed basis beyond the register are candidates for deduction: measured on the window and reported, never asserted.",
     "feature": "tools/r30/discover.py", "evidence": "bin/r30 discover --window 256 --degree 2"},
]

# The pruning of the register's routes: the audit of the conditional
# refutations (auditmodel) and the induce phase of the saved round workflow.
# Each id has its scenario and a test whose name ends in the id.
API_IDS += [
    {"id": "conditional-audit", "level": "build", "suite": "register",
     "statement": "bin/r30 audit reads, in one Lean introspection of the research library, every theorem concluding not CenterPeriodic T P, Problem1 or not CenterPer T P (or False under a CenterPeriodic hypothesis), identifies each hypothesis beyond the period and the arithmetic side conditions by its head, and classifies the conditional refutation dead (a hypothesis refuted under a period by a named theorem), live-discharged (every hypothesis discharged and the composition kernel-checked in Lean) or open (the hypotheses neither refuted nor discharged); --write records it in model/audit.toml and Audit.lex.tex, whose kernel-decided theorems are that every dead entry names a refuting theorem, the statuses are declared, the theorem names are distinct, and the count of each status; claim --related lists the open hypotheses of the conditional refutations a claim concerns.",
     "feature": "rule30-api/src/Audit.lex.tex",
     "evidence": "bin/r30 audit; bin/r30 verify api --modules src/Audit.lex.tex; scripts/tests/test_audit.py AuditTests.test_classification_of_recorded_statements_conditional_audit"},
    {"id": "induce-phase", "level": "build", "suite": "register",
     "statement": "The saved round workflow .claude/workflows/rule30-round.js opens with an Induce phase before Propose: one agent runs bin/r30 discover --window 256 --degree 2 --json and bin/r30 audit --json (a missing command is reported and contributes nothing) and returns the observed relations not in the register and the open audit obligations, which every lens receives as context and which enter Refute and Mechanize as proposals of their own (an observed relation is a candidate theorem for all t whose window certificate is already decided); the view publishes the workflow.",
     "feature": ".claude/workflows/rule30-round.js",
     "evidence": "scripts/tests/test_audit.py RoundWorkflowTests.test_the_round_opens_with_the_induce_phase_induce_phase"},
]

# What each command mutates (`never` when it only reads). A leaf of the
# parser without a row here is reported by `check`.
MUTATES = {
    "api_sync": "api-modules-and-model", "theorem_add": "paper-modules-and-glossary", "theorem_remove": "paper-modules-and-glossary",
    "define": "paper-modules-and-glossary", "frontier_add": "register", "frontier_set": "register", "frontier_render": "paper-modules",
    "module_add": "lean-workspace", "module_build": "lake-build", "commit": "repository", "verify": "lexlean-build",
    "check": "lexlean-build", "interface": "interface-sheets", "view_render": "view-directory", "experiment_run": "never",
    "api_production": "lexlean-build", "sequences": "sequences-data", "discover": "register",
}
MUTATES["audit"] = "audit-register-and-module"  # --write: model/audit.toml and src/Audit.lex.tex

# Commands whose result is a published contract rather than a result schema
# of its own: `frontier list` prints the register, `interface` the sheet.
SCHEMA_OF = {"frontier_list": "r30/register/1", "interface": "r30/interface-sheet/1"}

# The standards register itself lives in `standardsmodel` (rows, module and
# TOML); the ISO rows carry the vendored lexicon facets the architecture is
# built on, which `check` confirms exist under rule30-api/language.
from .standardsmodel import FACETS as STANDARD_FACETS  # noqa: E402

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
        {"module": "Presentation", "type_name": "Paragraph", "target": "explainer"},
        {"module": "Presentation", "type_name": "Pole", "target": "poles"},
        {"module": "Presentation", "type_name": "Step", "target": "steps"},
        {"module": "Presentation", "type_name": "Verification", "target": "verifications"},
        {"module": "Presentation", "type_name": "Pattern", "target": "navPatterns"},
        {"module": "Presentation", "type_name": "Navigation", "target": "navigations"},
        {"module": "Presentation", "type_name": "NavItem", "target": "navItems"},
        {"module": "Presentation", "type_name": "Token", "target": "tokens"},
        {"module": "Presentation", "type_name": "ContrastPair", "target": "contrastPairs"},
        {"module": "Presentation", "type_name": "TypeStep", "target": "typeScale"},
        {"module": "Presentation", "type_name": "SpaceStep", "target": "spacing"},
        {"module": "Presentation", "type_name": "Motion", "target": "motion"},
        {"module": "Presentation", "type_name": "Landing", "target": "landing"},
        {"module": "Application", "type_name": "StatusMark", "target": "statusMarks"},
        {"module": "Observer", "type_name": "Quadruple", "target": "quadruples"},
        {"module": "Observer", "type_name": "Overlap", "target": "overlaps"},
        {"module": "Observer", "type_name": "Interaction", "target": "interactions"},
        {"module": "Observer", "type_name": "Facet", "target": "facets"},
        {"module": "Standards", "type_name": "Standard", "target": "standards"},
    ],
}

CONTRACTS = [
    {"schema": "r30/register/1", "path": "schemas/register.schema.json", "media_type": "application/vnd.r30.register.v1+json",
     "identity": "sha256-canonical-json", "maximum_bytes": 1048576, "maximum_items": 4096, "extension_policy": "closed",
     "compatibility": "exact-major", "produced_by": "frontier_list", "artifact": "register.json"},
    {"schema": "r30/interface-sheet/1", "path": "schemas/interface-sheet.schema.json", "media_type": "application/vnd.r30.interface-sheet.v1+json",
     "identity": "sha256-canonical-json", "maximum_bytes": 1048576, "maximum_items": 4096, "extension_policy": "closed",
     "compatibility": "exact-major", "produced_by": "interface", "artifact": "interfaces"},
    {"schema": "r30/standards/1", "path": "schemas/standards.schema.json", "media_type": "application/vnd.r30.standards.v1+json",
     "identity": "sha256-canonical-json", "maximum_bytes": 1048576, "maximum_items": 4096, "extension_policy": "closed",
     "compatibility": "exact-major", "produced_by": "view_render", "artifact": "standards.json"},
] + [
    # the `--json` reports of the read-only commands (schema.RESULTS)
    {"schema": f"r30/{name}/1", "path": f"schemas/{name}.schema.json", "media_type": f"application/vnd.r30.{name}.v1+json",
     "identity": "sha256-canonical-json", "maximum_bytes": 1048576, "maximum_items": 4096, "extension_policy": "closed",
     "compatibility": "exact-major", "produced_by": name[:-len("-result")].replace("-", "_"), "artifact": "--json"}
    for name in ("status-result", "brief-result", "chain-result", "claim-result", "kappa-result", "api-check-result", "api-production-result",
                 "sequences-result", "discover-result")
]
from . import auditmodel  # noqa: E402
CONTRACTS.append(auditmodel.CONTRACT)  # the audit's --json report (auditmodel.RESULT_SCHEMA)

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
            "relation": {"type": "array", "items": {"type": "string"}},
            "window": {"type": "integer"},
            "kappa": {"type": "string", "pattern": "^sha256:[0-9a-f]{64}$"},
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
                  f"result_schema = {_q(result_schema(r['name']))}", ""]
    return "\n".join(lines)


def result_schema(command):
    return SCHEMA_OF.get(command, "r30/" + command.replace("_", "-") + "-result/1")


def standards():
    """`model/standards.toml`: the rows of `Standards.lex.tex` (standardsmodel)."""
    from . import standardsmodel
    return standardsmodel.register_toml()


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


def errors():
    lines = ['spec = "prismpm/errors/1"', ""]
    for e in ERRORS:
        lines += ["[[error]]", f"code = {_q(e['code'])}", f"title = {_q(e['title'])}", f"class = {_q(e['class'])}",
                  f"exit = {e['exit']}", f"statement = {_q(e['statement'])}", "commands = " + _list(e["commands"]), ""]
    return "\n".join(lines)


STDLIB = {
    "name": "prism-stdlib", "version": "0.2.0",
    "description": "Generated portable Prism application and production-system runtime; the Foundation.Arch and Foundation.Qual modules and the prism.arch and prism.qual lexicons are vendored here",
    "repository": "https://github.com/UOR-Foundation/PrismPM", "homepage": "https://github.com/UOR-Foundation/PrismPM",
    "license": "MIT OR Apache-2.0", "language": "1.2",
    "modules": ["Foundation.Arch", "Foundation.Qual"], "lexicons": ["prism.arch@1.0.0", "prism.qual@1.0.0"],
    "vendored_at": ["rule30-api/stdlib", "rule30-api/language"],
}


def stdlib_package():
    lines = ['spec = "prismpm/stdlib-package/1"']
    for k in ("name", "version", "description", "repository", "homepage", "license", "language"):
        lines.append(f"{k} = {_q(STDLIB[k])}")
    for k in ("modules", "lexicons", "vendored_at"):
        lines.append(f"{k} = " + _list(STDLIB[k]))
    return "\n".join(lines) + "\n"


def tree_sha256(root):
    """SHA-256 over the sorted relative paths and contents of a tree."""
    h = hashlib.sha256()
    for p in sorted(x for x in root.rglob("*") if x.is_file()):
        h.update(str(p.relative_to(root)).encode() + b"\0" + hashlib.sha256(p.read_bytes()).hexdigest().encode() + b"\n")
    return h.hexdigest()


def dependencies():
    """The pinned toolchain and the vendored sources, with the digests
    `lexlean.lock` records for the lexicon packages."""
    from .production import LEXLEAN_VERSION
    lock = tomllib.loads((API / "lexlean.lock").read_text())
    project = tomllib.loads((API / "lexlean.toml").read_text())
    packages = {p["id"]: p for p in lock["package"]}
    lines = ['spec = "prismpm/dependencies/1"', "",
             "[[dependency]]", 'id = "lexlean"', f"version = {_q(LEXLEAN_VERSION)}", f"language = {_q(lock['language'])}",
             f"revision = {_q(lock['compiler_semantics'])}", 'source = "pinned-binary"', 'role = "compiler"',
             'path = ".local/bin/lexlean"', "",
             "[[dependency]]", 'id = "lean4"', f"version = {_q(project['lean_toolchain'])}", 'source = "elan"',
             'role = "kernel"', ""]
    for pid in ("lexlean.core", "lexlean.std.bool", "lexlean.std.nat"):
        p = packages[pid]
        lines += ["[[dependency]]", f"id = {_q(pid)}", f"version = {_q(p['version'])}", 'source = "embedded"',
                  'role = "lexicon"', f"tree_sha256 = {_q(p['tree_sha256'])}", ""]
    lines += ["[[dependency]]", 'id = "prism-stdlib"', f"version = {_q(STDLIB['version'])}", 'source = "vendored"',
              'role = "stdlib"', f"repository = {_q(STDLIB['repository'])}", ""]
    for pid in ("prism.arch", "prism.qual"):
        p = packages[pid]
        lines += ["[[dependency.artifact]]", 'kind = "tree-manifest"', f"path = {_q('rule30-api/' + p['source'])}",
                  f"sha256 = {_q(p['tree_sha256'])}", 'recorded_by = "lexlean.lock"', ""]
    lines += ["[[dependency.artifact]]", 'kind = "tree-manifest"', 'path = "rule30-api/stdlib/Foundation"',
              f"sha256 = {_q(tree_sha256(API / 'stdlib' / 'Foundation'))}", 'recorded_by = "bin/r30 api sync"', "",
              "[[dependency]]", 'id = "python"', 'version = "3"', 'source = "host"', 'role = "interim-runtime"',
              'statement = "The standard library only: tools/r30 is subprocess calls and file I/O around the LexLean modules."', ""]
    return "\n".join(lines)


def all_ids(claims):
    """Every row of ids.toml with its ledger evidence, by suite."""
    by_id = {}
    for c in claims:
        evidence = (f"frontier check: {c['lean']} kernel-checked under propext and Quot.sound and published"
                    if c["status"] == "proved" else f"register: {c['status']}" + (f" ({c['lean']})" if c.get("lean") else ""))
        by_id[c["id"]] = {"id": c["id"], "level": LEVEL[c["status"]], "suite": "register", "statement": c["statement"],
                          "evidence": evidence, "lean": c.get("lean"), "status": c["status"]}
    for x in API_IDS:
        by_id[x["id"]] = {**x, "status": None, "lean": None}
    return by_id


STEPS = {
    # one scenario shape per honesty level (R2): what the suite does with the id
    "some-true": ("Given the register entry {id} and the refutation it names ({source})",
                  "When the suite reproduces {id}",
                  "Then the route is reported refuted from its authority and nothing is established here"),
    "build": ("Given {source}",
              "When the suite exercises {id}",
              "Then its oracle accepts it: {evidence}"),
    "open": ("Given the register entry {id} ({source})",
             "When the suite measures {id}",
             "Then the claim is reported open and never asserted"),
}


def features(claims):
    """{suite: Gherkin text}: one scenario per id, tagged with the id and its level."""
    ids_ = all_ids(claims)
    suites = {}
    for row in ids_.values():
        suites.setdefault(row["suite"], []).append(row)
    about = {"register": "The claims of frontier.toml: the kernel is the judge of every proved one.",
             "api": "The LexLean API modules, the PrismPM model and the stakeholder view.",
             "discovery": "Induction mechanized: the basis of the map, the relation and recurrence engines, their certified roots, bin/r30 discover and the observed status."}
    out = {}
    for suite, rws in suites.items():
        lines = [f"Feature: {suite}", "", f"  {about[suite]}", ""]
        for r in rws:
            source = r["feature"] if "feature" in r else (r["lean"] or "experiment")
            if r["level"] == "build" and r.get("lean"):
                source = f"frontier.toml names {r['lean']} for {r['id']}"
            g, w, t = (s.format(id=r["id"], source=source, evidence=r["evidence"]) for s in STEPS[r["level"]])
            lines += [f"  @{r['id']} @{r['level']}", f"  Scenario: {r['statement']}", f"    {g}", f"    {w}", f"    {t}", ""]
        out[suite] = "\n".join(lines)
    return out


def conformance(claims):
    ids_ = all_ids(claims)
    lines = ["<!-- @generated by `bin/r30 api sync` from model/ids.toml, authorities.toml and ledger.toml. -->",
             "<!-- Do not edit. R1: the model is the single source. -->", "", "# CONFORMANCE", "",
             "The conformance ID register of `rule30-api`. Every id has exactly one scenario in",
             "`features/suites/<suite>.feature`, tagged with the id and its level, and the evidence",
             "`model/ledger.toml` names; `bin/r30 api check` refuses drift between them.", "",
             "The three honesty levels (R2):", "", "| Level | Meaning |", "| --- | --- |",
             "| `some-true` | A fact reproduced from an authority (here: a refuted route, from its Lean refutation or experiment). **Not established here.** |",
             "| `build` | Constructed here and validated against its oracle (the Lean kernel, `lexlean verify`, `api check`). Evidence, not a proof. |",
             "| `open` | Measured and reported. **Never asserted.** |", "",
             "## Cited authorities", "", "Never re-derived, vendored as sources, or gated on.", "",
             "| Authority | Citation | Realized by |", "| --- | --- | --- |"]
    for a in AUTHORITIES:
        lines.append(f"| {a['name']} | {a['citation']} | {', '.join('`' + x + '`' for x in a['realized_by'](claims))} |")
    for suite in ("register", "api", "discovery"):
        lines += ["", f"## {suite}", "", "| ID | Level | Statement | Evidence |", "| --- | --- | --- | --- |"]
        for r in ids_.values():
            if r["suite"] == suite:
                lines.append(f"| `{r['id']}` | `{r['level']}` | {r['statement']} | {r['evidence']} |")
    return "\n".join(lines) + "\n"


def files(claims):
    """Every generated file of the model: path -> text."""
    from . import observermodel, production, schema, standardsmodel
    out = {
        MODEL / "authorities.toml": authorities(claims),
        MODEL / "ids.toml": ids(claims),
        MODEL / "ledger.toml": ledger(claims),
        MODEL / "commands.toml": commands(),
        MODEL / "standards.toml": standards(),
        MODEL / "projection.toml": projection(),
        MODEL / "contracts.toml": contracts(),
        MODEL / "errors.toml": errors(),
        MODEL / "dependencies.toml": dependencies(),
        MODEL / "stdlib-package.toml": stdlib_package(),
        MODEL / "observer.toml": observermodel.register_toml(observermodel.data()),
        SCHEMAS / "register.schema.json": json.dumps(REGISTER_SCHEMA, indent=1) + "\n",
        SCHEMAS / "interface-sheet.schema.json": json.dumps(SHEET_SCHEMA, indent=1) + "\n",
        SCHEMAS / "standards.schema.json": json.dumps(standardsmodel.STANDARDS_SCHEMA, indent=1) + "\n",
        API / "prismpm.toml": PRISMPM,
        CONFORMANCE: conformance(claims),
    }
    out.update(production.files())
    out.update(auditmodel.files())
    for name in schema.RESULTS:
        out[SCHEMAS / f"{name}.schema.json"] = json.dumps(schema.document(name), indent=1) + "\n"
    for suite, text in features(claims).items():
        out[FEATURES / f"{suite}.feature"] = text
    return out


REGISTERS = 12  # the model/*.toml files `files` writes


def sync():
    claims = rows()
    changed = False
    for path, text in files(claims).items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
            changed = True
    return {"model": str(MODEL.relative_to(repo.ROOT)), "claims": len(claims), "registers": REGISTERS, "changed": changed}


def check():
    claims = rows()
    generated = files(claims)
    for path, text in generated.items():
        if not path.exists() or path.read_text() != text:
            return {"ok": False, "reason": f"{path.relative_to(repo.ROOT)} drifted from its sources; run `bin/r30 api sync`"}
    stray = [p for p in FEATURES.glob("*.feature") if p not in generated]
    if stray:
        return {"ok": False, "reason": f"feature files without a suite in ids.toml: {', '.join(p.name for p in stray)}"}
    from . import apimodel
    surface = {r["name"] for r in apimodel.surface()}
    missing = [r["name"] for r in apimodel.surface() if r["name"] not in MUTATES and _mutating(r)]
    if missing:
        return {"ok": False, "reason": f"commands without a mutation class in prismmodel.MUTATES: {', '.join(missing)}"}
    unknown = sorted({c for e in ERRORS for c in e["commands"]} - surface - {c.replace("-", "_") for c in surface})
    if unknown:
        return {"ok": False, "reason": f"errors.toml names commands the parser does not have: {', '.join(unknown)}"}
    for sid, st in STANDARD_FACETS.items():
        facet = API / "language" / st["package"] / "entries"
        absent = [e for e in st["entries"] if not (facet / f"{e}.toml").exists()]
        if absent:
            return {"ok": False, "reason": f"{sid} names lexicon entries absent from rule30-api/language: {', '.join(absent)}"}
    return {"ok": True, "reason": None}


def _mutating(row):
    """A command with a `--write`-like flag or a sub-verb that is not a query
    must declare what it mutates."""
    verbs = {"add", "set", "remove", "sync", "render", "build", "run", "commit", "write"}
    return bool(set(row["path"]) & verbs) or any(a["name"] == "write" for a in row["arguments"])
