"""The PrismPM project model of the API, generated from the register.

`rule30-api/model/{authorities,ids,ledger}.toml` follow the `template/1`
registers of UOR-Foundation/template and PrismPM: authorities are the
conceptual model and the sources the project realizes (the Rule 30 Prize,
Problem 1; LexLean and PrismPM as the observer facets of the proof), ids are
the register's claims as capabilities with a level, and the ledger maps each
claim to its evidence. `prismpm.toml` binds the LexLean project. No PrismPM
toolchain runs here: the gate is the pre-commit hook, and CI only renders;
the model is kept so that a pinned PrismPM can build the generated runtime
and publish to the stakeholders without any change to the sources."""

from . import frontier, repo

API = repo.ROOT / "rule30-api"
MODEL = API / "model"

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
     "statement": "Model registers (authorities, ids, ledger) and the generated runtime of LexLean application models.",
     "realized_by": lambda claims: ["api-modules"]},
]


def _q(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def rows():
    return frontier.load()["claim"]


def authorities(claims):
    lines = ['spec = "template/1"', ""]
    for a in AUTHORITIES:
        lines += ["[[authority]]", f"id = {_q(a['id'])}", f"name = {_q(a['name'])}", f"citation = {_q(a['citation'])}",
                  f"statement = {_q(a['statement'])}",
                  "realized_by = [" + ", ".join(_q(x) for x in a["realized_by"](claims)) + "]", ""]
    return "\n".join(lines)


def ids(claims):
    lines = ['spec = "template/1"', ""]
    for c in claims:
        lines += ["[[id]]", f"id = {_q(c['id'])}", f"level = {_q(LEVEL[c['status']])}", 'suite = "register"',
                  f"statement = {_q(c['statement'])}", ""]
    lines += ["[[id]]", 'id = "api-modules"', 'level = "build"', 'suite = "api"',
              'statement = "The command surface, the register and the architecture are LexLean semantic modules verified by the gate."', ""]
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
    lines += ["[[claim]]", 'id = "api-modules"', 'level = "build"',
              'statement = "The command surface, the register and the architecture are LexLean semantic modules verified by the gate."',
              'feature = "rule30-api/src"', 'evidence = "lexlean verify rule30-api (scripts/verify_lexlean.sh); bin/r30 api check"', ""]
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


def sync():
    MODEL.mkdir(parents=True, exist_ok=True)
    claims = rows()
    changed = False
    for name, text in (("authorities.toml", authorities(claims)), ("ids.toml", ids(claims)),
                       ("ledger.toml", ledger(claims))):
        path = MODEL / name
        if not path.exists() or path.read_text() != text:
            path.write_text(text)
            changed = True
    toml = API / "prismpm.toml"
    if not toml.exists() or toml.read_text() != PRISMPM:
        toml.write_text(PRISMPM)
        changed = True
    return {"model": str(MODEL.relative_to(repo.ROOT)), "claims": len(claims), "changed": changed}


def check():
    claims = rows()
    for name, text in (("authorities.toml", authorities(claims)), ("ids.toml", ids(claims)),
                       ("ledger.toml", ledger(claims))):
        path = MODEL / name
        if not path.exists() or path.read_text() != text:
            return {"ok": False, "reason": f"rule30-api/model/{name} drifted from the register; run `bin/r30 api sync`"}
    return {"ok": True, "reason": None}
