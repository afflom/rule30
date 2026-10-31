"""The architecture description as a LexLean semantic module.

`rule30-api/src/Architecture.lex.tex` declares, as data with decided
theorems, the conceptual model (the Rule 30 Prize, Problem 1), the
stakeholders of the effort and their concerns, and the views that address
each concern (the reduction tree, the register, the API modules, the current
view published on every push). The form follows ISO/IEC 42010 as PrismPM's
`prism.arch` lexicon models it (stakeholders, concerns, viewpoints, views);
the module is self-contained so that it needs no pinned SDK, and it is
checked by the same `lexlean verify` as the paper."""

from . import repo

MODULE = repo.ROOT / "rule30-api" / "src" / "Architecture.lex.tex"

STR = {"kind": "string"}
BOOL = {"kind": "bool"}

CONCEPTUAL_MODEL = {
    "id": "rule30-problem-1",
    "statement": "Wolfram's Rule 30 Prize, Problem 1: the center column of Rule 30 from a single black cell is not eventually periodic.",
    "citation": "https://www.rule30prize.org",
}

STAKEHOLDERS = [
    {"id": "wolfram", "name": "Stephen Wolfram and the Rule 30 Prize committee",
     "concerns": ["closure", "evidence"]},
    {"id": "researcher", "name": "The researcher driving the proof",
     "concerns": ["closure", "optimal-implementation", "comprehension"]},
    {"id": "community", "name": "The community and industry reading and reusing the work",
     "concerns": ["evidence", "comprehension", "current-view"]},
    {"id": "uor-foundation", "name": "The UOR Foundation (LexLean and prism-stdlib improve through this research)",
     "concerns": ["stdlib", "optimal-implementation", "current-view"]},
]

CONCERNS = [
    {"id": "closure", "statement": "Problem 1 is closed by a kernel-checked chain of reductions."},
    {"id": "evidence", "statement": "Every claim is backed by kernel evidence; nothing unproved is called proved."},
    {"id": "optimal-implementation", "statement": "The implementation stays optimal: validation runs once, in the gate, and never impedes the research."},
    {"id": "comprehension", "statement": "The features of the problem and of the solution are labeled and readable from the register."},
    {"id": "current-view", "statement": "Each push publishes the current state of the implementation."},
    {"id": "stdlib", "statement": "What the research needs from LexLean and prism-stdlib is identified and fed back."},
]

VIEWS = [
    {"id": "reduction-tree", "concern": "closure", "command": "chain",
     "statement": "The register as one DAG from problem1 to the open leaves, every arrow a theorem."},
    {"id": "register-evidence", "concern": "evidence", "command": "frontier_check",
     "statement": "frontier check: proved claims kernel-checked under propext and Quot.sound and published; Register.lex.tex decided."},
    {"id": "gate", "concern": "optimal-implementation", "command": "commit",
     "statement": "One validate-and-commit step with cached Lake directories and reused LexLean attestations; CI renders, it does not re-validate."},
    {"id": "interface-sheets", "concern": "comprehension", "command": "interface",
     "statement": "The labeled interface sheet of every claim: chain, notions, exact facts, handles."},
    {"id": "published-view", "concern": "current-view", "command": "chain",
     "statement": "The view workflow uploads the tree, the register, the sheets and the API modules on every push to main."},
    {"id": "api-modules", "concern": "stdlib", "command": "api_sync",
     "statement": "The command surface, the register and this architecture are LexLean semantic modules; what they needed from the language is recorded in AGENTS.md."},
]


def _s(v):
    return {"kind": "string", "value": v}


def _b(v):
    return {"kind": "bool", "value": bool(v)}


def _var(n):
    return {"kind": "var", "name": n}


def _call(f, *args):
    return {"kind": "call", "function": {"name": f}, "arguments": list(args)}


def _list(elements, element_type):
    node = {"kind": "nil", "element": element_type}
    for e in reversed(elements):
        node = {"kind": "cons", "head": e, "tail": node}
    return node


def _named(name):
    return {"kind": "named", "member": {"name": name}, "arguments": []}


def _list_t(t):
    return {"kind": "list", "element": t}


def _eq(a, b):
    return {"kind": "primitive", "operation": "equal", "result": BOOL, "arguments": [a, b]}


def _if(c, t, e):
    return {"kind": "if", "condition": c, "then_value": t, "else_value": e}


def _match_list(scrutinee, nil_body, head, tail, cons_body):
    return {"kind": "match", "scrutinee": scrutinee, "branches": [
        {"constructor": {"name": "List.nil"}, "binders": [], "body": nil_body},
        {"constructor": {"name": "List.cons"}, "binders": [head, tail], "body": cons_body}]}


def _proj(v, f):
    return {"kind": "project", "value": v, "field": f}


def _record(type_name, **fields):
    return {"kind": "record", "type": {"name": type_name},
            "fields": [{"field": k, "value": v} for k, v in fields.items()]}


def _structure(name, fields):
    return {"kind": "structure", "name": name, "parameters": [], "type_parameters": [],
            "fields": [{"name": n, "type": t} for n, t in fields]}


def _definition(name, result, body, parameters=(), recursive=None):
    d = {"kind": "definition", "name": name, "parameters": [{"name": n, "type": t} for n, t in parameters],
         "result": result, "axioms": [], "body": body}
    if recursive:
        d["recursive_argument"] = recursive
    return d


def _theorem(name, left, right, proof="decide"):
    return {"kind": "theorem", "name": name, "parameters": [], "axioms": [],
            "statement": {"kind": "eq", "left": left, "right": right}, "proof": {"kind": proof}}


def declarations():
    sh_t, co_t, vw_t, cm_t = _named("Stakeholder"), _named("Concern"), _named("View"), _named("ConceptualModel")
    return [
        _structure("ConceptualModel", [("id", STR), ("statement", STR), ("citation", STR)]),
        _structure("Stakeholder", [("id", STR), ("name", STR), ("concerns", _list_t(STR))]),
        _structure("Concern", [("id", STR), ("statement", STR)]),
        _structure("View", [("id", STR), ("concern", STR), ("command", STR), ("statement", STR)]),
        _definition("conceptualModel", cm_t, _record("ConceptualModel", **{k: _s(v) for k, v in CONCEPTUAL_MODEL.items()})),
        _definition("stakeholders", _list_t(sh_t), _list([
            _record("Stakeholder", id=_s(s["id"]), name=_s(s["name"]), concerns=_list([_s(c) for c in s["concerns"]], STR))
            for s in STAKEHOLDERS], sh_t)),
        _definition("concerns", _list_t(co_t), _list([
            _record("Concern", id=_s(c["id"]), statement=_s(c["statement"])) for c in CONCERNS], co_t)),
        _definition("views", _list_t(vw_t), _list([
            _record("View", id=_s(v["id"]), concern=_s(v["concern"]), command=_s(v["command"]), statement=_s(v["statement"]))
            for v in VIEWS], vw_t)),
        _definition("memberString", BOOL,
                    _match_list(_var("values"), _b(False), "head", "tail",
                                _if(_eq(_var("value"), _var("head")), _b(True), _call("memberString", _var("value"), _var("tail")))),
                    parameters=[("value", STR), ("values", _list_t(STR))], recursive="values"),
        _definition("concernIds", _list_t(STR),
                    _match_list(_var("cs"), {"kind": "nil", "element": STR}, "head", "tail",
                                {"kind": "cons", "head": _proj(_var("head"), "id"), "tail": _call("concernIds", _var("tail"))}),
                    parameters=[("cs", _list_t(co_t))], recursive="cs"),
        _definition("viewConcerns", _list_t(STR),
                    _match_list(_var("vs"), {"kind": "nil", "element": STR}, "head", "tail",
                                {"kind": "cons", "head": _proj(_var("head"), "concern"), "tail": _call("viewConcerns", _var("tail"))}),
                    parameters=[("vs", _list_t(vw_t))], recursive="vs"),
        _definition("allMembers", BOOL,
                    _match_list(_var("values"), _b(True), "head", "tail",
                                _if(_call("memberString", _var("head"), _var("ids")), _call("allMembers", _var("tail"), _var("ids")), _b(False))),
                    parameters=[("values", _list_t(STR)), ("ids", _list_t(STR))], recursive="values"),
        _definition("stakeholderConcernsExist", BOOL,
                    _match_list(_var("ss"), _b(True), "head", "tail",
                                _if(_call("allMembers", _proj(_var("head"), "concerns"), _var("ids")),
                                    _call("stakeholderConcernsExist", _var("tail"), _var("ids")), _b(False))),
                    parameters=[("ss", _list_t(sh_t)), ("ids", _list_t(STR))], recursive="ss"),
        # every concern of every stakeholder is a declared concern
        _theorem("stakeholderConcernsDeclared",
                 _call("stakeholderConcernsExist", _call("stakeholders"), _call("concernIds", _call("concerns"))), _b(True)),
        # every declared concern is addressed by some view
        _theorem("everyConcernAddressed",
                 _call("allMembers", _call("concernIds", _call("concerns")), _call("viewConcerns", _call("views"))), _b(True)),
        # every view addresses a declared concern
        _theorem("everyViewHasConcern",
                 _call("allMembers", _call("viewConcerns", _call("views")), _call("concernIds", _call("concerns"))), _b(True)),
    ]


def render():
    from . import lexmod
    return lexmod.module("Architecture", declarations())


def sync():
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    text = render()
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "stakeholders": len(STAKEHOLDERS), "changed": changed}


def check():
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Architecture.lex.tex is missing; run `bin/r30 api sync`"}
    ok = MODULE.read_text() == render()
    return {"ok": ok, "reason": None if ok else "Architecture.lex.tex drifted; run `bin/r30 api sync`"}
