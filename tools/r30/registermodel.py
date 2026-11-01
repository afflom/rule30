"""The register as a LexLean semantic module.

`rule30-api/src/Register.lex.tex` declares the claims of `frontier.toml` as
data (`Claim` records: id, status, Lean name, depends) together with decidable
well-formedness functions and theorems the kernel checks: every `depends`
target is a claim id, and every proved claim names a Lean theorem. The gate
still confirms the Lean names against the kernel (`frontier check`); the
module makes the plan itself a checked object, written in LexLean."""

from . import frontier, repo, semantic

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Register.lex.tex"


STR = {"kind": "string"}
BOOL = {"kind": "bool"}


def _s(v):
    return {"kind": "string", "value": v}


def _b(v):
    return {"kind": "bool", "value": bool(v)}


def _var(n):
    return {"kind": "var", "name": n}


def _call(f, *args):
    return {"kind": "call", "function": {"name": f}, "arguments": list(args)}


def _list(elements, element_type):
    return semantic.lst(elements, element_type)


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


def _and(a, b):
    return _if(a, b, _b(False))


def rows():
    return [{"id": c["id"], "status": c["status"], "lean": c.get("lean") or "", "depends": c.get("depends", []),
             "relation": c.get("relation", []), "kappa": c.get("kappa") or ""}
            for c in frontier.load()["claim"]]


def declarations(claims):
    claim_t = _named("Claim")
    rec = lambda c: {"kind": "record", "type": {"name": "Claim"}, "fields": [
        {"field": "id", "value": _s(c["id"])}, {"field": "status", "value": _s(c["status"])},
        {"field": "lean", "value": _s(c["lean"])},
        {"field": "depends", "value": _list([_s(d) for d in c["depends"]], STR)},
        {"field": "relation", "value": _list([_s(d) for d in c.get("relation", [])], STR)},
        {"field": "kappa", "value": _s(c.get("kappa", ""))}]}
    proj = lambda v, f: {"kind": "project", "value": v, "field": f}
    length = lambda x: {"kind": "primitive", "operation": "length", "result": {"kind": "nat"}, "arguments": [x]}
    return [
        {"kind": "structure", "name": "Claim", "parameters": [], "type_parameters": [], "fields": [
            {"name": "id", "type": STR}, {"name": "status", "type": STR}, {"name": "lean", "type": STR},
            {"name": "depends", "type": _list_t(STR)}, {"name": "relation", "type": _list_t(STR)},
            {"name": "kappa", "type": STR}]},
        {"kind": "definition", "name": "claims", "parameters": [], "result": _list_t(claim_t), "axioms": [],
         "body": _list([rec(c) for c in claims], claim_t)},
        {"kind": "definition", "name": "memberString", "axioms": [], "result": BOOL, "recursive_argument": "values",
         "parameters": [{"name": "value", "type": STR}, {"name": "values", "type": _list_t(STR)}],
         "body": _match_list(_var("values"), _b(False), "head", "tail",
                             _if(_eq(_var("value"), _var("head")), _b(True), _call("memberString", _var("value"), _var("tail"))))},
        {"kind": "definition", "name": "allMembers", "axioms": [], "result": BOOL, "recursive_argument": "values",
         "parameters": [{"name": "values", "type": _list_t(STR)}, {"name": "ids", "type": _list_t(STR)}],
         "body": _match_list(_var("values"), _b(True), "head", "tail",
                             _and(_call("memberString", _var("head"), _var("ids")), _call("allMembers", _var("tail"), _var("ids"))))},
        {"kind": "definition", "name": "idsOf", "axioms": [], "result": _list_t(STR), "recursive_argument": "cs",
         "parameters": [{"name": "cs", "type": _list_t(claim_t)}],
         "body": _match_list(_var("cs"), {"kind": "nil", "element": STR}, "head", "tail",
                             {"kind": "cons", "head": proj(_var("head"), "id"), "tail": _call("idsOf", _var("tail"))})},
        {"kind": "definition", "name": "dependsResolve", "axioms": [], "result": BOOL, "recursive_argument": "cs",
         "parameters": [{"name": "cs", "type": _list_t(claim_t)}, {"name": "ids", "type": _list_t(STR)}],
         "body": _match_list(_var("cs"), _b(True), "head", "tail",
                             _and(_call("allMembers", proj(_var("head"), "depends"), _var("ids")),
                                  _call("dependsResolve", _var("tail"), _var("ids"))))},
        {"kind": "definition", "name": "provedHaveLean", "axioms": [], "result": BOOL, "recursive_argument": "cs",
         "parameters": [{"name": "cs", "type": _list_t(claim_t)}],
         "body": _match_list(_var("cs"), _b(True), "head", "tail",
                             _and(_if(_eq(proj(_var("head"), "status"), _s("proved")),
                                      _if(_eq(proj(_var("head"), "lean"), _s("")), _b(False), _b(True)), _b(True)),
                                  _call("provedHaveLean", _var("tail"))))},
        # an observed claim (a relation certified on a window by `bin/r30
        # discover`) carries its relation and its κ-label; Discovery.lex.tex
        # decides that every relation of the register vanishes on its window
        {"kind": "definition", "name": "observedHaveRelations", "axioms": [], "result": BOOL, "recursive_argument": "cs",
         "parameters": [{"name": "cs", "type": _list_t(claim_t)}],
         "body": _match_list(_var("cs"), _b(True), "head", "tail",
                             _and(_if(_eq(proj(_var("head"), "status"), _s("observed")),
                                      _if({"kind": "beq", "left": length(proj(_var("head"), "relation")), "right": {"kind": "nat", "value": 0}},
                                          _b(False), _if(_eq(proj(_var("head"), "kappa"), _s("")), _b(False), _b(True))),
                                      _b(True)),
                                  _call("observedHaveRelations", _var("tail"))))},
        {"kind": "theorem", "name": "registerObservedHaveRelations", "parameters": [], "axioms": [],
         "statement": {"kind": "eq", "left": _call("observedHaveRelations", _call("claims")), "right": _b(True)},
         "proof": {"kind": "decide"}},
        {"kind": "theorem", "name": "registerDependsResolve", "parameters": [], "axioms": [],
         "statement": {"kind": "eq", "left": _call("dependsResolve", _call("claims"), _call("idsOf", _call("claims"))),
                       "right": _b(True)}, "proof": {"kind": "decide"}},
        {"kind": "theorem", "name": "registerProvedHaveLean", "parameters": [], "axioms": [],
         "statement": {"kind": "eq", "left": _call("provedHaveLean", _call("claims")), "right": _b(True)},
         "proof": {"kind": "decide"}},
    ]


def data_form(claims=None):
    import json
    data = {"spec": "lexlean/semantic-module/1", "declarations": declarations(claims if claims is not None else rows())}
    return json.dumps(data, separators=(",", ":"), sort_keys=True)


def render(claims=None):
    from . import lexmod
    return lexmod.module("Register", declarations(claims if claims is not None else rows()))


def sync():
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    text = render()
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "claims": len(rows()), "changed": changed}


def check():
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Register.lex.tex is missing; run `bin/r30 api sync`"}
    ok = MODULE.read_text() == render()
    return {"ok": ok, "reason": None if ok else "the register drifted from Register.lex.tex; run `bin/r30 api sync`"}
