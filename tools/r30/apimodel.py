"""The API as a LexLean semantic module.

`rule30-api/src/Api.lex.tex` declares the command surface of `r30` as data
(structures `Argument` and `Command`, the list `commands`) with kernel-checked
properties, in LexLean's semantic-module form (`lexlean/semantic-module/1`),
from which LexLean emits Lean (and, under PrismPM, Rust). `sync` regenerates
the module from the CLI parser; `check` refuses a parser that drifted from the
module. The module is the published description of the API; the CLI and the MCP
tools are its runtime."""

import argparse
import json
from pathlib import Path

from . import repo

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Api.lex.tex"

HEADER = ("\\begin{lexlean}{Api}\n\\useglossary{lexlean.std.bool@1.2.0}\n"
          "\\useglossary{lexlean.std.nat@1.2.0}\n\\title{Boolean}\n\\begin{semanticmodule}")
FOOTER = "\\end{semanticmodule}\n\\end{lexlean}\n"


def _string(v):
    return {"kind": "string", "value": v}


def _bool(v):
    return {"kind": "bool", "value": bool(v)}


def _list(elements, element_type):
    node = {"kind": "nil", "element": element_type}
    for e in reversed(elements):
        node = {"kind": "cons", "head": e, "tail": node}
    return node


def _named(name):
    return {"kind": "named", "member": {"name": name}, "arguments": []}


def surface():
    """The leaves of the CLI parser as plain data."""
    from . import cli
    from .mcp_server import _leaves, _arguments, _tool_name
    rows = []
    for path, parser, help_text in _leaves(cli.build_parser()):
        args = []
        for a in _arguments(parser):
            if isinstance(a, argparse._StoreTrueAction):
                kind = "flag"
            elif a.type is int:
                kind = "integer"
            else:
                kind = "string"
            args.append({"name": a.dest, "kind": kind, "many": a.nargs in ("+", "*"),
                         "optional": bool(a.option_strings) or a.nargs in ("?", "*"), "help": a.help or ""})
        rows.append({"name": _tool_name(path), "path": list(path), "help": help_text or "", "arguments": args})
    return rows


def declarations(rows):
    arg_t = _named("Argument")
    cmd_t = _named("Command")
    str_t = {"kind": "string"}
    arg_record = lambda a: {"kind": "record", "type": {"name": "Argument"}, "fields": [
        {"field": "name", "value": _string(a["name"])}, {"field": "kind", "value": _string(a["kind"])},
        {"field": "many", "value": _bool(a["many"])}, {"field": "optional", "value": _bool(a["optional"])},
        {"field": "help", "value": _string(a["help"])}]}
    cmd_record = lambda c: {"kind": "record", "type": {"name": "Command"}, "fields": [
        {"field": "name", "value": _string(c["name"])},
        {"field": "path", "value": _list([_string(p) for p in c["path"]], str_t)},
        {"field": "help", "value": _string(c["help"])},
        {"field": "arguments", "value": _list([arg_record(a) for a in c["arguments"]], arg_t)}]}
    return [
        {"kind": "structure", "name": "Argument", "parameters": [], "type_parameters": [], "fields": [
            {"name": "name", "type": str_t}, {"name": "kind", "type": str_t}, {"name": "many", "type": {"kind": "bool"}},
            {"name": "optional", "type": {"kind": "bool"}}, {"name": "help", "type": str_t}]},
        {"kind": "structure", "name": "Command", "parameters": [], "type_parameters": [], "fields": [
            {"name": "name", "type": str_t}, {"name": "path", "type": {"kind": "list", "element": str_t}},
            {"name": "help", "type": str_t}, {"name": "arguments", "type": {"kind": "list", "element": arg_t}}]},
        {"kind": "definition", "name": "commands", "parameters": [], "result": {"kind": "list", "element": cmd_t},
         "axioms": [], "body": _list([cmd_record(c) for c in rows], cmd_t)},
        {"kind": "definition", "name": "commandCount", "parameters": [], "result": {"kind": "nat"}, "axioms": [],
         "body": {"kind": "primitive", "operation": "length", "result": {"kind": "nat"},
                  "arguments": [{"kind": "call", "function": {"name": "commands"}, "arguments": []}]}},
        {"kind": "theorem", "name": "commandCountIs", "parameters": [], "axioms": [],
         "statement": {"kind": "eq", "left": {"kind": "call", "function": {"name": "commandCount"}, "arguments": []},
                       "right": {"kind": "nat", "value": str(len(rows))}},
         "proof": {"kind": "reflexivity"}},
    ]


def _lit(s):
    return json.dumps(s)


def _expr(node):
    """The language-1.2 authoring notation of an expression (SPEC.md §17.21),
    as `lexlean migrate` writes it from the data form."""
    k = node["kind"]
    if k == "string":
        return _lit(node["value"])
    if k == "bool":
        return "true" if node["value"] else "false"
    if k == "nat":
        return node["value"]
    if k == "nil":
        return f"(nil {_type(node['element'])})"
    if k == "cons":
        return f"(cons {_expr(node['head'])} {_expr(node['tail'])})"
    if k == "record":
        fields = ", ".join(f"{f['field']} := {_expr(f['value'])}" for f in node["fields"])
        return f"(record {node['type']['name']} {{{fields}}})"
    if k == "call":
        args = " ".join(_expr(a) for a in node["arguments"])
        return f"({node['function']['name']}{(' ' + args) if args else ''})"
    if k == "primitive":
        args = " ".join(_expr(a) for a in node["arguments"])
        return f"(prim {node['operation']} {args} : {_type(node['result'])})"
    raise ValueError(f"no notation for {k}")


def _type(t):
    k = t["kind"]
    if k == "string":
        return "String"
    if k == "bool":
        return "Bool"
    if k == "nat":
        return "Nat"
    if k == "list":
        return f"(List {_type(t['element'])})"
    if k == "named":
        return t["member"]["name"]
    raise ValueError(f"no notation for type {k}")


def _decl(d):
    k = d["kind"]
    if k == "structure":
        fields = ",\n".join(f"    {{name: {f['name']}, type: {_type(f['type'])}}}" for f in d["fields"])
        return (f"structure{{\n  name: {d['name']},\n  type_parameters: [],\n  parameters: [],\n"
                f"  fields: [\n{fields}\n  ]\n}}")
    if k == "definition":
        return (f"definition{{\n  name: {d['name']},\n  parameters: [],\n  result: {_type(d['result'])},\n"
                f"  body: {_expr(d['body'])},\n  axioms: []\n}}")
    if k == "theorem":
        st = d["statement"]
        return (f"theorem{{\n  name: {d['name']},\n  parameters: [],\n"
                f"  statement: ({_expr(st['left'])} = {_expr(st['right'])}),\n"
                f"  proof: reflexivity{{}},\n  axioms: []\n}}")
    raise ValueError(k)


def render(rows):
    body = "\n\n".join(_decl(d) for d in declarations(rows))
    return HEADER + "\n" + body + "\n" + FOOTER


def sync():
    MODULE.parent.mkdir(parents=True, exist_ok=True)
    text = render(surface())
    changed = not MODULE.exists() or MODULE.read_text() != text
    if changed:
        MODULE.write_text(text)
    return {"module": str(MODULE.relative_to(repo.ROOT)), "commands": len(surface()), "changed": changed}


def check():
    """The module matches the parser exactly."""
    if not MODULE.exists():
        return {"ok": False, "reason": "rule30-api/src/Api.lex.tex is missing; run `bin/r30 api sync`"}
    ok = MODULE.read_text() == render(surface())
    return {"ok": ok, "reason": None if ok else "the CLI drifted from Api.lex.tex; run `bin/r30 api sync`"}
