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

from . import repo, semantic

API = repo.ROOT / "rule30-api"
MODULE = API / "src" / "Api.lex.tex"

# The production roots of the module (SPEC §17.13): the executable definitions
# `lexlean production` exports to certified Rust. Strings and lists live on
# the heap, so the roots require `allocation` and only `rust-std` realizes
# them; nothing here overflows or recurses. `production.py` builds the
# request and the runtime-roots register from this table.
PRODUCTION_ROOTS = {
    "commands": {"effects": ["allocation"], "targets": ["rust-std"]},
    "commandCount": {"effects": ["allocation"], "targets": ["rust-std"]},
}



def _string(v):
    return {"kind": "string", "value": v}


def _bool(v):
    return {"kind": "bool", "value": bool(v)}


def _list(elements, element_type):
    return semantic.lst(elements, element_type)


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
         "axioms": [], "body": _list([cmd_record(c) for c in rows], cmd_t),
         "executable": True, "production": PRODUCTION_ROOTS["commands"]},
        {"kind": "definition", "name": "commandCount", "parameters": [], "result": {"kind": "nat"}, "axioms": [],
         "body": {"kind": "primitive", "operation": "length", "result": {"kind": "nat"},
                  "arguments": [{"kind": "call", "function": {"name": "commands"}, "arguments": []}]},
         "executable": True, "production": PRODUCTION_ROOTS["commandCount"]},
        {"kind": "theorem", "name": "commandCountIs", "parameters": [], "axioms": [],
         "statement": {"kind": "eq", "left": {"kind": "call", "function": {"name": "commandCount"}, "arguments": []},
                       "right": {"kind": "nat", "value": str(len(rows))}},
         "proof": {"kind": "reflexivity"}},
    ]


def render(rows):
    from . import lexmod
    return lexmod.module("Api", declarations(rows))


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
