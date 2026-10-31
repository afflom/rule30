"""A minimal MCP server (stdio, JSON-RPC 2.0) exposing the `r30` commands as tools.

Register with a client, for example Claude Code:
    claude mcp add r30 -- python3 /path/to/rule30-uor-work/tools/r30/mcp_server.py

The server has no dependencies beyond the standard library. It implements the
methods a tool-only server needs: `initialize`, `ping`, `tools/list` and
`tools/call`. Long operations (`verify`, `commit`) return a log path and the
client polls `tail_log`.
"""

import io
import json
import sys
from contextlib import redirect_stdout

from . import cli, repo

PROTOCOL = "2025-06-18"

import argparse

TAIL_LOG = {"name": "tail_log", "description": "Last lines of a log file under .r30/.",
            "inputSchema": {"type": "object", "properties": {"path": {"type": "string"}, "lines": {"type": "integer"}}}}


def _leaves(parser, path=(), help_text=None):
    """Every leaf subcommand of the CLI parser as (path, parser, help)."""
    subs = [a for a in parser._actions if isinstance(a, argparse._SubParsersAction)]
    if not subs:
        yield path, parser, help_text
        return
    helps = {c.dest: c.help for c in subs[0]._choices_actions}
    for name, sub in subs[0].choices.items():
        yield from _leaves(sub, path + (name,), helps.get(name) or help_text)


def _arguments(parser):
    """The positional and optional arguments of a leaf, in declaration order."""
    return [a for a in parser._actions
            if not isinstance(a, (argparse._HelpAction, argparse._SubParsersAction))]


def _schema(action):
    if isinstance(action, argparse._StoreTrueAction):
        t = {"type": "boolean"}
    elif action.nargs in ("+", "*"):
        t = {"type": "array", "items": {"type": "string"}}
    elif action.type is int:
        t = {"type": "integer"}
    else:
        t = {"type": "string"}
    if action.help:
        t["description"] = action.help
    return t


def _tool_name(path):
    return "_".join(path).replace("-", "_")


def tools():
    """{tool name: (path, parser)} derived from the CLI; discovery is automatic."""
    return {_tool_name(path): (path, parser, help_text) for path, parser, help_text in _leaves(cli.build_parser())}


def tool_list():
    rows = []
    for name, (path, parser, help_text) in tools().items():
        props = {a.dest: _schema(a) for a in _arguments(parser)}
        desc = help_text or parser.description or ("r30 " + " ".join(path))
        rows.append({"name": name, "description": desc, "inputSchema": {"type": "object", "properties": props}})
    rows.append(TAIL_LOG)
    return rows


def argv_for(name, a):
    """Rebuild the CLI argv of a tool call from the parser's own argument list."""
    path, parser, _ = tools()[name]
    argv = list(path)
    for action in _arguments(parser):
        value = a.get(action.dest)
        if not action.option_strings:  # positional
            if action.nargs in ("+", "*"):
                argv += [str(v) for v in (value or [])]
            elif value is not None:
                argv.append(str(value))
        elif isinstance(action, argparse._StoreTrueAction):
            if value:
                argv.append(action.option_strings[0])
        elif action.nargs in ("+", "*"):
            if value:
                argv += [action.option_strings[0], *[str(v) for v in value]]
        elif value is not None:
            argv += [action.option_strings[0], str(value)]
    return argv


def call(name, a):
    if name == "tail_log":
        path = repo.ROOT / a.get("path", "")
        if repo.SCRATCH not in path.resolve().parents:
            return "refused: log path must be under .r30/", True
        lines = path.read_text().splitlines()[-int(a.get("lines", 20)):]
        return "\n".join(lines), False
    buf = io.StringIO()
    failed = False
    try:
        with redirect_stdout(buf):
            cli.main(argv_for(name, a))
    except SystemExit as e:
        if e.code not in (0, None):
            failed = True
            if isinstance(e.code, str):
                buf.write(e.code)
    except Exception as e:  # report, never crash the server
        failed = True
        buf.write(f"error: {e}")
    return buf.getvalue().strip(), failed


def serve(stdin=sys.stdin, stdout=sys.stdout):
    for line in stdin:
        line = line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except json.JSONDecodeError:
            continue
        rid, method, params = req.get("id"), req.get("method"), req.get("params") or {}
        if method == "initialize":
            result = {"protocolVersion": PROTOCOL, "capabilities": {"tools": {}},
                      "serverInfo": {"name": "r30", "version": "0.1.0"}}
        elif method == "ping":
            result = {}
        elif method == "tools/list":
            result = {"tools": tool_list()}
        elif method == "tools/call":
            text, failed = call(params.get("name"), params.get("arguments") or {})
            result = {"content": [{"type": "text", "text": text}], "isError": failed}
        elif rid is None:
            continue  # notification
        else:
            stdout.write(json.dumps({"jsonrpc": "2.0", "id": rid,
                                     "error": {"code": -32601, "message": f"unknown method {method}"}}) + "\n")
            stdout.flush()
            continue
        if rid is not None:
            stdout.write(json.dumps({"jsonrpc": "2.0", "id": rid, "result": result}) + "\n")
            stdout.flush()


if __name__ == "__main__":
    serve()
