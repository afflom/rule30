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

TOOLS = [
    ("status", "Repository status: HEAD, dirty files, frontier counts, whether a gate is running.", {}),
    ("brief", "The one-screen session briefing: open claims, proved reductions, refuted routes, the loop.", {}),
    ("claim", "One frontier claim in full: register entry, Lean type, published statement, dependents.", {"id": "string"}),
    ("gate", "Is the pre-commit gate running, its last stage and log tail.", {}),
    ("lexicon_search", "Find lexemes by id, surface or Lean name.",
     {"query": "string", "limit": "integer"}),
    ("lexicon_show", "Show one lexeme (by qualified id or Lean name).", {"id": "string"}),
    ("sig", "Lean types of declarations as s-expressions.", {"names": "array"}),
    ("theorem_preview", "Translate Lean theorems to a LexLean entry and statement without writing.",
     {"names": "array", "lexicon": "string"}),
    ("theorem_add", "Publish Lean theorems on the LexLean surface: entry, statement, check, probe.",
     {"names": "array", "lexicon": "string", "slug": "string", "target": "string"}),
    ("unpublished", "Theorems without a lexeme and whether the converter can publish them.",
     {"prefixes": "array", "lexicon": "string", "only_ok": "boolean"}),
    ("probe", "Elaborate the verify-time probe for declarations (seconds).", {"names": "array", "lexicon": "string"}),
    ("check", "lexlean check. project: paper|core|all; modules: paths like src/Observations.lex.tex (seconds).",
     {"project": "string", "modules": "array"}),
    ("verify", "lexlean verify. With modules: seconds; whole project: minutes.",
     {"project": "string", "modules": "array"}),
    ("axioms", "Axioms of declarations.", {"names": "array"}),
    ("choice_audit", "Theorems under module prefixes that depend on Classical.choice.", {"prefixes": "array"}),
    ("frontier_list", "Claims in frontier.toml.", {"status": "string"}),
    ("frontier_add", "Add a claim.", {"id": "string", "statement": "string", "status": "string",
                                      "lean": "string", "lexeme": "string", "note": "string"}),
    ("frontier_set", "Update a claim.", {"id": "string", "status": "string", "lean": "string",
                                         "lexeme": "string", "note": "string"}),
    ("frontier_check", "Check frontier.toml against the kernel: proved claims are checked and published.", {}),
    ("commit", "Commit through the pre-commit gate in the background; returns a log path.",
     {"message": "string", "push": "boolean", "paths": "array"}),
    ("tail_log", "Last lines of a log file under .r30/.", {"path": "string", "lines": "integer"}),
    ("experiment_run", "Run experiments/<name>.py with arguments.", {"name": "string", "args": "array"}),
]

JSON_TYPES = {"string": {"type": "string"}, "integer": {"type": "integer"},
              "boolean": {"type": "boolean"}, "array": {"type": "array", "items": {"type": "string"}}}


def tool_list():
    return [{"name": n, "description": d,
             "inputSchema": {"type": "object", "properties": {k: JSON_TYPES[v] for k, v in props.items()}}}
            for n, d, props in TOOLS]


def argv_for(name, a):
    g = lambda k, d=None: a.get(k, d)
    names = list(g("names", []) or [])
    if name == "status":
        return ["status"]
    if name == "gate":
        return ["gate"]
    if name == "brief":
        return ["brief"]
    if name == "claim":
        return ["claim", g("id", "")]
    if name == "lexicon_search":
        return ["lexicon", "search", g("query", ""), "--limit", str(g("limit", 40))]
    if name == "lexicon_show":
        return ["lexicon", "show", g("id", "")]
    if name == "sig":
        return ["sig", *names]
    if name in ("theorem_preview", "theorem_add"):
        argv = ["theorem", name.split("_")[1], *names, "--lexicon", g("lexicon", "r30.observation")]
        if g("slug"):
            argv += ["--slug", g("slug")]
        if g("target"):
            argv += ["--target", g("target")]
        return argv
    if name == "unpublished":
        return ["unpublished", *(g("prefixes") or ["Rule30UOR"]), "--lexicon", g("lexicon", "r30.observation")] + \
            (["--only-ok"] if g("only_ok") else [])
    if name == "probe":
        return ["probe", *names, "--lexicon", g("lexicon", "r30.observation")]
    if name == "check":
        return ["check", g("project", "all")] + (["--modules", *g("modules")] if g("modules") else [])
    if name == "verify":
        return ["verify", g("project", "paper")] + (["--modules", *g("modules")] if g("modules") else [])
    if name == "axioms":
        return ["axioms", *names]
    if name == "choice_audit":
        return ["choice-audit", *(g("prefixes") or ["Rule30UOR"])]
    if name == "frontier_list":
        return ["frontier", "list"] + (["--status", g("status")] if g("status") else [])
    if name in ("frontier_add", "frontier_set"):
        argv = ["frontier", name.split("_")[1], g("id", "")]
        if name == "frontier_add":
            argv.append(g("statement", ""))
        for k in ("status", "lean", "lexeme", "note"):
            if g(k):
                argv += ["--" + k, g(k)]
        return argv
    if name == "frontier_check":
        return ["frontier", "check"]
    if name == "commit":
        return ["commit", "-m", g("message", "")] + (["--push"] if g("push") else []) + list(g("paths") or [])
    if name == "experiment_run":
        return ["experiment", "run", g("name", ""), *(g("args") or [])]
    raise KeyError(name)


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
