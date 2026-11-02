"""The JSON schemas of the `--json` reports of the read-only `r30` commands
(`rule30-api/schemas/<name>.schema.json`, the `result_schema` ids of
`model/commands.toml`), and a validator for the subset of JSON Schema they use.

Each schema was derived from the command's recorded output and is closed
(`additionalProperties: false`), so a field added to a report without a
schema change fails `scripts/tests/test_r30.py`. The validator covers what the
schemas state (type, enum, const, required, properties, additionalProperties,
items, pattern, $ref to a `$defs` entry) and nothing else; the tests use it so
that the gate needs no `jsonschema` package."""

import re

from . import frontier

DRAFT = "https://json-schema.org/draft/2020-12/schema"
STATUS = {"type": "string", "enum": list(frontier.STATUSES)}

# A register claim as `frontier list --json` prints it (and `register.json`).
CLAIM_PROPERTIES = {
    "id": {"type": "string", "pattern": "^[a-z][a-z0-9-]*$"},
    "status": STATUS,
    "statement": {"type": "string"},
    "lean": {"type": "string"},
    "lexeme": {"type": "string"},
    "since": {"type": "string"},
    "note": {"type": "string"},
    "depends": {"type": "array", "items": {"type": "string"}},
    "relation": {"type": "array", "items": {"type": "string"}},
    "window": {"type": "integer"},
    "kappa": {"type": "string", "pattern": "^sha256:[0-9a-f]{64}$"},
}
CLAIM = {"type": "object", "required": ["id", "status", "statement"], "additionalProperties": False,
         "properties": CLAIM_PROPERTIES}
OK = {"type": "object", "required": ["ok", "reason"], "additionalProperties": False,
      "properties": {"ok": {"type": "boolean"}, "reason": {"type": ["string", "null"]}}}

KAPPA = {"type": "string", "pattern": "^sha256:[0-9a-f]{64}$"}

RESULTS = {
    "status-result": {
        "title": "status --json: HEAD, dirty files, the frontier counts, the compiler, the gate",
        "type": "object", "additionalProperties": False,
        "required": ["head", "dirty", "ahead_of_origin", "frontier", "lexlean", "gate_running"],
        "properties": {
            "head": {"type": "array", "items": {"type": "string"}},
            "dirty": {"type": "integer"},
            "ahead_of_origin": {"type": "integer"},
            "frontier": {"type": "object", "required": ["counts", "open"], "additionalProperties": False,
                         "properties": {"counts": {"type": "object", "required": list(frontier.STATUSES), "additionalProperties": False,
                                                   "properties": {s: {"type": "integer"} for s in frontier.STATUSES}},
                                        "open": {"type": "array", "items": {"type": "string"}}}},
            "lexlean": {"type": "string"},
            "gate_running": {"type": "boolean"},
        },
    },
    "brief-result": {
        "title": "brief --json: the open claims, the proved reductions, the refuted routes",
        "type": "object", "additionalProperties": False, "required": ["open", "proved", "refuted"],
        "properties": {k: {"type": "array", "items": {"$ref": "#/$defs/claim"}} for k in ("open", "proved", "refuted")},
        "$defs": {"claim": CLAIM},
    },
    "chain-result": {
        "title": "chain --json: the pre-order walk of the reduction tree",
        "type": "array",
        "items": {"type": "object", "required": ["depth", "id", "lean", "status"], "additionalProperties": False,
                  "properties": {"depth": {"type": "integer"}, "id": {"type": "string"},
                                 "lean": {"type": ["string", "null"]}, "status": STATUS}},
    },
    "claim-result": {
        "title": "claim --json: one register entry with its dependents, Lean type, published statement and related facts",
        "type": "object", "additionalProperties": False, "required": ["id", "status", "statement", "dependents"],
        "properties": {**CLAIM_PROPERTIES,
                       "dependents": {"type": "array", "items": {"type": "string"}},
                       "lean_type": {"type": "string"},
                       "published": {"type": "string"},
                       "published_in": {"type": "string"},
                       "related": {"type": "object", "additionalProperties": {"type": "array", "items": {"type": "string"}}},
                       # with --related: the audited conditional refutations the claim concerns (auditmodel.related)
                       "audit": {"type": "array", "items": {
                           "type": "object", "required": ["theorem", "status", "open", "refutedBy"], "additionalProperties": False,
                           "properties": {"theorem": {"type": "string"},
                                          "status": {"type": "string", "enum": ["dead", "live-discharged", "open"]},
                                          "open": {"type": "array", "items": {"type": "string"}},
                                          "refutedBy": {"type": "array", "items": {"type": "string"}}}}}},
    },
    "kappa-result": {
        "title": "kappa --json: the κ-label of each module and, with --declarations, of each of its declarations",
        "type": "object",
        "additionalProperties": {
            "type": "object", "required": ["kappa"], "additionalProperties": False,
            "properties": {"kappa": KAPPA,
                           "declarations": {"type": "array", "items": {
                               "type": "object", "required": ["name", "kappa"], "additionalProperties": False,
                               "properties": {"name": {"type": "string"}, "kappa": KAPPA}}}}},
    },
    "api-check-result": {
        "title": "api check --json: whether each generated surface of rule30-api matches its sources",
        "type": "object", "additionalProperties": False,
        "required": ["api", "register", "architecture", "presentation", "observer", "convert", "standards", "core", "sequences",
                     "discovery", "engine", "model", "logo"],
        "properties": {k: OK for k in ("api", "register", "architecture", "presentation", "observer", "convert", "standards", "core",
                                       "sequences", "discovery", "engine", "model", "logo")},
    },
    "sequences-result": {
        "title": "sequences --json: the basis (every sequence with its lexeme, parameters and κ-label), the excluded notions, and the problems of the committed data",
        "type": "object", "additionalProperties": False, "required": ["window", "requested_window", "sequences", "excluded", "problems"],
        "properties": {
            "window": {"type": ["integer", "null"]},
            "requested_window": {"type": "integer"},
            "sequences": {"type": "array", "items": {
                "type": "object", "required": ["id", "lexeme", "parameters", "kappa"], "additionalProperties": False,
                "properties": {"id": {"type": "string"}, "lexeme": {"type": "string"},
                               "parameters": {"type": "array", "items": {"type": "integer"}}, "kappa": KAPPA}}},
            "excluded": {"type": "array", "items": {
                "type": "object", "required": ["id", "lexeme", "lean", "reason"], "additionalProperties": False,
                "properties": {k: {"type": "string"} for k in ("id", "lexeme", "lean", "reason")}}},
            "problems": {"type": "array", "items": {"type": "string"}},
        },
    },
    "discover-result": {
        "title": "discover --json: the runtime that ran, the relations of the extended basis on the window with their certificates and classes, the recurrences of the base windows, and the claims written",
        "type": "object", "additionalProperties": False,
        "required": ["runtime", "why", "window", "stored_window", "degree", "columns", "rank", "relations", "counts", "recurrences", "written"],
        "properties": {
            "runtime": {"type": "string", "enum": ["rust", "python"]},
            "why": {"type": "string"},
            "window": {"type": "integer"}, "stored_window": {"type": "integer"}, "degree": {"type": "integer"},
            "columns": {"type": "integer"}, "rank": {"type": "integer"},
            "relations": {"type": "array", "items": {
                "type": "object", "additionalProperties": False,
                "required": ["columns", "kappa", "class", "claim", "scope", "dependent", "rank", "chance_log2"],
                "properties": {"columns": {"type": "array", "items": {"type": "string"}}, "kappa": KAPPA,
                               "class": {"type": "string", "enum": ["register", "trivial", "consequence", "new"]},
                               "claim": {"type": ["string", "null"]}, "scope": {"type": "string", "enum": ["self", "cross"]},
                               "dependent": {"type": "string"}, "rank": {"type": "integer"}, "chance_log2": {"type": "integer"}}}},
            "counts": {"type": "object", "required": ["register", "trivial", "consequence", "new"], "additionalProperties": False,
                       "properties": {k: {"type": "integer"} for k in ("register", "trivial", "consequence", "new")}},
            "recurrences": {"type": "array", "items": {
                "type": "object", "additionalProperties": False,
                "required": ["id", "kappa", "length", "window", "connection", "margin", "determined"],
                "properties": {"id": {"type": "string"}, "kappa": KAPPA, "length": {"type": "integer"}, "window": {"type": "integer"},
                               "connection": {"type": "array", "items": {"type": "integer"}}, "margin": {"type": "integer"},
                               "determined": {"type": "boolean"}}}},
            "written": {"type": "array", "items": {"type": "string"}},
        },
    },
    "deduce-result": {
        "title": "deduce --json: every attempt (claim, κ-label, strategy, template digest, family, outcome, failure point, seconds, theorem), the claims proved, known (proved by the library theorem that states them), refuted, and the attempts left for the budget",
        "type": "object", "additionalProperties": False,
        "required": ["attempts", "proved", "refuted", "known", "skipped", "dry_run"],
        "properties": {
            "attempts": {"type": "array", "items": {"$ref": "#/$defs/attempt"}},
            "proved": {"type": "array", "items": {"$ref": "#/$defs/proof"}},
            "known": {"type": "array", "items": {"$ref": "#/$defs/proof"}},
            "refuted": {"type": "array", "items": {
                "type": "object", "required": ["id", "lean", "t"], "additionalProperties": False,
                "properties": {"id": {"type": "string"}, "lean": {"type": "string"}, "t": {"type": "integer"}}}},
            "skipped": {"type": "array", "items": {
                "type": "object", "required": ["id", "strategy", "reason"], "additionalProperties": False,
                "properties": {k: {"type": "string"} for k in ("id", "strategy", "reason")}}},
            "dry_run": {"type": "boolean"},
        },
        "$defs": {
            "attempt": {"type": "object", "additionalProperties": False,
                        "required": ["claim", "kappa", "strategy", "template", "family", "outcome", "failure", "seconds", "theorem"],
                        "properties": {"claim": {"type": "string"}, "kappa": KAPPA, "strategy": {"type": "string"},
                                       "template": KAPPA, "family": {"type": "string"},
                                       "library": {"type": "string", "pattern": "^(sha256:[0-9a-f]{64})?$"},
                                       "outcome": {"type": "string", "enum": ["proved", "known", "refuted", "failed", "timeout", "dry-run"]},
                                       "failure": {"type": "string"}, "seconds": {"type": "number"}, "theorem": {"type": "string"}}},
            "proof": {"type": "object", "required": ["id", "lean"], "additionalProperties": False,
                      "properties": {"id": {"type": "string"}, "lean": {"type": "string"}}},
        },
    },
    "engine-tick-result": {
        "title": "engine tick --json: the tick summary the ledger records (start, base, stages with seconds and allowances, counts, outcome)",
        "$ref": "#/$defs/tick",
        "$defs": {"tick": {
            "type": "object", "additionalProperties": False,
            "required": ["number", "start", "base", "budget", "stages", "outcome", "seconds", "commit", "observed", "proved",
                         "refuted", "known", "attempts", "new_relations", "minted"],
            "properties": {
                "number": {"type": "integer"}, "start": {"type": "string"}, "base": {"type": "string"},
                "budget": {"type": "integer"},
                "stages": {"type": "array", "items": {
                    "type": "object", "required": ["id", "seconds", "allowance", "outcome", "note", "runtime"], "additionalProperties": False,
                    "properties": {"id": {"type": "string", "enum": ["build", "induction", "pruning", "deduction", "learning", "hypotheses", "gate"]},
                                   "runtime": {"type": "string"},
                                   "seconds": {"type": "number"}, "allowance": {"type": "number"},
                                   "outcome": {"type": "string", "enum": ["ok", "cut", "error"]}, "note": {"type": "string"}}}},
                "outcome": {"type": "string", "enum": ["idle", "cut", "stale", "uncommitted", "committed", "pushed", "dropped",
                                                       "refused", "error", "stalled"]},
                "pending": {"type": ["integer", "null"]},
                "seconds": {"type": "number"}, "commit": {"type": "string"},
                "observed": {"type": "integer"}, "proved": {"type": "integer"}, "refuted": {"type": "integer"},
                "known": {"type": "integer"}, "attempts": {"type": "integer"}, "new_relations": {"type": "integer"}, "minted": {"type": "integer"}}}},
    },
    "engine-status-result": {
        "title": "engine status --json: the last tick, the network (units, synapses, events), the attempts by outcome, the pending attempts and the learned weights",
        "type": "object", "additionalProperties": False,
        "required": ["last", "hypotheses", "units", "synapses", "events", "attempts", "pending", "weights"],
        "properties": {
            "last": {"type": ["object", "null"]},
            "units": {"type": "integer"},
            "synapses": {"type": "object", "required": ["observed", "proved", "refuted"], "additionalProperties": False,
                         "properties": {k: {"type": "integer"} for k in ("observed", "proved", "refuted")}},
            "events": {"type": "integer"},
            "attempts": {"type": "object", "additionalProperties": {"type": "integer"}},
            "pending": {"type": ["integer", "string"]},
            "hypotheses": {"type": "object", "additionalProperties": {"type": "integer"}},
            "weights": {"type": "array", "items": {
                "type": "object", "required": ["strategy", "family", "value"], "additionalProperties": False,
                "properties": {"strategy": {"type": "string"}, "family": {"type": "string"}, "value": {"type": "integer"}}}},
        },
    },
    "engine-prune-result": {
        "title": "engine prune --json: what of the gate's evidence the next run can use (kept) and what it cannot (dropped, deleted with --apply)",
        "type": "object", "additionalProperties": False,
        "required": ["root", "key", "procedure", "kept", "dropped", "kept_bytes", "dropped_bytes", "applied"],
        "properties": {
            "root": {"type": "string"},
            "key": {"type": ["string", "null"], "pattern": "^[0-9a-f]{16}$"},
            "procedure": {"type": ["string", "null"], "pattern": "^[0-9a-f]{16}$"},
            "kept": {"type": "array", "items": {"type": "string"}},
            "dropped": {"type": "array", "items": {"type": "string"}},
            "kept_bytes": {"type": "integer"}, "dropped_bytes": {"type": "integer"},
            "applied": {"type": "boolean"},
        },
    },
    "api-production-result": {
        "title": "api production --json: the certified Rust bundle lexlean production published, or the stage that failed",
        "type": "object", "additionalProperties": False, "required": ["ok", "stage", "diagnostics"],
        "properties": {
            "ok": {"type": "boolean"},
            "stage": {"type": "string", "enum": ["lock", "build", "replay"]},
            "diagnostics": {"type": "array", "items": {"type": "string"}},
            "bundle": {"type": "string"},
            "result_id": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "semantic_id": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
            "compiler": {"type": "object", "required": ["version", "semantics", "lean_toolchain"], "additionalProperties": False,
                         "properties": {"version": {"type": "string"}, "semantics": {"type": "string"}, "lean_toolchain": {"type": "string"}}},
            "outputs": {"type": "array", "items": {
                "type": "object", "additionalProperties": False,
                "required": ["root", "target", "package", "crate", "certification", "axioms", "effects", "optimality"],
                "properties": {"root": {"type": "string"}, "target": {"type": "string", "enum": ["rust-core", "rust-std"]},
                               "package": {"type": "string"}, "crate": {"type": "string"},
                               "certification": {"type": "string", "const": "kernel-checked"},
                               "axioms": {"type": "array", "items": {"type": "string"}},
                               "effects": {"type": "array", "items": {"type": "string", "enum": ["allocation", "overflow", "recursion"]}},
                               "optimality": {"type": ["string", "null"]}}}},
            "needs_stack": {"type": "integer"},
            "replay": {"type": "string", "enum": ["bindings-verified", "failed"]},
        },
    },
}


def document(name):
    """The schema file of a result: the draft, the id and the shape."""
    return {"$schema": DRAFT, "$id": f"r30/{name}/1", **RESULTS[name]}


class Invalid(ValueError):
    pass


_TYPES = {"object": dict, "array": list, "string": str, "integer": int, "number": (int, float), "boolean": bool,
          "null": type(None)}


def validate(schema, value, root=None, path="$"):
    """Raise `Invalid` naming the first place `value` leaves `schema`."""
    root = root if root is not None else schema
    if "$ref" in schema:
        ref = schema["$ref"]
        if not ref.startswith("#/$defs/"):
            raise Invalid(f"{path}: unsupported $ref {ref}")
        return validate(root["$defs"][ref[len("#/$defs/"):]], value, root, path)
    types = schema.get("type")
    if types is not None:
        allowed = [types] if isinstance(types, str) else types
        ok = any(isinstance(value, _TYPES[t]) and not (t in ("integer", "number") and isinstance(value, bool)) for t in allowed)
        if not ok:
            raise Invalid(f"{path}: expected {types}, got {type(value).__name__}")
    if "enum" in schema and value not in schema["enum"]:
        raise Invalid(f"{path}: {value!r} is not one of {schema['enum']}")
    if "const" in schema and value != schema["const"]:
        raise Invalid(f"{path}: {value!r} is not {schema['const']!r}")
    if "pattern" in schema and isinstance(value, str) and not re.search(schema["pattern"], value):
        raise Invalid(f"{path}: {value!r} does not match {schema['pattern']}")
    if isinstance(value, dict):
        for k in schema.get("required", []):
            if k not in value:
                raise Invalid(f"{path}: missing {k}")
        props = schema.get("properties", {})
        extra = schema.get("additionalProperties", True)
        for k, v in value.items():
            if k in props:
                validate(props[k], v, root, f"{path}.{k}")
            elif extra is False:
                raise Invalid(f"{path}: unexpected field {k}")
            elif isinstance(extra, dict):
                validate(extra, v, root, f"{path}.{k}")
    if isinstance(value, list) and "items" in schema:
        for i, v in enumerate(value):
            validate(schema["items"], v, root, f"{path}[{i}]")
    return True
