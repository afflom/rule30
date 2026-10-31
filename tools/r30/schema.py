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
}
CLAIM = {"type": "object", "required": ["id", "status", "statement"], "additionalProperties": False,
         "properties": CLAIM_PROPERTIES}
OK = {"type": "object", "required": ["ok", "reason"], "additionalProperties": False,
      "properties": {"ok": {"type": "boolean"}, "reason": {"type": ["string", "null"]}}}

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
                       "related": {"type": "object", "additionalProperties": {"type": "array", "items": {"type": "string"}}}},
    },
    "api-check-result": {
        "title": "api check --json: whether each generated surface of rule30-api matches its sources",
        "type": "object", "additionalProperties": False,
        "required": ["api", "register", "architecture", "presentation", "observer", "convert", "model", "logo"],
        "properties": {k: OK for k in ("api", "register", "architecture", "presentation", "observer", "convert", "model", "logo")},
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


_TYPES = {"object": dict, "array": list, "string": str, "integer": int, "boolean": bool, "null": type(None)}


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
        ok = any(isinstance(value, _TYPES[t]) and not (t == "integer" and isinstance(value, bool)) for t in allowed)
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
