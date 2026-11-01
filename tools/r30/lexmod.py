"""The language-1.2 authoring notation of LexLean semantic modules (SPEC.md
§17.21), emitted from the data form (`lexlean/semantic-module/1`). The
notation is what `lexlean migrate --to 1.2` writes; the API modules are
generated in it directly.

A member of an imported module is written `Module::name` (a type
`Foundation.Arch::Stakeholder`, a call `(Foundation.Arch::stakeholderOperator)`,
a constructor `Foundation.Arch::ModelKind.qualityModel`); the data form carries
the module in the member's `module` field, which `qualified` renders."""

import json
import re


def lit(s):
    return json.dumps(s)


def qualified(member):
    """`{name, module?}` as the notation spells a member reference."""
    if member.get("module"):
        return f"{member['module']}::{member['name']}"
    return member["name"]


def type_(t):
    k = t["kind"]
    if k == "string":
        return "String"
    if k == "bool":
        return "Bool"
    if k == "nat":
        return "Nat"
    if k == "list":
        return f"(List {type_(t['element'])})"
    if k == "option":
        return f"(Option {type_(t['value'])})"
    if k == "named":
        return qualified(t["member"])
    if k == "prop":
        return "Prop"
    if k == "product":
        return f"({type_(t['left'])} * {type_(t['right'])})"
    if k == "result":
        return f"(Result {type_(t['ok'])} {type_(t['error'])})"
    if k == "contract_violation":
        return "ContractViolation"
    raise ValueError(f"no notation for type {k}")


_INFIX = {"add": "+", "eq": "=", "le": "<=", "lt": "<", "beq": "=?", "ble": "<=?", "blt": "<?",
          "and": "&&", "or": "||", "prop_and": "/\\", "iff": "<->"}


def expr(node, indent="    "):
    k = node["kind"]
    if k == "string":
        return lit(node["value"])
    if k == "bool":
        return "true" if node["value"] else "false"
    if k == "nat":
        return str(node["value"])
    if k == "var":
        return node["name"]
    if k == "nil":
        return f"(nil {type_(node['element'])})"
    if k == "cons":
        return f"(cons {expr(node['head'], indent)} {expr(node['tail'], indent)})"
    if k == "record":
        fields = ", ".join(f"{f['field']} := {expr(f['value'], indent)}" for f in node["fields"])
        return f"(record {qualified(node['type'])} {{{fields}}})"
    if k == "project":
        return f"(project {expr(node['value'], indent)} {node['field']})"
    if k == "call":
        args = " ".join(expr(a, indent) for a in node["arguments"])
        return f"({qualified(node['function'])}{(' ' + args) if args else ''})"
    if k == "constructor":
        args = " ".join(expr(a, indent) for a in node.get("arguments", []))
        return f"(ctor {qualified(node['constructor'])}{(' ' + args) if args else ''})"
    if k == "primitive":
        args = " ".join(expr(a, indent) for a in node["arguments"])
        return f"(prim {node['operation']} {args} : {type_(node['result'])})"
    if k in _INFIX:
        return f"({expr(node['left'], indent)} {_INFIX[k]} {expr(node['right'], indent)})"
    if k == "not":
        return f"(not {expr(node['value'], indent)})"
    if k == "implies":
        return f"({expr(node['premise'], indent)} -> {expr(node['conclusion'], indent)})"
    if k == "pair":
        return f"({expr(node['left'], indent)}, {expr(node['right'], indent)})"
    if k in ("first", "second"):
        return f"({k} {expr(node['value'], indent)})"
    if k == "let":
        b = node["binder"]
        return (f"(let {b['name']} : {type_(b['type'])} := {expr(node['value'], indent)}; "
                f"{expr(node['body'], indent)})")
    if k == "checked_apply":
        args = " ".join(expr(a, indent) for a in node["arguments"])
        return f"(checked {qualified(node['model'])} {args} with [{', '.join(node['checks'])}])"
    if k == "if":
        return (f"(if {expr(node['condition'], indent)} then {expr(node['then_value'], indent)} "
                f"else {expr(node['else_value'], indent)})")
    if k == "match":
        arms = []
        for b in node["branches"]:
            binders = (" " + " ".join(b["binders"])) if b["binders"] else ""
            arms.append(f"\n{indent}| {qualified(b['constructor'])}{binders} => {expr(b['body'], indent)}")
        return f"(match {expr(node['scrutinee'], indent)}{''.join(arms)})"
    raise ValueError(f"no notation for {k}")


# The member order of the generic notation (SPEC §17.21.3): these first, the
# others in key order.
_ORDER = ["name", "type_parameters", "parameters", "type", "result", "statement", "fields", "constructors",
          "arguments", "body", "proof", "axioms"]
# Positions whose value is a term or a type (read in their readable forms).
_TERMS = {"statement", "body"}
_TYPES = {"type", "result", "output"}
_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.'/-]*")


def generic(value, key=None, indent=""):
    """A value in the generic notation, with terms, types, parameters and
    members in their readable forms at the positions that read them: the
    declarations the readable layout of `decl` does not cover (theorems with
    parameters or a proof payload, contracts, realizations, evidence, models)."""
    inner = indent + "  "
    if key in _TERMS and isinstance(value, dict):
        return expr(value)
    if key in _TYPES and isinstance(value, dict) and "kind" in value:
        return type_(value)
    if key == "parameters" and isinstance(value, list):
        return "[" + ", ".join(f"{p['name']} : {type_(p['type'])}" for p in value) + "]"
    if isinstance(value, dict):
        if set(value) <= {"name", "module"} and "name" in value:
            return qualified(value)
        keys = [k for k in _ORDER if k in value] + sorted(k for k in value if k not in _ORDER and k != "kind")
        fields = [f"{k}: {generic(value[k], k, inner)}" for k in keys]
        head = value.get("kind", "")
        flat = head + "{" + ", ".join(fields) + "}"
        if len(indent) + len(flat) <= 100 and "\n" not in flat:
            return flat
        return head + "{\n" + ",\n".join(inner + f for f in fields) + "\n" + indent + "}"
    if isinstance(value, list):
        items = [generic(v, None, inner) for v in value]
        flat = "[" + ", ".join(items) + "]"
        if len(indent) + len(flat) <= 100 and "\n" not in flat:
            return flat
        return "[\n" + ",\n".join(inner + i for i in items) + "\n" + indent + "]"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return value if _NAME.fullmatch(value) and value not in ("true", "false") else lit(value)
    raise ValueError(f"no generic notation for {value!r}")


def _general_theorem(d):
    """A theorem with parameters, a statement other than an equation, or a
    proof with a payload (induction, simplify, linear arithmetic)."""
    fields = [f"name: {d['name']}", "parameters: " + generic(d.get("parameters", []), "parameters"),
              f"statement: {expr(d['statement'])}", "proof: " + generic(d["proof"], None, "  "),
              "axioms: [" + ", ".join(d.get("axioms", [])) + "]"]
    return "theorem{\n" + ",\n".join("  " + f for f in fields) + "\n}"


def decl(d):
    k = d["kind"]
    if k in ("contract", "realization", "evidence", "model"):
        return generic(d)
    if k == "theorem" and (d.get("parameters") or d["statement"]["kind"] != "eq" or set(d["proof"]) != {"kind"}):
        return _general_theorem(d)
    if k == "structure":
        fields = ",\n".join(f"    {{name: {f['name']}, type: {type_(f['type'])}}}" for f in d["fields"])
        return (f"structure{{\n  name: {d['name']},\n  type_parameters: [],\n  parameters: [],\n"
                f"  fields: [\n{fields}\n  ]\n}}")
    if k == "definition":
        params = ", ".join(f"{p['name']} : {type_(p['type'])}" for p in d.get("parameters", []))
        rec = f",\n  recursive_argument: {d['recursive_argument']}" if d.get("recursive_argument") else ""
        # a production root (SPEC §17.13): executable, with its effects and
        # targets from the closed registry, in the order `fmt` writes them
        exe = ",\n  executable: true" if d.get("executable") else ""
        prod = d.get("production")
        prod = (f",\n  production: {{effects: [{', '.join(prod['effects'])}], targets: [{', '.join(prod['targets'])}]}}"
                if prod else "")
        return (f"definition{{\n  name: {d['name']},\n  parameters: [{params}],\n  result: {type_(d['result'])},\n"
                f"  body: {expr(d['body'])},\n  axioms: []{rec}{exe}{prod}\n}}")
    if k == "theorem":
        st = d["statement"]
        proof = d["proof"]["kind"]
        return (f"theorem{{\n  name: {d['name']},\n  parameters: [],\n"
                f"  statement: ({expr(st['left'])} = {expr(st['right'])}),\n"
                f"  proof: {proof}{{}},\n  axioms: []\n}}")
    raise ValueError(k)


def module(name, declarations, title="Boolean", imports=(), glossaries=()):
    """A module in the notation. `imports` are project modules (`\\importmodule`,
    sorted as `fmt` sorts them); `glossaries` are lexicon packages beyond the
    two builtin ones (`package@version`)."""
    packages = sorted({"lexlean.std.bool@1.2.0", "lexlean.std.nat@1.2.0", *glossaries})
    header = [f"\\begin{{lexlean}}{{{name}}}"]
    header += [f"\\useglossary{{{p}}}" for p in packages]
    header += [f"\\importmodule{{{m}}}" for m in sorted(imports)]
    header += [f"\\title{{{title}}}", "\\begin{semanticmodule}"]
    body = "\n\n".join(decl(d) for d in declarations)
    return "\n".join(header) + "\n" + body + "\n\\end{semanticmodule}\n\\end{lexlean}\n"
