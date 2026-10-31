"""The language-1.2 authoring notation of LexLean semantic modules (SPEC.md
§17.21), emitted from the data form (`lexlean/semantic-module/1`). The
notation is what `lexlean migrate --to 1.2` writes; the API modules are
generated in it directly.

A member of an imported module is written `Module::name` (a type
`Foundation.Arch::Stakeholder`, a call `(Foundation.Arch::stakeholderOperator)`,
a constructor `Foundation.Arch::ModelKind.qualityModel`); the data form carries
the module in the member's `module` field, which `qualified` renders."""

import json


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
    raise ValueError(f"no notation for type {k}")


_INFIX = {"add": "+", "eq": "=", "le": "<=", "lt": "<", "beq": "=?", "ble": "<=?", "blt": "<?",
          "and": "&&", "or": "||"}


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


def decl(d):
    k = d["kind"]
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
