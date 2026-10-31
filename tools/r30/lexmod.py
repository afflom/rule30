"""The language-1.2 authoring notation of LexLean semantic modules (SPEC.md
§17.21), emitted from the data form (`lexlean/semantic-module/1`). The
notation is what `lexlean migrate --to 1.2` writes; the API modules are
generated in it directly."""

import json


def lit(s):
    return json.dumps(s)


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
    if k == "named":
        return t["member"]["name"]
    raise ValueError(f"no notation for type {k}")


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
        return f"(record {node['type']['name']} {{{fields}}})"
    if k == "project":
        return f"(project {expr(node['value'], indent)} {node['field']})"
    if k == "call":
        args = " ".join(expr(a, indent) for a in node["arguments"])
        return f"({node['function']['name']}{(' ' + args) if args else ''})"
    if k == "primitive":
        args = " ".join(expr(a, indent) for a in node["arguments"])
        return f"(prim {node['operation']} {args} : {type_(node['result'])})"
    if k == "if":
        return (f"(if {expr(node['condition'], indent)} then {expr(node['then_value'], indent)} "
                f"else {expr(node['else_value'], indent)})")
    if k == "match":
        arms = []
        for b in node["branches"]:
            binders = (" " + " ".join(b["binders"])) if b["binders"] else ""
            arms.append(f"\n{indent}| {b['constructor']['name']}{binders} => {expr(b['body'], indent)}")
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
        return (f"definition{{\n  name: {d['name']},\n  parameters: [{params}],\n  result: {type_(d['result'])},\n"
                f"  body: {expr(d['body'])},\n  axioms: []{rec}\n}}")
    if k == "theorem":
        st = d["statement"]
        proof = d["proof"]["kind"]
        return (f"theorem{{\n  name: {d['name']},\n  parameters: [],\n"
                f"  statement: ({expr(st['left'])} = {expr(st['right'])}),\n"
                f"  proof: {proof}{{}},\n  axioms: []\n}}")
    raise ValueError(k)


def module(name, declarations, title="Boolean"):
    header = (f"\\begin{{lexlean}}{{{name}}}\n\\useglossary{{lexlean.std.bool@1.2.0}}\n"
              f"\\useglossary{{lexlean.std.nat@1.2.0}}\n\\title{{{title}}}\n\\begin{{semanticmodule}}")
    body = "\n\n".join(decl(d) for d in declarations)
    return header + "\n" + body + "\n\\end{semanticmodule}\n\\end{lexlean}\n"
