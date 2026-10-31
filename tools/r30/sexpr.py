"""The s-expressions used by LexLean signatures and by the Lean signature dump.

A node is either a string atom or a list of nodes. `parse` reads one node and
`dumps` writes it back in LexLean's canonical single-space form.
"""


def parse(text):
    node, i = _parse(text, 0)
    rest = text[i:].strip()
    if rest:
        raise ValueError(f"trailing input after s-expression: {rest[:40]!r}")
    return node


def _parse(s, i):
    n = len(s)
    while i < n and s[i].isspace():
        i += 1
    if i >= n:
        raise ValueError("unexpected end of s-expression")
    if s[i] == "(":
        i += 1
        out = []
        while True:
            while i < n and s[i].isspace():
                i += 1
            if i >= n:
                raise ValueError("unclosed parenthesis")
            if s[i] == ")":
                return out, i + 1
            node, i = _parse(s, i)
            out.append(node)
    j = i
    while j < n and not s[j].isspace() and s[j] not in "()":
        j += 1
    return s[i:j], j


def dumps(node):
    if isinstance(node, str):
        return node
    return "(" + " ".join(dumps(x) for x in node) + ")"


def is_app(node, head=None):
    return isinstance(node, list) and len(node) >= 1 and node[0] == "app" and \
        (head is None or (isinstance(node[1], list) and node[1][:2] == ["const", head]))


def const_name(node):
    if isinstance(node, list) and len(node) == 2 and node[0] == "const":
        return node[1]
    return None
