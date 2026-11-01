#!/usr/bin/env python3
"""The κ-labeling procedure: everything that decides a label, and nothing else.

The memo of labels (`kappa_research.memo_labels`) is keyed by the digest of
this file and of the exporter, so only an edit here or there relabels.

κ-address the research modules: the label of what the kernel replays.

A κ-label (UOR-Foundation/uor-addr) is `sha256:<64 hex>`, the SHA-256 of a
published canonical form of what a value means, with no prefix or framing
added to the canonical bytes: two values that mean the same get the same
label. For S-expressions the canonical form is Rivest 1997 §4.3: an atom is
`<n>:<bytes>`, a list is `(s1 s2 ... sn)` with single-space separators, nil is
`()`. Labels compose: a label is an atom like any other, so the address of a
structure of addressed parts is the address of a canonical S-expression whose
atoms are the parts' 71-byte labels (an address of addresses).

What a Lean module means to the kernel is its declarations: names, universe
parameters, kinds, types and values. Its `.olean` also carries source
positions, docstrings, extension data and the order of elaboration, which
change when no theorem changes, so the κ of a module is computed from the
declaration stream `rule30-core-lean/scripts/KappaExport.lean` prints (the
constants of the module's most private object-file part, exactly the set
`leanchecker` replays), never from the object-file bytes.

The canonical S-expression of a Lean declaration (rule30 profile)
-----------------------------------------------------------------

Terms. Every `Level` and `Expr` subterm is a node whose canonical form is
`(<ctor> <fields...> <κ of child 1> ... <κ of child n>)`, the children's
labels as atoms, so κ(node) is defined bottom-up and a shared subterm has one
label wherever it occurs (the exporter's stream names nodes by id to state
that sharing; the ids are not part of the meaning):

    (lzero)  (lsucc u)  (lmax u v)  (limax u v)  (lparam <name>)
    (bvar <index>)                         de Bruijn index, so binder names
                                           are not part of the meaning
    (sort <κ level>)
    (const <name> <κ level>...)
    (app <κ fn> <κ arg>)
    (lam <binder info> <κ type> <κ body>)        binder info: default |
    (forallE <binder info> <κ type> <κ body>)    implicit | strictImplicit |
                                                 instImplicit
    (letE <nondep: 0|1> <κ type> <κ value> <κ body>)
    (lit nat <decimal>)   (lit str <bytes>)
    (proj <structure name> <index> <κ struct>)

`mdata` carries no kernel meaning and is transparent: the label of
`mdata d e` is the label of `e`. Free variables and metavariables do not
occur in closed declarations (the exporter refuses them). Names are atoms in
Lean's printed form (`Name.toString`); numbers are decimal atoms.

Declarations. κ(decl) is the label of

    (decl <name> <kind> (levels <universe names>...) <κ type> <κ value | ()> <extras>...)

with kind and extras by constant kind, the extras being the parts of the
declaration the kernel checks besides its type and value:

    axiom   (safety safe|unsafe)
    def     (safety safe|unsafe|partial)      reducibility hints are omitted:
                                              the kernel accepts any hints
    thm     (no extras)
    opaque  (safety safe|unsafe)
    quot    (kind type|ctor|lift|ind)
    induct  (params n) (indices n) (ctors <names>...) (all <names>...)
            (nested n) (safety ...)
    ctor    (induct <name>) (cidx n) (params n) (fields n) (safety ...)
    rec     (all <names>...) (params n) (indices n) (motives n) (minors n)
            (rules (rule <ctor> <nfields> <κ rhs>)...) (k 0|1) (safety ...)

Modules. κ(module) is the label of

    (lean-module <module name> <κ decl 1> ... <κ decl n>)

with the declarations sorted by name (then by label), so the order of
elaboration is not part of the meaning.

Usage: kappa_research.py [--declarations] [--json] <Lean module names>, run
in the repository (the research library must be built)."""

import hashlib
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPORTER = "scripts/KappaExport.lean"
SCHEME = "sha256:"

# Leading atoms of a term node that are fields; every later element is a child id.
NODE_FIELDS = {"lzero": 0, "lsucc": 0, "lmax": 0, "limax": 0, "lparam": 1, "bvar": 1, "sort": 0,
               "const": 1, "app": 0, "lam": 1, "forallE": 1, "letE": 1, "lit": 2, "proj": 2}


def canonical(value):
    """The Rivest canonical bytes of a value: str/bytes atoms, list/tuple lists."""
    if isinstance(value, (list, tuple)):
        return b"(" + b" ".join(canonical(v) for v in value) + b")"
    if isinstance(value, str):
        value = value.encode()
    return b"%d:" % len(value) + value


def label(canonical_bytes):
    """The κ-label of canonical bytes: the SHA-256 of exactly those bytes."""
    return SCHEME + hashlib.sha256(canonical_bytes).hexdigest()


def kappa(value):
    return label(canonical(value))


def parse(data):
    """The top-level values of a canonical S-expression stream, as bytes atoms and lists.
    About 7 µs per term node in CPython; the 3.1 million nodes of the library take 25 s."""
    i, n, stack = 0, len(data), []
    while i < n:
        c = data[i]
        if c == 40:  # (
            stack.append([])
            i += 1
        elif c == 41:  # )
            if not stack:
                raise ValueError(f"unbalanced ')' at byte {i}")
            done = stack.pop()
            i += 1
            if stack:
                stack[-1].append(done)
            else:
                yield done
        elif c in b" \t\r\n":
            i += 1
        else:
            j = data.find(b":", i)
            if j < 0 or not data[i:j].isdigit():
                raise ValueError(f"not a canonical atom at byte {i}: {data[i:i + 20]!r}")
            start = j + 1
            end = start + int(data[i:j])
            if end > n:
                raise ValueError(f"truncated atom at byte {i}")
            atom = data[start:end]
            i = end
            if stack:
                stack[-1].append(atom)
            else:
                yield atom
    if stack:
        raise ValueError("unterminated list")


def labels_from_stream(data):
    """{module: {"kappa", "declarations": [(name, κ)], "statements": [(name, statement κ, exact κ)],
    "kinds": {name: kind}, "reserved": [names Lean reserves]}} from the exporter's stream. The declaration κ (and the module κ
    composed from them, the key of the replay receipts) is exact, binder info included. A
    theorem's statement κ is the κ of its type as a meaning: binder info (implicit or explicit is
    elaboration) is omitted and universe parameters are numbered by first occurrence, so two
    theorems that state the same thing share it whatever their names, binders and universe names.
    It is computed for theorem types only, memoized per module."""
    result, ids, forms, loose, exact, current, decls, stmts, kinds, reserved = {}, {}, {}, {}, {}, None, [], [], {}, []
    for form in parse(data):
        head = form[0]
        if head == b"module":
            current, ids, forms, loose, exact, decls, stmts, kinds, reserved = form[1].decode(), {}, {}, {}, {}, [], [], {}, []
        elif head == b"node":
            ctor = form[2]
            split = 3 + NODE_FIELDS[ctor.decode()]
            fields, children = list(form[3:split]), list(form[split:])
            ids[form[1]] = kappa([ctor, *fields, *(ids[child] for child in children)])
            forms[form[1]] = (ctor, fields, children)
        elif head == b"decl":
            _, name, kind, levels, type_id, value_id, *extras = form
            parts = [b"decl", name, kind, levels, ids[type_id], [] if value_id == [] else ids[value_id]]
            is_reserved = False
            for extra in extras:
                if extra == [b"reserved"]:
                    # Lean reserves the name (it realizes the lemma itself): not part of the meaning
                    is_reserved = True
                    continue
                if extra[0] == b"rules":
                    extra = [b"rules"] + [[b"rule", rule[1], rule[2], ids[rule[3]]] for rule in extra[1:]]
                parts.append(extra)
            decls.append((name, kappa(parts)))
            kinds[name.decode()] = kind.decode()
            if is_reserved:
                reserved.append(name.decode())
            if kind == b"thm":
                params = list(levels[1:]) if isinstance(levels, list) else []
                statement = positional(forms, type_id, params, None if params else loose)
                # the binder check's κ: binder info kept, universe parameters by declaration order
                binders = positional(forms, type_id, params, None if params else exact, keep_binders=True,
                                     by_declaration=True)
                stmts.append((name, statement, binders))
        elif head == b"end":
            if form[1].decode() != current:
                raise ValueError(f"stream ends {form[1].decode()!r} inside {current!r}")
            decls.sort()
            result[current] = {"kappa": kappa([b"lean-module", current, *(k for _, k in decls)]),
                               "declarations": [(name.decode(), k) for name, k in decls],
                               "statements": sorted((name.decode(), k, e) for name, k, e in stmts),
                               "kinds": dict(sorted(kinds.items())), "reserved": sorted(reserved)}
            current = None
    if current is not None:
        raise ValueError(f"stream ends inside module {current}")
    return result


def positional(forms, root, params, cache=None, keep_binders=False, by_declaration=False):
    """The statement κ of a type: binder info omitted and each universe parameter of `params`
    numbered by its first occurrence in a left-to-right walk (so `.{u, v}` and `.{v, u}` agree).
    With no parameters the labels depend on the node alone and `cache` is shared across theorems."""
    index = {}
    if params and by_declaration:
        index = {name: str(i).encode() for i, name in enumerate(params)}
    elif params:
        seen, stack = set(), [root]
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            ctor, fields, children = forms[node]
            if ctor == b"lparam" and fields[0] in params and fields[0] not in index:
                index[fields[0]] = str(len(index)).encode()
            stack.extend(reversed(children))
    done = cache if cache is not None and not params else {}
    stack = [(root, False)]
    while stack:
        node, expanded = stack.pop()
        if node in done:
            continue
        ctor, fields, children = forms[node]
        if not expanded:
            stack.append((node, True))
            stack.extend((child, False) for child in children if child not in done)
            continue
        if ctor in (b"lam", b"forallE") and not keep_binders:
            fields = []
        elif ctor == b"lparam" and fields[0] in index:
            fields = [b"#" + index[fields[0]]]
        done[node] = kappa([ctor, *fields, *(done[child] for child in children)])
    return done[root]


def export(core, modules):
    """The declaration stream of the modules, from the built research library."""
    result = subprocess.run(["lake", "env", "lean", "--run", EXPORTER, *modules], cwd=core,
                            capture_output=True)
    if result.returncode != 0:
        detail = result.stderr.decode(errors="replace").strip().splitlines()[-3:]
        raise RuntimeError(f"the κ exporter failed (exit {result.returncode}): " + " | ".join(detail))
    return result.stdout


def module_labels(core, modules, exporter=None):
    """κ of each module, from one exporter run (an injectable one for tests)."""
    exporter = exporter or export
    labels = labels_from_stream(exporter(core, modules)) if modules else {}
    missing = [m for m in modules if m not in labels]
    if missing:
        raise RuntimeError(f"the κ exporter returned no declarations for {' '.join(missing)}")
    return labels


