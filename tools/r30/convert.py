"""Lean types to LexLean: the glossary signature, the Lean probe type, and the
controlled-English statement, all from one Lean declaration.

The conversion is total on the fragment the paper uses and refuses anything
else with a message naming the Lean constant and, when one exists, the lexeme
to use instead. A refusal here is a statement that `lexlean verify` would have
rejected five minutes later.
"""

from dataclasses import dataclass, field
import re

from . import sexpr
from .lexicon import Lexicon

SORT_WORD = {"lexlean.std.nat::nat": "natural number", "lexlean.std.int::int": "integer",
             "lexlean.std.bool::bool": "truth value"}
SORT_LEAN = {"Nat": "lexlean.std.nat::nat", "Int": "lexlean.std.int::int", "Bool": "lexlean.std.bool::bool"}
CORE = {"Eq": "lexlean.core::eq", "And": "lexlean.core::land", "Or": "lexlean.core::lor",
        "Iff": "lexlean.core::iff", "Not": "lexlean.core::lnot"}
# Heterogeneous operator classes: (class method) -> {carrier type: underlying Lean function}
HOPS = {
    "HAdd.hAdd": {"Nat": "Nat.add", "Int": "Int.add"},
    "HSub.hSub": {"Nat": "Nat.sub", "Int": "Int.sub"},
    "HMul.hMul": {"Nat": "Nat.mul", "Int": "Int.mul"},
    "HDiv.hDiv": {"Nat": "Nat.div", "Int": "Int.div"},
    "HMod.hMod": {"Nat": "Nat.mod", "Int": "Int.emod"},
    "HPow.hPow": {"Nat": "Nat.pow"},
    "HXor.hXor": {"Nat": "Nat.xor"},
    "HAnd.hAnd": {"Nat": "Nat.land"},
    "HOr.hOr": {"Nat": "Nat.lor"},
    "HShiftLeft.hShiftLeft": {"Nat": "Nat.shiftLeft"},
    "HShiftRight.hShiftRight": {"Nat": "Nat.shiftRight"},
    "LE.le": {"Nat": "Nat.le", "Int": "Int.le"},
    "LT.lt": {"Nat": "Nat.lt", "Int": "Int.lt"},
    "Neg.neg": {"Int": "Int.neg"},
}
ALIASES = {"and": "Bool.and", "or": "Bool.or", "not": "Bool.not", "Bool.true": "Bool.true",
           "Bool.false": "Bool.false"}
# Lean constants the paper states through a definitionally equal wrapper. The
# Lean probe checks the equality, so a wrong row here cannot reach verify.
DEFEQ = {"Nat.testBit": "Rule30UOR.WittDefect.rowBit", "Bool.toNat": "Rule30UOR.WittDefect.naturalBit"}
HINTS = {"Bool.xor": "use Rule30UOR.Core.bxor (r30.local::bxor)",
         "xor": "use Rule30UOR.Core.bxor (r30.local::bxor)",
         "bne": "use Rule30UOR.Core.bxor (r30.local::bxor)",
         "Nat.testBit": "use Rule30UOR.WittDefect.rowBit (r30.observation::row-bit) or wittBitBool",
         "Bool.toNat": "use Rule30UOR.WittDefect.naturalBit (r30.observation::natural-bit)",
         "Nat.cast": "no lexeme for casts; state the fact over one carrier type",
         "IntCast.intCast": "no lexeme for casts",
         "Int.ofNat": "no lexeme for casts",
         "Decidable.decide": "no lexeme for decide; state the Bool directly",
         "ite": "no lexeme for if-then-else; use a named function"}


LOGIC = ("lexlean.core::land", "lexlean.core::lor", "lexlean.core::iff", "->")
# Surfaces that are also grammar words must be written as \lexeme{...}.
RESERVED_SURFACES = {"and", "or", "if", "then", "for", "every", "there", "exists", "such",
                     "that", "implies"}
# Binder names that an applied core entry binds implicitly; a user binder with the
# same name is captured by LexLean's interface probe (observed with `a` of `eq`).
RESERVED_BINDERS = {"a"}


class Unsupported(Exception):
    pass


# --- term AST -------------------------------------------------------------

@dataclass
class Term:
    """An LSE term: (qid, args) application, a local, or a numeral."""
    kind: str                      # "app" | "local" | "nat" | "pi" | "lam" | "sort"
    head: str = ""                 # qid for app, name for local, digits for nat
    args: list = field(default_factory=list)
    binders: list = field(default_factory=list)   # [(name, Term)] for pi / lam
    body: "Term | None" = None

    def lse(self):
        if self.kind == "local":
            return ["local", self.head]
        if self.kind == "nat":
            return ["nat", self.head]
        if self.kind == "sort":
            return ["sort", "prop"]
        if self.kind == "app":
            node = ["const", self.head]
            return ["app", node, *[a.lse() for a in self.args]] if self.args else node
        groups = [["explicit", n, t.lse()] for n, t in self.binders]
        return [self.kind, groups, self.body.lse()]


class Converter:
    def __init__(self, lexicon: Lexicon, target_package: str):
        self.lx = lexicon
        self.target = target_package
        self.visible = lexicon.visible_from(target_package)
        self.used: set[str] = set()
        self.rename: list[tuple[str, str]] = []
        self.bound: set[str] = set()
        self.hyp_counter = 0
        self.has_numeral = False
        self.sorts: dict[str, str] = {}   # binder name -> sort qid (nat/int/bool)

    # ---- Lean s-expression -> Term ----
    def term(self, node):
        if not self.rename and not self.bound:
            # LexLean's probe ascribes a numeral under `=` with eq's implicit binder `a`;
            # a user binder `a` is then captured. Rename it only in that situation.
            self.has_numeral = _numeral_under_eq(node)
        return self._term(node)

    def _term(self, node):
        if isinstance(node, list):
            tag = node[0]
            if tag == "local":
                for raw, new in reversed(self.rename):
                    if raw == node[1]:
                        return Term("local", new)
                return Term("local", node[1])
            if tag == "nat":
                return Term("nat", node[1])
            if tag == "sort":
                if node[1] in ("0", "Prop"):
                    return Term("sort")
                raise Unsupported(f"type-level sort {node[1]} is not a proposition")
            if tag == "const":
                return self.const(node[1], [])
            if tag == "app":
                head = node[1]
                args = node[2:]
                if sexpr.const_name(head) is not None:
                    return self.const(sexpr.const_name(head), args)
                raise Unsupported(f"application of a non-constant head: {sexpr.dumps(head)[:60]}")
            if tag == "pi":
                return self.pi(node)
            if tag == "lam":
                _, name, ty, body = node
                t = self._term(ty)
                new = self.binder_name(name, False)
                self.rename.append((name, new))
                self.bound.add(new)
                if t.kind == "app" and t.head in SORT_WORD:
                    self.sorts[new] = t.head
                out = Term("lam", binders=[(new, t)], body=self._term(body))
                self.rename.pop()
                return out
        raise Unsupported(f"cannot translate {sexpr.dumps(node)[:80]}")

    def binder_name(self, raw, is_hyp):
        """A legal, unambiguous LexLean binder name."""
        name = raw
        if "._@" in name or name == "[anonymous]" or not name:
            name = None
        else:
            name = name.replace("'", "prime").lstrip("_")
            name = re.sub(r"[^A-Za-z0-9]", "", name)
        if not name:
            self.hyp_counter += 1
            name = f"h{self.hyp_counter}"
        if name in RESERVED_BINDERS and self.has_numeral:
            name += "0"
        while name in self.bound:
            name += "0"
        return name

    def pi(self, node):
        """Flatten a binder chain into variable binders then hypothesis binders."""
        vars_, hyps = [], []
        cur = node
        while isinstance(cur, list) and cur[0] == "pi":
            _, kind, name, ty, body = cur
            if kind != "explicit":
                raise Unsupported(f"{kind} binder `{name}` cannot be stated in LexLean; make it explicit")
            t = self._term(ty)
            is_var = t.kind == "app" and t.head in SORT_WORD and not t.args
            new = self.binder_name(name, not is_var)
            self.rename.append((name, new))
            self.bound.add(new)
            if is_var:
                self.sorts[new] = t.head
                if hyps:
                    raise Unsupported(f"variable `{name}` is bound after a hypothesis; reorder binders")
                vars_.append((new, t))
            else:
                hyps.append((new, t))
            cur = body
        body = self._term(cur)
        for _ in range(len(vars_) + len(hyps)):
            self.rename.pop()
        if hyps:
            body = Term("pi", binders=hyps, body=body)
        if vars_:
            body = Term("pi", binders=vars_, body=body)
        return body

    def const(self, name, args):
        if name == "OfNat.ofNat":
            # OfNat.ofNat τ (nat n) inst
            lit = args[1]
            if isinstance(lit, list) and lit[0] == "nat":
                return Term("nat", lit[1])
            raise Unsupported("non-literal OfNat")
        if name in SORT_LEAN and not args:
            return Term("app", SORT_LEAN[name])
        if name == "Nat.zero" and not args:
            return Term("nat", "0")
        if name in CORE:
            # Eq α a b ; And a b ; ...
            payload = args[1:] if name == "Eq" else args
            return Term("app", CORE[name], [self._term(a) for a in payload])
        if name == "Ne":
            return Term("app", "lexlean.core::lnot",
                        [Term("app", "lexlean.core::eq", [self._term(a) for a in args[1:]])])
        if name == "Exists":
            lam = args[1]
            if not (isinstance(lam, list) and lam[0] == "lam"):
                raise Unsupported("existential without a literal binder")
            return Term("app", "lexlean.core::exists-op", [self._term(lam)])
        if name in HOPS:
            carrier = sexpr.const_name(args[0])
            under = HOPS[name].get(carrier)
            if under is None:
                raise Unsupported(f"{name} over {carrier}")
            # H-class: α β γ inst a b ; LE/LT: α inst a b ; Neg: α inst a
            n_type = {"LE.le": 1, "LT.lt": 1, "Neg.neg": 1}.get(name, 3)
            payload = args[n_type + 1:]
            return self.lexeme(under, payload, name)
        name = ALIASES.get(name, name)
        if name in DEFEQ and self.lx.for_lean(DEFEQ[name]) is not None:
            return self.lexeme(DEFEQ[name], args, name)
        return self.lexeme(name, args, name)

    def lexeme(self, lean_name, args, shown):
        entry = self.lx.for_lean(lean_name, self.visible)
        if entry is None:
            hint = HINTS.get(shown) or HINTS.get(lean_name)
            msg = f"no lexeme denotes `{shown}`"
            if hint:
                msg += f"; {hint}"
            else:
                cands = [e.qid for e in self.lx.entries.values()
                         if e.lean_name and e.lean_name.split(".")[-1].lower() ==
                         lean_name.split(".")[-1].lower()]
                if cands:
                    msg += f"; similar: {', '.join(cands[:4])}"
            raise Unsupported(msg)
        if entry.package not in self.visible and entry.project != "builtin":
            raise Unsupported(f"`{entry.qid}` is not visible from {self.target} "
                              f"(imports: {sorted(self.visible)})")
        if entry.arity != len(args):
            raise Unsupported(f"`{entry.qid}` takes {entry.arity} arguments, got {len(args)}")
        self.used.add(entry.qid)
        return Term("app", entry.qid, [self._term(a) for a in args])

    # ---- Term -> Lean probe type ----
    def lean_type(self, t: Term):
        return self._lean(t, 0)

    def _lean(self, t, depth):
        if t.kind == "local":
            return t.head
        if t.kind == "nat":
            return t.head
        if t.kind == "sort":
            return "Prop"
        if t.kind in ("pi", "lam"):
            bs = " ".join(f"({n} : {self._lean(ty, depth)})" for n, ty in t.binders)
            arrow = "∀ " + bs + ", " if t.kind == "pi" else "fun " + bs + " => "
            return "(" + arrow + self._lean(t.body, depth) + ")"
        e = self.lx.get(t.head)
        lean = {"lexlean.core::eq": "Eq", "lexlean.core::land": "And", "lexlean.core::lor": "Or",
                "lexlean.core::iff": "Iff", "lexlean.core::lnot": "Not",
                "lexlean.core::exists-op": "Exists"}.get(t.head) or e.lean_name
        if not t.args:
            return lean
        return "(" + lean + " " + " ".join(self._lean(a, depth + 1) for a in t.args) + ")"

    # ---- Term -> controlled English ----
    def statement(self, t: Term):
        return self._prop(t, top=True, spine=True)

    def _prop(self, t, top, spine=False):
        """Controlled English. `spine`: the proposition is a step of the statement's
        own if/then chain; a hypothesis implication off the spine is a math arrow."""
        if t.kind == "pi":
            if all(ty.kind == "app" and ty.head in SORT_WORD for _, ty in t.binders):
                lead = "For every " if top else "for every "
                names = " and ".join(f"{SORT_WORD[ty.head]} \\({n}\\)" for n, ty in t.binders)
                return lead + names + ", " + self._prop(t.body, False, True)
            if not spine and not self._quantified(t):
                return "\\(" + self.math(t) + "\\)"
            out = ""
            for _, ty in t.binders:
                out += "if " + self._prop(ty, False, True) + ", then "
            return out + self._prop(t.body, False, True)
        if t.kind == "app" and t.head == "lexlean.core::exists-op":
            lam = t.args[0]
            (n, ty), = lam.binders
            word = SORT_WORD.get(ty.head)
            if word is None:
                raise Unsupported("existential over a non-basic type")
            art = "an" if word[0] in "aeiou" else "a"
            return f"there exists {art} {word} \\({n}\\) such that " + self._prop(lam.body, False, True)
        if t.kind == "app" and t.head == "lexlean.core::lnot" and self._quantified(t.args[0]):
            return "not " + self._prop(t.args[0], False, True)
        if t.kind == "app" and t.head == "lexlean.core::land" and any(self._quantified(a) for a in t.args):
            return " and ".join(self._prop(a, False, True) for a in t.args)
        return "\\(" + self.math(t) + "\\)"

    def _quantified(self, t):
        """Needs prose: binds a variable somewhere outside a math island."""
        if t.kind == "pi":
            return any(ty.kind == "app" and ty.head in SORT_WORD for _, ty in t.binders) or \
                any(self._quantified(ty) for _, ty in t.binders) or self._quantified(t.body)
        if t.kind == "app" and t.head == "lexlean.core::exists-op":
            return True
        return t.kind == "app" and t.head in ("lexlean.core::lnot", "lexlean.core::land") \
            and any(self._quantified(a) for a in t.args)

    def math(self, t: Term, parent=None, side=None):
        if t.kind == "local":
            return t.head
        if t.kind == "nat":
            return t.head
        if t.kind in ("pi", "lam", "sort"):
            raise Unsupported("binder inside a math island")
        e = self.lx.get(t.head)
        if e.frame == "atom" or not t.args:
            return e.surface
        if e.frame == "call":
            return e.surface + "(" + ", ".join(self.math(a) for a in t.args) + ")"
        if e.frame == "prefix":
            a = t.args[0]
            inner = self.math(a)
            if self._compound(a):
                inner = "(" + inner + ")"
            return f"{e.surface} {inner}"
        if e.frame == "infix":
            l, r = t.args
            ls, rs = self.math(l, e, "left"), self.math(r, e, "right")
            return f"{ls} {e.surface} {rs}" if not self._needs(l, e, "left") or True else ""
        raise Unsupported(f"frame {e.frame} of {e.qid}")

    def sort_of(self, t):
        """The carrier of a term: a sort qid, or None when unknown (a numeral)."""
        if t.kind == "local":
            return self.sorts.get(t.head)
        if t.kind == "nat":
            return None
        if t.kind == "app":
            e = self.lx.get(t.head)
            if e and e.signature:
                node = sexpr.parse(e.signature)
                while isinstance(node, list) and node and node[0] == "pi":
                    node = node[2]
                return sexpr.const_name(node)
        return None

    def _is_nat_eq(self, eq):
        a, b = (self.sort_of(x) for x in eq.args)
        return {a, b} <= {"lexlean.std.nat::nat", None} and (a or b) is not None

    def _compound(self, t):
        return t.kind == "app" and bool(t.args) and self.lx.get(t.head).frame in ("infix", "prefix")

    def _needs(self, child, parent, side):
        return False

    def math_child(self, child, parent, side):
        s = self.math(child)
        if child.kind == "pi":
            return "(" + s + ")"
        if child.kind != "app" or not child.args:
            return s
        if child.head == "lexlean.core::lnot" and child.args[0].kind == "app" \
                and child.args[0].head == "lexlean.core::eq" and self._is_nat_eq(child.args[0]):
            ce = _NE
        else:
            ce = self.lx.get(child.head)
        if ce.frame not in ("infix", "prefix"):
            return s
        cp, pp = ce.precedence or 0, parent.precedence or 0
        if cp > pp:
            return s
        if cp == pp and ce.associativity == parent.associativity and side == parent.associativity \
                and parent.associativity in ("left", "right"):
            return s
        return "(" + s + ")"


def _patch_math(cls):
    """Infix rendering with precedence-aware parentheses (kept out of the main
    method body for readability)."""
    def math(self, t, parent=None, side=None):
        if t.kind == "local" or t.kind == "nat":
            return t.head
        if t.kind == "pi":
            if any(ty.kind == "app" and ty.head in SORT_WORD for _, ty in t.binders):
                raise Unsupported("quantifier inside a math island")
            parts = [self.math_child(ty, _ARROW, "left") for _, ty in t.binders]
            return " → ".join(parts + [self.math_child(t.body, _ARROW, "right")])
        if t.kind in ("lam", "sort"):
            raise Unsupported("binder inside a math island")
        if t.kind == "app" and t.head == "lexlean.core::lnot" and t.args[0].kind == "app" \
                and t.args[0].head == "lexlean.core::eq" and self._is_nat_eq(t.args[0]):
            l, r = t.args[0].args
            ne = _NE
            return f"{self.math_child(l, ne, 'left')} ≠ {self.math_child(r, ne, 'right')}"
        e = self.lx.get(t.head)
        if e is None or e.surface is None:
            raise Unsupported(f"`{t.head}` has no math surface; it cannot appear in a statement")
        if e.frame == "atom" or not t.args:
            return e.surface
        surface = f"\\lexeme{{{e.qid}}}" if e.surface in RESERVED_SURFACES else e.surface
        if e.frame == "call":
            return surface + "(" + ", ".join(self.math(a) for a in t.args) + ")"
        if e.frame == "prefix":
            a = t.args[0]
            inner = self.math(a)
            return f"{surface} ({inner})" if self._compound(a) else f"{surface} {inner}"
        if e.frame == "infix":
            l, r = t.args
            return f"{self.math_child(l, e, 'left')} {e.surface} {self.math_child(r, e, 'right')}"
        raise Unsupported(f"frame {e.frame} of {e.qid}")
    cls.math = math


_patch_math(Converter)

from .lexicon import Entry as _Entry
_ARROW = _Entry("->", "infix-function", "infix", 2, "→", 25, "right")
_NE = _Entry("lexlean.core::ne", "infix-predicate", "infix", 2, "≠", 50, "none")


def _numeral_under_eq(node):
    if not isinstance(node, list):
        return False
    if sexpr.is_app(node, "Eq") and any(sexpr.is_app(a, "OfNat.ofNat") for a in node[2:]):
        return True
    return any(_numeral_under_eq(x) for x in node)


def variables(t: Term):
    """The theorem's surface arguments: its leading variable binders."""
    if t.kind == "pi" and all(ty.kind == "app" and ty.head in SORT_WORD for _, ty in t.binders):
        return [n for n, _ in t.binders]
    return []
