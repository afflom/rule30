import Lean
open Lean

/-!
# The declaration stream of research modules

Run from `rule30-core-lean`:

    lake env lean --run scripts/KappaExport.lean Rule30UOR.KernelParity ...

For each module this prints, on stdout, the declarations the kernel replays
(the constants of the module's most private `.olean` part, exactly the set
`leanchecker` replays) as a stream of canonical S-expressions (Rivest 1997
§4.3: atoms `<n>:<bytes>`, lists with single spaces). `scripts/kappa_research.py`
documents the profile and computes the κ-labels from this stream; nothing
here hashes.

The stream encodes `Level` and `Expr` terms as a DAG with explicit sharing:
every distinct subterm is emitted once as `(node <id> <ctor> <fields...>
<child ids...>)` in post-order, and a declaration refers to its type and value
by id. `mdata` is transparent (the inner expression's id is reused), binder
names are not emitted (bound variables are de Bruijn indices), and free or
meta variables are an error: a closed declaration has none.

The constants are read from the named modules' object files. The environment of
those modules is imported once, only to ask Lean which theorems someone wrote: a
theorem with a declaration range (`declRangeExt`, the source position Lean records
for every declaration it elaborates from source) is marked `(authored)`; a lemma
Lean generated (equation lemmas, functional induction, auxiliary proofs, matcher
equations) has none. The redundancy check counts authored theorems only, by this
mark and never by their names. The mark is not part of any κ-label.
-/

namespace KappaExport

def atom (s : String) : String := s!"{s.utf8ByteSize}:{s}"
def natAtom (n : Nat) : String := atom (toString n)
def nameAtom (n : Name) : String := atom n.toString
def lst (xs : List String) : String := "(" ++ " ".intercalate xs ++ ")"
def flag (b : Bool) : String := atom (if b then "1" else "0")

structure St where
  -- keyed by structural equality (`Expr.equal` compares binder info, which `Expr`'s own `BEq`
  -- ignores): a node is shared only with a node that prints the same
  exprIds : Std.HashMap ExprStructEq Nat := {}
  levelIds : Std.HashMap Level Nat := {}
  next : Nat := 0
  buf : String := ""

abbrev M := StateRefT St IO

def flush : M Unit := do
  let s ← get
  (← IO.getStdout).putStr s.buf
  set { s with buf := "" }

def emit (line : String) : M Unit := do
  modify fun s => { s with buf := s.buf ++ line ++ "\n" }
  if (← get).buf.utf8ByteSize > 4000000 then flush

def node (ctor : String) (fields : List String) (children : List Nat) : M Nat := do
  let id := (← get).next
  modify fun s => { s with next := id + 1 }
  emit (lst ([atom "node", natAtom id, atom ctor] ++ fields ++ children.map natAtom))
  return id

partial def visitLevel (l : Level) : M Nat := do
  if let some id := (← get).levelIds[l]? then return id
  let id ← match l with
    | .zero => node "lzero" [] []
    | .succ u => do let a ← visitLevel u; node "lsucc" [] [a]
    | .max u v => do let a ← visitLevel u; let b ← visitLevel v; node "lmax" [] [a, b]
    | .imax u v => do let a ← visitLevel u; let b ← visitLevel v; node "limax" [] [a, b]
    | .param n => node "lparam" [nameAtom n] []
    | .mvar _ => throw <| IO.userError "universe metavariable in a closed declaration"
  modify fun s => { s with levelIds := s.levelIds.insert l id }
  return id

def binderAtom : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def children : Expr → List Expr
  | .app f a => [f, a]
  | .lam _ t b _ => [t, b]
  | .forallE _ t b _ => [t, b]
  | .letE _ t v b _ => [t, v, b]
  | .mdata _ b => [b]
  | .proj _ _ b => [b]
  | _ => []

/-- Post-order emission of every subterm of `root` not yet emitted; an explicit
stack, so the depth of a proof term is never the depth of the C stack. -/
def visitExpr (root : Expr) : M Nat := do
  let mut stack : List (Expr × Bool) := [(root, false)]
  repeat
    match stack with
    | [] => break
    | (e, expanded) :: rest =>
      stack := rest
      if (← get).exprIds.contains ⟨e⟩ then continue
      if !expanded then
        stack := (children e).map (·, false) ++ (e, true) :: stack
        continue
      let ids ← (children e).mapM fun c => do pure (← get).exprIds[(⟨c⟩ : ExprStructEq)]!
      let id ← match e with
        | .bvar i => node "bvar" [natAtom i] []
        | .fvar .. => throw <| IO.userError "free variable in a closed declaration"
        | .mvar .. => throw <| IO.userError "metavariable in a closed declaration"
        | .sort u => do let l ← visitLevel u; node "sort" [] [l]
        | .const n us => do let ls ← us.mapM visitLevel; node "const" [nameAtom n] ls
        | .app .. => node "app" [] ids
        | .lam _ _ _ bi => node "lam" [atom (binderAtom bi)] ids
        | .forallE _ _ _ bi => node "forallE" [atom (binderAtom bi)] ids
        | .letE _ _ _ _ nonDep => node "letE" [flag nonDep] ids
        | .lit (.natVal n) => node "lit" [atom "nat", natAtom n] []
        | .lit (.strVal s) => node "lit" [atom "str", atom s] []
        | .mdata _ b => pure (← get).exprIds[(⟨b⟩ : ExprStructEq)]!
        | .proj s i _ => node "proj" [nameAtom s, natAtom i] ids
      modify fun s => { s with exprIds := s.exprIds.insert ⟨e⟩ id }
  return (← get).exprIds[(⟨root⟩ : ExprStructEq)]!

def safetyAtom : DefinitionSafety → String
  | .safe => "safe"
  | .unsafe => "unsafe"
  | .partial => "partial"

def unsafeAtom (b : Bool) : String := if b then "unsafe" else "safe"

def quotAtom : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def safety (s : String) : String := lst [atom "safety", atom s]
def count (label : String) (n : Nat) : String := lst [atom label, natAtom n]
def names (label : String) (ns : List Name) : String := lst (atom label :: ns.map nameAtom)

def emitDecl (isAuthored : Name → Bool) (ci : ConstantInfo) : M Unit := do
  let t ← visitExpr ci.type
  let (kind, value, extras) ← match ci with
    | .axiomInfo i => pure ("axiom", none, [safety (unsafeAtom i.isUnsafe)])
    | .defnInfo i => do
      let v ← visitExpr i.value
      pure ("def", some v, [safety (safetyAtom i.safety)])
    | .thmInfo i => do
      let v ← visitExpr i.value
      pure ("thm", some v, if isAuthored ci.name then [lst [atom "authored"]] else [])
    | .opaqueInfo i => do
      let v ← visitExpr i.value
      pure ("opaque", some v, [safety (unsafeAtom i.isUnsafe)])
    | .quotInfo i => pure ("quot", none, [lst [atom "kind", atom (quotAtom i.kind)]])
    | .inductInfo i => pure ("induct", none,
      [count "params" i.numParams, count "indices" i.numIndices, names "ctors" i.ctors,
       names "all" i.all, count "nested" i.numNested, safety (unsafeAtom i.isUnsafe)])
    | .ctorInfo i => pure ("ctor", none,
      [lst [atom "induct", nameAtom i.induct], count "cidx" i.cidx, count "params" i.numParams,
       count "fields" i.numFields, safety (unsafeAtom i.isUnsafe)])
    | .recInfo i => do
      let rules ← i.rules.mapM fun r => do
        let rhs ← visitExpr r.rhs
        pure (lst [atom "rule", nameAtom r.ctor, natAtom r.nfields, natAtom rhs])
      pure ("rec", none,
        [names "all" i.all, count "params" i.numParams, count "indices" i.numIndices,
         count "motives" i.numMotives, count "minors" i.numMinors, lst (atom "rules" :: rules),
         lst [atom "k", flag i.k], safety (unsafeAtom i.isUnsafe)])
  let levels := lst (atom "levels" :: ci.levelParams.map nameAtom)
  emit (lst ([atom "decl", nameAtom ci.name, atom kind, levels, natAtom t,
              value.elim "()" natAtom] ++ extras))

/-- The parts of a module's object file, chosen as `leanchecker` chooses them:
the last ("most private") part holds every constant the kernel replays. -/
def exportModule (isAuthored : Name → Bool) (mod : Name) : IO Unit := do
  let mFile ← findOLean mod
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {mod} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError s!"failed to read module data of {mod}" else
  let (data, _) := parts[parts.size - 1]
  let act : M Unit := do
    emit (lst [atom "module", nameAtom mod, count "constants" data.constants.size])
    for ci in data.constants do
      emitDecl isAuthored ci
    emit (lst [atom "end", nameAtom mod])
    flush
  act.run' {}

end KappaExport

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run scripts/KappaExport.lean <module names>"
    return 2
  let mods := args.map (·.toName)
  if let some bad := args.find? (·.toName.isAnonymous) then
    throw <| IO.userError s!"not a module name: {bad}"
  let env ← importModules (mods.toArray.map fun m => { module := m }) {}
  -- authored: Lean recorded where in the source the declaration was written
  let isAuthored := fun n => (declRangeExt.find? env n).isSome
  for mod in mods do
    KappaExport.exportModule isAuthored mod
  return 0
