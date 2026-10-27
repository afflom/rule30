import Lean.CoreM
import Lean.Replay
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
# The Rule 30 Prize submission checker

```
lake build Rule30Submission
lake env lean --run Check.lean Rule30Submission --claim problem1
lake env lean --run Check.lean Rule30Submission --claim partial --headline Rule30Submission.no_period_one
```

It reads the compiled module (its `.olean` must be on `LEAN_PATH`, which `lake env` sets) and checks
three things.

1. **Kernel replay.** Every constant the module declares goes through the kernel again, in an
   environment built only from the module's imports. This is the check `leanchecker` does. It catches
   declarations that were added without type checking, for example under `debug.skipKernelTC`, which
   an axiom audit alone does not see.
2. **Statement.** The headline theorem has exactly the official type, as an expression, not just up to
   definitional unfolding, and its `Problem1` or `Problem2` is the kit's. Every submission must import
   the statement module `Ruliology.CellularAutomata.Rule30Prize` (`Rule30PrizeKit` does), so it
   cannot declare a `Problem1` of its own under the official name:

   | `--claim`      | theorem                         | type                                               |
   |----------------|---------------------------------|----------------------------------------------------|
   | `problem1`     | `Rule30Submission.problem1`     | `Ruliology.CellularAutomata.Rule30Prize.Problem1`   |
   | `not_problem1` | `Rule30Submission.not_problem1` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem1` |
   | `problem2`     | `Rule30Submission.problem2`     | `Ruliology.CellularAutomata.Rule30Prize.Problem2`   |
   | `not_problem2` | `Rule30Submission.not_problem2` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem2` |
   | `partial`      | each `--headline` name          | any type: a person reviews what it says            |

3. **Axioms.** Each headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
   This rules out `sorryAx`, `Lean.ofReduceBool` and `Lean.trustCompiler` (from `native_decide`), and
   any new `axiom`.

It prints one JSON object, and exits with 0 when the claim verifies, 1 when it does not, and 2 on bad
usage. The import closure is trusted: the kit, `lean/`, `equivalents/` and Mathlib. The `.olean`
file is trusted to be well formed, as with `leanchecker`, so run untrusted builds in a sandbox.
-/

open Lean

namespace Rule30Check

/-- The axioms a verified theorem may use. -/
def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def problem1 : Expr := .const `Ruliology.CellularAutomata.Rule30Prize.Problem1 []
def problem2 : Expr := .const `Ruliology.CellularAutomata.Rule30Prize.Problem2 []
def mkNotExpr (p : Expr) : Expr := .app (.const `Not []) p

/-- The module that states the problems. -/
def statementModule : Name := `Ruliology.CellularAutomata.Rule30Prize

/-- Whether the constant `c` was imported from the statement module, rather than declared by the
module under check. -/
def fromStatementModule (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c, env.getModuleIdx? statementModule with
  | some i, some j => i == j
  | _, _ => false

/-- The claims with an official statement: claim, theorem name, expected type. -/
def officialTargets : List (String × Name × Expr) :=
  [("problem1", `Rule30Submission.problem1, problem1),
   ("not_problem1", `Rule30Submission.not_problem1, mkNotExpr problem1),
   ("problem2", `Rule30Submission.problem2, problem2),
   ("not_problem2", `Rule30Submission.not_problem2, mkNotExpr problem2)]

/-- Remove metadata annotations, which the kernel ignores too. -/
partial def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n t b bi => .lam n (stripMData t) (stripMData b) bi
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i e => .proj s i (stripMData e)
  | e => e

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

/-- The axioms `n` depends on, as `#print axioms` reports them. -/
def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (collectAxioms n : ReaderT Environment Id (Array Name)).run env

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/--
Replay the constants of `module` into an environment made from its imports, as `leanchecker` does.
Returns that environment and the module's constants.
-/
unsafe def replayModule (module : Name) : IO (Environment × Std.HashMap Name ConstantInfo) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  -- The last ("most private") part subsumes the others.
  for name in parts[parts.size - 1].1.constNames, ci in parts[parts.size - 1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  return (env', newConstants)

/-- Check one headline theorem. `expected? = none` accepts any statement (partial results). -/
def checkTheorem (env : Environment) (mine : Std.HashMap Name ConstantInfo) (n : Name)
    (expected? : Option Expr) : Json × Bool :=
  -- Replayed constants live in the kernel environment, which `Environment.find?` does not search.
  match mine.get? n, env.toKernelEnv.find? n with
  | none, _ =>
    (Json.mkObj [("name", toJson n.toString), ("found", false),
      ("problem", toJson s!"the module declares no constant {n}")], false)
  | some _, none =>
    (Json.mkObj [("name", toJson n.toString), ("found", false),
      ("problem", toJson s!"{n} did not survive the kernel replay")], false)
  | some _, some ci =>
    let isThm := ci matches .thmInfo _
    let monomorphic := ci.levelParams.isEmpty
    let typeOk := match expected? with
      | some e => stripMData ci.type == e
      | none => true
    -- The official constants in the type must be the statement module's. `Not` is Init's: a module
    -- that imports the statement module cannot declare another.
    let foreign := match expected? with
      | some e => e.getUsedConstants.filter fun c => c != ``Not && !fromStatementModule env c
      | none => #[]
    let axs := axiomsOf env n
    let bad := axs.filter (fun a => !standardAxioms.contains a)
    let ok := isThm && monomorphic && typeOk && foreign.isEmpty && bad.isEmpty
    let problems : List String :=
      (if isThm then [] else [s!"{n} is a {kindOf ci}, not a theorem"]) ++
      (if monomorphic then [] else [s!"{n} has universe parameters"]) ++
      (if typeOk then [] else [s!"{n} does not have the official type"]) ++
      (if foreign.isEmpty then [] else
        [s!"{n} states {foreign.toList} from the module itself, not from {statementModule}"]) ++
      (if bad.isEmpty then [] else [s!"{n} uses non-standard axioms: {bad.toList}"])
    (Json.mkObj [("name", toJson n.toString), ("found", true), ("kind", toJson (kindOf ci)),
      ("typeMatches", toJson (typeOk && foreign.isEmpty)), ("axioms", toJson (axs.map (·.toString))),
      ("ok", toJson ok), ("problems", toJson problems)], ok)

structure Args where
  module : Name := .anonymous
  claim : String := "auto"
  headlines : Array Name := #[]

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--claim" :: c :: rest, a => parseArgs rest { a with claim := c }
  | "--headline" :: h :: rest, a => parseArgs rest { a with headlines := a.headlines.push h.toName }
  | s :: rest, a =>
    if s.startsWith "-" then .error s!"unknown flag {s}"
    else if a.module.isAnonymous then parseArgs rest { a with module := s.toName }
    else .error s!"unexpected argument {s}"

unsafe def run (args : Args) : IO UInt32 := do
  let claims := ["auto", "partial"] ++ officialTargets.map (·.1)
  unless claims.contains args.claim do
    IO.eprintln s!"--claim must be one of {claims}"
    return 2
  let replayed ← try
      pure (Except.ok (← replayModule args.module))
    catch e => pure (Except.error e.toString)
  match replayed with
  | .error msg =>
    IO.println <| Json.compress <| Json.mkObj [("module", toJson args.module.toString),
      ("claim", toJson args.claim), ("replay", Json.mkObj [("ok", false), ("error", toJson msg)]),
      ("verdict", "fail"), ("reasons", toJson [s!"kernel replay failed: {msg}"])]
    return 1
  | .ok (env, mine) =>
    -- Every official target the module declares, whatever the claim.
    let mut official : Array Json := #[]
    let mut passed : Array String := #[]
    for (claim, n, e) in officialTargets do
      if mine.contains n then
        let (j, ok) := checkTheorem env mine n (some e)
        official := official.push (j.setObjVal! "claim" (toJson claim))
        if ok then passed := passed.push claim
    let headlines ← args.headlines.mapM fun n => pure (checkTheorem env mine n none)
    -- Everything the module declares, for the reviewer.
    let declared := (mine.toArray.filter (fun (n, _) => !n.isInternal)).qsort
      (fun a b => Name.lt a.1 b.1) |>.map fun (n, ci) =>
        let axs := axiomsOf env n
        Json.mkObj [("name", toJson n.toString), ("kind", toJson (kindOf ci)),
          ("standardAxioms", toJson (axs.all standardAxioms.contains))]
    let newAxioms := mine.toArray.filterMap fun (n, ci) =>
      if ci matches .axiomInfo _ then some n.toString else none
    let inconsistent := (passed.contains "problem1" && passed.contains "not_problem1") ||
      (passed.contains "problem2" && passed.contains "not_problem2")
    -- Partial results too must be about the official definitions.
    let importsStatements := (env.getModuleIdx? statementModule).isSome
    let (ok, reasons) : Bool × List String :=
      if !importsStatements then
        (false, [s!"the module does not import {statementModule}, the official statements: import Rule30PrizeKit"])
      else if inconsistent then
        (false, ["the module proves a statement and its negation: the environment is inconsistent"])
      else match args.claim with
      | "auto" =>
        if passed.isEmpty then (false, ["no official target verified"]) else (true, [])
      | "partial" =>
        if args.headlines.isEmpty then (false, ["--claim partial needs at least one --headline"])
        else if headlines.all (·.2) then (true, [])
        else (false, ["a headline theorem did not verify"])
      | c =>
        if passed.contains c then (true, [])
        else (false, [s!"the claimed target {c} did not verify"])
    IO.println <| Json.compress <| Json.mkObj [
      ("module", toJson args.module.toString), ("claim", toJson args.claim),
      ("replay", Json.mkObj [("ok", true), ("constants", toJson mine.size)]),
      ("importsStatements", toJson importsStatements),
      ("official", Json.arr official), ("verifiedTargets", toJson passed),
      ("headlines", Json.arr (headlines.map (·.1))), ("newAxioms", toJson newAxioms),
      ("declared", Json.arr declared),
      ("verdict", toJson (if ok then "pass" else "fail")), ("reasons", toJson reasons)]
    return if ok then 0 else 1

end Rule30Check

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match Rule30Check.parseArgs args {} with
  | .error msg =>
    IO.eprintln msg
    return 2
  | .ok a =>
    if a.module.isAnonymous then
      IO.eprintln "usage: lean --run Check.lean MODULE [--claim C] [--headline NAME]..."
      return 2
    Rule30Check.run a
