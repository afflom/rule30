import Rule30PrizeKit
-- Fails: `problem1` is added without kernel checking, with `True.intro` as its "proof". Its axiom
-- list is empty, so an axiom audit alone would accept it; only the kernel replay rejects it.
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `Rule30Submission.problem1, levelParams := [],
  type := mkConst ``Ruliology.CellularAutomata.Rule30Prize.Problem1,
  value := mkConst ``True.intro }
