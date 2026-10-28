import Rule30UOR.Interfaces
import Rule30UOR.TemporalDefect
import Rule30UOR.WittDefect
import Rule30UOR.Collision
import Rule30UOR.DefectSource
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Fail, rather than merely print, if a research theorem depends on an unapproved axiom.
Run from rule30-core-lean after lake build:
  lake env lean scripts/CheckResearchAxioms.lean
-/

elab "#check_research_axioms" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let audits : Array Name := #[
    ``Rule30UOR.Interfaces.lhBandAgree_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.prefix_tail_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.late_scale_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.single_row_zero_diag_succ_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.engine_input_iff_not_centerPeriodic,
    ``Rule30UOR.Interfaces.problem1_iff_engine_input]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if audits.contains name || (`Rule30UOR.TemporalDefect).isPrefixOf name ||
        (`Rule30UOR.WittDefect).isPrefixOf name ||
        (`Rule30UOR.Collision).isPrefixOf name || (`Rule30UOR.DefectSource).isPrefixOf name then
      if let .thmInfo _ := info then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "{name} depends on unapproved axiom {axiomName}"
        checked := checked + 1
  unless checked > audits.size do
    throwError "Temporal-defect theorems were not found"
  logInfo m!"Checked {checked} research theorems; all axioms are in propext, Classical.choice, Quot.sound."

#check_research_axioms
