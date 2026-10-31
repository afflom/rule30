import Rule30UOR.CentralCollision
import Rule30UOR.Collision
import Rule30UOR.CompilePoints
import Rule30UOR.Constructive
import Rule30UOR.KitConstructive
import Rule30UOR.Core
import Rule30UOR.DefectFront
import Rule30UOR.DefectSource
import Rule30UOR.Fixed
import Rule30UOR.Frontier
import Rule30UOR.Intent
import Rule30UOR.Interfaces
import Rule30UOR.Interfaces.Part01
import Rule30UOR.Interfaces.Part02
import Rule30UOR.Interfaces.Part03
import Rule30UOR.Interfaces.Part04
import Rule30UOR.Interfaces.Part05
import Rule30UOR.Interfaces.Part06
import Rule30UOR.Interfaces.Part07
import Rule30UOR.Interfaces.Part08
import Rule30UOR.Interfaces.Part09
import Rule30UOR.Interfaces.Part10
import Rule30UOR.Interfaces.Part11
import Rule30UOR.Interfaces.Part12
import Rule30UOR.Interfaces.Part13
import Rule30UOR.Interfaces.Part14
import Rule30UOR.Interfaces.Part15
import Rule30UOR.Interfaces.Part16
import Rule30UOR.Interfaces.Part17
import Rule30UOR.Kit
import Rule30UOR.MaskedObservation
import Rule30UOR.Project
import Rule30UOR.Rational
import Rule30UOR.Right
import Rule30UOR.Scale
import Rule30UOR.TemporalDefect
import Rule30UOR.WittDefect
import Rule30UOR.ZeroDiagonals
import Rule30UOR.Horizon
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Fail, rather than merely print, if a research theorem depends on an unapproved axiom.
Run from rule30-core-lean after lake build:
  lake env lean scripts/CheckResearchAxioms.lean
-/

elab "#check_research_axioms" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let audits : Array Name := #[
    ``Rule30UOR.Interfaces.lhBandAgree_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.prefix_tail_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.late_scale_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.single_row_zero_diag_succ_engine_hypotheses_unsat,
    ``Rule30UOR.Interfaces.engine_input_iff_not_centerPeriodic,
    ``Rule30UOR.Interfaces.problem1_iff_engine_input]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if (`Rule30UOR).isPrefixOf name then
      if let .thmInfo _ := info then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "{name} depends on unapproved axiom {axiomName}"
        checked := checked + 1
  unless checked > audits.size do
    throwError "Rule30UOR theorems were not found"
  logInfo m!"Checked {checked} research theorems; all axioms are in propext, Quot.sound."

#check_research_axioms
