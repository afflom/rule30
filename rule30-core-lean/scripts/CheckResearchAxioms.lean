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
import Rule30UOR.LeftCone
import Rule30UOR.Ledger
import Rule30UOR.Automatic
import Rule30UOR.Gasket
import Rule30UOR.Rules
import Rule30UOR.EdgeSplit
import Rule30UOR.Routes
import Rule30UOR.EdgeParity
import Rule30UOR.KernelParity
import Rule30UOR.Intersection
import Rule30UOR.Band
import Rule30UOR.StableKernel
import Rule30UOR.DyadicRow
import Rule30UOR.LeftBand
import Rule30UOR.KernelLaw
import Rule30UOR.ClassObligation
import Rule30UOR.Antidiagonal
import Rule30UOR.LeftTower
import Rule30UOR.RightPeriods
import Rule30UOR.DiagonalCone
import Rule30UOR.DoublingDepth
import Rule30UOR.ColumnCone
import Rule30UOR.KernelRoot
import Rule30UOR.ResidueJen
import Rule30UOR.TowerBoundary
import Rule30UOR.DrivenLucas
import Rule30UOR.UnitSeedMask
import Rule30UOR.Walled
import Rule30UOR.MaskSlice
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
  -- Every proof is a `theorem`: a definition whose type is a proposition would escape the axiom
  -- audit above and the statement-κ redundancy check of the kernel replay, which label theorems.
  -- Constants are selected by their module, so private declarations are covered too.
  let mut proofDefs : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Rule30UOR).isPrefixOf (env.header.moduleNames[idx.toNat]!) then
        let ty? := match info with
          | .defnInfo d => some d.type
          | .opaqueInfo d => some d.type
          | _ => none
        -- generated declarations are not authored: matchers, recursors (casesOn, recOn, below),
        -- and auxiliary internal details directly under the declaration that generated them
        -- (judged on the user-facing name, so an authored private definition is still covered)
        let user := (privateToUserName? name).getD name
        let generated := user.isInternalDetail && (env.contains name.getPrefix || env.contains user.getPrefix)
        if let some ty := ty? then
          unless generated || Meta.isMatcherCore env name || isAuxRecursor env name do
            if ← liftTermElabM (Meta.isProp ty) then
              proofDefs := proofDefs.push name
  unless proofDefs.isEmpty do
    throwError "research definitions whose type is a proposition (state them as theorems): {proofDefs.toList.take 20}"
  logInfo m!"Checked {checked} research theorems; all axioms are in propext, Quot.sound."

#check_research_axioms
