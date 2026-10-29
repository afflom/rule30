module

public import Rule30UOR.CentralCollision
public import Rule30UOR.Interfaces

/-!
# Problem 1 frontier equivalences

This module packages the current reduction frontier into exact equivalences:

* `Problem1`
* `NoRowCenterPeriod`
* `Scale.NoPeriod`
* `CentralCollision.NoRecurrentCentralCollision`

No new dynamics are introduced here; this is a composition layer for downstream
closure arguments.
-/

@[expose] public section

namespace Rule30UOR.Frontier

open Ruliology.CellularAutomata Rule30Prize

theorem noPeriod_iff_noRecurrentCentralCollision :
    Rule30UOR.Scale.NoPeriod ↔ Rule30UOR.CentralCollision.NoRecurrentCentralCollision :=
  Rule30UOR.CentralCollision.no_recurrent_central_collision_iff_noPeriod.symm

theorem noRowCenterPeriod_iff_noRecurrentCentralCollision :
    Rule30UOR.Interfaces.NoRowCenterPeriod ↔
      Rule30UOR.CentralCollision.NoRecurrentCentralCollision := by
  rw [← Rule30UOR.Interfaces.problem1_iff_noRowCenterPeriod,
    Rule30UOR.CentralCollision.problem1_iff_no_recurrent_central_collision]

theorem problem1_iff_noRecurrentCentralCollision :
    Problem1 ↔ Rule30UOR.CentralCollision.NoRecurrentCentralCollision :=
  Rule30UOR.CentralCollision.problem1_iff_no_recurrent_central_collision

theorem noPeriod_of_noRecurrentCentralCollision
    (h : Rule30UOR.CentralCollision.NoRecurrentCentralCollision) :
    Rule30UOR.Scale.NoPeriod :=
  noPeriod_iff_noRecurrentCentralCollision.2 h

theorem not_centerPeriodic_of_noRecurrentCentralCollision
    (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.CentralCollision.NoRecurrentCentralCollision) :
    ¬ Rule30UOR.Scale.CenterPeriodic T P :=
  noPeriod_of_noRecurrentCentralCollision h T P hP

theorem not_eventuallyPeriodic_center_of_noRecurrentCentralCollision
    (h : Rule30UOR.CentralCollision.NoRecurrentCentralCollision) :
    ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic
      Ruliology.CellularAutomata.Rule30Prize.center := by
  simpa only [Problem1] using problem1_iff_noRecurrentCentralCollision.2 h

theorem problem1_of_noRecurrentCentralCollision
    (h : Rule30UOR.CentralCollision.NoRecurrentCentralCollision) : Problem1 :=
  problem1_iff_noRecurrentCentralCollision.2 h

theorem noRecurrentCentralCollision_of_problem1
    (h : Problem1) : Rule30UOR.CentralCollision.NoRecurrentCentralCollision :=
  problem1_iff_noRecurrentCentralCollision.1 h

end Rule30UOR.Frontier
