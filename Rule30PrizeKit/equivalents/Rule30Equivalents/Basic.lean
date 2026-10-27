module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Shared definitions for the equivalent forms of Rule 30 Problem 1

`Problem1` (from the core-Lean snapshot in `../lean`) says that the center column of rule 30,
started from a single black cell, is not eventually periodic:

    Problem1 := ¬ EventuallyPeriodic center
    EventuallyPeriodic f := ∃ T P, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

Each file in this library proves `Problem1 ↔ X` for one reformulation `X`, usually by proving a
general statement about every `b : ℕ → Bool` and then specializing it to the center column `c`.
-/

@[expose] public section

namespace Rule30Equivalents

open Ruliology.CellularAutomata

/-- The center column `c(t)` of rule 30 from a single black cell (`true` = black). -/
abbrev c : Nat → Bool := Rule30Prize.center

/-- Eventual periodicity of a `Bool` sequence, as used by `Problem1`. -/
abbrev EventuallyPeriodic (b : Nat → Bool) : Prop := Rule30Jen.EventuallyPeriodic b

/-- `Problem1` unfolded: the center column is not eventually periodic. -/
theorem problem1_iff : Rule30Prize.Problem1 ↔
    ¬ ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → c (t + P) = c t := Iff.rfl

/-- `Problem1` in terms of `EventuallyPeriodic`. -/
theorem problem1_iff_not_eventuallyPeriodic :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic c := Iff.rfl

end Rule30Equivalents
