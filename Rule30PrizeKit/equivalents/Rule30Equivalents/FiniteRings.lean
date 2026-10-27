module

public import Rule30Equivalents.AlgebraicDegree
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Rule 30 on a ring of `n` cells

A configuration of a ring of `n` cells is an `n`-periodic
configuration of `{0,1}^ℤ`, and rule 30 on the ring is rule 30 on such configurations
(`evol_ringSeed_add`). Start from one black cell, `ringSeed n`.

* `evol_ringSeed_eq_center`: **the center of the ring agrees with the center column `c(t)` for
  every `t < n`**. The cell `(t, 0)` sees only the cells `-t, …, t`, and for `t < n` the only black
  one among them is the cell `0` (`AlgebraicDegree.evol_congr`).
* `evol_ringSeed_eq_cell`: the whole light cone `|p| ≤ t` of the ring agrees with the single-seed
  pattern while `2t < n`; later the two sides of the cone meet around the ring.

For `n = 3` the ring's center is `1, 1, 0, 0, …` against `c = 1, 1, 0, 1, …`, so the bound
`t < n` cannot be improved in general.
-/

@[expose] public section

namespace Rule30Equivalents.FiniteRings

open Ruliology.CellularAutomata Rule30Realization

/-- One black cell on a ring of `n` cells: black exactly at the multiples of `n`. -/
def ringSeed (n : ℕ) (p : ℤ) : Bool := decide (p % n = 0)

/-- The evolution of `ringSeed n` stays `n`-periodic: it is rule 30 on the ring. -/
theorem evol_ringSeed_add (n t : ℕ) (p : ℤ) :
    evol (ringSeed n) t (p + n) = evol (ringSeed n) t p :=
  Rule30ZeroBoundaryBarriers.evol_shift_all (x := ringSeed n) (x' := ringSeed n) (d := n)
    (fun q => by simp [ringSeed]) t p

/-- Within distance `n` of the cell `0`, the ring seed is the single seed. -/
theorem ringSeed_eq_seed {n : ℕ} {j : ℤ} (hj : |j| < n) : ringSeed n j = seed j := by
  simp only [ringSeed, seed]
  refine decide_eq_decide.2 ⟨fun h => ?_, fun h => by simp [h]⟩
  exact Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero h) hj

/-- **The center of a ring of `n` cells agrees with the center column for every `t < n`.** -/
theorem evol_ringSeed_eq_center {n t : ℕ} (ht : t < n) :
    evol (ringSeed n) t 0 = Rule30Prize.center t := by
  rw [Rule30Prize.center, ← evol_seed]
  refine AlgebraicDegree.evol_congr t 0 fun j hj1 hj2 => ringSeed_eq_seed ?_
  rw [abs_lt]
  constructor <;> omega

/-- The whole light cone of the ring agrees with the single-seed pattern while `2t < n`. -/
theorem evol_ringSeed_eq_cell {n t : ℕ} (ht : 2 * t < n) {p : ℤ} (hp : |p| ≤ t) :
    evol (ringSeed n) t p = Rule30Jen.cell t p := by
  rw [← evol_seed]
  refine AlgebraicDegree.evol_congr t p fun j hj1 hj2 => ringSeed_eq_seed ?_
  rw [abs_le] at hp
  rw [abs_lt]
  constructor <;> omega

end Rule30Equivalents.FiniteRings
