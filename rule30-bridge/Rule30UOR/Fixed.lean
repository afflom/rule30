module

public import Rule30UOR.Right

/-!
# The center as the fixed point of its two halves

Run rule 30 on the left half (`p < 0`) and on the right half (`p > 0`) from the seed's white
halves, each fed at position `0` by a given column `c`: `Lh c` and `Rh c`. The left half sees `c`
only through `c t || ·` (`left_input`); the right half sees it through `xor` (`right_input`).
Recombining the two neighbours of position `0` defines a causal operator

  `Phi c (t + 1) = rule (Lh c t (-1)) (c t) (Rh c t 1)`.

* `center_fixed`: the center column is a fixed point (`center (t + 1) = Phi center (t + 1)`).
* `fixed_unique`: it is the only column with `c 0 = true` that is a fixed point.
* `problem1_iff_no_periodic_fixed`: **Problem 1 holds exactly when `Phi` has no eventually periodic
  fixed point.** Form (the two driven halves) and function (the column they reproduce) meet in one
  equation; nothing of the seed is dropped.
-/

@[expose] public section

namespace Rule30UOR.Fixed

open Ruliology.CellularAutomata Rule30Jen Rule30Prize

/-- The left half driven by `c` from white. -/
def Lh (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then false else c 0
  | t + 1, p => if p < 0 then rule (Lh c t (p - 1)) (Lh c t p) (Lh c t (p + 1)) else c (t + 1)

/-- The right half driven by `c` from white. -/
def Rh (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => if 0 < p then false else c 0
  | t + 1, p => if 0 < p then rule (Rh c t (p - 1)) (Rh c t p) (Rh c t (p + 1)) else c (t + 1)

/-- The recombination of the two halves at position `0`. -/
def Phi (c : Nat → Bool) (t : Nat) : Bool := rule (Lh c t (-1)) (c t) (Rh c t 1)

theorem Lh_center : ∀ t p, p ≤ 0 → Lh center t p = cell t p := by
  intro t
  induction t with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · simp only [Lh, if_pos h, cell]; exact (decide_eq_false (by omega)).symm
    · simp only [Lh, if_neg h]; rw [show p = 0 by omega]; rfl
  | succ t ih =>
    intro p hp
    by_cases h : p < 0
    · simp only [Lh, if_pos h]
      rw [ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]; rfl
    · simp only [Lh, if_neg h]; rw [show p = 0 by omega]; rfl

theorem Rh_center : ∀ t p, 0 ≤ p → Rh center t p = cell t p := by
  intro t
  induction t with
  | zero =>
    intro p hp
    by_cases h : 0 < p
    · simp only [Rh, if_pos h, cell]; exact (decide_eq_false (by omega)).symm
    · simp only [Rh, if_neg h]; rw [show p = 0 by omega]; rfl
  | succ t ih =>
    intro p hp
    by_cases h : 0 < p
    · simp only [Rh, if_pos h]
      rw [ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]; rfl
    · simp only [Rh, if_neg h]; rw [show p = 0 by omega]; rfl

/-- **The center reproduces itself.** -/
theorem center_fixed (t : Nat) : center (t + 1) = Phi center t := by
  show cell (t + 1) 0 = rule (Lh center t (-1)) (center t) (Rh center t 1)
  rw [Lh_center t (-1) (by omega), Rh_center t 1 (by omega)]; rfl

/-- The halves at time `t` depend only on the column up to `t`. -/
theorem Lh_congr {c c' : Nat → Bool} : ∀ t, (∀ k, k ≤ t → c k = c' k) → ∀ p, Lh c t p = Lh c' t p := by
  intro t
  induction t with
  | zero => intro h p; simp only [Lh, h 0 (Nat.le_refl 0)]
  | succ t ih =>
    intro h p
    have h' : ∀ k, k ≤ t → c k = c' k := fun k hk => h k (by omega)
    simp only [Lh, ih h', h (t + 1) (Nat.le_refl _)]

theorem Rh_congr {c c' : Nat → Bool} : ∀ t, (∀ k, k ≤ t → c k = c' k) → ∀ p, Rh c t p = Rh c' t p := by
  intro t
  induction t with
  | zero => intro h p; simp only [Rh, h 0 (Nat.le_refl 0)]
  | succ t ih =>
    intro h p
    have h' : ∀ k, k ≤ t → c k = c' k := fun k hk => h k (by omega)
    simp only [Rh, ih h', h (t + 1) (Nat.le_refl _)]

/-- **Uniqueness.** A column that starts black and reproduces itself is the center. -/
theorem fixed_unique {c : Nat → Bool} (h0 : c 0 = true) (hfix : ∀ t, c (t + 1) = Phi c t) :
    ∀ t, c t = center t := by
  have key : ∀ t, ∀ k, k ≤ t → c k = center k := by
    intro t
    induction t with
    | zero => intro k hk; rw [show k = 0 by omega, h0]; rfl
    | succ t ih =>
      intro k hk
      rcases Nat.lt_or_ge k (t + 1) with h | h
      · exact ih k (by omega)
      · rw [show k = t + 1 by omega, hfix t, center_fixed t]
        unfold Phi
        rw [Lh_congr t ih, Rh_congr t ih, ih t (Nat.le_refl _)]
  exact fun t => key t t (Nat.le_refl t)

/-- A fixed point of `Phi`. -/
def IsFixed (c : Nat → Bool) : Prop := c 0 = true ∧ ∀ t, c (t + 1) = Phi c t

/-- **Problem 1 is exactly: `Phi` has no eventually periodic fixed point.** -/
theorem problem1_iff_no_periodic_fixed :
    Problem1 ↔ ∀ c, IsFixed c → ¬ EventuallyPeriodic c := by
  constructor
  · intro h1 c hc hep
    have e : c = center := funext (fixed_unique hc.1 hc.2)
    rw [e] at hep; exact h1 hep
  · intro h hep
    exact h center ⟨rfl, center_fixed⟩ hep

end Rule30UOR.Fixed

namespace Rule30UOR.Fixed

open Ruliology.CellularAutomata Rule30Prize

/-- No eventually periodic column is a fixed point of `Phi`. -/
def NoPeriodicFixed : Prop := ∀ c, IsFixed c → ¬ Rule30Jen.EventuallyPeriodic c

theorem problem1_of_noPeriodicFixed (h : NoPeriodicFixed) : Problem1 :=
  problem1_iff_no_periodic_fixed.2 h

theorem noPeriodicFixed_of_problem1 (h : Problem1) : NoPeriodicFixed :=
  problem1_iff_no_periodic_fixed.1 h

end Rule30UOR.Fixed

namespace Rule30UOR.Fixed

open Ruliology.CellularAutomata Rule30Prize

/-- The recombination applied to the center itself. -/
def phiCenter (t : Nat) : Bool := Phi center t

theorem center_fixed_readout (t : Nat) : center (t + 1) = phiCenter t := center_fixed t

end Rule30UOR.Fixed
