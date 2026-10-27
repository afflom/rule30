module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule 30, Problem 1: meaning → intent → outcomes

**Meaning.** The left diagonals `D j t` (kit), their eventual patterns `E j t` (the zero-state),
the transparent times (`E (s-1) s = false`) and the zero-state's center `E s s`.

**Intent.** `Problem1` is the root claim. It is discharged by two obligations:
* `ObFront`: if the center is eventually periodic, the left half is eventually the zero-state.
* `ObZero`: no eventually periodic sequence agrees with the zero-state's center at all large
  transparent times. A statement about the zero-state alone.

**Outcome (this file).** `gate : ObFront → ObZero → Problem1`, kernel-checked; the obligations are
stated as propositions and carry no proof here.
-/

@[expose] public section

namespace Rule30UOR.Intent

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals

/-! ### Meaning: the zero-state -/

/-- A settling time of diagonal `j` (from the kit's `D_periodic`). -/
noncomputable def settle (j : Nat) : Nat := Classical.choose (D_periodic j)

theorem settle_spec (j : Nat) : ∀ t, settle j ≤ t → D j (t + 2 ^ j) = D j t :=
  Classical.choose_spec (D_periodic j)

theorem per_mul (j : Nat) : ∀ k t, settle j ≤ t → D j (t + k * 2 ^ j) = D j t := by
  intro k
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [show t + (k + 1) * 2 ^ j = (t + k * 2 ^ j) + 2 ^ j by rw [Nat.succ_mul]; omega,
      settle_spec j _ (by omega), ih t ht]

/-- A monotone settling bound. -/
noncomputable def bound : Nat → Nat
  | 0 => settle 0
  | j + 1 => bound j + settle (j + 1)

theorem settle_le_bound : ∀ j, settle j ≤ bound j
  | 0 => Nat.le_refl _
  | j + 1 => by simp only [bound]; omega

theorem bound_mono : ∀ i j, i ≤ j → bound i ≤ bound j := by
  intro i j h
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := ih (by omega); simp only [bound]; omega
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

/-- **The zero-state**: diagonal `j` read far enough out that it has settled. -/
noncomputable def E (j t : Nat) : Bool := D j (t + bound j * 2 ^ j)

/-- Two late readings of a diagonal agree when they differ by a multiple of its period. -/
theorem D_late (j a b : Nat) (ha : settle j ≤ a) (hb : settle j ≤ b) (k l : Nat)
    (h : a + k * 2 ^ j = b + l * 2 ^ j) : D j a = D j b := by
  rw [← per_mul j k a ha, ← per_mul j l b hb, h]

theorem E_eq_D (j t : Nat) (ht : settle j ≤ t) : E j t = D j t :=
  per_mul j (bound j) t ht

/-- Reading a settled diagonal at an offset that is a larger multiple of its period changes
nothing. -/
theorem late (i s Bi Bk c : Nat) (hset : settle i ≤ Bi) (hle : Bi ≤ Bk) (hc : 1 ≤ c) :
    D i (s + Bk * (c * 2 ^ i)) = D i (s + Bi * 2 ^ i) := by
  have hX : 0 < 2 ^ i := Nat.two_pow_pos i
  have h1 : Bi ≤ Bk * c := Nat.le_trans hle (Nat.le_mul_of_pos_right Bk hc)
  have h2 : Bi * 2 ^ i ≤ Bk * c * 2 ^ i := Nat.mul_le_mul_right _ h1
  have h3 : Bi ≤ Bi * 2 ^ i := Nat.le_mul_of_pos_right Bi hX
  have e : s + Bk * (c * 2 ^ i) = (s + Bi * 2 ^ i) + (Bk * c - Bi) * 2 ^ i := by
    rw [Nat.sub_mul, ← Nat.mul_assoc]
    omega
  rw [e, per_mul i _ _ (by omega)]

/-- The zero-state obeys the diagonal recurrence. -/
theorem E_step (j s : Nat) :
    E (j + 2) (s + 1) = xor (E j s) (E (j + 1) s || E (j + 2) s) := by
  have p0 : 2 ^ (j + 2) = 4 * 2 ^ j := by rw [Nat.pow_add]; omega
  have p1 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
  unfold E
  rw [show s + 1 + bound (j + 2) * 2 ^ (j + 2) = (s + bound (j + 2) * 2 ^ (j + 2)) + 1 by omega,
    D_step]
  have e0 : D j (s + bound (j + 2) * 2 ^ (j + 2)) = D j (s + bound j * 2 ^ j) := by
    rw [p0]; exact late j s _ _ 4 (settle_le_bound j) (bound_mono _ _ (by omega)) (by omega)
  have e1 : D (j + 1) (s + bound (j + 2) * 2 ^ (j + 2)) = D (j + 1) (s + bound (j + 1) * 2 ^ (j + 1)) := by
    rw [p1]; exact late (j + 1) s _ _ 2 (settle_le_bound (j + 1)) (bound_mono _ _ (by omega)) (by omega)
  rw [e0, e1]

/-! ### Intent: the obligations -/

/-- **Obligation (front).** An eventually periodic center forces the left half (depths below the
center's) to be the zero-state from some time on. -/
def ObFront : Prop :=
  EventuallyPeriodic Rule30Prize.center → ∃ T, ∀ t, T ≤ t → ∀ j, j < t → D j t = E j t

/-- **Obligation (zero-state).** No eventually periodic sequence agrees with the zero-state's center
`E s s` at every large transparent time `s` (those with `E (s-1) s = false`). -/
def ObZero : Prop :=
  ∀ u : Nat → Bool, EventuallyPeriodic u →
    ¬ ∃ T, ∀ t, T ≤ t → E (t + 1) (t + 2) = false → u (t + 2) = E (t + 2) (t + 2)

/-! ### Outcome: the gate -/

/-- Once the left half is the zero-state, the center equals the zero-state's center at every
transparent time. -/
theorem center_eq_zero_center (T : Nat) (h : ∀ t, T ≤ t → ∀ j, j < t → D j t = E j t) :
    ∀ t, T ≤ t → E (t + 1) (t + 2) = false →
      Rule30Prize.center (t + 2) = E (t + 2) (t + 2) := by
  intro t ht hz
  have h1 := h (t + 3) (by omega) (t + 2) (by omega)
  rw [show t + 3 = (t + 2) + 1 by omega, D_step, E_step, h (t + 2) (by omega) t (by omega),
    h (t + 2) (by omega) (t + 1) (by omega), hz] at h1
  have hc : Rule30Prize.center (t + 2) = D (t + 2) (t + 2) := center_eq_D (t + 2)
  rw [hc]
  revert h1
  cases E t (t + 2) <;> cases D (t + 2) (t + 2) <;> cases E (t + 2) (t + 2) <;> simp

/-- **The gate.** The two obligations discharge Problem 1. -/
theorem gate (hF : ObFront) (hZ : ObZero) : Rule30Prize.Problem1 := by
  intro hEP
  obtain ⟨T, hT⟩ := hF hEP
  exact hZ Rule30Prize.center hEP ⟨T, center_eq_zero_center T hT⟩

end Rule30UOR.Intent
