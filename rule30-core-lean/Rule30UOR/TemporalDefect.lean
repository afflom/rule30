module

public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# Temporal differences of the single-seed Rule 30 orbit

The difference equation retains every nonlinear term. Its alternative linear form uses
coefficients from both compared rows; these coefficients are not assumed periodic.

For a Boolean sequence, a positive-shift difference is eventually periodic exactly when the
sequence is. Together with Jen's theorem, this excludes eventually periodic compensation
signals on every other column under a periodic-center hypothesis. It does not exclude
aperiodic compensation, and does not prove Problem 1.
-/

@[expose] public section

namespace Rule30UOR.TemporalDefect

open Ruliology.CellularAutomata Rule30Jen Rule30Prize

/-- Difference between a sequence and its time shift. -/
def difference (f : Nat → Bool) (Q t : Nat) : Bool := xor (f (t + Q)) (f t)

/-- Temporal difference on a physical column, with the single seed retained. -/
def defect (Q t : Nat) (p : Int) : Bool := difference (fun s => cell s p) Q t

theorem difference_eq_false_iff (f : Nat → Bool) (Q t : Nat) :
    difference f Q t = false ↔ f (t + Q) = f t := by
  unfold difference
  cases f (t + Q) <;> cases f t <;> decide

/-- Exchange the two shifts in a commuting difference rectangle. -/
theorem difference_period_swap {f : Nat → Bool} {T Q R : Nat}
    (h : ∀ t, T ≤ t → difference f Q (t + R) = difference f Q t) :
    ∀ t, T ≤ t → difference f R (t + Q) = difference f R t := by
  intro t ht
  have hh := h t ht
  unfold difference at hh ⊢
  rw [show t + Q + R = t + R + Q by omega]
  cases hA : f (t + R + Q) <;> cases hB : f (t + R) <;>
    cases hC : f (t + Q) <;> cases hD : f t <;>
    simp_all

/-- Integrating an `R`-periodic `Q`-difference gives period `2 * (R * Q)`.
No finite-state or bounded-complexity assumption is used. -/
theorem period_of_difference_period {f : Nat → Bool} {T Q R : Nat}
    (h : ∀ t, T ≤ t → difference f Q (t + R) = difference f Q t) :
    ∀ t, T ≤ t → f (t + (R * Q + R * Q)) = f t := by
  have hB : ∀ t, T ≤ t → difference f Q (t + R * Q) = difference f Q t := by
    intro t ht
    rw [Nat.mul_comm R Q]
    exact periodic_mul h Q t ht
  have hs := difference_period_swap hB
  intro t ht
  have hh := periodic_mul hs R t ht
  unfold difference at hh
  rw [show t + (R * Q + R * Q) = t + R * Q + R * Q by omega]
  cases hA : f (t + R * Q + R * Q) <;> cases hC : f (t + R * Q) <;> cases hD : f t <;>
    simp_all

/-- A positive temporal difference loses no eventual-aperiodicity information. -/
theorem difference_eventuallyPeriodic_iff (f : Nat → Bool) (Q : Nat) (hQ : 0 < Q) :
    EventuallyPeriodic (difference f Q) ↔ EventuallyPeriodic f := by
  constructor
  · rintro ⟨T, R, hR, h⟩
    have hRQ : 0 < R * Q := Nat.mul_pos hR hQ
    exact ⟨T, R * Q + R * Q, by omega, period_of_difference_period h⟩
  · rintro ⟨T, R, hR, h⟩
    refine ⟨T, R, hR, fun t ht => ?_⟩
    unfold difference
    rw [show t + R + Q = (t + Q) + R by omega, h (t + Q) (by omega), h t ht]

/-- The complete Boolean difference of the Rule 30 update. -/
theorem rule_difference (a b c a' b' c' : Bool) :
    xor (rule a' b' c') (rule a b c) =
      xor (xor (xor (xor a' a) ((!c) && xor b' b)) ((!b) && xor c' c))
        ((xor b' b) && (xor c' c)) := by
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> rfl

/-- Exact linear-in-difference form: the middle coefficient uses the *later* right cell. -/
theorem rule_difference_linear (a b c a' b' c' : Bool) :
    xor (rule a' b' c') (rule a b c) =
      xor (xor (xor a' a) ((!c') && xor b' b)) ((!b) && xor c' c) := by
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> rfl

theorem defect_step (Q t : Nat) (p : Int) :
    defect Q (t + 1) p =
      xor (xor (xor (defect Q t (p - 1)) ((!cell t (p + 1)) && defect Q t p))
        ((!cell t p) && defect Q t (p + 1)))
        ((defect Q t p) && (defect Q t (p + 1))) := by
  unfold defect difference
  rw [show t + 1 + Q = (t + Q) + 1 by omega]
  exact rule_difference _ _ _ _ _ _

theorem defect_step_linear (Q t : Nat) (p : Int) :
    defect Q (t + 1) p =
      xor (xor (defect Q t (p - 1)) ((!cell (t + Q) (p + 1)) && defect Q t p))
        ((!cell t p) && defect Q t (p + 1)) := by
  unfold defect difference
  rw [show t + 1 + Q = (t + Q) + 1 by omega]
  exact rule_difference_linear _ _ _ _ _ _

/-- A defect-free column at two consecutive times forces the precise neighbor matching. -/
theorem neighbor_matching (Q t : Nat) (p : Int)
    (h0 : defect Q t p = false) (h1 : defect Q (t + 1) p = false) :
    defect Q t (p - 1) = ((!cell t p) && defect Q t (p + 1)) := by
  rw [defect_step_linear, h0] at h1
  simpa using h1

/-- A hypothetical periodic center imposes matching for every multiple of its period. -/
theorem center_matching {T P : Nat}
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (m t : Nat) (ht : T ≤ t) :
    defect (m * P) t (-1) = ((!center t) && defect (m * P) t 1) := by
  apply neighbor_matching (m * P) t 0
  · exact (difference_eq_false_iff center (m * P) t).mpr (periodic_mul hc m t ht)
  · exact (difference_eq_false_iff center (m * P) (t + 1)).mpr
      (periodic_mul hc m (t + 1) (by omega))

/-- Under a periodic center, every positive-shift difference on any other column is
aperiodic. This excludes periodic compensation, not all compensation. -/
theorem other_column_defect_not_eventuallyPeriodic (hc : EventuallyPeriodic center)
    (Q : Nat) (hQ : 0 < Q) (p : Int) (hp : p ≠ 0) :
    ¬ EventuallyPeriodic (fun t => defect Q t p) := by
  intro hd
  have hcol := (difference_eventuallyPeriodic_iff (fun t => cell t p) Q hQ).mp hd
  exact jen p 0 hp ⟨hcol, hc⟩

/-- At every positive period multiple, even the masked right compensation signal must be
aperiodic if the center were periodic. -/
theorem masked_defect_not_eventuallyPeriodic {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (m : Nat) (hm : 0 < m) :
    ¬ EventuallyPeriodic (fun t => (!center t) && defect (m * P) t 1) := by
  rintro ⟨U, R, hR, hr⟩
  apply other_column_defect_not_eventuallyPeriodic ⟨T, P, hP, hc⟩ (m * P)
    (Nat.mul_pos hm hP) (-1) (by decide)
  refine ⟨max T U, R, hR, fun t ht => ?_⟩
  change defect (m * P) (t + R) (-1) = defect (m * P) t (-1)
  rw [center_matching hc m (t + R) (by omega), center_matching hc m t (by omega)]
  exact hr t (by omega)

end Rule30UOR.TemporalDefect
