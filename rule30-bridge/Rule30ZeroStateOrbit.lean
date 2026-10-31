module

public import Rule30UOR.KitConstructive
public import Rule30Intent
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

/-!
# The zero-state is a rule-30 orbit with a left edge

Place the zero-state's diagonal `j` at depth `j` from a left edge: `Ecell t p = E (p + t) t` for
`p + t ≥ 0`, white to the left. This is rule 30 run from its own time-0 row `ezero`
(`evol_ezero`), and `ezero` has its leftmost black cell at `0`. So every theorem the kit proves for
configurations with a leftmost black cell holds for the zero-state:

* `zero_no_constant_column`: no column of the zero-state is eventually constant;
* `zero_jen`: no two different columns of the zero-state are both eventually periodic;
* `zero_masked_jen`: masked Jen for the zero-state.

The zero-state's center is column `0` (`E t t`), its transparency column is `-1`
(`E (t - 1) t`): `ObZero` is a masked statement about two adjacent columns of this orbit.
-/

@[expose] public section

namespace Rule30ZeroStateOrbit

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30Realization Rule30Intent

/-! ### Choice-free Jen's theorem for configurations with a leftmost black cell

The kit's proofs of these two statements use `Classical.choice` through its
pigeonhole lemma and a classical eventual-constancy step. These copies keep the
kit's statements and definitions and use only `propext` and `Quot.sound`. -/

private theorem fc_between_periodic {x : Int → Bool} {j k : Int} (hjk : j + 1 < k)
    (hj : EventuallyPeriodic fun t => Rule30Realization.evol x t j)
    (hk : EventuallyPeriodic fun t => Rule30Realization.evol x t k) :
    EventuallyPeriodic fun t => Rule30Realization.evol x t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := Rule30Jen.common_period hj hk
  obtain ⟨m, n, hmn, -, he⟩ := Rule30UOR.KitConstructive.pigeonhole (k - j - 1).toNat
    (fun m => Rule30FiniteConfigs.strip x j k (T + m * P))
    (fun m => by simp only [Rule30FiniteConfigs.strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have hmul : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega)
  have key := Rule30FiniteConfigs.strip_agree (by omega) he (fun r => ⟨?_, ?_⟩)
    (t - (T + m * P)) (j + 1) (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by rw [Nat.sub_mul]; omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by rw [Nat.sub_mul]; omega]
    exact (periodic_mul (f := fun t => Rule30Realization.evol x t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by rw [Nat.sub_mul]; omega]
    exact (periodic_mul (f := fun t => Rule30Realization.evol x t k) hpk (n - m) _ (by omega)).symm

private theorem fc_jen {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j k : Int) (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => Rule30Realization.evol x t j) ∧
      EventuallyPeriodic (fun t => Rule30Realization.evol x t k)) := by
  have lt_case : ∀ a b : Int, a < b → (EventuallyPeriodic fun t => Rule30Realization.evol x t a) →
      (EventuallyPeriodic fun t => Rule30Realization.evol x t b) → False := by
    intro a b hab ha hb
    by_cases hadj : b = a + 1
    · subst hadj; exact Rule30FiniteConfigs.not_adjacent hlo hzero a ha hb
    · exact Rule30FiniteConfigs.not_adjacent hlo hzero a ha (fc_between_periodic (by omega) ha hb)
  rintro ⟨hj, hk⟩
  rcases Int.lt_or_gt_of_ne hjk with h | h
  · exact lt_case j k h hj hk
  · exact lt_case k j h hk hj

private theorem fc_no_column_eventually_constant {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (i : Int) :
    ¬ ∃ T b, ∀ t, T ≤ t → Rule30Realization.evol x t i = b := by
  rintro ⟨T, b, h⟩
  cases b
  · have hmono : ∀ t, T ≤ t → Rule30Realization.evol x t (i + 1) = true →
        Rule30Realization.evol x (t + 1) (i + 1) = true := by
      intro t ht h1
      show rule (Rule30Realization.evol x t (i + 1 - 1)) (Rule30Realization.evol x t (i + 1))
        (Rule30Realization.evol x t (i + 1 + 1)) = true
      rw [show i + 1 - 1 = i by omega, h t ht, h1]
      rfl
    have hi := Rule30Prize.eventuallyPeriodic_of_const h
    have hblack : ¬ ∃ t₀, T ≤ t₀ ∧ Rule30Realization.evol x t₀ (i + 1) = true := by
      rintro ⟨t₀, ht₀, hf⟩
      have hk : ∀ k, Rule30Realization.evol x (t₀ + k) (i + 1) = true := by
        intro k
        induction k with
        | zero => exact hf
        | succ k ih => exact hmono (t₀ + k) (by omega) ih
      refine Rule30FiniteConfigs.not_adjacent hlo hzero i hi
        (Rule30Prize.eventuallyPeriodic_of_const (T := t₀) (b := true) ?_)
      intro t ht
      have := hk (t - t₀)
      rwa [show t₀ + (t - t₀) = t by omega] at this
    refine Rule30FiniteConfigs.not_adjacent hlo hzero i hi
      (Rule30Prize.eventuallyPeriodic_of_const (T := T) (b := false) ?_)
    intro t ht
    cases hft : Rule30Realization.evol x t (i + 1)
    · rfl
    · exact absurd ⟨t, ht, hft⟩ hblack
  · have hleft : ∀ t, T ≤ t → Rule30Realization.evol x t (i - 1) = false := by
      intro t ht
      have e := h (t + 1) (by omega)
      have hc : Rule30Realization.evol x (t + 1) i = rule (Rule30Realization.evol x t (i - 1))
          (Rule30Realization.evol x t i) (Rule30Realization.evol x t (i + 1)) := rfl
      rw [hc, h t ht] at e
      revert e
      cases Rule30Realization.evol x t (i - 1) <;> cases Rule30Realization.evol x t (i + 1) <;>
        decide
    refine Rule30FiniteConfigs.not_adjacent hlo hzero (i - 1)
      (Rule30Prize.eventuallyPeriodic_of_const hleft) ?_
    rw [show i - 1 + 1 = i by omega]
    exact Rule30Prize.eventuallyPeriodic_of_const h

/-- The first diagonal settles at a positive time (it is white at `0` and black from `1` on). -/
theorem settle_one_pos : 1 ≤ settle 1 := by
  rcases Nat.eq_zero_or_pos (settle 1) with h | h
  · have e := settle_spec 1 0 (by omega)
    rw [show (0 : Nat) + 2 ^ 1 = 1 + 1 by rfl, D_one] at e
    exact absurd e (by decide)
  · exact h

theorem E_zero (t : Nat) : E 0 t = true := D_zero _

theorem E_one (t : Nat) : E 1 t = true := by
  have hb : 1 ≤ bound 1 := Nat.le_trans settle_one_pos (settle_le_bound 1)
  unfold E
  obtain ⟨s, hs⟩ : ∃ s, t + bound 1 * 2 ^ 1 = s + 1 := ⟨t + bound 1 * 2 - 1, by
    simp only [Nat.pow_one]; omega⟩
  rw [hs]; exact D_one s

/-- The zero-state placed at its left edge. -/
noncomputable def Ecell (t : Nat) (p : Int) : Bool :=
  if p + t < 0 then false else E (p + t).toNat t

/-- Its time-0 row. -/
noncomputable def ezero (p : Int) : Bool := Ecell 0 p

theorem ezero_edge : ezero 0 = true := by
  simp [ezero, Ecell, E_zero]

theorem ezero_left : ∀ p, p < 0 → ezero p = false := by
  intro p hp
  unfold ezero Ecell
  rw [if_pos (by omega)]

/-- **The zero-state is a rule-30 orbit.** -/
theorem evol_ezero : ∀ t p, evol ezero t p = Ecell t p := by
  intro t
  induction t with
  | zero => intro p; rfl
  | succ t ih =>
    intro p
    show rule (evol ezero t (p - 1)) (evol ezero t p) (evol ezero t (p + 1)) = Ecell (t + 1) p
    rw [ih, ih, ih]
    unfold Ecell
    by_cases h0 : p + ((t + 1 : Nat) : Int) < 0
    · rw [if_pos h0, if_pos (by omega), if_pos (by omega), if_pos (by omega)]; rfl
    · rw [if_neg h0]
      obtain ⟨j, hj⟩ : ∃ j : Nat, p + ((t + 1 : Nat) : Int) = (j : Int) := ⟨(p + (t + 1 : Nat)).toNat, by omega⟩
      rw [hj, Int.toNat_natCast]
      rcases j with _ | _ | j
      · rw [if_pos (by omega), if_pos (by omega)]
        rw [if_neg (by omega), show (p + 1 + (t : Int)).toNat = 0 by omega, E_zero, E_zero]; rfl
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
          show (p + (t : Int)).toNat = 0 by omega, show (p + 1 + (t : Int)).toNat = 1 by omega,
          E_zero, E_one, E_one]; rfl
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show (p - 1 + (t : Int)).toNat = j by omega, show (p + (t : Int)).toNat = j + 1 by omega,
          show (p + 1 + (t : Int)).toNat = j + 2 by omega, E_step]; rfl

/-- **No column of the zero-state is eventually constant.** -/
theorem zero_no_constant_column (i : Int) : ¬ ∃ T b, ∀ t, T ≤ t → Ecell t i = b := by
  rintro ⟨T, b, h⟩
  exact fc_no_column_eventually_constant ezero_edge ezero_left i
    ⟨T, b, fun t ht => by rw [evol_ezero]; exact h t ht⟩

/-- **Jen's theorem for the zero-state.** -/
theorem zero_jen (j k : Int) (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => Ecell t j) ∧ EventuallyPeriodic (fun t => Ecell t k)) := by
  have e : ∀ i, (fun t => Ecell t i) = (fun t => evol ezero t i) := fun i => by
    funext t; rw [evol_ezero]
  rw [e j, e k]
  exact fc_jen ezero_edge ezero_left j k hjk

/-- **Masked Jen for the zero-state.** -/
theorem zero_masked_jen (i : Int) {T P : Nat} (hP : 0 < P)
    (h0 : ∀ t, T ≤ t → Ecell (t + P) i = Ecell t i)
    (h1 : ∀ t, T ≤ t → Ecell t i = false → Ecell (t + P) (i + 1) = Ecell t (i + 1)) : False :=
  Rule30FiniteMaskedJen.masked_jen ezero_edge ezero_left i hP
    (fun t ht => by rw [evol_ezero, evol_ezero]; exact h0 t ht)
    (fun t ht hw => by rw [evol_ezero, evol_ezero]; rw [evol_ezero] at hw; exact h1 t ht hw)

/-- The zero-state's center is its column `0`. -/
theorem center_col (t : Nat) : Ecell t 0 = E t t := by
  simp [Ecell]

/-- **The Zero-State Center is Never Eventually Constant.** -/
theorem zcenter_not_eventually_constant : ¬ ∃ T b, ∀ t, T ≤ t → E t t = b := by
  rintro ⟨T, b, h⟩
  exact zero_no_constant_column 0 ⟨T, b, fun t ht => by rw [center_col]; exact h t ht⟩

/-- **Jen's Theorem for the Zero-State Center (`zcenter`) vs Any Other Column `k ≠ 0` of `Ecell`.** -/
theorem zcenter_jen (k : Int) (hk : k ≠ 0) :
    ¬ (EventuallyPeriodic (fun t => E t t) ∧ EventuallyPeriodic (fun t => Ecell t k)) := by
  have e0 : (fun t => E t t) = (fun t => Ecell t 0) := by
    funext t; exact (center_col t).symm
  rw [e0]
  exact zero_jen 0 k (Ne.symm hk)

/-- **Masked Jen for the Zero-State Center (`i = 0`) and Column `+1` (`E (t + 1) t`).** -/
theorem zcenter_masked_jen_right {T P : Nat} (hP : 0 < P)
    (h0 : ∀ t, T ≤ t → E (t + P) (t + P) = E t t)
    (h1 : ∀ t, T ≤ t → E t t = false → E (t + P + 1) (t + P) = E (t + 1) t) : False := by
  have he1 : ∀ s : Nat, Ecell s 1 = E (s + 1) s := fun s => by
    unfold Ecell
    rw [if_neg (by omega), show ((1 : Int) + (s : Int)).toNat = s + 1 by omega]
  exact zero_masked_jen 0 hP
    (fun t ht => by rw [center_col, center_col]; exact h0 t ht)
    (fun t ht hw => by
      rw [center_col] at hw
      show Ecell (t + P) 1 = Ecell t 1
      rw [he1 (t + P), he1 t]
      exact h1 t ht hw)

/-- **Masked Jen for Zero-State Column `-1` (`E (t - 1) t`) and the Zero-State Center (`E t t`).** -/
theorem zcenter_masked_jen_left {T P : Nat} (hP : 0 < P)
    (h_minus1 : ∀ t, T ≤ t → Ecell (t + P) (-1) = Ecell t (-1))
    (h_center : ∀ t, T ≤ t → Ecell t (-1) = false → E (t + P) (t + P) = E t t) : False := by
  exact zero_masked_jen (-1) hP h_minus1
    (fun t ht hw => by
      show Ecell (t + P) 0 = Ecell t 0
      rw [center_col, center_col]
      exact h_center t ht hw)

end Rule30ZeroStateOrbit
