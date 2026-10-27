module

public import Rule30Equivalents.AutomatonGroup
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
# The frozen-boundary family: edge decoupling, reduction to FinConf, and period 1

`AutomatonGroup.FrozenBoundaryConjecture` concerns the 8 steps `g = f ∘ Φ`, with `f` one of the 8
automorphisms of the two lowest bits, and the diagonal readouts `t ↦ bit (t + d)` of their orbits.

**Edge decoupling.** Every step is rule 30 in the bulk and an autonomous rule on the two edge
cells.
* `testBit_step_add_two`: bit `k + 2` of `g(x)` is `x_{k+2} ⊕ (x_{k+1} ∨ x_k)`.
* `testBit_step_zero`, `testBit_step_one`: the edge bits are `x_0 ⊕ α` and
  `x_1 ⊕ x_0 ⊕ (β if x is even, γ if odd)`. They depend on nothing above them.

**The genuine frozen boundaries are FinConf.** Three steps are rule 30 with a frozen two-cell
boundary: `Φ` (white, white), `b = PhiS 1` (white, black) and `a = PhiS 3` (black, any).
* `Phi_iota`, `iterate_Phi_odd`: `b` embeds into finite seeds through
  `ι(y) = 4y + 2(y mod 2) + 1`, and `a` through `2y + 1`.
* `genuineFrozen_iff_finConfRows`: so the conjecture for these three steps is equivalent to
  FinConf in the frame of the right edge (`FinConfRows`: no column of a nonzero finite
  configuration is eventually periodic).

The remaining five steps change the edge cells by rules that no rule-30 boundary produces.
`FrozenBoundaryCore` reduces three of them to `Φ` and `b`: the steps `(0,0,1)`, `(0,1,0)` and
`(0,1,1)`, and also `(1,0,1)` on seeds whose bit `1` is black. It does so by dropping edge bits that
the bulk sees only as a fixed pattern. What is left beyond FinConf is the white-blinking edge of
`(1,0,1)` and the step `(1,1,1)`, which is `Φ` followed by complementing the two edge cells.

**Period 1 for every step** (new partial results, including the irreducible core).
* `readout_left`, `readout_right`: in the bulk, the readouts obey rule 30's column relations.
* `step_top`, `iterate_top`: once `x ≥ 4`, the top bit rises by exactly 2 per step. This is the left
  edge of the half-line.
* `not_adjacent_readouts` (Jen's argument): no two adjacent readouts `d` and `d - 1` are both
  eventually periodic.
* `frozenBoundary_period_one`: for every step and every seed with an unbounded orbit, no readout is
  eventually constant. This is the period-1 case of the conjecture, for all 8 steps.
-/

@[expose] public section

namespace Rule30Equivalents.FrozenBoundary

open Ruliology.CellularAutomata
open Rule30Equivalents.TFunction (Phi orbit low testBit_Phi)
open Rule30Equivalents.AutomatonGroup (PhiS bdry step step_white testBit_one_eq testBit_three_eq
  PhiS_one PhiS_three Phi_two_mul_add_one le_iterate_Phi)

/-! ### Edge decoupling -/

theorem testBit_two_eq (j : ℕ) : (2 : ℕ).testBit j = decide (j = 1) := by
  rcases j with _ | _ | j
  · decide
  · decide
  · simp [Nat.testBit_succ]

theorem testBit_bdry_add_two (α β γ : Bool) (y k : ℕ) :
    (bdry α β γ y).testBit (k + 2) = y.testBit (k + 2) := by
  unfold bdry
  rw [Nat.testBit_xor]
  cases α <;> cases β <;> cases γ <;> by_cases h : y % 2 = 0 <;>
    simp [h, testBit_one_eq, testBit_two_eq, testBit_three_eq]

theorem Phi_mod_two (x : ℕ) : Phi x % 2 = x % 2 := by
  have h := testBit_Phi x 0
  simp only [low] at h
  simp only [Nat.testBit_zero] at h
  have : decide (Phi x % 2 = 1) = decide (x % 2 = 1) := by simpa using h
  have h1 := Nat.mod_two_eq_zero_or_one (Phi x)
  have h2 := Nat.mod_two_eq_zero_or_one x
  by_cases hx : x % 2 = 1 <;> simp_all

/-- **Bulk.** Bits `≥ 2` of every frozen-boundary step follow rule 30. -/
theorem testBit_step_add_two (α β γ : Bool) (x k : ℕ) :
    (step α β γ x).testBit (k + 2) = xor (x.testBit (k + 2)) (x.testBit (k + 1) || x.testBit k) := by
  rw [step, testBit_bdry_add_two, testBit_Phi]
  simp [low]

/-- **Edge, bit 0**: `x_0 ⊕ α`. -/
theorem testBit_step_zero (α β γ : Bool) (x : ℕ) :
    (step α β γ x).testBit 0 = xor (x.testBit 0) α := by
  have hp := testBit_Phi x 0
  simp only [low] at hp
  unfold step bdry
  rw [Nat.testBit_xor, hp]
  cases α <;> cases β <;> cases γ <;> by_cases h : Phi x % 2 = 0 <;> simp [h]

/-- **Edge, bit 1**: `x_1 ⊕ x_0 ⊕ (β if x is even, γ if x is odd)`. -/
theorem testBit_step_one (α β γ : Bool) (x : ℕ) :
    (step α β γ x).testBit 1 =
      xor (xor (x.testBit 1) (x.testBit 0)) (if x % 2 = 0 then β else γ) := by
  have hp := testBit_Phi x 1
  simp only [low] at hp
  have hm := Phi_mod_two x
  unfold step bdry
  rw [Nat.testBit_xor, hp, hm]
  cases α <;> cases β <;> cases γ <;> by_cases h : x % 2 = 0 <;>
    simp [h, testBit_one_eq, testBit_two_eq, testBit_three_eq]

/-! ### The genuine frozen boundaries are FinConf -/

theorem step_b : step true false false = PhiS 1 := by
  funext x
  rw [PhiS_one]
  simp [step, bdry]

theorem step_a : step true true false = PhiS 3 := by
  funext x
  rw [PhiS_three, step, bdry, Phi_mod_two]
  by_cases h : x % 2 = 0 <;> simp [h]

/-- The embedding of `b` into finite seeds: `ι(y) = 4y + 2(y mod 2) + 1`. -/
def iota (y : ℕ) : ℕ := 4 * y + 2 * (y % 2) + 1

theorem testBit_iota (y j : ℕ) :
    (iota y).testBit j = (j = 0 || (j = 1 && y.testBit 0) || (2 ≤ j && y.testBit (j - 2))) := by
  rcases j with _ | _ | j
  · rw [Nat.testBit_zero, show iota y % 2 = 1 by unfold iota; omega]
    rfl
  · rw [Nat.testBit_succ, Nat.testBit_zero, Nat.testBit_zero,
      show iota y / 2 % 2 = y % 2 by unfold iota; omega]
    simp
  · rw [Nat.testBit_succ, Nat.testBit_succ, show iota y / 2 / 2 = y by unfold iota; omega]
    simp

/-- **`b` embeds into finite seeds**: `Φ(ι(y)) = ι(b(y))`. -/
theorem Phi_iota (y : ℕ) : Phi (iota y) = iota (PhiS 1 y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_Phi, testBit_iota, PhiS_one]
  simp only [low, testBit_iota, Nat.testBit_xor, testBit_one_eq, testBit_Phi]
  rcases j with _ | _ | _ | _ | j <;> simp

theorem iterate_Phi_iota (y : ℕ) : ∀ t, Phi^[t] (iota y) = iota ((PhiS 1)^[t] y)
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_Phi_iota y t, Phi_iota]

theorem iterate_Phi_odd (y : ℕ) : ∀ t, Phi^[t] (2 * y + 1) = 2 * (PhiS 3)^[t] y + 1
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_Phi_odd y t,
      Phi_two_mul_add_one]

/-- FinConf in the frame of the right edge: no column `-d` of the evolution of a nonzero `row a` is
eventually periodic. Every column of every nonzero finite configuration is such a column after a
translation (`AutomatonGroup.column_not_eventuallyPeriodic_of_conjecture` reads it as a column). -/
def FinConfRows : Prop :=
  ∀ a d : ℕ, a ≠ 0 → ¬ EventuallyPeriodic (fun t => (Phi^[t] a).testBit (t + d))

/-- The frozen-boundary conjecture for the three genuine frozen boundaries `Φ`, `b`, `a`. -/
def GenuineFrozenConjecture : Prop :=
  ∀ s : ℕ, (s = 0 ∨ s = 1 ∨ s = 3) → ∀ y d : ℕ, (∀ K, ∃ t, K < (PhiS s)^[t] y) →
    ¬ EventuallyPeriodic (fun t => ((PhiS s)^[t] y).testBit (t + d))

/-- **The conjecture on genuine frozen boundaries is exactly FinConf.** -/
theorem genuineFrozen_iff_finConfRows : GenuineFrozenConjecture ↔ FinConfRows := by
  constructor
  · intro h a d ha
    have := h 0 (Or.inl rfl) a d (fun K => ⟨K + 1, by
      have := le_iterate_Phi ha (K + 1)
      rw [show PhiS 0 = Phi from funext AutomatonGroup.PhiS_zero]; omega⟩)
    rwa [show PhiS 0 = Phi from funext AutomatonGroup.PhiS_zero] at this
  · intro h s hs y d hunb
    rcases hs with rfl | rfl | rfl
    · rw [show PhiS 0 = Phi from funext AutomatonGroup.PhiS_zero] at hunb ⊢
      refine h y d fun hy => ?_
      obtain ⟨t, ht⟩ := hunb 0
      subst hy
      rw [show Phi^[t] 0 = 0 by rw [← TFunctionCycles.orbit_eq_iterate]; exact
        AutomatonGroup.orbit_zero t] at ht
      omega
    · have hc := h (iota y) (d + 2) (by unfold iota; omega)
      have e : (fun t => (Phi^[t] (iota y)).testBit (t + (d + 2))) =
          fun t => ((PhiS 1)^[t] y).testBit (t + d) := by
        funext t
        rw [iterate_Phi_iota, testBit_iota]
        have h1 : t + (d + 2) ≠ 1 := by omega
        have h2 : 2 ≤ t + (d + 2) := by omega
        simp [h1, h2, show t + (d + 2) - 2 = t + d by omega]
      rwa [e] at hc
    · have hc := h (2 * y + 1) (d + 1) (by omega)
      have e : (fun t => (Phi^[t] (2 * y + 1)).testBit (t + (d + 1))) =
          fun t => ((PhiS 3)^[t] y).testBit (t + d) := by
        funext t
        rw [iterate_Phi_odd, AutomatonGroup.testBit_two_mul_add_one]
        simp [show t + (d + 1) - 1 = t + d by omega]
      rwa [e] at hc

/-! ### Period 1 for every frozen-boundary step -/

section Readout
variable (α β γ : Bool)

/-- Readout `d` of the orbit of `a`: `t ↦ bit (t + d)` of `gᵗ(a)`. -/
def readout (a d t : ℕ) : Bool := ((step α β γ)^[t] a).testBit (t + d)

theorem readout_shift (a d s t : ℕ) :
    readout α β γ ((step α β γ)^[s] a) (d + s) t = readout α β γ a d (t + s) := by
  unfold readout
  rw [← Function.iterate_add_apply, show t + (d + s) = t + s + d by omega]

/-- **Reconstruction to the left** (column `d + 1` from columns `d` and `d - 1`). -/
theorem readout_left (a d t : ℕ) (hd : 1 ≤ d) :
    readout α β γ a (d + 1) t =
      xor (readout α β γ a d (t + 1)) (readout α β γ a d t || readout α β γ a (d - 1) t) := by
  unfold readout
  rw [Function.iterate_succ_apply', show t + 1 + d = (t + d - 1) + 2 by omega,
    testBit_step_add_two, show t + d - 1 + 2 = t + (d + 1) by omega,
    show t + d - 1 + 1 = t + d by omega, show t + d - 1 = t + (d - 1) by omega]
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- **The forward rule for column `d - 1`.** -/
theorem readout_right (a d t : ℕ) (hd : 2 ≤ d) :
    readout α β γ a (d - 1) (t + 1) =
      xor (readout α β γ a d t) (readout α β γ a (d - 1) t || readout α β γ a (d - 2) t) := by
  unfold readout
  rw [Function.iterate_succ_apply', show t + 1 + (d - 1) = (t + d - 2) + 2 by omega,
    testBit_step_add_two, show t + d - 2 + 2 = t + d by omega,
    show t + d - 2 + 1 = t + (d - 1) by omega, show t + d - 2 = t + (d - 2) by omega]

/-- **Once `x ≥ 4`, the top bit rises by exactly 2.** -/
theorem step_top {x m : ℕ} (htop : x.testBit m = true) (hz : ∀ i, m < i → x.testBit i = false) :
    (step α β γ x).testBit (m + 2) = true ∧
      ∀ i, m + 2 < i → (step α β γ x).testBit i = false := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [testBit_step_add_two, hz (m + 2) (by omega), hz (m + 1) (by omega), htop]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    rw [testBit_step_add_two, hz (k + 2) (by omega), hz (k + 1) (by omega), hz k (by omega)]
    rfl

theorem iterate_top {a m : ℕ} (htop : a.testBit m = true) (hz : ∀ i, m < i → a.testBit i = false) :
    ∀ t, ((step α β γ)^[t] a).testBit (m + 2 * t) = true ∧
      ∀ i, m + 2 * t < i → ((step α β γ)^[t] a).testBit i = false
  | 0 => by simpa using ⟨htop, hz⟩
  | t + 1 => by
    obtain ⟨h1, h2⟩ := iterate_top htop hz t
    rw [Function.iterate_succ_apply', show m + 2 * (t + 1) = m + 2 * t + 2 by omega]
    exact step_top α β γ h1 h2

/-- **Jen's argument**: no two adjacent readouts `d` and `d - 1` are both eventually periodic. -/
theorem not_adjacent_readouts {a m : ℕ} (htop : a.testBit m = true)
    (hz : ∀ i, m < i → a.testBit i = false) (d : ℕ) (hd : 1 ≤ d)
    (h0 : EventuallyPeriodic (readout α β γ a d))
    (h1 : EventuallyPeriodic (readout α β γ a (d - 1))) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := Rule30Jen.common_period h0 h1
  -- every column to the left is periodic from `T`
  have hper : ∀ k, (∀ t, T ≤ t → readout α β γ a (d + k) (t + P) = readout α β γ a (d + k) t) ∧
      (∀ t, T ≤ t → readout α β γ a (d + k - 1) (t + P) = readout α β γ a (d + k - 1) t) := by
    intro k
    induction k with
    | zero => exact ⟨fun t ht => hp0 t ht, fun t ht => hp1 t ht⟩
    | succ k ih =>
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [show d + (k + 1) = (d + k) + 1 by omega, readout_left α β γ a (d + k) (t + P) (by omega),
          readout_left α β γ a (d + k) t (by omega), show t + P + 1 = (t + 1) + P by omega,
          ih.1 (t + 1) (by omega), ih.1 t ht, ih.2 t ht]
      · rw [show d + (k + 1) - 1 = d + k by omega]
        exact ih.1 t ht
  -- far to the left, the edge arrives after `T + P`
  obtain ⟨hc, -⟩ := hper (m + T + P)
  have hD : d + (m + T + P) = m + (d + T + P) := by omega
  set t₁ := d + T + P with ht₁
  have hon := (iterate_top α β γ htop hz t₁).1
  have hoff := (iterate_top α β γ htop hz (t₁ - P)).2 (t₁ - P + (d + (m + T + P)))
    (by omega)
  have e := hc (t₁ - P) (by omega)
  unfold readout at e
  rw [show t₁ - P + P = t₁ by omega, show t₁ + (d + (m + T + P)) = m + 2 * t₁ by omega, hon,
    hoff] at e
  exact absurd e (by decide)

theorem readout_not_const_of_ge_two {a m : ℕ} (htop : a.testBit m = true)
    (hz : ∀ i, m < i → a.testBit i = false) (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ T b, ∀ t, T ≤ t → readout α β γ a d t = b := by
  rintro ⟨T, b, h⟩
  cases b
  · -- column `d` eventually white: column `d - 1` can only turn black, so it is eventually constant
    have hmono : ∀ t, T ≤ t → readout α β γ a (d - 1) t = true →
        readout α β γ a (d - 1) (t + 1) = true := by
      intro t ht h1
      rw [readout_right α β γ a d t hd, h t ht, h1]
      rfl
    obtain ⟨T', b', h'⟩ := Rule30Prize.eventually_const_of_mono hmono
    exact not_adjacent_readouts α β γ htop hz d (by omega) (Rule30Prize.eventuallyPeriodic_of_const h)
      (Rule30Prize.eventuallyPeriodic_of_const h')
  · -- column `d` eventually black: column `d + 1` is eventually white
    have hw : ∀ t, T ≤ t → readout α β γ a (d + 1) t = false := by
      intro t ht
      rw [readout_left α β γ a d t (by omega), h (t + 1) (by omega), h t ht]
      rfl
    refine not_adjacent_readouts α β γ htop hz (d + 1) (by omega)
      (Rule30Prize.eventuallyPeriodic_of_const hw) ?_
    rw [show d + 1 - 1 = d by omega]
    exact Rule30Prize.eventuallyPeriodic_of_const h

end Readout

/-- **The period-1 case of the frozen-boundary conjecture**, for all 8 steps: if the orbit of `a`
is unbounded, no readout `t ↦ bit (t + d)` is eventually constant. -/
theorem frozenBoundary_period_one (α β γ : Bool) (a d : ℕ)
    (hunb : ∀ K, ∃ t, K < (step α β γ)^[t] a) :
    ¬ ∃ T b, ∀ t, T ≤ t → ((step α β γ)^[t] a).testBit (t + d) = b := by
  rintro ⟨T, b, h⟩
  -- go to a time `s` when the orbit is at least `4`, then two more steps for the offset
  obtain ⟨s, hs⟩ := hunb 3
  set y := (step α β γ)^[s] a with hy
  have hy0 : y ≠ 0 := by omega
  have htop : y.testBit y.log2 = true := Nat.testBit_log2 hy0
  have hz : ∀ i, y.log2 < i → y.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) hi))
  obtain ⟨htop2, hz2⟩ := iterate_top α β γ htop hz 2
  refine readout_not_const_of_ge_two α β γ htop2 hz2 (d + s + 2) (by omega) ⟨T, b, fun t ht => ?_⟩
  unfold readout
  rw [← Function.iterate_add_apply, hy, ← Function.iterate_add_apply,
    show t + 2 + s = t + s + 2 by omega, show t + (d + s + 2) = (t + s + 2) + d by omega]
  exact h (t + s + 2) (by omega)

end Rule30Equivalents.FrozenBoundary
