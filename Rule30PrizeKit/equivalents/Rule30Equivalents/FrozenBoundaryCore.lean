module

public import Rule30Equivalents.FrozenBoundary
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
# The frozen-boundary conjecture is FinConf plus a two-step core

`FrozenBoundary` shows that on the three genuine frozen boundaries `Φ`, `b`, `a` the conjecture is
FinConf. This module reduces three more steps, and half of a fourth, to those three. The reduction
drops edge bits that the bulk sees only as a fixed pattern. What is left is the core: the step
`(1,1,1)` and the white-blinking edge of `(1,0,1)`.

**Dropping the edge.** When `α = 0`, bit `0` is frozen and bit `1` flips by a constant. The bulk
then sees the same inputs as from a genuine edge one or two bits lower.
* `step_of_even`, `step_of_odd`: each step is `Φ` followed by a mask that depends only on the parity.
* `step_white_of_even`, `step_white_of_odd`: `(0,0,γ)` on even seeds and `(0,β,0)` on odd seeds are
  `Φ`.
* `step_two_mul`: `(0,1,γ)` maps `2z` to `2·b(z)`.
* `step_two_mul_add_one`: `(0,β,1)` maps `2y + 1` to `2·Φ(y) + 1` when `y` is odd.
* `step_four_mul_add_one`: `(0,β,1)` maps `4z + 1` to `4·b(z) + 1`.
* `step_101`: `(1,0,1)` maps `2y + e` to `2·Φ(y) + 1 - e` when `y` is odd. Bit `1` stays black,
  and the blinking bit `0` never reaches the bulk.
* `transfer`: suppose `gᵗ(x) = 2^j·hᵗ(y) + eₜ` with `eₜ < 2^j`. Then after `j` steps every readout
  of the `g`-orbit is a readout of an `h`-orbit, and unboundedness carries over.

**The reductions.** `noPeriodicReadout_001`, `noPeriodicReadout_010`, `noPeriodicReadout_011`: the
conjecture for these three steps follows from the conjecture for `Φ` and `b`. By
`FrozenBoundary.genuineFrozen_iff_finConfRows` it therefore follows from FinConf.
`noPeriodicReadout_101_black`: the same holds for `(1,0,1)` on seeds whose bit `1` is black.

**The core as switching boundaries.** Above its two edge bits, each core step applies the genuine
steps in a fixed cycle. In the language of `FrozenBoundary` it is rule 30 on a half-line whose frozen
boundary switches periodically between genuine ones.
* `step_101_four_mul`, `step_101_four_mul_add_one`, `step_101_two_steps`: the white-blinking edge
  alternates `Φ` and `b`, so two of its steps are `b ∘ Φ`.
* `step_111_four_mul` and its three companions, `step_111_four_steps`: `(1,1,1)` cycles through
  `Φ, a, a, b`, so four of its steps are `b ∘ a ∘ a ∘ Φ`.
* Both products lie in the automaton group 2369. FinConf is the case of a boundary that never
  switches.

**The core.** `frozenBoundaryConjecture_iff_core`: the frozen-boundary conjecture holds iff FinConf
holds, the white-blinking edge of `(1,0,1)` has no eventually periodic readout (`WhiteBlinking`:
bit `1` white, bit `0` blinking), and neither has the step `(1,1,1)`. Earlier computations, which
matched diagonal pairs with finite seeds, suggest that a further 3/16 of the residues of `(1,0,1)`
reduce at greater depth. That has not been proved.

Numerically, every residue of these three steps matches a finite seed at depth at most 2, and the
shift identities explain why.
-/

@[expose] public section

namespace Rule30Equivalents.FrozenBoundaryCore

open Ruliology.CellularAutomata
open Rule30Equivalents.TFunction (Phi)
open Rule30Equivalents.AutomatonGroup (PhiS step bdry step_white FrozenBoundaryConjecture PhiS_zero
  PhiS_one PhiS_three Phi_two_mul Phi_two_mul_add_one testBit_one_eq testBit_three_eq
  testBit_two_mul_add_one)
open Rule30Equivalents.FrozenBoundary (Phi_mod_two step_b step_a testBit_two_eq FinConfRows
  GenuineFrozenConjecture genuineFrozen_iff_finConfRows)
open Rule30Equivalents.IntegerRows (testBit_two_mul)

/-- No unbounded orbit of `h` has an eventually periodic readout `t ↦ bit (t + d)`. For a step this
is the frozen-boundary conjecture for that step. -/
def NoPeriodicReadout (h : ℕ → ℕ) : Prop :=
  ∀ y d : ℕ, (∀ K, ∃ t, K < h^[t] y) → ¬ EventuallyPeriodic (fun t => (h^[t] y).testBit (t + d))

/-! ### Transfer -/

theorem eventuallyPeriodic_shift {f : ℕ → Bool} (s : ℕ) (h : EventuallyPeriodic f) :
    EventuallyPeriodic (fun t => f (t + s)) := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T, P, hP, fun t ht => ?_⟩
  show f (t + P + s) = f (t + s)
  rw [show t + P + s = t + s + P by omega]
  exact hper (t + s) (by omega)

/-- An unbounded orbit is unbounded after any finite time. -/
theorem unbounded_after {h : ℕ → ℕ} {y : ℕ} (hunb : ∀ K, ∃ t, K < h^[t] y) :
    ∀ T K, ∃ t, T ≤ t ∧ K < h^[t] y := by
  intro T
  induction T with
  | zero =>
    intro K
    obtain ⟨t, ht⟩ := hunb K
    exact ⟨t, Nat.zero_le _, ht⟩
  | succ T ih =>
    intro K
    obtain ⟨t, hT, ht⟩ := ih (max K (h^[T] y))
    refine ⟨t, ?_, Nat.lt_of_le_of_lt (Nat.le_max_left _ _) ht⟩
    rcases Nat.lt_or_ge T t with h1 | h1
    · omega
    · rw [show t = T by omega] at ht
      exact absurd ht (Nat.not_lt.2 (Nat.le_max_right _ _))

theorem testBit_two_pow_mul_add {j M e : ℕ} (he : e < 2 ^ j) (k : ℕ) :
    (2 ^ j * M + e).testBit (k + j) = M.testBit k := by
  rw [← Nat.testBit_div_two_pow, Nat.mul_add_div (Nat.two_pow_pos j), Nat.div_eq_of_lt he,
    Nat.add_zero]

/-- **Transfer.** If `gᵗ(x) = 2^j·hᵗ(y) + eₜ` with `eₜ < 2^j` for all `t`, then no readout of an
unbounded `g`-orbit of `x` is eventually periodic, provided `h` has no eventually periodic readout
on any unbounded orbit. -/
theorem transfer {g h : ℕ → ℕ} (hconj : NoPeriodicReadout h) {x y j : ℕ} {e : ℕ → ℕ}
    (he : ∀ t, e t < 2 ^ j) (horb : ∀ t, g^[t] x = 2 ^ j * h^[t] y + e t) (d : ℕ)
    (hunb : ∀ K, ∃ t, K < g^[t] x) :
    ¬ EventuallyPeriodic (fun t => (g^[t] x).testBit (t + d)) := by
  intro hep
  refine hconj (h^[j] y) d (fun K => ?_) ?_
  · obtain ⟨t, ht, hK⟩ := unbounded_after hunb j (2 ^ j * (K + 1))
    refine ⟨t - j, ?_⟩
    rw [← Function.iterate_add_apply, show t - j + j = t by omega]
    rw [horb t, Nat.mul_succ] at hK
    have h1 := he t
    refine Nat.lt_of_not_le fun hle => ?_
    have h2 : 2 ^ j * h^[t] y ≤ 2 ^ j * K := Nat.mul_le_mul_left _ hle
    omega
  · have e2 : (fun t => (h^[t] (h^[j] y)).testBit (t + d)) =
        fun t => (fun t => (g^[t] x).testBit (t + d)) (t + j) := by
      funext t
      show _ = (g^[t + j] x).testBit (t + j + d)
      rw [horb, show t + j + d = (t + d) + j by omega, testBit_two_pow_mul_add (he _),
        ← Function.iterate_add_apply]
    rw [e2]
    exact eventuallyPeriodic_shift j hep

/-! ### Dropping the edge -/

/-- On even seeds a step is `Φ` followed by flipping bit `0` if `α` and bit `1` if `β`. -/
theorem step_of_even (α β γ : Bool) {x : ℕ} (hx : x % 2 = 0) :
    step α β γ x = Phi x ^^^ ((if α then 1 else 0) + (if β then 2 else 0)) := by
  unfold step bdry
  rw [Phi_mod_two, ite_eq_left hx]
  cases β <;> rfl

/-- On odd seeds a step is `Φ` followed by flipping bit `0` if `α` and bit `1` if `γ`. -/
theorem step_of_odd (α β γ : Bool) {x : ℕ} (hx : x % 2 = 1) :
    step α β γ x = Phi x ^^^ ((if α then 1 else 0) + (if γ then 2 else 0)) := by
  unfold step bdry
  rw [Phi_mod_two, ite_eq_right (show ¬ (x % 2 = 0) by omega)]
  cases γ <;> rfl

theorem iterate_Phi_mod_two (x : ℕ) : ∀ t, Phi^[t] x % 2 = x % 2
  | 0 => rfl
  | t + 1 => by rw [Function.iterate_succ_apply', Phi_mod_two, iterate_Phi_mod_two x t]

theorem step_white_of_even (γ : Bool) {x : ℕ} (hx : x % 2 = 0) : step false false γ x = Phi x := by
  rw [step_of_even _ _ _ hx]
  simp

theorem step_white_of_odd (β : Bool) {x : ℕ} (hx : x % 2 = 1) : step false β false x = Phi x := by
  rw [step_of_odd _ _ _ hx]
  simp

/-- `(0,1,γ)` maps `2z` to `2·b(z)`: bit `0` stays white and bit `1` blinks, so the rest is `b` one
bit higher. -/
theorem step_two_mul (γ : Bool) (z : ℕ) :
    step false true γ (2 * z) = 2 * step true false false z := by
  rw [step_b, PhiS_one, step_of_even _ _ _ (by omega), Phi_two_mul]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_one_eq, testBit_two_eq, Bool.false_eq_true,
    ↓reduceIte, Nat.zero_add]
  rcases j with _ | _ | j <;> simp

/-- `(0,β,1)` maps `2y + 1` to `2·Φ(y) + 1` when `y` is odd: bits `0` and `1` stay black. -/
theorem step_two_mul_add_one (β : Bool) {y : ℕ} (hy : y % 2 = 1) :
    step false β true (2 * y + 1) = 2 * Phi y + 1 := by
  rw [step_of_odd _ _ _ (by omega), Phi_two_mul_add_one, PhiS_three, ite_eq_right (by omega)]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, testBit_two_mul_add_one, testBit_one_eq, testBit_two_eq,
    Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  rcases j with _ | _ | j <;> simp

/-- `(0,β,1)` maps `4z + 1` to `4·b(z) + 1`: bit `0` stays black and bit `1` white, so the rest is
`b` two bits higher. -/
theorem step_four_mul_add_one (β : Bool) (z : ℕ) :
    step false β true (4 * z + 1) = 4 * step true false false z + 1 := by
  rw [step_b, PhiS_one, step_of_odd _ _ _ (by omega), show 4 * z + 1 = 2 * (2 * z) + 1 by omega,
    Phi_two_mul_add_one, PhiS_three, Phi_two_mul, ite_eq_left (by omega),
    show 4 * (Phi z ^^^ 1) + 1 = 2 * (2 * (Phi z ^^^ 1)) + 1 by omega]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, testBit_two_mul_add_one, testBit_two_mul, testBit_one_eq,
    testBit_two_eq, testBit_three_eq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  rcases j with _ | _ | _ | j <;> simp

/-- `(1,0,1)` maps `2y + e` to `2·Φ(y) + 1 - e` when `y` is odd: bit `1` stays black, bit `0`
blinks, and the rest is `Φ` one bit higher. -/
theorem step_101 {y : ℕ} (hy : y % 2 = 1) {e : ℕ} (he : e < 2) :
    step true false true (2 * y + e) = 2 * Phi y + (1 - e) := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [step_of_even _ _ _ (by omega), Nat.add_zero, Phi_two_mul]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_xor, testBit_two_mul, testBit_one_eq, testBit_two_mul_add_one,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.sub_zero]
    rcases j with _ | j <;> simp
  · rw [step_of_odd _ _ _ (by omega), Phi_two_mul_add_one, PhiS_three, ite_eq_right (by omega)]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_xor, testBit_two_mul_add_one, testBit_two_mul, testBit_one_eq,
      ↓reduceIte, Nat.add_zero, Nat.sub_self]
    rcases j with _ | _ | j <;> simp [testBit_three_eq]

/-! ### Orbits -/

theorem iterate_white_of_even (γ : Bool) {x : ℕ} (hx : x % 2 = 0) :
    ∀ t, (step false false γ)^[t] x = Phi^[t] x
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_white_of_even γ hx t,
      step_white_of_even γ (by rw [iterate_Phi_mod_two, hx])]

theorem iterate_white_of_odd (β : Bool) {x : ℕ} (hx : x % 2 = 1) :
    ∀ t, (step false β false)^[t] x = Phi^[t] x
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_white_of_odd β hx t,
      step_white_of_odd β (by rw [iterate_Phi_mod_two, hx])]

theorem iterate_two_mul (γ : Bool) (z : ℕ) :
    ∀ t, (step false true γ)^[t] (2 * z) = 2 * (step true false false)^[t] z
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_two_mul γ z t,
      step_two_mul]

theorem iterate_two_mul_add_one (β : Bool) {y : ℕ} (hy : y % 2 = 1) :
    ∀ t, (step false β true)^[t] (2 * y + 1) = 2 * Phi^[t] y + 1
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_two_mul_add_one β hy t,
      step_two_mul_add_one β (by rw [iterate_Phi_mod_two, hy])]

theorem iterate_four_mul_add_one (β : Bool) (z : ℕ) :
    ∀ t, (step false β true)^[t] (4 * z + 1) = 4 * (step true false false)^[t] z + 1
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_four_mul_add_one β z t,
      step_four_mul_add_one]

theorem iterate_101 {y : ℕ} (hy : y % 2 = 1) {e : ℕ} (he : e < 2) :
    ∀ t, (step true false true)^[t] (2 * y + e) = 2 * Phi^[t] y + (e + t) % 2
  | 0 => by rw [Nat.add_zero, Nat.mod_eq_of_lt he]; rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_101 hy he t,
      step_101 (by rw [iterate_Phi_mod_two, hy]) (Nat.mod_lt _ (by omega))]
    congr 1
    omega

/-! ### The reductions -/

theorem noPeriodicReadout_Phi (hG : GenuineFrozenConjecture) : NoPeriodicReadout Phi := by
  have h := hG 0 (Or.inl rfl)
  rwa [show PhiS 0 = Phi from funext PhiS_zero] at h

theorem noPeriodicReadout_b (hG : GenuineFrozenConjecture) :
    NoPeriodicReadout (step true false false) := by
  have h := hG 1 (Or.inr (Or.inl rfl))
  rwa [← step_b] at h

theorem noPeriodicReadout_a (hG : GenuineFrozenConjecture) :
    NoPeriodicReadout (step true true false) := by
  have h := hG 3 (Or.inr (Or.inr rfl))
  rwa [← step_a] at h

/-- **Step `(0,0,1)`**: even seeds follow `Φ`, seeds `≡ 3 mod 4` follow `Φ` one bit higher, and
seeds `≡ 1 mod 4` follow `b` two bits higher. -/
theorem noPeriodicReadout_001 (hΦ : NoPeriodicReadout Phi)
    (hb : NoPeriodicReadout (step true false false)) : NoPeriodicReadout (step false false true) := by
  intro x d hunb
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
  · exact transfer hΦ (y := x) (j := 0) (e := fun _ => 0) (fun _ => Nat.two_pow_pos 0)
      (fun t => by rw [iterate_white_of_even true h0 t]; simp) d hunb
  · rcases (show x % 4 = 1 ∨ x % 4 = 3 by omega) with h | h
    · obtain ⟨z, rfl⟩ : ∃ z, x = 4 * z + 1 := ⟨x / 4, by omega⟩
      exact transfer hb (j := 2) (e := fun _ => 1) (fun _ => by show 1 < 2 ^ _; decide)
        (fun t => by rw [iterate_four_mul_add_one false z t]; rfl) d hunb
    · obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y + 1 := ⟨x / 2, by omega⟩
      exact transfer hΦ (j := 1) (e := fun _ => 1) (fun _ => by show 1 < 2 ^ _; decide)
        (fun t => by rw [iterate_two_mul_add_one false (by omega) t]; rfl) d hunb

/-- **Step `(0,1,0)`**: odd seeds follow `Φ`, and even seeds follow `b` one bit higher. -/
theorem noPeriodicReadout_010 (hΦ : NoPeriodicReadout Phi)
    (hb : NoPeriodicReadout (step true false false)) : NoPeriodicReadout (step false true false) := by
  intro x d hunb
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
  · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
    exact transfer hb (j := 1) (e := fun _ => 0) (fun _ => Nat.two_pow_pos 1)
      (fun t => by rw [iterate_two_mul false z t]; rfl) d hunb
  · exact transfer hΦ (y := x) (j := 0) (e := fun _ => 0) (fun _ => Nat.two_pow_pos 0)
      (fun t => by rw [iterate_white_of_odd true h1 t]; simp) d hunb

/-- **Step `(0,1,1)`**: even seeds follow `b` one bit higher, seeds `≡ 3 mod 4` follow `Φ` one bit
higher, and seeds `≡ 1 mod 4` follow `b` two bits higher. -/
theorem noPeriodicReadout_011 (hΦ : NoPeriodicReadout Phi)
    (hb : NoPeriodicReadout (step true false false)) : NoPeriodicReadout (step false true true) := by
  intro x d hunb
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
  · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
    exact transfer hb (j := 1) (e := fun _ => 0) (fun _ => Nat.two_pow_pos 1)
      (fun t => by rw [iterate_two_mul true z t]; rfl) d hunb
  · rcases (show x % 4 = 1 ∨ x % 4 = 3 by omega) with h | h
    · obtain ⟨z, rfl⟩ : ∃ z, x = 4 * z + 1 := ⟨x / 4, by omega⟩
      exact transfer hb (j := 2) (e := fun _ => 1) (fun _ => by show 1 < 2 ^ _; decide)
        (fun t => by rw [iterate_four_mul_add_one true z t]; rfl) d hunb
    · obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y + 1 := ⟨x / 2, by omega⟩
      exact transfer hΦ (j := 1) (e := fun _ => 1) (fun _ => by show 1 < 2 ^ _; decide)
        (fun t => by rw [iterate_two_mul_add_one true (by omega) t]; rfl) d hunb

/-- **Step `(1,0,1)` with bit `1` black**: bit `1` never changes, and the seed follows `Φ` one bit
higher while bit `0` blinks. -/
theorem noPeriodicReadout_101_black (hΦ : NoPeriodicReadout Phi) {x d : ℕ}
    (hx : x.testBit 1 = true) (hunb : ∀ K, ∃ t, K < (step true false true)^[t] x) :
    ¬ EventuallyPeriodic (fun t => ((step true false true)^[t] x).testBit (t + d)) := by
  rw [Nat.testBit_succ, Nat.testBit_zero] at hx
  have hy : x / 2 % 2 = 1 := of_decide_eq_true hx
  rw [show x = 2 * (x / 2) + x % 2 by omega] at hunb ⊢
  exact transfer hΦ (j := 1) (e := fun t => (x % 2 + t) % 2) (fun t => by
      show (x % 2 + t) % 2 < 2 ^ 1
      rw [Nat.pow_one]
      exact Nat.mod_lt _ (by omega))
    (fun t => by rw [iterate_101 hy (Nat.mod_lt _ (by omega)) t]; rfl) d hunb

/-! ### The core -/

/-- **The white-blinking edge of `(1,0,1)`** (open): bit `1` white and bit `0` blinking. No readout
of an unbounded orbit is eventually periodic. -/
def WhiteBlinking : Prop :=
  ∀ x d : ℕ, x.testBit 1 = false → (∀ K, ∃ t, K < (step true false true)^[t] x) →
    ¬ EventuallyPeriodic (fun t => ((step true false true)^[t] x).testBit (t + d))

/-- **The frozen-boundary conjecture is FinConf plus its core**: the white-blinking edge of `(1,0,1)`
and the step `(1,1,1)`. -/
theorem frozenBoundaryConjecture_iff_core : FrozenBoundaryConjecture ↔
    FinConfRows ∧ WhiteBlinking ∧ NoPeriodicReadout (step true true true) := by
  constructor
  · intro h
    refine ⟨genuineFrozen_iff_finConfRows.1 fun s hs y d hunb => ?_,
      fun x d _ hunb => h true false true x d hunb, h true true true⟩
    rcases hs with rfl | rfl | rfl
    · rw [show PhiS 0 = step false false false by rw [step_white]; exact funext PhiS_zero] at hunb ⊢
      exact h _ _ _ y d hunb
    · rw [← step_b] at hunb ⊢
      exact h _ _ _ y d hunb
    · rw [← step_a] at hunb ⊢
      exact h _ _ _ y d hunb
  · rintro ⟨hF, hW, h111⟩
    have hG := genuineFrozen_iff_finConfRows.2 hF
    have hΦ := noPeriodicReadout_Phi hG
    have hb := noPeriodicReadout_b hG
    intro α β γ
    cases α <;> cases β <;> cases γ
    · rw [step_white]; exact hΦ
    · exact noPeriodicReadout_001 hΦ hb
    · exact noPeriodicReadout_010 hΦ hb
    · exact noPeriodicReadout_011 hΦ hb
    · exact hb
    · intro x d hunb
      cases hx : x.testBit 1
      · exact hW x d hx hunb
      · exact noPeriodicReadout_101_black hΦ hx hunb
    · exact noPeriodicReadout_a hG
    · exact h111

/-- **FinConf settles six of the eight steps**, and half of a seventh. -/
theorem noPeriodicReadout_of_finConfRows (hF : FinConfRows) :
    NoPeriodicReadout (step false false false) ∧ NoPeriodicReadout (step true false false) ∧
      NoPeriodicReadout (step true true false) ∧ NoPeriodicReadout (step false false true) ∧
      NoPeriodicReadout (step false true false) ∧ NoPeriodicReadout (step false true true) := by
  have hG := genuineFrozen_iff_finConfRows.2 hF
  have hΦ := noPeriodicReadout_Phi hG
  have hb := noPeriodicReadout_b hG
  refine ⟨?_, hb, noPeriodicReadout_a hG, noPeriodicReadout_001 hΦ hb, noPeriodicReadout_010 hΦ hb,
    noPeriodicReadout_011 hΦ hb⟩
  rw [step_white]
  exact hΦ

/-! ### The core: genuine boundaries switching periodically -/

theorem Phi_four_mul (y : ℕ) : Phi (4 * y) = 2 * (2 * Phi y) := by
  rw [show 4 * y = 2 * (2 * y) by omega, Phi_two_mul, Phi_two_mul]

theorem Phi_four_mul_add_one (y : ℕ) : Phi (4 * y + 1) = 2 * (2 * Phi y ^^^ 3) + 1 := by
  rw [show 4 * y + 1 = 2 * (2 * y) + 1 by omega, Phi_two_mul_add_one, PhiS_three,
      ite_eq_left (by omega),
    Phi_two_mul]

theorem Phi_four_mul_add_two (y : ℕ) : Phi (4 * y + 2) = 2 * (2 * PhiS 3 y + 1) := by
  rw [show 4 * y + 2 = 2 * (2 * y + 1) by omega, Phi_two_mul, Phi_two_mul_add_one]

theorem Phi_four_mul_add_three (y : ℕ) :
    Phi (4 * y + 3) = 2 * ((2 * PhiS 3 y + 1) ^^^ 1) + 1 := by
  rw [show 4 * y + 3 = 2 * (2 * y + 1) + 1 by omega, Phi_two_mul_add_one, PhiS_three,
    ite_eq_right (by omega), Phi_two_mul_add_one]

/-- **The white-blinking edge applies `Φ` and `b` in turn** to the bits above the edge:
`(1,0,1)(4y) = 4·Φ(y) + 1` and `(1,0,1)(4y + 1) = 4·b(y)`. -/
theorem step_101_four_mul (y : ℕ) : step true false true (4 * y) = 4 * Phi y + 1 := by
  rw [step_of_even _ _ _ (by omega), Phi_four_mul, show 4 * Phi y + 1 = 2 * (2 * Phi y) + 1 by omega]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_two_mul_add_one, testBit_one_eq,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rcases j with _ | _ | j <;> simp

theorem step_101_four_mul_add_one (y : ℕ) :
    step true false true (4 * y + 1) = 4 * step true false false y := by
  rw [step_b, PhiS_one, step_of_odd _ _ _ (by omega), Phi_four_mul_add_one,
    show 4 * (Phi y ^^^ 1) = 2 * (2 * (Phi y ^^^ 1)) by omega]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_two_mul_add_one, testBit_one_eq,
    ↓reduceIte]
  rcases j with _ | _ | _ | j <;> simp [testBit_three_eq]

/-- **Step `(1,1,1)` cycles through `Φ, a, a, b`** on the bits above the edge, with edge states
`0 → 3 → 2 → 1 → 0`. -/
theorem step_111_four_mul (y : ℕ) : step true true true (4 * y) = 4 * Phi y + 3 := by
  rw [step_of_even _ _ _ (by omega), Phi_four_mul,
    show 4 * Phi y + 3 = 2 * (2 * Phi y + 1) + 1 by omega]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_two_mul_add_one, ↓reduceIte]
  rcases j with _ | _ | j <;> simp [testBit_three_eq]

theorem step_111_four_mul_add_three (y : ℕ) :
    step true true true (4 * y + 3) = 4 * step true true false y + 2 := by
  rw [step_a, step_of_odd _ _ _ (by omega), Phi_four_mul_add_three,
    show 4 * PhiS 3 y + 2 = 2 * (2 * PhiS 3 y + 1) by omega]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_two_mul_add_one, testBit_one_eq,
    ↓reduceIte]
  rcases j with _ | _ | _ | j <;> simp [testBit_three_eq]

theorem step_111_four_mul_add_two (y : ℕ) :
    step true true true (4 * y + 2) = 4 * step true true false y + 1 := by
  rw [step_a, step_of_even _ _ _ (by omega), Phi_four_mul_add_two,
    show 4 * PhiS 3 y + 1 = 2 * (2 * PhiS 3 y) + 1 by omega]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_two_mul_add_one, ↓reduceIte]
  rcases j with _ | _ | _ | j <;> simp [testBit_three_eq]

theorem step_111_four_mul_add_one (y : ℕ) :
    step true true true (4 * y + 1) = 4 * step true false false y := by
  rw [step_b, PhiS_one, step_of_odd _ _ _ (by omega), Phi_four_mul_add_one,
    show 4 * (Phi y ^^^ 1) = 2 * (2 * (Phi y ^^^ 1)) by omega]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_two_mul, testBit_two_mul_add_one, testBit_one_eq,
    ↓reduceIte]
  rcases j with _ | _ | _ | j <;> simp [testBit_three_eq]

/-- Two steps of the white-blinking edge are `b ∘ Φ`, an element of the automaton group 2369. -/
theorem step_101_two_steps (y : ℕ) :
    (step true false true)^[2] (4 * y) = 4 * step true false false (Phi y) := by
  show step true false true (step true false true (4 * y)) = _
  rw [step_101_four_mul, step_101_four_mul_add_one]

/-- Four steps of `(1,1,1)` are `b ∘ a ∘ a ∘ Φ`, an element of the automaton group 2369. -/
theorem step_111_four_steps (y : ℕ) :
    (step true true true)^[4] (4 * y) =
      4 * step true false false (step true true false (step true true false (Phi y))) := by
  show step true true true (step true true true (step true true true (step true true true (4 * y)))) = _
  rw [step_111_four_mul, step_111_four_mul_add_three, step_111_four_mul_add_two,
    step_111_four_mul_add_one]

end Rule30Equivalents.FrozenBoundaryCore
