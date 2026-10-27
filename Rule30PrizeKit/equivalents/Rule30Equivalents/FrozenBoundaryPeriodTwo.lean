module

public import Rule30Equivalents.FrozenBoundary
public import Ruliology.CellularAutomata.Rule30FiniteConfigs
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
# The frozen-boundary family at period 2: exact death, `Q01` and `CQ01`

`FrozenBoundary` proves the period-1 case of `AutomatonGroup.FrozenBoundaryConjecture` for all 8
steps. This module takes the period-2 case as far as the finite-seed case has been taken.

**Exact death.** Every step is triangular: bit `i` of `g(x)` is `x_i` plus a function of the bits
below `i`.
* `step_triangular`, `testBit_step_eq`: if two seeds agree below bit `i`, so do their images, and
  bit `i` of the images differs exactly when bit `i` of the seeds does. So every step satisfies the
  hypothesis of `TFunctionCycles`. The two theorems below are instances of its
  `diagonal_exact_death` and `eq_of_diagonal_eq`, which hold for every invertible T-function.
* `exact_death`: two seeds that agree below bit `d + m` and differ at bit `d + m` have the same
  readout `d` before time `m` and different readouts at time `m`.
* `eq_of_readout_eq`: a seed is determined by its bits below `d` and its readout `d`. So for each
  right part (the bits below `d`) at most one seed has a given readout, and in particular at most
  one has an alternating readout. Every other seed with that right part follows the alternation
  exactly until the first bit where it differs from that one.

**The period-2 question for one step.** `AlternationFree α β γ`: no seed has a readout that
alternates `1, 0, 1, 0, …` from time `0`.
* `alternationFree_iff`: this is exactly the period-2 case of the conjecture for that step (the
  constant case is `FrozenBoundary.frozenBoundary_period_one`).

**`Q01` settles period 2 for all 8 steps.** Suppose readout `D ≥ 1` alternates. The left part (the
bits above `D`) sees the readout only through rule 30's `or`. At a black step the cell to its left
is forced black, so the `or` is already black and the part to the right is masked. So the left
part evolves as the zero-boundary left half (`zbl_of_alternating`). It is finitely supported and
keeps column `-1` black at every even step (`inX_of_alternating`).
* `alternationFree_of_Q01`, `frozenBoundary_period_two_of_Q01`: `Q01` implies the period-2 case
  for every step, including the irreducible step `(1,1,1)`.

**The genuine boundaries at period 2 are `CQ01`.**
* `alternationFree_white_iff_CQ01`: for `Φ` the period-2 question is `CQ01`, the coupled question
  of finite configurations (`Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating`). The proof
  goes through the dictionary `TFunction.testBit_orbit` and the encoding `enc` of a finite
  configuration as a number.
* `alternationFree_a_of_white`, `alternationFree_b_of_white`: the black wall `a` and the state `b`
  follow from `Φ`, through `2y + 1` and `ι`.

What remains at period 2 is the coupling with the right part, as in `CQ01`. For the step `(1,1,1)`
the column next to an alternating readout is not, numerically, a finite-seed column. So its
period-2 question is a coupled question of its own: it is implied by `Q01`, but no reduction to
`CQ01` is known.

Numerically, the forced seed of each right part, computed for all 8 steps up to depth 1200, is
never finite.
-/

@[expose] public section

namespace Rule30Equivalents.FrozenBoundaryPeriodTwo

open Ruliology.CellularAutomata
open Rule30Realization (evol)
open Rule30ZeroBoundary (zrow zrow_succ zrow_wall zrow_zero_of_pos InX FinSupp Q01)
open Rule30PeriodTwoCoupled (altCol CQ01)
open Rule30Equivalents.TFunction (Phi orbit row testBit_orbit)
open Rule30Equivalents.AutomatonGroup (PhiS step step_white)
open Rule30Equivalents.FrozenBoundary (readout readout_shift readout_left testBit_step_add_two
  testBit_step_zero testBit_step_one frozenBoundary_period_one)

theorem altCol_add_two (t : ℕ) : altCol (t + 2) = altCol t := by
  unfold altCol
  rw [Nat.add_mod_right]

theorem xor_xor_cancel (a b c : Bool) : xor (xor a c) (xor b c) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ### Exact death -/

section Triangular
variable (α β γ : Bool)

/-- **Every step is triangular**: if `x, y` agree below bit `i`, so do `g(x), g(y)`, and bit `i` of
`g(x), g(y)` differs exactly when bit `i` of `x, y` does. -/
theorem step_triangular {i x y : ℕ} (h : ∀ j, j < i → x.testBit j = y.testBit j) :
    (∀ j, j < i → (step α β γ x).testBit j = (step α β γ y).testBit j) ∧
      xor ((step α β γ x).testBit i) ((step α β γ y).testBit i) =
        xor (x.testBit i) (y.testBit i) := by
  have hpar : 0 < i → x % 2 = y % 2 := fun hi => by
    have h0 := h 0 hi
    rw [Nat.testBit_zero, Nat.testBit_zero] at h0
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [hx, hy] at h0 ⊢
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases j with _ | _ | j
    · rw [testBit_step_zero, testBit_step_zero, h 0 hj]
    · rw [testBit_step_one, testBit_step_one, h 1 hj, h 0 (by omega), hpar (by omega)]
    · rw [testBit_step_add_two, testBit_step_add_two, h _ hj, h (j + 1) (by omega),
        h j (by omega)]
  · rcases i with _ | _ | i
    · rw [testBit_step_zero, testBit_step_zero, xor_xor_cancel]
    · rw [testBit_step_one, testBit_step_one, h 0 (by omega), hpar (by omega), xor_xor_cancel,
        xor_xor_cancel]
    · rw [testBit_step_add_two, testBit_step_add_two, h (i + 1) (by omega), h i (by omega),
        xor_xor_cancel]

/-- So each step satisfies the hypothesis of `TFunctionCycles`: bit `i` of `g(x)` is `x_i` plus a
function of `x mod 2^i`. -/
theorem testBit_step_eq (i x : ℕ) :
    (step α β γ x).testBit i = xor (x.testBit i) ((step α β γ (x % 2 ^ i)).testBit i) := by
  have hlow : ∀ j, j < i → x.testBit j = (x % 2 ^ i).testBit j := fun j hj => by
    rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
  have h := (step_triangular α β γ hlow).2
  rw [Nat.testBit_mod_two_pow, decide_eq_false (Nat.lt_irrefl i), Bool.false_and,
    Bool.xor_false] at h
  rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- **Exact death.** Two seeds that agree below bit `d + m` and differ at bit `d + m` have the same
readout `d` before time `m`, and different readouts at time `m`. -/
theorem exact_death {a b d m : ℕ} (hag : ∀ j, j < d + m → a.testBit j = b.testBit j)
    (hne : a.testBit (d + m) ≠ b.testBit (d + m)) :
    (∀ t, t < m → readout α β γ a d t = readout α β γ b d t) ∧
      readout α β γ a d m ≠ readout α β γ b d m :=
  TFunctionCycles.diagonal_exact_death (f := step α β γ) (ψ := fun i z => (step α β γ z).testBit i)
    (testBit_step_eq α β γ) ((TFunctionCycles.mod_two_pow_eq_iff _ _ _).2 hag) hne

/-- **A seed is determined by its bits below `d` and its readout `d`.** -/
theorem eq_of_readout_eq {a b d : ℕ} (hlow : ∀ j, j < d → a.testBit j = b.testBit j)
    (hr : ∀ t, readout α β γ a d t = readout α β γ b d t) : a = b :=
  TFunctionCycles.eq_of_diagonal_eq (f := step α β γ) (ψ := fun i z => (step α β γ z).testBit i)
    (testBit_step_eq α β γ) ((TFunctionCycles.mod_two_pow_eq_iff _ _ _).2 hlow) hr

/-- **At most one alternating seed for each right part.** -/
theorem alternating_seed_unique {a b d : ℕ} (hlow : ∀ j, j < d → a.testBit j = b.testBit j)
    (ha : ∀ t, readout α β γ a d t = altCol t) (hb : ∀ t, readout α β γ b d t = altCol t) :
    a = b :=
  eq_of_readout_eq α β γ hlow fun t => (ha t).trans (hb t).symm

end Triangular

/-! ### The period-2 question for one step -/

/-- **The period-2 question for the step `(α, β, γ)`** (open for every step): no seed has a readout
that alternates `1, 0, 1, 0, …` from time `0`. -/
def AlternationFree (α β γ : Bool) : Prop := ∀ a d : ℕ, ¬ ∀ t, readout α β γ a d t = altCol t

/-- **`AlternationFree` is the period-2 case of the frozen-boundary conjecture** for its step. -/
theorem alternationFree_iff (α β γ : Bool) : AlternationFree α β γ ↔
    ∀ a d, (∀ K, ∃ t, K < (step α β γ)^[t] a) →
      ¬ ∃ T, ∀ t, T ≤ t → readout α β γ a d (t + 2) = readout α β γ a d t := by
  constructor
  · rintro hA a d hunb ⟨T, hT⟩
    obtain ⟨T', -, hT'⟩ := Rule30FiniteConfigs.exists_restart
      (Rule30FiniteConfigs.alternates_of_period_two hT (frozenBoundary_period_one α β γ a d hunb))
    refine hA ((step α β γ)^[T'] a) (d + T') fun t => ?_
    rw [readout_shift, Nat.add_comm t T']
    exact hT' t
  · intro h a d halt
    refine h a d (fun K => ⟨2 * K, ?_⟩) ⟨0, fun t _ => by rw [halt, halt, altCol_add_two]⟩
    have h1 : ((step α β γ)^[2 * K] a).testBit (2 * K + d) = true := by
      have := halt (2 * K)
      unfold readout at this
      rw [this]
      unfold altCol
      simp
    have h2 := Nat.ge_two_pow_of_testBit h1
    have h3 : K < 2 ^ (2 * K + d) :=
      Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
    omega

/-! ### `Q01` settles period 2 for all 8 steps -/

section Masked
variable (α β γ : Bool)

/-- **The masked step.** If readout `D ≥ 1` alternates from time `0`, the bits above it evolve as
the zero-boundary left half started from them. -/
theorem zbl_of_alternating {y D : ℕ} (hD : 1 ≤ D) (halt : ∀ t, readout α β γ y D t = altCol t) :
    ∀ t k, 1 ≤ k →
      zrow (fun k => y.testBit (D + k)) t k = ((step α β γ)^[t] y).testBit (t + D + k) := by
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [zrow_zero_of_pos _ hk]
    simp
  | succ t ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, Function.iterate_succ_apply',
      show t + 1 + D + (j + 1) = t + D + j + 2 by omega, testBit_step_add_two,
      ih (j + 2) (by omega), ih (j + 1) (by omega),
      show t + D + (j + 2) = t + D + j + 2 by omega, show t + D + (j + 1) = t + D + j + 1 by omega]
    congr 1
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hr : readout α β γ y D t = ((step α β γ)^[t] y).testBit (t + D + 0) := rfl
      rw [zrow_wall, ← hr, halt t]
      cases hc : altCol t
      · rfl
      · have hl := readout_left α β γ y D t hD
        rw [halt (t + 1), halt t, Rule30FiniteConfigs.altCol_succ, hc] at hl
        have hl' : readout α β γ y (D + 1) t = true := by rw [hl]; rfl
        unfold readout at hl'
        rw [show t + D + 0 + 1 = t + (D + 1) by omega, hl']
        rfl
    · rw [ih j hj]

/-- Under an alternating readout, the left part keeps column `-1` black at every even step. -/
theorem inX_of_alternating {y D : ℕ} (hD : 1 ≤ D) (halt : ∀ t, readout α β γ y D t = altCol t) :
    InX (fun k => y.testBit (D + k)) := by
  intro s
  rw [zbl_of_alternating α β γ hD halt (2 * s) 1 (Nat.le_refl 1)]
  have hl := readout_left α β γ y D (2 * s) hD
  rw [halt (2 * s + 1), halt (2 * s), Rule30FiniteConfigs.altCol_succ] at hl
  have h0 : altCol (2 * s) = true := by unfold altCol; simp
  rw [h0] at hl
  have hl' : readout α β γ y (D + 1) (2 * s) = true := by rw [hl]; rfl
  unfold readout at hl'
  rw [show 2 * s + D + 1 = 2 * s + (D + 1) by omega]
  exact hl'

theorem finSupp_bits (y D : ℕ) : FinSupp (fun k => y.testBit (D + k)) :=
  ⟨y, fun _ hk => Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega)))⟩

/-- **`Q01` excludes an alternating readout `D ≥ 1`.** -/
theorem not_alternating_of_Q01 (hQ : Q01) {y D : ℕ} (hD : 1 ≤ D) :
    ¬ ∀ t, readout α β γ y D t = altCol t := fun halt =>
  hQ _ (finSupp_bits y D) (inX_of_alternating α β γ hD halt)

end Masked

/-- **`Q01` implies the period-2 question for every frozen-boundary step.** -/
theorem alternationFree_of_Q01 (hQ : Q01) (α β γ : Bool) : AlternationFree α β γ := by
  intro a d halt
  refine not_alternating_of_Q01 α β γ hQ (y := (step α β γ)^[2] a) (D := d + 2) (by omega)
    fun t => ?_
  rw [readout_shift, halt, altCol_add_two]

/-- **`Q01` implies the period-2 case of the frozen-boundary conjecture**, for all 8 steps: if the
orbit of `a` is unbounded, no readout is eventually 2-periodic. -/
theorem frozenBoundary_period_two_of_Q01 (hQ : Q01) (α β γ : Bool) (a d : ℕ)
    (hunb : ∀ K, ∃ t, K < (step α β γ)^[t] a) :
    ¬ ∃ T, ∀ t, T ≤ t → readout α β γ a d (t + 2) = readout α β γ a d t :=
  (alternationFree_iff α β γ).1 (alternationFree_of_Q01 hQ α β γ) a d hunb

/-! ### The genuine boundaries at period 2 -/

/-- The bits `f 0, …, f (n - 1)` as a number. -/
def enc : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => 2 * enc n (fun i => f (i + 1)) + (if f 0 then 1 else 0)

theorem testBit_enc : ∀ (n : ℕ) (f : ℕ → Bool) (i : ℕ),
    (enc n f).testBit i = (decide (i < n) && f i)
  | 0, f, i => by simp [enc]
  | n + 1, f, 0 => by
    have h : enc (n + 1) f % 2 = if f 0 then 1 else 0 := by
      show (2 * enc n (fun i => f (i + 1)) + (if f 0 then 1 else 0)) % 2 = _
      split <;> omega
    rw [Nat.testBit_zero, h]
    cases f 0 <;> simp
  | n + 1, f, i + 1 => by
    have h : enc (n + 1) f / 2 = enc n (fun i => f (i + 1)) := by
      show (2 * enc n (fun i => f (i + 1)) + (if f 0 then 1 else 0)) / 2 = _
      split <;> omega
    rw [Nat.testBit_succ, h, testBit_enc n _ i]
    simp

/-- A finite configuration, moved left by `W`, is the row of a number. -/
theorem row_enc (x : Int → Bool) (W : ℕ) (hW : ∀ p : Int, W < p.natAbs → x p = false) (q : Int) :
    row (enc (2 * W + 1) fun i => x ((W : Int) - i)) q = x (q + W) := by
  unfold row
  split
  · rename_i hq
    rw [testBit_enc]
    by_cases hlt : (-q).toNat < 2 * W + 1
    · rw [decide_eq_true hlt, Bool.true_and]
      congr 1
      omega
    · rw [decide_eq_false hlt, Bool.false_and]
      exact (hW _ (by omega)).symm
  · rename_i hq
    exact (hW _ (by omega)).symm

/-- For `Φ`, readout `d` is column `-d` of the configuration `row a`. -/
theorem readout_white (a d t : ℕ) :
    readout false false false a d t = evol (row a) t (-(d : Int)) := by
  unfold readout
  rw [step_white, ← Rule30Equivalents.TFunctionCycles.orbit_eq_iterate, testBit_orbit]
  congr 1
  omega

/-- **For `Φ`, the period-2 question is `CQ01`**: no seed's readout alternates from time `0` exactly
when no finite configuration has center column `1, 0, 1, 0, …`. -/
theorem alternationFree_white_iff_CQ01 : AlternationFree false false false ↔ CQ01 := by
  rw [Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating]
  constructor
  · rintro hA ⟨x, ⟨W, hW⟩, hx⟩
    refine hA (enc (2 * W + 1) fun i => x ((W : Int) - i)) W fun t => ?_
    have hs := Rule30ZeroBoundaryBarriers.evol_shift_all (x := x)
      (x' := row (enc (2 * W + 1) fun i => x ((W : Int) - i))) (d := -(W : Int))
      (fun p => by rw [row_enc x W hW]; congr 1; omega) t 0
    rw [readout_white, ← hx t, ← hs]
    congr 1
    omega
  · rintro h a d halt
    refine h ⟨fun p => row a (p - d), ⟨a + d, fun p hp => ?_⟩, fun t => ?_⟩
    · show row a (p - d) = false
      unfold row
      split
      · rename_i hp'
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega)))
      · rfl
    · have hs := Rule30ZeroBoundaryBarriers.evol_shift_all (x := fun p => row a (p - d))
        (x' := row a) (d := -(d : Int)) (fun p => by show row a _ = row a _; congr 1) t 0
      rw [← hs, ← halt t, readout_white]
      congr 1
      omega

/-- **The black wall at period 2 follows from `Φ`**, through `y ↦ 2y + 1`. -/
theorem alternationFree_a_of_white (h : AlternationFree false false false) :
    AlternationFree true true false := by
  intro y d halt
  refine h (2 * y + 1) (d + 1) fun t => ?_
  rw [← halt t]
  unfold readout
  rw [step_white, FrozenBoundary.step_a, FrozenBoundary.iterate_Phi_odd,
    AutomatonGroup.testBit_two_mul_add_one]
  simp [show t + (d + 1) - 1 = t + d by omega]

/-- **The state `b` at period 2 follows from `Φ`**, through `ι`. -/
theorem alternationFree_b_of_white (h : AlternationFree false false false) :
    AlternationFree true false false := by
  intro y d halt
  refine h (FrozenBoundary.iota y) (d + 2) fun t => ?_
  rw [← halt t]
  unfold readout
  rw [step_white, FrozenBoundary.step_b, FrozenBoundary.iterate_Phi_iota,
    show t + (d + 2) = t + d + 2 by omega, FrozenBoundary.testBit_iota]
  simp

end Rule30Equivalents.FrozenBoundaryPeriodTwo
