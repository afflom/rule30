module

public import Rule30Equivalents.Basic
public import Ruliology.CellularAutomata.Rule30RightPeriods
public import Ruliology.CellularAutomata.Rule30Realization
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Ring

/-!
# Two exact formulas for the center column

Both express `c(t)` over `𝔽₂`.

* `toF_center_eq_sum` (**the center from the right half**): for `t ≥ 1` and every period `K ≥ t`
  of the diagonal `t` (for example `K = 2^t`),
  `c(t) = ∑_{t ≤ s < K} [cell(s, s - t + 1) ∨ cell(s, s - t + 2)]`. The cells on the right lie in
  the columns `≥ 1`, so `c` is determined by the right half of the pattern. Proof: down the
  diagonal `t` each step adds that cell (`R_succ`), and the diagonal returns to its value `0` at
  time `K`.
* `center_duhamel` (**Duhamel's formula**): rule 30 is rule 150 plus the product of the center and
  right cells (`X_succ`: `x' = L x + N x` with `(L x)_p = x_{p-1} + x_p + x_{p+1}` and
  `(N x)_p = x_p x_{p+1}`). So `x(t) = Lᵗ x(0) + ∑_{s < t} L^(t-1-s) N(x(s))` (`duhamel`), and at
  the center of the single seed
  `c(t) = 1 + ∑_{s < t} ∑_{|p| ≤ t-1-s} T(t-1-s, p) cell(s, p) cell(s, p + 1)`, where
  `T(m, p)` is rule 150 from a single seed (the trinomial coefficients `[zᵖ](z⁻¹ + 1 + z)ᵐ` mod 2),
  whose center is `1` (`Rule30Realization.center150`).

Neither formula decides Problem 1. The first is the identity behind the right-half reductions;
the second shows that the nonlinear part `x_p x_{p+1}` is what separates rule 30 from rule 150,
whose center column is constant.
-/

@[expose] public section

namespace Rule30Equivalents.CenterFormulas

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30RightPeriods Finset

/-- A color as an element of `𝔽₂`. -/
def toF (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toF_xor (a b : Bool) : toF (xor a b) = toF a + toF b := by
  cases a <;> cases b <;> decide

theorem toF_or (a b : Bool) : toF (a || b) = toF a + toF b + toF a * toF b := by
  cases a <;> cases b <;> decide

/-! ### The center from the right half -/

/-- One step down the diagonal `j`: it adds `cell(s, s-j+1) ∨ cell(s, s-j+2)`. -/
theorem R_succ (j s : ℕ) :
    R j (s + 1) = xor (R j s) (cell s ((s : ℤ) - j + 1) || cell s ((s : ℤ) - j + 2)) := by
  have h : ∀ q : ℤ, cell (s + 1) q = xor (cell s (q - 1)) (cell s q || cell s (q + 1)) :=
    fun q => rfl
  unfold R
  rw [h, show ((s + 1 : ℕ) : ℤ) - j - 1 = (s : ℤ) - j by push_cast; omega,
    show ((s + 1 : ℕ) : ℤ) - j + 1 = (s : ℤ) - j + 2 by push_cast; omega,
    show ((s + 1 : ℕ) : ℤ) - j = (s : ℤ) - j + 1 by push_cast; omega]

/-- Telescoping down the diagonal `j` from time `t`. -/
theorem toF_R_add (j t : ℕ) : ∀ n, toF (R j (t + n)) = toF (R j t) +
    ∑ s ∈ Ico t (t + n), toF (cell s ((s : ℤ) - j + 1) || cell s ((s : ℤ) - j + 2))
  | 0 => by simp
  | n + 1 => by
    rw [← add_assoc, R_succ, toF_xor, toF_R_add j t n, sum_Ico_succ_top (by omega), add_assoc]

/-- **The center from the right half.** For `t ≥ 1` and every period `K ≥ t` of the diagonal
`t`, `c(t)` is the parity of the times `s ∈ [t, K)` at which `cell(s, s - t + 1)` or
`cell(s, s - t + 2)`, a cell in the columns `≥ 1`, is black. -/
theorem toF_center_eq_sum {t K : ℕ} (ht : 1 ≤ t) (hK : t ≤ K) (hper : Per t K) :
    toF (Rule30Prize.center t) =
      ∑ s ∈ Ico t K, toF (cell s ((s : ℤ) - t + 1) || cell s ((s : ℤ) - t + 2)) := by
  have h1 := toF_R_add t t (K - t)
  rw [Nat.add_sub_cancel' hK] at h1
  have h2 : R t K = false := by
    have := hper 0
    rw [Nat.zero_add] at this
    rw [this, R_init ht]
  have hc : Rule30Prize.center t = R t t := by
    simp [Rule30Prize.center, R]
  rw [h2, show toF false = 0 from rfl] at h1
  rw [hc]
  have := eq_neg_of_add_eq_zero_left h1.symm
  rwa [ZMod.neg_eq_self_mod_two] at this

/-- The right-half formula over one full period `2^t` of the diagonal `t`. -/
theorem toF_center_eq_sum_two_pow {t : ℕ} (ht : 1 ≤ t) :
    toF (Rule30Prize.center t) =
      ∑ s ∈ Ico t (2 ^ t), toF (cell s ((s : ℤ) - t + 1) || cell s ((s : ℤ) - t + 2)) :=
  toF_center_eq_sum ht Nat.lt_two_pow_self.le (per_R_periodic t)

/-! ### Duhamel's formula -/

/-- Rule 150, the linear part of rule 30, on configurations over `𝔽₂`. -/
def L : AddMonoid.End (ℤ → ZMod 2) where
  toFun y p := y (p - 1) + y p + y (p + 1)
  map_zero' := by funext p; simp
  map_add' y z := by funext p; simp only [Pi.add_apply]; ring

theorem L_apply (y : ℤ → ZMod 2) (p : ℤ) : L y p = y (p - 1) + y p + y (p + 1) := rfl

theorem L_pow_succ (n : ℕ) (y : ℤ → ZMod 2) : (L ^ (n + 1)) y = L ((L ^ n) y) := by
  rw [pow_succ']
  rfl

/-- The nonlinear part of rule 30: `x_p x_{p+1}`. -/
def N (y : ℤ → ZMod 2) : ℤ → ZMod 2 := fun p => y p * y (p + 1)

/-- The space-time diagram of rule 30 from `x`, over `𝔽₂`. -/
def X (x : ℤ → Bool) (t : ℕ) : ℤ → ZMod 2 := fun p => toF (Rule30Realization.evol x t p)

/-- **Rule 30 is rule 150 plus `x_p x_{p+1}`.** -/
theorem X_succ (x : ℤ → Bool) (t : ℕ) : X x (t + 1) = L (X x t) + N (X x t) := by
  funext p
  simp only [Pi.add_apply, L_apply, N, X]
  show toF (xor (Rule30Realization.evol x t (p - 1))
    (Rule30Realization.evol x t p || Rule30Realization.evol x t (p + 1))) = _
  rw [toF_xor, toF_or]
  ring

/-- **Duhamel's formula**: `x(t) = Lᵗ x(0) + ∑_{s < t} L^(t-1-s) N(x(s))`. -/
theorem duhamel (x : ℤ → Bool) : ∀ t : ℕ,
    X x t = (L ^ t) (X x 0) + ∑ s ∈ range t, (L ^ (t - 1 - s)) (N (X x s))
  | 0 => by simp
  | t + 1 => by
    have hd := duhamel x t
    rw [X_succ]
    nth_rw 1 [hd]
    rw [map_add, map_sum, ← L_pow_succ, sum_range_succ, show t + 1 - 1 - t = 0 by omega, pow_zero]
    have hsum : ∑ s ∈ range t, L ((L ^ (t - 1 - s)) (N (X x s))) =
        ∑ s ∈ range t, (L ^ (t + 1 - 1 - s)) (N (X x s)) := by
      refine sum_congr rfl fun s hs => ?_
      rw [← L_pow_succ, show t - 1 - s + 1 = t + 1 - 1 - s by
        have := mem_range.1 hs; omega]
    rw [hsum, add_assoc]
    rfl

/-! ### The Green's function: rule 150 from a single seed -/

/-- `T m p`: rule 150 from a single seed, over `𝔽₂` (the trinomial coefficients mod 2). -/
def T (m : ℕ) (p : ℤ) : ZMod 2 := toF (Rule30Realization.run Rule30Realization.g150 m p)

theorem T_succ (m : ℕ) (p : ℤ) : T (m + 1) p = T m (p - 1) + T m p + T m (p + 1) := by
  simp only [T]
  show toF (xor _ (xor _ _)) = _
  rw [toF_xor, toF_xor]
  ring

theorem T_eq_zero (m : ℕ) {p : ℤ} (hp : m < |p|) : T m p = 0 := by
  have hs := Rule30Realization.run_symm Rule30Realization.g150
    (by intro a b c; cases a <;> cases b <;> cases c <;> rfl) m
  have hl : ∀ q : ℤ, q < -(m : ℤ) → T m q = 0 := fun q hq => by
    simp only [T, Rule30Realization.run_eq_false_of_lt Rule30Realization.g150 rfl m q hq]
    rfl
  rcases le_or_gt 0 p with h | h
  · rw [abs_of_nonneg h] at hp
    rw [T, ← hs p]
    exact hl (-p) (by omega)
  · rw [abs_of_neg h] at hp
    exact hl p (by omega)

/-- **The Green's function of rule 150**: `(Lᵐ y)(q) = ∑_{|q - p| ≤ m} T(m, q - p) y(p)`. -/
theorem L_pow_apply : ∀ (m : ℕ) (y : ℤ → ZMod 2) (q : ℤ),
    (L ^ m) y q = ∑ p ∈ Icc (q - m) (q + m), T m (q - p) * y p
  | 0, y, q => by
    simp only [pow_zero, Nat.cast_zero, sub_zero, add_zero, Icc_self, sum_singleton, sub_self, T]
    show y q = toF (decide ((0 : ℤ) = 0)) * y q
    simp [toF]
  | m + 1, y, q => by
    rw [L_pow_succ, L_apply, L_pow_apply m y (q - 1), L_pow_apply m y q, L_pow_apply m y (q + 1)]
    -- extend the three sums to `Icc (q - (m + 1)) (q + (m + 1))`
    have hext : ∀ r : ℤ, (r - m ≥ q - (m + 1 : ℕ)) → (r + m ≤ q + (m + 1 : ℕ)) →
        ∑ p ∈ Icc (r - m) (r + m), T m (r - p) * y p =
          ∑ p ∈ Icc (q - (m + 1 : ℕ)) (q + (m + 1 : ℕ)), T m (r - p) * y p := by
      intro r h1 h2
      refine sum_subset (fun p hp => ?_) (fun p hp hp' => ?_)
      · simp only [mem_Icc] at hp ⊢
        omega
      · simp only [mem_Icc] at hp hp'
        rw [T_eq_zero m (by rw [lt_abs]; omega), zero_mul]
    rw [hext (q - 1) (by push_cast; omega) (by push_cast; omega), hext q (by push_cast; omega)
      (by push_cast; omega), hext (q + 1) (by push_cast; omega) (by push_cast; omega),
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [T_succ, show q - p - 1 = q - 1 - p by omega, show q - p + 1 = q + 1 - p by omega]
    ring

/-- **Duhamel's formula at the center of the single seed.** Over `𝔽₂`,
`c(t) = 1 + ∑_{s < t} ∑_{|p| ≤ t-1-s} T(t-1-s, p) cell(s, p) cell(s, p + 1)`. -/
theorem center_duhamel (t : ℕ) :
    toF (Rule30Prize.center t) = 1 + ∑ s ∈ range t,
      ∑ p ∈ Icc (-((t - 1 - s : ℕ) : ℤ)) ((t - 1 - s : ℕ) : ℤ),
        T (t - 1 - s) p * (toF (cell s p) * toF (cell s (p + 1))) := by
  have hX : ∀ s, X Rule30Realization.seed s = fun p => toF (cell s p) := fun s => by
    funext p
    simp only [X, Rule30Realization.evol_seed]
  have h := congrFun (duhamel Rule30Realization.seed t) 0
  simp only [Pi.add_apply, Finset.sum_apply] at h
  have hc : toF (Rule30Prize.center t) = X Rule30Realization.seed t 0 := by
    simp [X, Rule30Realization.evol_seed, Rule30Prize.center]
  rw [hc, h]
  have h0 : (L ^ t) (X Rule30Realization.seed 0) 0 = 1 := by
    have : X Rule30Realization.seed 0 = fun p => toF (decide (p = 0)) := by
      funext p
      simp [X, Rule30Realization.evol, Rule30Realization.seed]
    rw [this, L_pow_apply]
    rw [sum_eq_single 0]
    · simp only [sub_zero, T, Rule30Realization.center150]
      simp [toF]
    · intro p _ hp
      simp [toF, hp]
    · intro h
      simp at h
  rw [h0]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [L_pow_apply, hX s]
  have hs := Rule30Realization.run_symm Rule30Realization.g150
    (by intro a b c; cases a <;> cases b <;> cases c <;> rfl) (t - 1 - s)
  refine sum_nbij' (fun p => p) (fun p => p) (fun p hp => ?_) (fun p hp => ?_) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun p _ => ?_)
  · simp only [mem_Icc] at hp ⊢
    omega
  · simp only [mem_Icc] at hp ⊢
    omega
  · simp only [N, zero_sub, T]
    rw [hs p]

end Rule30Equivalents.CenterFormulas
