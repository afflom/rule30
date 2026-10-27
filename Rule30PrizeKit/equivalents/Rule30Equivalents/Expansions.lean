module

public import Rule30Equivalents.BinaryIrrational
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
# Problem 1 through the Engel, Sylvester, Lüroth and factorial expansions of `x₂`

`x₂ = 0.c(0)c(1)c(2)…` in base 2 (`BinaryIrrational.centerBinary`).

* **Engel.** `engelRem x` is the sequence of remainders of the Engel expansion
  `x = 1/a₁ + 1/(a₁a₂) + 1/(a₁a₂a₃) + ⋯`: a nonzero remainder `r` is followed by `⌈1/r⌉ r - 1`.
  `irrational_iff_engelRem_ne_zero`: for `x ≥ 0`, the expansion is infinite exactly when `x` is
  irrational. `problem1_iff_engel_infinite`: Problem 1 holds iff the Engel expansion
  of `x₂` is infinite.
* **Sylvester.** `sylvesterRem x` is the sequence of remainders of the greedy Egyptian-fraction
  expansion: a nonzero remainder `r` is followed by `r - 1/⌈1/r⌉`.
  `problem1_iff_sylvester_infinite`: Problem 1 holds iff the Sylvester expansion of `x₂` is
  infinite.
* **Lüroth.** `lurothStep` maps `x ∈ (0, 1]` with digit `a = ⌊1/x⌋ + 1` to `a(a - 1)x - (a - 1)`,
  again in `(0, 1]`, so every expansion is infinite. `lurothDigits_eventuallyPeriodic_iff`: the
  digits are eventually periodic iff `x` is rational. A rational orbit stays among the finitely many
  points `k/q`. Two points with the same digits are within `2⁻ⁿ` for every `n`
  (`luroth_injective`), so periodic digits make a remainder a fixed point of an affine map with
  rational coefficients. `problem1_iff_luroth_not_eventuallyPeriodic`: Problem 1 holds iff the
  Lüroth expansion of `x₂` is not eventually periodic.
* **Factorial base.** `factRem x k = fract (k! x)` and `factDigit x k = ⌊(k + 1) factRem x k⌋`
  satisfy `r_{k+1} = (k + 1) r_k - d_{k+1}` with `0 ≤ d_{k+1} ≤ k`, and `fract_eq_sum` is the
  expansion `fract x = ∑ d_{j+1}/(j+1)! + r_n/n!`. `irrational_iff_factRem_ne_zero`: the expansion
  is infinite iff `x` is irrational. `problem1_iff_factorial_infinite`: Problem 1 holds iff no
  `k! · x₂` is an integer.

**Proof.** For a rational remainder `m / d` with `m > 0`, let `a = ⌈d / m⌉`. Then
`d ≤ a m < d + m`, so the next remainder is `(a m - d) / d` (Engel) or `(a m - d) / (a d)`
(Sylvester), with a smaller numerator: rational inputs terminate. An irrational positive remainder
`r` has `a ≥ 1`, and `a r - 1` and `r - 1/a` are irrational and positive: irrational inputs never
reach `0`. Then apply `BinaryIrrational.problem1_iff_irrational_binary`.

Sources: P. Erdős, A. Rényi and P. Szüsz, *On Engel's and Sylvester's series*, Ann. Univ. Sci.
Budapest. Eötvös Sect. Math. 1 (1958) 7–32; J. Lüroth, *Ueber eine eindeutige Entwickelung von
Zahlen in eine unendliche Reihe*, Math. Ann. 21 (1883) 411–423; J. Galambos, *Representations of Real Numbers by
Infinite Series*, Springer (1976).
-/

@[expose] public section

namespace Rule30Equivalents.Expansions

open Ruliology.CellularAutomata

/-! ### The ceiling bound behind both algorithms -/

/-- For `m, d > 0` and `a = ⌈d / m⌉`: `d ≤ a m < d + m`, so `a m - d` is a natural number below
`m`, and `a ≥ 1`. -/
theorem ceil_bounds (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (d : ℤ) ≤ ⌈((m : ℝ) / d)⁻¹⌉ * m ∧ ⌈((m : ℝ) / d)⁻¹⌉ * m < d + m ∧ 1 ≤ ⌈((m : ℝ) / d)⁻¹⌉ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hinv : ((m : ℝ) / d)⁻¹ = (d : ℝ) / m := inv_div _ _
  have h1 : (d : ℝ) / m ≤ ⌈((m : ℝ) / d)⁻¹⌉ := hinv ▸ Int.le_ceil _
  have h2 : (⌈((m : ℝ) / d)⁻¹⌉ : ℝ) < (d : ℝ) / m + 1 := hinv ▸ Int.ceil_lt_add_one _
  have h3 : (d : ℝ) ≤ ⌈((m : ℝ) / d)⁻¹⌉ * m := by rwa [div_le_iff₀ hm'] at h1
  have h4 : (⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * m < d + m := by
    have := mul_lt_mul_of_pos_right h2 hm'
    rwa [add_mul, div_mul_cancel₀ _ hm'.ne', one_mul] at this
  have h5 : (0 : ℝ) < ⌈((m : ℝ) / d)⁻¹⌉ := lt_of_lt_of_le (div_pos hd' hm') h1
  refine ⟨by exact_mod_cast h3, by exact_mod_cast h4, ?_⟩
  have : (0 : ℤ) < ⌈((m : ℝ) / d)⁻¹⌉ := by exact_mod_cast h5
  omega

/-! ### Engel -/

/-- One step of the Engel algorithm. -/
noncomputable def engelStep (r : ℝ) : ℝ := if r = 0 then 0 else (⌈r⁻¹⌉ : ℝ) * r - 1

/-- The remainders of the Engel expansion of `x`. -/
noncomputable def engelRem (x : ℝ) (n : ℕ) : ℝ := engelStep^[n] x

theorem engelRem_zero (x : ℝ) : engelRem x 0 = x := rfl

theorem engelRem_succ (x : ℝ) (n : ℕ) : engelRem x (n + 1) =
    if engelRem x n = 0 then 0 else (⌈(engelRem x n)⁻¹⌉ : ℝ) * engelRem x n - 1 :=
  Function.iterate_succ_apply' engelStep n x

theorem engelStep_rat (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ∃ m' : ℕ, m' < m ∧ engelStep ((m : ℝ) / d) = (m' : ℝ) / d := by
  obtain ⟨h3, h4, -⟩ := ceil_bounds m d hm hd
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨(⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat, by omega, ?_⟩
  unfold engelStep
  rw [ite_eq_right (div_ne_zero (by exact_mod_cast hm.ne') hd')]
  have hcast : (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      ((⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * m - d) := by
    rw [show (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  rw [hcast]
  field_simp

theorem exists_engelRem_eq_zero (d : ℕ) (hd : 0 < d) :
    ∀ m : ℕ, ∃ n, engelRem ((m : ℝ) / d) n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simp [engelRem]⟩
    · obtain ⟨m', hlt, heq⟩ := engelStep_rat m d hm hd
      obtain ⟨n, hn⟩ := ih m' hlt
      exact ⟨n + 1, by rw [engelRem, Function.iterate_succ_apply, heq]; exact hn⟩

theorem engelStep_irrational {r : ℝ} (h : Irrational r) (hr : 0 < r) :
    Irrational (engelStep r) ∧ 0 < engelStep r := by
  have ha : 1 ≤ ⌈r⁻¹⌉ := Int.one_le_ceil_iff.2 (inv_pos.2 hr)
  have hirr : Irrational ((⌈r⁻¹⌉ : ℝ) * r - 1) := by
    simpa using (h.intCast_mul (m := ⌈r⁻¹⌉) (by omega)).sub_natCast 1
  have hge : 1 ≤ (⌈r⁻¹⌉ : ℝ) * r := by
    have := mul_le_mul_of_nonneg_right (Int.le_ceil r⁻¹) hr.le
    rwa [inv_mul_cancel₀ hr.ne'] at this
  unfold engelStep
  rw [ite_eq_right hr.ne']
  exact ⟨hirr, lt_of_le_of_ne (by linarith) (Ne.symm hirr.ne_zero)⟩

/-- **For `x ≥ 0`, the Engel expansion is infinite iff `x` is irrational.** -/
theorem irrational_iff_engelRem_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    Irrational x ↔ ∀ n, engelRem x n ≠ 0 := by
  constructor
  · intro h
    have key : ∀ n, Irrational (engelRem x n) ∧ 0 < engelRem x n := by
      intro n
      induction n with
      | zero => exact ⟨h, lt_of_le_of_ne hx (Ne.symm h.ne_zero)⟩
      | succ n ih =>
        rw [engelRem, Function.iterate_succ_apply']
        exact engelStep_irrational ih.1 ih.2
    exact fun n => (key n).1.ne_zero
  · intro h hq
    obtain ⟨q, rfl⟩ := hq
    have hq0 : 0 ≤ q := by exact_mod_cast hx
    obtain ⟨n, hn⟩ := exists_engelRem_eq_zero q.den q.den_pos q.num.toNat
    refine h n ?_
    have : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)]
      exact (Rat.cast_def q).symm
    rwa [this] at hn

/-- **Problem 1 ⟺ the Engel expansion of `x₂` is infinite**. -/
theorem problem1_iff_engel_infinite :
    Rule30Prize.Problem1 ↔ ∀ n, engelRem BinaryIrrational.centerBinary n ≠ 0 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  refine irrational_iff_engelRem_ne_zero (tsum_nonneg fun t => ?_)
  split_ifs <;> positivity

/-! ### Sylvester -/

/-- One step of the greedy Egyptian-fraction (Sylvester) algorithm. -/
noncomputable def sylvesterStep (r : ℝ) : ℝ := if r = 0 then 0 else r - (⌈r⁻¹⌉ : ℝ)⁻¹

/-- The remainders of the Sylvester expansion of `x`. -/
noncomputable def sylvesterRem (x : ℝ) (n : ℕ) : ℝ := sylvesterStep^[n] x

theorem sylvesterStep_rat (m d : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ∃ m' d' : ℕ, m' < m ∧ 0 < d' ∧ sylvesterStep ((m : ℝ) / d) = (m' : ℝ) / d' := by
  obtain ⟨h3, h4, h1⟩ := ceil_bounds m d hm hd
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨(⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat, (⌈((m : ℝ) / d)⁻¹⌉ * d).toNat, by omega,
    by have : (0 : ℤ) < ⌈((m : ℝ) / d)⁻¹⌉ * d := by positivity
       omega, ?_⟩
  unfold sylvesterStep
  rw [ite_eq_right (div_ne_zero (by exact_mod_cast hm.ne') hd')]
  have c1 : (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      ((⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * m - d) := by
    rw [show (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℕ) : ℝ) =
      (((⌈((m : ℝ) / d)⁻¹⌉ * m - d).toNat : ℤ) : ℝ) from rfl, Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  have c2 : (((⌈((m : ℝ) / d)⁻¹⌉ * d).toNat : ℕ) : ℝ) = ((⌈((m : ℝ) / d)⁻¹⌉ : ℝ) * d) := by
    rw [show (((⌈((m : ℝ) / d)⁻¹⌉ * d).toNat : ℕ) : ℝ) =
      (((⌈((m : ℝ) / d)⁻¹⌉ * d).toNat : ℤ) : ℝ) from rfl,
      Int.toNat_of_nonneg (by have : (0 : ℤ) < ⌈((m : ℝ) / d)⁻¹⌉ * d := by positivity
                              omega)]
    push_cast; ring
  rw [c1, c2]
  field_simp

theorem exists_sylvesterRem_eq_zero : ∀ m d : ℕ, 0 < d → ∃ n, sylvesterRem ((m : ℝ) / d) n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro d hd
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simp [sylvesterRem]⟩
    · obtain ⟨m', d', hlt, hd', heq⟩ := sylvesterStep_rat m d hm hd
      obtain ⟨n, hn⟩ := ih m' hlt d' hd'
      exact ⟨n + 1, by rw [sylvesterRem, Function.iterate_succ_apply, heq]; exact hn⟩

theorem sylvesterStep_irrational {r : ℝ} (h : Irrational r) (hr : 0 < r) :
    Irrational (sylvesterStep r) ∧ 0 < sylvesterStep r := by
  have ha : 1 ≤ ⌈r⁻¹⌉ := Int.one_le_ceil_iff.2 (inv_pos.2 hr)
  have ha' : (0 : ℝ) < ⌈r⁻¹⌉ := by exact_mod_cast (show (0 : ℤ) < ⌈r⁻¹⌉ by omega)
  have hirr : Irrational (r - (⌈r⁻¹⌉ : ℝ)⁻¹) := by
    have := h.sub_ratCast (q := ((⌈r⁻¹⌉ : ℚ))⁻¹)
    simpa using this
  have hle : (⌈r⁻¹⌉ : ℝ)⁻¹ ≤ r := by
    rw [inv_le_comm₀ ha' hr]
    exact Int.le_ceil r⁻¹
  unfold sylvesterStep
  rw [ite_eq_right hr.ne']
  exact ⟨hirr, lt_of_le_of_ne (by linarith) (Ne.symm hirr.ne_zero)⟩

/-- **For `x ≥ 0`, the Sylvester expansion is infinite iff `x` is irrational.** -/
theorem irrational_iff_sylvesterRem_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    Irrational x ↔ ∀ n, sylvesterRem x n ≠ 0 := by
  constructor
  · intro h
    have key : ∀ n, Irrational (sylvesterRem x n) ∧ 0 < sylvesterRem x n := by
      intro n
      induction n with
      | zero => exact ⟨h, lt_of_le_of_ne hx (Ne.symm h.ne_zero)⟩
      | succ n ih =>
        rw [sylvesterRem, Function.iterate_succ_apply']
        exact sylvesterStep_irrational ih.1 ih.2
    exact fun n => (key n).1.ne_zero
  · intro h hq
    obtain ⟨q, rfl⟩ := hq
    have hq0 : 0 ≤ q := by exact_mod_cast hx
    obtain ⟨n, hn⟩ := exists_sylvesterRem_eq_zero q.num.toNat q.den q.den_pos
    refine h n ?_
    have : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)]
      exact (Rat.cast_def q).symm
    rwa [this] at hn

/-- **Problem 1 ⟺ the Sylvester expansion of `x₂` is infinite.** -/
theorem problem1_iff_sylvester_infinite :
    Rule30Prize.Problem1 ↔ ∀ n, sylvesterRem BinaryIrrational.centerBinary n ≠ 0 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  refine irrational_iff_sylvesterRem_ne_zero (tsum_nonneg fun t => ?_)
  split_ifs <;> positivity

/-! ### The factorial base -/

/-- The factorial-base remainders of `x`: `factRem x k = fract (k! · x)`. -/
noncomputable def factRem (x : ℝ) (k : ℕ) : ℝ := Int.fract ((k.factorial : ℝ) * x)

/-- The factorial-base digits: `factDigit x k = ⌊(k + 1) · factRem x k⌋`, the digit of `1/(k+1)!`. -/
noncomputable def factDigit (x : ℝ) (k : ℕ) : ℕ := ⌊((k + 1 : ℕ) : ℝ) * factRem x k⌋₊

theorem factRem_nonneg (x : ℝ) (k : ℕ) : 0 ≤ factRem x k := Int.fract_nonneg _

theorem factRem_lt_one (x : ℝ) (k : ℕ) : factRem x k < 1 := Int.fract_lt_one _

/-- The digit of `1/(k+1)!` lies in `[0, k]`. -/
theorem factDigit_le (x : ℝ) (k : ℕ) : factDigit x k ≤ k := by
  unfold factDigit
  have h1 := factRem_lt_one x k
  have h0 := factRem_nonneg x k
  have : ((k + 1 : ℕ) : ℝ) * factRem x k < ((k + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hfl := (Nat.floor_lt (by positivity)).2 this
  omega

/-- The remainder recursion `r_{k+1} = (k + 1) r_k - d_{k+1}`. -/
theorem factRem_succ (x : ℝ) (k : ℕ) :
    factRem x (k + 1) = ((k + 1 : ℕ) : ℝ) * factRem x k - factDigit x k := by
  have hy : 0 ≤ ((k + 1 : ℕ) : ℝ) * factRem x k := by
    have := factRem_nonneg x k
    positivity
  have e : ((k + 1).factorial : ℝ) * x =
      ((((k + 1 : ℕ) : ℤ) * ⌊(k.factorial : ℝ) * x⌋ : ℤ) : ℝ) + ((k + 1 : ℕ) : ℝ) * factRem x k := by
    rw [factRem, Nat.factorial_succ, Int.fract]
    push_cast
    ring
  rw [factRem, e, Int.fract_intCast_add, Int.fract, factDigit, ← Int.natCast_floor_eq_floor hy]
  push_cast
  ring

/-- **The factorial-base expansion**: for `n ≥ 1`,
`fract x = ∑_{1 ≤ j < n} d_{j+1}/(j+1)! + r_n/n!`. -/
theorem fract_eq_sum (x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Int.fract x = ∑ j ∈ Finset.Ico 1 n, (factDigit x j : ℝ) / ((j + 1).factorial : ℝ) +
      factRem x n / (n.factorial : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => simp [factRem]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih, factRem_succ]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hf' : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **The factorial-base expansion of `x` is infinite iff `x` is irrational**: no remainder
`fract (k! x)` vanishes. -/
theorem irrational_iff_factRem_ne_zero (x : ℝ) : Irrational x ↔ ∀ n, factRem x n ≠ 0 := by
  constructor
  · intro h n hn
    have hirr : Irrational ((n.factorial : ℝ) * x) := h.natCast_mul (Nat.factorial_ne_zero n)
    have e : (n.factorial : ℝ) * x = ⌊(n.factorial : ℝ) * x⌋ := by
      have := hn; unfold factRem Int.fract at this; linarith
    exact hirr.ne_int _ e
  · intro h hq
    obtain ⟨q, rfl⟩ := hq
    refine h q.den ?_
    have e : ((q.den.factorial : ℕ) : ℝ) * (q : ℝ) = ((q.num * ((q.den - 1).factorial : ℕ) : ℤ) : ℝ) := by
      have hd : (q.den : ℝ) ≠ 0 := by positivity
      rw [Rat.cast_def, ← Nat.mul_factorial_pred q.den_pos.ne']
      push_cast
      field_simp
    rw [factRem, e, Int.fract_intCast]

/-- **Problem 1 ⟺ the factorial-base expansion of `x₂` is infinite**: no `k! · x₂`
is an integer. -/
theorem problem1_iff_factorial_infinite :
    Rule30Prize.Problem1 ↔ ∀ n, factRem BinaryIrrational.centerBinary n ≠ 0 := by
  rw [BinaryIrrational.problem1_iff_irrational_binary]
  exact irrational_iff_factRem_ne_zero _

/-! ### Lüroth -/

/-- The Lüroth digit of `x ∈ (0, 1]`: `a = ⌊1/x⌋ + 1`, so that `1/a < x ≤ 1/(a - 1)`. -/
noncomputable def lurothDigit (x : ℝ) : ℕ := ⌊x⁻¹⌋₊ + 1

/-- The Lüroth map `T(x) = a(a - 1)x - (a - 1)`, with `a` the digit of `x`. It maps `(0, 1]` to
itself. -/
noncomputable def lurothStep (x : ℝ) : ℝ :=
  (lurothDigit x : ℝ) * ((lurothDigit x : ℝ) - 1) * x - ((lurothDigit x : ℝ) - 1)

/-- The remainders `Tⁿ(x)` of the Lüroth expansion. -/
noncomputable def lurothRem (x : ℝ) (n : ℕ) : ℝ := lurothStep^[n] x

/-- The Lüroth digits `a₁, a₂, …` of `x`: `x = 1/a₁ + 1/(a₁(a₁-1)a₂) + ⋯`. -/
noncomputable def lurothDigits (x : ℝ) (n : ℕ) : ℕ := lurothDigit (lurothRem x n)

theorem luroth_bounds {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (1 : ℝ) ≤ ⌊x⁻¹⌋₊ ∧ (⌊x⁻¹⌋₊ : ℝ) * x ≤ 1 ∧ 1 < ((⌊x⁻¹⌋₊ : ℝ) + 1) * x := by
  have h1 : (⌊x⁻¹⌋₊ : ℝ) ≤ x⁻¹ := Nat.floor_le (inv_nonneg.2 hx0.le)
  have h2 : x⁻¹ < (⌊x⁻¹⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).2 hx1
  refine ⟨by exact_mod_cast (Nat.one_le_floor_iff _).2 hinv, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h1 hx0.le
    rwa [inv_mul_cancel₀ hx0.ne'] at this
  · have := mul_lt_mul_of_pos_right h2 hx0
    rwa [inv_mul_cancel₀ hx0.ne'] at this

theorem lurothDigit_cast (x : ℝ) : (lurothDigit x : ℝ) = (⌊x⁻¹⌋₊ : ℝ) + 1 := by
  unfold lurothDigit; push_cast; ring

theorem lurothStep_eq (x : ℝ) :
    lurothStep x = ((⌊x⁻¹⌋₊ : ℝ) + 1) * ⌊x⁻¹⌋₊ * x - ⌊x⁻¹⌋₊ := by
  unfold lurothStep; rw [lurothDigit_cast]; ring

theorem lurothStep_mem {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 < lurothStep x ∧ lurothStep x ≤ 1 := by
  obtain ⟨hn, hnx, hnx'⟩ := luroth_bounds hx0 hx1
  rw [lurothStep_eq]
  constructor
  · nlinarith [mul_pos (by linarith : (0 : ℝ) < ⌊x⁻¹⌋₊) (by linarith : 0 < ((⌊x⁻¹⌋₊ : ℝ) + 1) * x - 1)]
  · nlinarith [mul_le_mul_of_nonneg_left hnx (by linarith : (0 : ℝ) ≤ (⌊x⁻¹⌋₊ : ℝ) + 1)]

theorem lurothRem_mem {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∀ n, 0 < lurothRem x n ∧ lurothRem x n ≤ 1
  | 0 => ⟨hx0, hx1⟩
  | n + 1 => by
    obtain ⟨h0, h1⟩ := lurothRem_mem hx0 hx1 n
    rw [lurothRem, Function.iterate_succ_apply', ← lurothRem]
    exact lurothStep_mem h0 h1

theorem two_le_lurothDigit {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : (2 : ℝ) ≤ lurothDigit x := by
  rw [lurothDigit_cast]; linarith [(luroth_bounds hx0 hx1).1]

theorem lurothStep_add (x : ℝ) :
    lurothStep x + ((lurothDigit x : ℝ) - 1) = (lurothDigit x : ℝ) * ((lurothDigit x : ℝ) - 1) * x := by
  unfold lurothStep; ring

/-- `x = 1/a + T(x)/(a(a - 1))`. -/
theorem luroth_affine {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x = 1 / (lurothDigit x : ℝ) +
      lurothStep x / ((lurothDigit x : ℝ) * ((lurothDigit x : ℝ) - 1)) := by
  have ha := two_le_lurothDigit hx0 hx1
  have h1 : (lurothDigit x : ℝ) ≠ 0 := by linarith
  have h2 : (lurothDigit x : ℝ) - 1 ≠ 0 := by linarith
  unfold lurothStep
  field_simp
  ring

/-- `x = A + B·Tⁿ(x)` with `A, B` rational and `0 < B ≤ 2⁻ⁿ`. -/
theorem luroth_affine_iter {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∀ n, ∃ A B : ℚ, 0 < B ∧ (B : ℝ) ≤ (1 / 2) ^ n ∧ x = A + B * lurothRem x n
  | 0 => ⟨0, 1, one_pos, by simp, by simp [lurothRem]⟩
  | n + 1 => by
    obtain ⟨A, B, hB, hBn, hx⟩ := luroth_affine_iter hx0 hx1 n
    obtain ⟨hz0, hz1⟩ := lurothRem_mem hx0 hx1 n
    have e := luroth_affine hz0 hz1
    have ha := two_le_lurothDigit hz0 hz1
    obtain ⟨a, haa⟩ : ∃ a, lurothDigit (lurothRem x n) = a := ⟨_, rfl⟩
    rw [haa] at e ha
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    have hD : (2 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 1) := by nlinarith
    refine ⟨A + B / a, B / (a * (a - 1)), ?_, ?_, ?_⟩
    · have : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      have : (0 : ℚ) < (a : ℚ) * ((a : ℚ) - 1) := by nlinarith
      positivity
    · push_cast
      rw [pow_succ, div_le_iff₀ (by linarith)]
      nlinarith
    · rw [lurothRem, Function.iterate_succ_apply', ← lurothRem]
      push_cast
      linear_combination hx + (B : ℝ) * e

/-- Points that share their first `n` digits are within `2⁻ⁿ`. -/
theorem luroth_close : ∀ n {x y : ℝ}, 0 < x → x ≤ 1 → 0 < y → y ≤ 1 →
    (∀ k, k < n → lurothDigits x k = lurothDigits y k) → |x - y| ≤ (1 / 2) ^ n
  | 0, x, y, hx0, hx1, hy0, hy1, _ => by
    rw [pow_zero, abs_le]; constructor <;> linarith
  | n + 1, x, y, hx0, hx1, hy0, hy1, h => by
    have hd : lurothDigit x = lurothDigit y := h 0 (by omega)
    obtain ⟨hTx0, hTx1⟩ := lurothStep_mem hx0 hx1
    obtain ⟨hTy0, hTy1⟩ := lurothStep_mem hy0 hy1
    have ih := luroth_close n hTx0 hTx1 hTy0 hTy1 (fun k hk => h (k + 1) (by omega))
    have ex := lurothStep_add x
    have ey := lurothStep_add y
    have ha := two_le_lurothDigit hy0 hy1
    rw [hd] at ex
    obtain ⟨a, haa⟩ : ∃ a, lurothDigit y = a := ⟨_, rfl⟩
    rw [haa] at ex ey ha
    have hD : (2 : ℝ) ≤ (a : ℝ) * ((a : ℝ) - 1) := by nlinarith
    have hxy : (x - y) * ((a : ℝ) * ((a : ℝ) - 1)) = lurothStep x - lurothStep y := by
      linear_combination ey - ex
    have habs : |x - y| * ((a : ℝ) * ((a : ℝ) - 1)) = |lurothStep x - lurothStep y| := by
      rw [← hxy, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < (a : ℝ) * ((a : ℝ) - 1))]
    rw [pow_succ]
    nlinarith [abs_nonneg (x - y)]

/-- **The Lüroth digits determine the point.** -/
theorem luroth_injective {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h : ∀ k, lurothDigits x k = lurothDigits y k) : x = y := by
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  linarith [luroth_close n hx0 hx1 hy0 hy1 (fun k _ => h k)]

/-- A rational point `k/q` of `(0, 1]` is mapped to another point `k'/q`. -/
theorem lurothStep_rat {q k : ℕ} (hq : 0 < q) (hk : 1 ≤ k) (hkq : k ≤ q) :
    ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ q ∧ lurothStep ((k : ℝ) / q) = (k' : ℝ) / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hz0 : 0 < (k : ℝ) / q := div_pos (by exact_mod_cast hk) hq'
  have hz1 : (k : ℝ) / q ≤ 1 := (div_le_one hq').2 (by exact_mod_cast hkq)
  obtain ⟨h0, h1⟩ := lurothStep_mem hz0 hz1
  obtain ⟨a, ha⟩ : ∃ a, lurothDigit ((k : ℝ) / q) = a := ⟨_, rfl⟩
  have hT : lurothStep ((k : ℝ) / q) =
      (((a : ℤ) * ((a : ℤ) - 1) * k - ((a : ℤ) - 1) * q : ℤ) : ℝ) / q := by
    unfold lurothStep
    rw [ha]
    push_cast
    field_simp
  rw [hT] at h0 h1
  generalize (a : ℤ) * ((a : ℤ) - 1) * k - ((a : ℤ) - 1) * q = m at hT h0 h1
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by
      have := mul_pos h0 hq'
      rwa [div_mul_cancel₀ _ hq'.ne'] at this
    exact_mod_cast this
  have hmq : m ≤ q := by
    have : (m : ℝ) ≤ q := (div_le_one hq').1 h1
    exact_mod_cast this
  refine ⟨m.toNat, by omega, by omega, ?_⟩
  rw [hT]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hm0.le).symm

theorem lurothRem_rat {q k : ℕ} (hq : 0 < q) (hk : 1 ≤ k) (hkq : k ≤ q) :
    ∀ n, ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ q ∧ lurothRem ((k : ℝ) / q) n = (k' : ℝ) / q
  | 0 => ⟨k, hk, hkq, rfl⟩
  | n + 1 => by
    obtain ⟨k', h1, h2, h⟩ := lurothRem_rat hq hk hkq n
    obtain ⟨k'', h3, h4, h5⟩ := lurothStep_rat hq h1 h2
    refine ⟨k'', h3, h4, ?_⟩
    rw [lurothRem, Function.iterate_succ_apply', ← lurothRem, h, h5]

/-- **Rational points have eventually periodic Lüroth digits**: the orbit of `k/q` stays in the
finite set `{1/q, …, q/q}`. -/
theorem lurothDigits_eventuallyPeriodic_of_rat {q k : ℕ} (hq : 0 < q) (hk : 1 ≤ k) (hkq : k ≤ q) :
    ∃ K P, 0 < P ∧ ∀ n, K ≤ n →
      lurothDigits ((k : ℝ) / q) (n + P) = lurothDigits ((k : ℝ) / q) n := by
  have hfin : ((fun j : ℕ => (j : ℝ) / q) '' Set.Icc 1 q).Finite := (Set.finite_Icc 1 q).image _
  obtain ⟨i, j, hij, hEq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := lurothRem ((k : ℝ) / q)) (fun n => by
      obtain ⟨k', h1, h2, h⟩ := lurothRem_rat hq hk hkq n
      exact ⟨k', ⟨h1, h2⟩, h.symm⟩) hfin
  refine ⟨i, j - i, by omega, fun n hn => ?_⟩
  unfold lurothDigits
  congr 1
  obtain ⟨s, rfl⟩ : ∃ s, n = i + s := ⟨n - i, by omega⟩
  unfold lurothRem at hEq ⊢
  rw [show i + s + (j - i) = s + j by omega, show i + s = s + i by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, hEq]

/-- A remainder that comes back after `P ≥ 1` steps makes the point rational. -/
theorem not_irrational_of_lurothRem_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {K P : ℕ} (hP : 0 < P)
    (h : lurothRem x (K + P) = lurothRem x K) : ¬ Irrational x := by
  obtain ⟨hy0, hy1⟩ := lurothRem_mem hx0 hx1 K
  obtain ⟨A, B, -, hBP, hyA⟩ := luroth_affine_iter hy0 hy1 P
  have hyy : lurothRem (lurothRem x K) P = lurothRem x K := by
    unfold lurothRem at h ⊢
    rw [← Function.iterate_add_apply, Nat.add_comm P K]
    exact h
  rw [hyy] at hyA
  have hB1 : (B : ℝ) < 1 := lt_of_le_of_lt hBP (pow_lt_one₀ (by norm_num) (by norm_num) hP.ne')
  have hyq : lurothRem x K = ((A / (1 - B) : ℚ) : ℝ) := by
    have hne : (1 : ℝ) - B ≠ 0 := by linarith
    push_cast
    field_simp
    linarith
  obtain ⟨A', B', -, -, hxA⟩ := luroth_affine_iter hx0 hx1 K
  intro hirr
  refine hirr ⟨A' + B' * (A / (1 - B)), ?_⟩
  rw [hxA, hyq]
  push_cast
  ring

/-- **For `x ∈ (0, 1]`, the Lüroth digits are eventually periodic iff `x` is rational.** -/
theorem lurothDigits_eventuallyPeriodic_iff {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (∃ K P, 0 < P ∧ ∀ n, K ≤ n → lurothDigits x (n + P) = lurothDigits x n) ↔
      ¬ Irrational x := by
  constructor
  · rintro ⟨K, P, hP, hper⟩
    refine not_irrational_of_lurothRem_eq hx0 hx1 (K := K) hP ?_
    have hm := lurothRem_mem hx0 hx1
    refine luroth_injective (hm (K + P)).1 (hm (K + P)).2 (hm K).1 (hm K).2 fun j => ?_
    have := hper (j + K) (by omega)
    unfold lurothDigits lurothRem at this ⊢
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show j + (K + P) = j + K + P by omega]
    exact this
  · intro hrat
    unfold Irrational at hrat
    rw [not_not] at hrat
    obtain ⟨q, rfl⟩ := hrat
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hx0
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = q.num :=
      ⟨q.num.toNat, Int.toNat_of_nonneg (Rat.num_pos.2 hq0).le⟩
    have hx : (q : ℝ) = (k : ℝ) / q.den := by
      rw [Rat.cast_def, ← hk]
      push_cast
      rfl
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < k := by
        rw [hx] at hx0
        have := mul_pos hx0 hden
        rwa [div_mul_cancel₀ _ hden.ne'] at this
      exact_mod_cast this
    have hkq : k ≤ q.den := by
      rw [hx] at hx1
      have : (k : ℝ) ≤ q.den := (div_le_one hden).1 hx1
      exact_mod_cast this
    rw [hx]
    exact lurothDigits_eventuallyPeriodic_of_rat q.den_pos hk1 hkq

theorem centerBinary_mem : 0 < BinaryIrrational.centerBinary ∧ BinaryIrrational.centerBinary ≤ 1 := by
  rw [BinaryIrrational.centerBinary_eq_baseValue]
  exact ⟨BinaryIrrational.baseValue_pos (le_refl 2) c (s := 0) (by decide),
    BinaryIrrational.baseValue_le_one (le_refl 2) c⟩

/-- **Problem 1 ⟺ the Lüroth expansion of `x₂` is not eventually periodic**. -/
theorem problem1_iff_luroth_not_eventuallyPeriodic :
    Rule30Prize.Problem1 ↔
      ¬ ∃ K P, 0 < P ∧ ∀ n, K ≤ n → lurothDigits BinaryIrrational.centerBinary (n + P) =
        lurothDigits BinaryIrrational.centerBinary n := by
  rw [BinaryIrrational.problem1_iff_irrational_binary,
    lurothDigits_eventuallyPeriodic_iff centerBinary_mem.1 centerBinary_mem.2, not_not]

end Rule30Equivalents.Expansions
