module

public import Rule30Equivalents.RandomConfigurations
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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
# The linear complexity profile of a random sequence

The linear complexity `Lₙ(v)` of the prefix of length `n` of a bit sequence `v` is the length of
the shortest linear feedback shift register over `𝔽₂` that generates it
(`StrongerStatements.linComplexity`). For almost every sequence `Lₙ = n/2 + O(log n)`
(Niederreiter's theorem); here it follows from two first-moment bounds and the Borel–Cantelli
lemma.

* `measure_generates`: a given register of length `d` generates the prefix of length `n` with
  probability `2^-(n-d)`, since each later bit must match its prediction
  (`RandomConfigurations.measure_triangular`). Counting the registers,
  `Lₙ ≤ m` with probability at most `2^(m+1) 2^-(n-m)` (`measure_linComplexity_le`).
* `linComplexity_le_of_rows`: if the rows `(v(t + i))_{i < ℓ}`, `t < n - ℓ`, of the Hankel matrix
  are linearly independent, a register of length `ℓ` generates the prefix, as a matrix with
  one-to-one transpose is onto (`mulVec_surjective_of_vecMul_injective`). A fixed nonzero
  combination of the rows vanishes with probability `2^-ℓ`: flipping the coin at its last index
  plus `j` flips its `j`-th entry and no earlier one (`measure_rows_vanish`). So `Lₙ > ℓ` with
  probability at most `2^(n-ℓ) 2^-ℓ` (`measure_lt_linComplexity`).
* `ae_eventually_linComplexity`: so for almost every sequence `|2Lₙ - n| ≤ 2 ⌊log₂ n⌋ + 2` from
  some `n` on. Both tails have probability at most `2 · 4^-(⌊log₂ n⌋ + 1)`, a summable sequence by
  Cauchy condensation. Hence `ae_tendsto_linComplexity`: `Lₙ/n → 1/2` almost surely, and
  `ae_tendsto_linComplexity_trace`: for almost every configuration the center column satisfies
  the hypothesis of `StrongerStatements.problem1_of_linComplexity_tendsto`.
-/

@[expose] public section

namespace Rule30Equivalents.LinearComplexity

open MeasureTheory Filter Topology Genericity RandomConfigurations StrongerStatements
open scoped Matrix

/-! ### Short registers -/

/-- A bit as an element of `𝔽₂`. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_not (b : Bool) : bit (!b) = bit b + 1 := by
  cases b <;> decide

theorem decide_add_one_eq (x y : ZMod 2) : decide (x + 1 = y) = !decide (x = y) := by
  revert x y
  decide

/-- The register `a` of length `d` generates the prefix of length `n` of `v`. -/
def Generates (v : ℕ → Bool) (n d : ℕ) (a : Fin d → ZMod 2) : Prop :=
  ∀ t, t + d < n → bit (v (t + d)) = ∑ i, a i * bit (v (t + i))

theorem linComplexity_eq (v : ℕ → Bool) (n : ℕ) :
    linComplexity v n = sInf {d | ∃ a, Generates v n d a} := rfl

/-- Every register of length `n` generates the prefix of length `n`. -/
theorem generates_self (v : ℕ → Bool) (n : ℕ) : Generates v n n fun _ => 0 :=
  fun t ht => absurd ht (by omega)

theorem linComplexity_le_self (v : ℕ → Bool) (n : ℕ) : linComplexity v n ≤ n :=
  Nat.sInf_le ⟨_, generates_self v n⟩

/-- **A register generates the prefix with probability `2^-(n - d)`**: flipping the coin at
`t + d` flips the `t`-th prediction test and none of the earlier ones. -/
theorem measure_generates (n d : ℕ) (a : Fin d → ZMod 2) :
    coins ℕ {v | Generates v n d a} = 2⁻¹ ^ (n - d) := by
  have h := measure_triangular (ι := ℕ)
    (fun t v => decide (bit (v (t + d)) = ∑ i, a i * bit (v (t + i))))
    (fun t => measurable_of_forall_lt (t + d + 1) fun v w hvw => by
      have h1 : v (t + d) = w (t + d) := hvw _ (by omega)
      have h2 : ∑ i, a i * bit (v (t + i)) = ∑ i, a i * bit (w (t + i)) :=
        Finset.sum_congr rfl fun i _ => by rw [hvw (t + i) (by have := i.isLt; omega)]
      simp only [h1, h2])
    (fun t => t + d)
    (fun t v => by
      have hne : ∀ i : Fin d, t + (i : ℕ) ≠ t + d := fun i => by have := i.isLt; omega
      simp only [Function.update_apply, hne, ite_false, ite_true, bit_not]
      exact decide_add_one_eq _ _)
    (fun t v t' ht' => by
      have h1 : t' + d ≠ t + d := by omega
      have h2 : ∀ i : Fin d, t' + (i : ℕ) ≠ t + d := fun i => by have := i.isLt; omega
      simp only [Function.update_apply, h1, h2, ite_false])
    (fun _ => true) (n - d)
  rw [← h]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Generates, decide_eq_true_eq]
  exact forall_congr' fun t => ⟨fun h ht => h (by omega), fun h ht => h (by omega)⟩

theorem two_pow_mul_inv_pow (a : ℕ) : (2 : ENNReal) ^ a * 2⁻¹ ^ a = 1 := by
  rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]

/-- **Short registers are rare**: `Lₙ ≤ m` with probability at most `2^(m+1) 2^-(n-m)`. -/
theorem measure_linComplexity_le (n m : ℕ) :
    coins ℕ {v | linComplexity v n ≤ m} ≤ 2 ^ (m + 1) * 2⁻¹ ^ (n - m) := by
  classical
  -- `Lₙ ≤ m` means that some register of length `d ≤ m` generates the prefix
  have hsub : {v | linComplexity v n ≤ m} ⊆
      ⋃ q : (Σ d : Fin (m + 1), Fin d → ZMod 2), {v | Generates v n q.1 q.2} := by
    intro v hv
    obtain ⟨a, ha⟩ := Nat.sInf_mem (s := {d | ∃ a, Generates v n d a}) ⟨n, _, generates_self v n⟩
    exact Set.mem_iUnion.2 ⟨⟨⟨_, Nat.lt_succ_of_le hv⟩, a⟩, ha⟩
  have hcard : Fintype.card (Σ d : Fin (m + 1), Fin d → ZMod 2) ≤ 2 ^ (m + 1) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun d => 2 ^ d) (m + 1)]
    exact (Nat.geomSum_lt (le_refl 2) fun i hi => Finset.mem_range.1 hi).le
  calc coins ℕ {v | linComplexity v n ≤ m}
      ≤ ∑ q : (Σ d : Fin (m + 1), Fin d → ZMod 2), coins ℕ {v | Generates v n q.1 q.2} :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _q : (Σ d : Fin (m + 1), Fin d → ZMod 2), (2⁻¹ : ENNReal) ^ (n - m) :=
        Finset.sum_le_sum fun q _ => by
          rw [measure_generates]
          exact pow_le_pow_right_of_le_one' (by norm_num) (by have := q.1.isLt; omega)
    _ ≤ 2 ^ (m + 1) * 2⁻¹ ^ (n - m) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard

/-! ### Long registers -/

/-- A matrix whose transpose is one-to-one is onto. -/
theorem mulVec_surjective_of_vecMul_injective {K : Type*} [Field K] {r ℓ : ℕ}
    (M : Matrix (Fin r) (Fin ℓ) K) (h : Function.Injective fun u => u ᵥ* M) :
    Function.Surjective M.mulVec := by
  have hker : LinearMap.ker Mᵀ.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro u w huw
    apply h
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using huw
  have hrank : M.rank = r := by
    rw [← Matrix.rank_transpose]
    have := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
    rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at this
    exact this
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hrank)
  intro y
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop y
  exact ⟨x, hx⟩

/-- **Independent Hankel rows give a short register**: if no nonzero combination of the rows
`(v(t + i))_{i < ℓ}`, `t < n - ℓ`, vanishes, a register of length `ℓ` generates the prefix of
length `n`. -/
theorem linComplexity_le_of_rows {v : ℕ → Bool} {n ℓ : ℕ}
    (h : ∀ u : Fin (n - ℓ) → ZMod 2, (∀ j : Fin ℓ, ∑ t, u t * bit (v (t + j)) = 0) → u = 0) :
    linComplexity v n ≤ ℓ := by
  let M : Matrix (Fin (n - ℓ)) (Fin ℓ) (ZMod 2) := Matrix.of fun t i => bit (v (t + i))
  obtain ⟨a, ha⟩ := mulVec_surjective_of_vecMul_injective M (fun u w huw => by
    have h0 : (u - w) ᵥ* M = 0 := by
      rw [Matrix.sub_vecMul]
      exact sub_eq_zero.2 huw
    refine sub_eq_zero.1 (h (u - w) fun j => ?_)
    have := congrFun h0 j
    simpa [Matrix.vecMul, dotProduct, M] using this) (fun t => bit (v (t + ℓ)))
  refine Nat.sInf_le ⟨a, fun t ht => ?_⟩
  show bit (v (t + ℓ)) = ∑ i, a i * bit (v (t + i))
  have := congrFun ha ⟨t, by omega⟩
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **A fixed nonzero combination of the rows vanishes with probability `2^-ℓ`**: with `s` the last
index of `u`, flipping the coin at `s + j` flips the `j`-th entry of the combination and changes
none of the earlier ones. -/
theorem measure_rows_vanish {r : ℕ} (u : Fin r → ZMod 2) (hu : u ≠ 0) (ℓ : ℕ) :
    coins ℕ {v | ∀ j < ℓ, ∑ t, u t * bit (v (t + j)) = 0} = 2⁻¹ ^ ℓ := by
  classical
  -- the last index of `u`
  obtain ⟨s, hs, hlast⟩ : ∃ s : Fin r, u s ≠ 0 ∧ ∀ t : Fin r, s < t → u t = 0 := by
    have hne : (Finset.univ.filter fun t => u t ≠ 0).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      exact hu (funext fun t => by simpa using hemp (Finset.mem_univ t))
    refine ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2, fun t ht => ?_⟩
    by_contra h
    exact absurd (Finset.le_max' _ t (Finset.mem_filter.2 ⟨Finset.mem_univ t, h⟩)) (not_le.2 ht)
  have hus : u s = 1 := by
    revert hs
    generalize u s = x
    revert x
    decide
  have h := measure_triangular (ι := ℕ) (fun j v => decide (∑ t, u t * bit (v (t + j)) = 0))
    (fun j => measurable_of_forall_lt (r + j) fun v w hvw => by
      have : ∀ t : Fin r, v (t + j) = w (t + j) := fun t => hvw _ (by have := t.isLt; omega)
      simp only [this])
    (fun j => s + j)
    (fun j v => by
      have hsplit : ∀ t : Fin r, u t * bit (Function.update v (s + j) (!v (s + j)) (t + j)) =
          u t * bit (v (t + j)) + if t = s then 1 else 0 := fun t => by
        by_cases hts : t = s
        · subst hts
          rw [Function.update_self, bit_not, hus, ite_eq_left rfl]
          ring
        · have hne : (t : ℕ) + j ≠ s + j := fun h => hts (Fin.ext (by omega))
          rw [Function.update_of_ne hne, ite_eq_right hts, add_zero]
      simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact decide_add_one_eq _ _)
    (fun j v j' hj' => by
      have hterm : ∀ t : Fin r,
          u t * bit (Function.update v (s + j) (!v (s + j)) (t + j')) = u t * bit (v (t + j')) :=
        fun t => by
          rcases le_or_gt t s with hts | hts
          · rw [Function.update_of_ne (by
              have : (t : ℕ) ≤ s := hts
              omega)]
          · rw [hlast t hts, zero_mul, zero_mul]
      simp only [hterm])
    (fun _ => true) ℓ
  rw [← h]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq]

/-- **Long registers are rare**: `Lₙ > ℓ` with probability at most `2^(n-ℓ) 2^-ℓ`. -/
theorem measure_lt_linComplexity (n ℓ : ℕ) :
    coins ℕ {v | ℓ < linComplexity v n} ≤ 2 ^ (n - ℓ) * 2⁻¹ ^ ℓ := by
  classical
  have hsub : {v | ℓ < linComplexity v n} ⊆
      ⋃ u ∈ (Finset.univ.filter fun u : Fin (n - ℓ) → ZMod 2 => u ≠ 0),
        {v | ∀ j < ℓ, ∑ t, u t * bit (v (t + j)) = 0} := by
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      not_exists] at hnot
    refine absurd (linComplexity_le_of_rows fun u hu => ?_) (not_le.2 hv)
    by_contra hu0
    exact hnot u hu0 fun j hj => hu ⟨j, hj⟩
  calc coins ℕ {v | ℓ < linComplexity v n}
      ≤ ∑ u ∈ (Finset.univ.filter fun u : Fin (n - ℓ) → ZMod 2 => u ≠ 0),
          coins ℕ {v | ∀ j < ℓ, ∑ t, u t * bit (v (t + j)) = 0} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ _u ∈ (Finset.univ.filter fun u : Fin (n - ℓ) → ZMod 2 => u ≠ 0), (2⁻¹ : ENNReal) ^ ℓ :=
        Finset.sum_congr rfl fun u hu => measure_rows_vanish u (Finset.mem_filter.1 hu).2 ℓ
    _ ≤ 2 ^ (n - ℓ) * 2⁻¹ ^ ℓ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have : (Finset.univ.filter fun u : Fin (n - ℓ) → ZMod 2 => u ≠ 0).card ≤ 2 ^ (n - ℓ) :=
          (Finset.card_filter_le _ _).trans (by simp [ZMod.card])
        exact_mod_cast this

/-! ### Both tails, almost surely -/

/-- The lower tail: `2Lₙ + 2k ≤ n` with probability at most `2 · 4^-k`. -/
theorem measure_lower_tail (n k : ℕ) :
    coins ℕ {v | 2 * linComplexity v n + 2 * k ≤ n} ≤ 2 * 2⁻¹ ^ (2 * k) := by
  rcases Nat.lt_or_ge n (2 * k) with h | h
  · have hemp : {v | 2 * linComplexity v n + 2 * k ≤ n} = ∅ :=
      Set.eq_empty_of_forall_notMem fun v hv => by
        simp only [Set.mem_ofPred_eq] at hv
        omega
    rw [hemp, measure_empty]
    exact zero_le
  set m := (n - 2 * k) / 2 with hm
  calc coins ℕ {v | 2 * linComplexity v n + 2 * k ≤ n}
      ≤ coins ℕ {v | linComplexity v n ≤ m} := measure_mono fun v hv => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        omega
    _ ≤ 2 ^ (m + 1) * 2⁻¹ ^ (n - m) := measure_linComplexity_le n m
    _ = 2 * 2⁻¹ ^ (2 * k) * ((2 ^ m * 2⁻¹ ^ m) * 2⁻¹ ^ (n - 2 * m - 2 * k)) := by
        rw [show n - m = m + 2 * k + (n - 2 * m - 2 * k) by omega, pow_add, pow_add, pow_succ]
        ring
    _ ≤ 2 * 2⁻¹ ^ (2 * k) := by
        rw [two_pow_mul_inv_pow, one_mul]
        exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (by norm_num))

/-- The upper tail: `n + 2k < 2Lₙ` with probability at most `2 · 4^-k`. -/
theorem measure_upper_tail (n k : ℕ) :
    coins ℕ {v | n + 2 * k < 2 * linComplexity v n} ≤ 2 * 2⁻¹ ^ (2 * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [mul_zero, pow_zero, mul_one]
    exact prob_le_one.trans (by norm_num)
  rcases Nat.lt_or_ge (n + 1) (2 * k) with h | h
  · have hemp : {v | n + 2 * k < 2 * linComplexity v n} = ∅ :=
      Set.eq_empty_of_forall_notMem fun v hv => by
        simp only [Set.mem_ofPred_eq] at hv
        have := linComplexity_le_self v n
        omega
    rw [hemp, measure_empty]
    exact zero_le
  -- `e` equations for a register of length `n - e`, with `n - 2e + 1 ≥ 2k`
  obtain ⟨e, he1, he2⟩ : ∃ e, n - 2 * k ≤ 2 * e ∧ 2 * e ≤ n + 1 - 2 * k :=
    ⟨(n + 1 - 2 * k) / 2, by omega, by omega⟩
  obtain ⟨f, hf, hfk⟩ : ∃ f, n - e = e + f ∧ 2 * k ≤ f + 1 := ⟨n - 2 * e, by omega, by omega⟩
  calc coins ℕ {v | n + 2 * k < 2 * linComplexity v n}
      ≤ coins ℕ {v | n - e < linComplexity v n} := measure_mono fun v hv => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        omega
    _ ≤ 2 ^ (n - (n - e)) * 2⁻¹ ^ (n - e) := measure_lt_linComplexity n (n - e)
    _ = 2⁻¹ ^ f := by
        rw [show n - (n - e) = e by omega, hf, pow_add, ← mul_assoc, two_pow_mul_inv_pow, one_mul]
    _ = 2 * 2⁻¹ ^ (f + 1) := by
        rw [pow_succ, mul_comm (2⁻¹ ^ f), ← mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * 2⁻¹ ^ (2 * k) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right_of_le_one' (by norm_num) hfk) zero_le

/-- The bounds `2 · 4^-(⌊log₂ n⌋ + 1)` are summable, by Cauchy condensation. -/
theorem tsum_tail_ne_top :
    ∑' n : ℕ, (2 : ENNReal) * 2⁻¹ ^ (2 * (Nat.log 2 n + 1)) ≠ ⊤ := by
  have hanti : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n →
      (2 : ENNReal) * 2⁻¹ ^ (2 * (Nat.log 2 n + 1)) ≤ 2 * 2⁻¹ ^ (2 * (Nat.log 2 m + 1)) :=
    fun m n _ hmn => mul_le_mul_of_nonneg_left (pow_le_pow_right_of_le_one' (by norm_num) (by
      have := Nat.log_mono_right (b := 2) hmn
      omega)) zero_le
  refine ne_top_of_le_ne_top ?_ (ENNReal.le_tsum_condensed hanti)
  have hterm : ∀ j : ℕ, (2 : ENNReal) ^ j * (2 * 2⁻¹ ^ (2 * (Nat.log 2 (2 ^ j) + 1))) =
      2⁻¹ ^ (j + 1) := fun j => by
    rw [Nat.log_pow (by norm_num), show 2 * (j + 1) = j + (j + 1) + 1 by ring, pow_add,
      pow_add, pow_one]
    calc (2 : ENNReal) ^ j * (2 * (2⁻¹ ^ j * 2⁻¹ ^ (j + 1) * 2⁻¹))
        = (2 ^ j * 2⁻¹ ^ j) * (2 * 2⁻¹) * 2⁻¹ ^ (j + 1) := by ring
      _ = 2⁻¹ ^ (j + 1) := by
        rw [two_pow_mul_inv_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul,
          one_mul]
  simp only [hterm]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)), ?_⟩
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j =>
    pow_le_pow_right_of_le_one' (by norm_num : (2⁻¹ : ENNReal) ≤ 1) (Nat.le_succ j))
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

/-- **The linear complexity profile of a random sequence** (Niederreiter): for almost every
fair-coin sequence, `|2Lₙ - n| ≤ 2 ⌊log₂ n⌋ + 2` from some `n` on. -/
theorem ae_eventually_linComplexity :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ n in atTop, 2 * linComplexity v n ≤ n + 2 * (Nat.log 2 n + 1) ∧
      n < 2 * linComplexity v n + 2 * (Nat.log 2 n + 1) := by
  have h1 := ae_eventually_notMem (μ := coins ℕ)
    (s := fun n => {v | 2 * linComplexity v n + 2 * (Nat.log 2 n + 1) ≤ n})
    (ne_top_of_le_ne_top tsum_tail_ne_top
      (ENNReal.tsum_le_tsum fun n => measure_lower_tail n _))
  have h2 := ae_eventually_notMem (μ := coins ℕ)
    (s := fun n => {v | n + 2 * (Nat.log 2 n + 1) < 2 * linComplexity v n})
    (ne_top_of_le_ne_top tsum_tail_ne_top
      (ENNReal.tsum_le_tsum fun n => measure_upper_tail n _))
  filter_upwards [h1, h2] with v hv1 hv2
  filter_upwards [hv1, hv2] with n hn1 hn2
  simp only [not_le, not_lt] at hn1 hn2
  exact ⟨hn2, hn1⟩

/-- `⌊log₂ n⌋ / n → 0`. -/
theorem tendsto_log_div : Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) / n) atTop (𝓝 0) := by
  have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  have hlog' : Tendsto (fun n : ℕ => Real.log n / Real.log 2 / n) atTop (𝓝 0) := by
    have := hlog.div_const (Real.log 2)
    rw [zero_div] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    ring
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlog'
  gcongr
  have := Real.natLog_le_logb n 2
  rwa [Real.logb, Nat.cast_ofNat] at this

/-- **`Lₙ/n → 1/2` for almost every fair-coin sequence.** -/
theorem ae_tendsto_linComplexity :
    ∀ᵐ v ∂(coins ℕ), Tendsto (fun n : ℕ => (linComplexity v n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  filter_upwards [ae_eventually_linComplexity] with v hv
  -- `|Lₙ/n - 1/2| ≤ (⌊log₂ n⌋ + 1)/n`
  have hbound : Tendsto (fun n : ℕ => ((Nat.log 2 n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have := tendsto_log_div.add (tendsto_one_div_atTop_nhds_zero_nat)
    rw [add_zero] at this
    exact this.congr fun n => by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hbound
  filter_upwards [hv, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have h1 : (2 * linComplexity v n : ℝ) ≤ n + 2 * ((Nat.log 2 n : ℝ) + 1) := by
    exact_mod_cast hn.1
  have h2 : (n : ℝ) < 2 * linComplexity v n + 2 * ((Nat.log 2 n : ℝ) + 1) := by
    exact_mod_cast hn.2
  have habs : |(2 * linComplexity v n : ℝ) - n| ≤ 2 * ((Nat.log 2 n : ℝ) + 1) :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have e : (linComplexity v n : ℝ) / n - 1 / 2 = ((2 * linComplexity v n : ℝ) - n) / (2 * n) := by
    field_simp
  calc ‖(linComplexity v n : ℝ) / n - 1 / 2‖ = |(2 * linComplexity v n : ℝ) - n| / (2 * n) := by
        rw [Real.norm_eq_abs, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
    _ ≤ 2 * ((Nat.log 2 n : ℝ) + 1) / (2 * n) := by gcongr
    _ = ((Nat.log 2 n : ℝ) + 1) / n := by field_simp

/-- **For almost every configuration the center column has `Lₙ/n → 1/2`**, the hypothesis of
`StrongerStatements.problem1_of_linComplexity_tendsto` with the seed replaced by the
configuration. -/
theorem ae_tendsto_linComplexity_trace :
    ∀ᵐ x ∂(coins ℤ),
      Tendsto (fun n : ℕ => (linComplexity (trace x) n : ℝ) / n) atTop (𝓝 (1 / 2)) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_tendsto_linComplexity

end Rule30Equivalents.LinearComplexity
