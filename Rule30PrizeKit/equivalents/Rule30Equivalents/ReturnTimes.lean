module

public import Rule30Equivalents.LongestRuns
public import Rule30Equivalents.LinearComplexity
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
# Return times of a random sequence

The prefix of length `n` of a fair-coin sequence first occurs again after about `2^n` steps: for
almost every sequence `(log₂ R_n)/n → 1`, the recurrence theorem of Wyner and Ziv, and of Ornstein
and Weiss, for fair coins.

* `returnTime v n`: the least `s ≥ 1` at which the prefix of length `n` occurs again.
* `measure_recurs`: the prefix occurs again at a given `s ≥ 1` with probability `2^-n`: flipping the
  coin at `s + j` decides the `j`-th comparison and none of the earlier ones
  (`RandomConfigurations.measure_triangular`). So it occurs again by time `M` with probability at
  most `M 2^-n` (`measure_exists_recurs_le`).
* `measure_not_recurs_blocks`: it does not occur at the starts `k n` of the blocks `k = 1, …, K`
  with probability `(1 - 2^-n)^K ≤ 1/(1 + K 2^-n)`: the blocks are independent fair words
  (`RandomConfigurations.map_blocks`), so given the first block each later one differs from it
  with probability `1 - 2^-n`.
* `ae_eventually_returnTime`: by the Borel–Cantelli lemma, for almost every sequence
  `2^n/(n + 1)² < R_n ≤ n (n + 1)² 2^n` from some `n` on, so `(log₂ R_n)/n → 1`
  (`ae_tendsto_logb_returnTime`). The same holds for the center column of almost every
  configuration (`ae_tendsto_logb_returnTime_trace`).
-/

@[expose] public section

namespace Rule30Equivalents.ReturnTimes

open MeasureTheory Filter Topology Genericity RandomConfigurations

/-- The prefix of length `n` of `v` occurs again at `s`. -/
def Recurs (v : ℕ → Bool) (n s : ℕ) : Prop := ∀ j < n, v (s + j) = v j

open Classical in
/-- The return time of the prefix of length `n`: the least `s ≥ 1` at which it occurs again, or
`0` if it never does. -/
noncomputable def returnTime (v : ℕ → Bool) (n : ℕ) : ℕ :=
  if h : ∃ s, 0 < s ∧ Recurs v n s then Nat.find h else 0

theorem returnTime_le {v : ℕ → Bool} {n s : ℕ} (hs : 0 < s) (h : Recurs v n s) :
    returnTime v n ≤ s := by
  classical
  have hex : ∃ s, 0 < s ∧ Recurs v n s := ⟨s, hs, h⟩
  rw [returnTime, dite_eq_left hex]
  exact Nat.find_min' hex ⟨hs, h⟩

theorem recurs_returnTime {v : ℕ → Bool} {n : ℕ} (h : ∃ s, 0 < s ∧ Recurs v n s) :
    0 < returnTime v n ∧ Recurs v n (returnTime v n) := by
  classical
  rw [returnTime, dite_eq_left h]
  exact Nat.find_spec h

/-! ### Probabilities -/

/-- **The prefix occurs again at a given `s ≥ 1` with probability `2^-n`.** -/
theorem measure_recurs (n : ℕ) {s : ℕ} (hs : 0 < s) :
    coins ℕ {v | Recurs v n s} = 2⁻¹ ^ n := by
  have h := measure_triangular (ι := ℕ) (fun j v => decide (v (s + j) = v j))
    (fun j => measurable_of_forall_lt (s + j + 1) fun v w hvw => by
      simp only [hvw (s + j) (by omega), hvw j (by omega)])
    (fun j => s + j)
    (fun j v => by
      simp only [Function.update_self, Function.update_of_ne (show j ≠ s + j by omega)]
      cases v (s + j) <;> cases v j <;> rfl)
    (fun j v j' hj' => by
      simp only [Function.update_of_ne (show s + j' ≠ s + j by omega),
        Function.update_of_ne (show j' ≠ s + j by omega)])
    (fun _ => true) n
  rw [← h]
  congr 1
  ext v
  simp [Recurs]

/-- The prefix of length `n` occurs again by time `M` with probability at most `M 2^-n`. -/
theorem measure_exists_recurs_le (n M : ℕ) :
    coins ℕ {v | ∃ s, 0 < s ∧ s ≤ M ∧ Recurs v n s} ≤ M * 2⁻¹ ^ n := by
  have hsub : {v | ∃ s, 0 < s ∧ s ≤ M ∧ Recurs v n s} ⊆
      ⋃ s ∈ Finset.Icc 1 M, {v | Recurs v n s} := by
    rintro v ⟨s, hs0, hsM, h⟩
    exact Set.mem_iUnion₂.2 ⟨s, Finset.mem_Icc.2 ⟨hs0, hsM⟩, h⟩
  calc coins ℕ {v | ∃ s, 0 < s ∧ s ≤ M ∧ Recurs v n s}
      ≤ ∑ s ∈ Finset.Icc 1 M, coins ℕ {v | Recurs v n s} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ _s ∈ Finset.Icc 1 M, (2⁻¹ : ENNReal) ^ n :=
        Finset.sum_congr rfl fun s hs => measure_recurs n (Finset.mem_Icc.1 hs).1
    _ = M * 2⁻¹ ^ n := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-- **The prefix avoids the starts of `K` disjoint blocks with probability `(1 - 2^-n)^K`**: the
blocks are independent fair words, so given the first block each later one differs from it with
probability `1 - 2^-n`. -/
theorem measure_not_recurs_blocks {n : ℕ} (hn : 0 < n) (K : ℕ) :
    coins ℕ {v | ∀ k ∈ Finset.Icc 1 K, ¬ Recurs v n (k * n)} = (1 - 2⁻¹ ^ n) ^ K := by
  classical
  let B : (ℕ → Bool) → ℕ → Fin n → Bool := fun v k j => v (0 + k * n + j)
  have hB : Measurable B := by fun_prop
  let t : (Fin n → Bool) → ℕ → Set (Fin n → Bool) := fun w k => if k = 0 then {w} else {w}ᶜ
  have ht : ∀ w k, MeasurableSet (t w k) := fun w k => by
    simp only [t]
    split_ifs
    · exact measurableSet_singleton w
    · exact (measurableSet_singleton w).compl
  -- the event in block coordinates, split by the first block
  have hpre : {v | ∀ k ∈ Finset.Icc 1 K, ¬ Recurs v n (k * n)} =
      B ⁻¹' ⋃ w, Set.pi (Finset.range (K + 1) : Set ℕ) (t w) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iUnion, Set.mem_pi, Finset.coe_range,
      Set.mem_Iio, t]
    constructor
    · intro hv
      refine ⟨B v 0, fun k hk => ?_⟩
      split_ifs with hk0
      · subst hk0
        rfl
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        refine hv k (Finset.mem_Icc.2 ⟨by omega, by omega⟩) fun j hj => ?_
        have := congrFun heq ⟨j, hj⟩
        simpa [B] using this
    · rintro ⟨w, hw⟩ k hk hrec
      have h0 : B v 0 = w := by simpa using hw 0 (by omega)
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
      have hk' : B v k ≠ w := by
        simpa [hk0] using hw k (by have := (Finset.mem_Icc.1 hk).2; omega)
      apply hk'
      rw [← h0]
      funext j
      simpa [B] using hrec j j.2
  have hdisj : Pairwise (Function.onFun Disjoint
      fun w => Set.pi (Finset.range (K + 1) : Set ℕ) (t w)) := by
    intro w w' hww'
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    have h0 := hω 0 (by simp)
    have h0' := hω' 0 (by simp)
    simp only [t, ite_eq_left rfl, Set.mem_singleton_iff] at h0 h0'
    exact hww' (h0.symm.trans h0')
  have hpiece : ∀ w, (Measure.infinitePi fun _ : ℕ => coins (Fin n))
      (Set.pi (Finset.range (K + 1) : Set ℕ) (t w)) = 2⁻¹ ^ n * (1 - 2⁻¹ ^ n) ^ K := by
    intro w
    rw [Measure.infinitePi_pi _ fun k _ => ht w k, Finset.prod_range_succ', mul_comm]
    congr 1
    · simp only [t, ite_eq_left rfl]
      exact LongestRuns.coins_fin_singleton n w
    · rw [Finset.prod_congr rfl fun k _ => show coins (Fin n) (t w (k + 1)) = 1 - 2⁻¹ ^ n by
          simp only [t, ite_eq_right (Nat.succ_ne_zero k)]
          rw [prob_compl_eq_one_sub (measurableSet_singleton w), LongestRuns.coins_fin_singleton],
        Finset.prod_const, Finset.card_range]
  rw [hpre, ← Measure.map_apply hB (MeasurableSet.iUnion fun w =>
      MeasurableSet.pi (Set.to_countable _) fun k _ => ht w k), map_blocks hn 0,
    measure_iUnion hdisj fun w => MeasurableSet.pi (Set.to_countable _) fun k _ => ht w k]
  simp only [hpiece, ENNReal.tsum_const, ENat.card_eq_coe_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rw [← mul_assoc]
  push_cast
  rw [LinearComplexity.two_pow_mul_inv_pow, one_mul]

/-! ### Almost surely -/

/-- **The return times of a random sequence**: for almost every fair-coin sequence,
`2^n/(n + 1)² < R_n ≤ n (n + 1)² 2^n` from some `n` on. -/
theorem ae_eventually_returnTime : ∀ᵐ v ∂(coins ℕ), ∀ᶠ n in atTop,
    2 ^ n / (n + 1) ^ 2 < returnTime v n ∧ returnTime v n ≤ n * ((n + 1) ^ 2 * 2 ^ n) := by
  have hsumm : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    refine this.congr fun n => ?_
    push_cast
    ring
  have hBC : ∀ s : ℕ → Set (ℕ → Bool), (∀ n, (coins ℕ).real (s n) ≤ 1 / ((n : ℝ) + 1) ^ 2) →
      ∑' n, coins ℕ (s n) ≠ ⊤ := by
    intro s hs
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hs n)
  -- early returns
  have hlow : ∀ n, (coins ℕ).real {v | ∃ s, 0 < s ∧ s ≤ 2 ^ n / (n + 1) ^ 2 ∧ Recurs v n s} ≤
      1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have h := measure_exists_recurs_le n (2 ^ n / (n + 1) ^ 2)
    have hM : ((2 ^ n / (n + 1) ^ 2 : ℕ) : ℝ) ≤ 2 ^ n / ((n : ℝ) + 1) ^ 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 ^ n) (n := (n + 1) ^ 2)
      push_cast at this
      exact this
    calc (coins ℕ).real {v | ∃ s, 0 < s ∧ s ≤ 2 ^ n / (n + 1) ^ 2 ∧ Recurs v n s}
        ≤ ((2 ^ n / (n + 1) ^ 2 : ℕ) : ℝ) * (1 / 2) ^ n := by
          rw [measureReal_def]
          refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
            (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))) h).trans (le_of_eq ?_)
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_inv,
            ENNReal.toReal_ofNat, one_div]
      _ ≤ 2 ^ n / ((n : ℝ) + 1) ^ 2 * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 1 / ((n : ℝ) + 1) ^ 2 := by
          rw [div_mul_eq_mul_div, ← mul_pow]
          norm_num
  -- late returns
  have hhigh : ∀ n, (coins ℕ).real {v | ∀ k ∈ Finset.Icc 1 ((n + 1) ^ 2 * 2 ^ n),
      ¬ Recurs v n (k * n)} ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hemp : {v : ℕ → Bool | ∀ k ∈ Finset.Icc 1 ((0 + 1) ^ 2 * 2 ^ 0),
          ¬ Recurs v 0 (k * 0)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun v hv =>
          hv 1 (by simp) fun j hj => absurd hj (Nat.not_lt_zero j)
      rw [hemp, measureReal_empty]
      positivity
    set K := (n + 1) ^ 2 * 2 ^ n
    set x : ℝ := (1 / 2) ^ n with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hval : (coins ℕ).real {v | ∀ k ∈ Finset.Icc 1 K, ¬ Recurs v n (k * n)} = (1 - x) ^ K := by
      rw [measureReal_def, measure_not_recurs_blocks hn K, ENNReal.toReal_pow,
        ENNReal.toReal_sub_of_le (pow_le_one₀ zero_le (by norm_num)) ENNReal.one_ne_top,
        ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, hx,
        one_div]
    have hKx : (K : ℝ) * x = ((n : ℝ) + 1) ^ 2 := by
      rw [hx, show (K : ℝ) = ((n : ℝ) + 1) ^ 2 * 2 ^ n by simp [K], mul_assoc, ← mul_pow]
      norm_num
    have hbern := LongestRuns.one_sub_pow_mul_le hx0 hx1 K
    rw [hval, le_div_iff₀ (by positivity)]
    rw [hKx] at hbern
    nlinarith [pow_nonneg (sub_nonneg.2 hx1) K]
  filter_upwards [ae_eventually_notMem (hBC _ hlow), ae_eventually_notMem (hBC _ hhigh)]
    with v h1 h2
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn0
  simp only [not_exists, not_and, not_forall, not_not] at hn1 hn2
  obtain ⟨k, hk, hrec⟩ := hn2
  have hk1 := (Finset.mem_Icc.1 hk).1
  have hex : ∃ s, 0 < s ∧ Recurs v n s := ⟨k * n, Nat.mul_pos hk1 hn0, hrec⟩
  obtain ⟨hR0, hR⟩ := recurs_returnTime hex
  refine ⟨?_, ?_⟩
  · by_contra hle
    push Not at hle
    exact hn1 _ hR0 hle hR
  · calc returnTime v n ≤ k * n := returnTime_le (Nat.mul_pos hk1 hn0) hrec
      _ ≤ (n + 1) ^ 2 * 2 ^ n * n := Nat.mul_le_mul_right n (Finset.mem_Icc.1 hk).2
      _ = n * ((n + 1) ^ 2 * 2 ^ n) := Nat.mul_comm _ _

/-- **`(log₂ R_n)/n → 1` for almost every fair-coin sequence.** -/
theorem ae_tendsto_logb_returnTime : ∀ᵐ v ∂(coins ℕ),
    Tendsto (fun n : ℕ => Real.logb 2 (returnTime v n) / n) atTop (𝓝 1) := by
  filter_upwards [ae_eventually_returnTime] with v hv
  -- `|logb 2 R_n - n| ≤ 3 logb 2 (n + 1)`
  have hlog : Tendsto (fun n : ℕ => 3 * Real.logb 2 ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    -- `log x / (x - 1)` at `x = n + 1`
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have := h1.const_mul (3 / Real.log 2)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, pow_one, one_mul, Real.logb]
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlog
  filter_upwards [hv, eventually_gt_atTop 0] with n hn hn0
  obtain ⟨h1, h2⟩ := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hR0 : 0 < returnTime v n := lt_of_le_of_lt (Nat.zero_le _) h1
  have hRpos : (0 : ℝ) < returnTime v n := by exact_mod_cast hR0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hlogn1 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) := Real.logb_nonneg one_lt_two hn1
  -- the lower bound: `R_n > 2^n/(n + 1)²`
  have hlo : (2 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 < returnTime v n := by
    have h1' : ((2 ^ n / (n + 1) ^ 2 : ℕ) : ℝ) + 1 ≤ returnTime v n := by
      exact_mod_cast Nat.succ_le_of_lt h1
    have := Nat.lt_div_mul_add (a := 2 ^ n) (b := (n + 1) ^ 2) (by positivity)
    have h3 : (2 : ℝ) ^ n < (((2 ^ n / (n + 1) ^ 2 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 := by
      have : ((2 ^ n : ℕ) : ℝ) < ((2 ^ n / (n + 1) ^ 2 * (n + 1) ^ 2 + (n + 1) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at this
      nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hhi : (returnTime v n : ℝ) ≤ n * (((n : ℝ) + 1) ^ 2 * 2 ^ n) := by exact_mod_cast h2
  have hL1 : (n : ℝ) - 2 * Real.logb 2 ((n : ℝ) + 1) < Real.logb 2 (returnTime v n) := by
    have := Real.logb_lt_logb one_lt_two (by positivity) hlo
    rwa [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one] at this
  have hL2 : Real.logb 2 (returnTime v n) ≤ n + 3 * Real.logb 2 ((n : ℝ) + 1) := by
    have h := Real.logb_le_logb_of_le one_lt_two hRpos hhi
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h
    push_cast at h
    have hn' : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((n : ℝ) + 1) :=
      Real.logb_le_logb_of_le one_lt_two hnpos (by linarith)
    linarith
  have e : Real.logb 2 (returnTime v n) / n - 1 = (Real.logb 2 (returnTime v n) - n) / n := by
    field_simp
  rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hnpos.le

/-- **Return times of random center columns**: for almost every configuration the prefix of length
`n` of the center column first occurs again after `2^(n(1 + o(1)))` steps. -/
theorem ae_tendsto_logb_returnTime_trace : ∀ᵐ x ∂(coins ℤ),
    Tendsto (fun n : ℕ => Real.logb 2 (returnTime (trace x) n) / n) atTop (𝓝 1) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_tendsto_logb_returnTime

end Rule30Equivalents.ReturnTimes
