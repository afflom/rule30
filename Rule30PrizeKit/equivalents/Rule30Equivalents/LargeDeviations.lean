module

public import Rule30Equivalents.LongestRuns
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
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
# Large deviations of the density of the center column

Cramér's theorem for fair coins, for the center column of a random configuration: at least `a n`
of its first `n` cells are black with probability `e^(-n I(a) + o(n))`, where
`I(a) = log 2 - H(a)` and `H(a) = -a log a - (1 - a) log (1 - a)` is the binary entropy, for
`1/2 ≤ a < 1`.

* `tendsto_log_measureReal_trace`: **`(1/n) log P(N(n) ≥ a n) → H(a) - log 2`.**

The upper bound is Chernoff's (`measureReal_le_exp`): for `t ≥ 0` at most `e^(-t a n) (1 + eᵗ)ⁿ`
words of length `n` have at least `a n` ones (`card_le_chernoff`), and `eᵗ = a/(1 - a)` gives
probability at most `e^(-n I(a))`, for every `n`. For the lower bound, with `k = ⌈a n⌉` and
`p = k/n` the binomial term `C(n, k) pᵏ (1 - p)ⁿ⁻ᵏ` is the largest of the `n + 1` terms of
`(p + (1 - p))ⁿ = 1` (`one_le_succ_mul_binomial_term`), so exactly `k` black cells have
probability at least `e^(-n I(p))/(n + 1)` (`log_measureReal_ge`), and `I` is continuous.
-/

@[expose] public section

namespace Rule30Equivalents.LargeDeviations

open MeasureTheory Filter Topology Genericity RandomConfigurations

/-- The binary entropy, written out. -/
theorem binEntropy_eq (p : ℝ) :
    Real.binEntropy p = p * Real.log p⁻¹ + (1 - p) * Real.log (1 - p)⁻¹ := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.log_inv, Real.log_inv]
  simp only [Real.negMulLog_def]
  ring

/-- The first `n` coins of a fair-coin sequence form a fair word. -/
theorem map_prefix (n : ℕ) : (coins ℕ).map (fun v (j : Fin n) => v j) = coins (Fin n) :=
  Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective

/-- **Chernoff's bound, counted**: for `t ≥ 0` at most `e^(-t a n) (1 + eᵗ)ⁿ` words of length `n`
have at least `a n` ones. -/
theorem card_le_chernoff (n : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((Finset.univ.filter fun w : Fin n → Bool => a * n ≤ ∑ j, black (w j)).card : ℝ) ≤
      Real.exp (-(t * (a * n))) * (1 + Real.exp t) ^ n := by
  classical
  calc ((Finset.univ.filter fun w : Fin n → Bool => a * n ≤ ∑ j, black (w j)).card : ℝ)
      = ∑ w ∈ Finset.univ.filter fun w : Fin n → Bool => a * n ≤ ∑ j, black (w j), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ w ∈ Finset.univ.filter fun w : Fin n → Bool => a * n ≤ ∑ j, black (w j),
          Real.exp (t * (∑ j, black (w j) - a * n)) :=
        Finset.sum_le_sum fun w hw => Real.one_le_exp (mul_nonneg ht
          (sub_nonneg.2 (Finset.mem_filter.1 hw).2))
    _ ≤ ∑ w : Fin n → Bool, Real.exp (t * (∑ j, black (w j) - a * n)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => (Real.exp_pos _).le
    _ = ∑ w : Fin n → Bool, Real.exp (-(t * (a * n))) * ∏ j, Real.exp (t * black (w j)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Real.exp_sum, ← Real.exp_add, mul_sub, Finset.mul_sum]
        ring_nf
    _ = Real.exp (-(t * (a * n))) * (1 + Real.exp t) ^ n := by
        rw [← Finset.mul_sum, show (∑ w : Fin n → Bool, ∏ j, Real.exp (t * black (w j))) =
            ∏ _j : Fin n, ∑ b : Bool, Real.exp (t * black b) from
            (Fintype.prod_sum fun _ b => Real.exp (t * black b)).symm, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, Fintype.sum_bool]
        simp [black, add_comm]

/-- **Chernoff's bound**: for `1/2 ≤ a < 1`, at least `a n` of `n` fair coins are black with
probability at most `e^(-n (log 2 - H(a)))`, with `eᵗ = a/(1 - a)` in `card_le_chernoff`. -/
theorem measureReal_le_exp (n : ℕ) {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    (coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)} ≤
      Real.exp (n * (Real.binEntropy a - Real.log 2)) := by
  classical
  set t := Real.log (a / (1 - a)) with htdef
  have ha0 : 0 < a := by linarith
  have h1a : 0 < 1 - a := by linarith
  have ht : 0 ≤ t := Real.log_nonneg (by rw [le_div_iff₀ h1a]; linarith)
  have het : Real.exp t = a / (1 - a) := Real.exp_log (by positivity)
  have key : Real.exp (-(t * a)) * (1 + Real.exp t) * 2⁻¹ =
      Real.exp (Real.binEntropy a - Real.log 2) := by
    have h1 : 1 + Real.exp t = Real.exp (-Real.log (1 - a)) := by
      rw [het, Real.exp_neg, Real.exp_log h1a]
      field_simp
      ring
    have h2 : (2 : ℝ)⁻¹ = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos]
    rw [h1, h2, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [htdef, Real.log_div ha0.ne' h1a.ne', binEntropy_eq, Real.log_inv, Real.log_inv]
    ring
  have hS : ({w | a * n ≤ ∑ j, black (w j)} : Set (Fin n → Bool)) =
      ↑(Finset.univ.filter fun w : Fin n → Bool => a * n ≤ ∑ j, black (w j)) := by
    ext w
    simp
  rw [hS, LongestRuns.measureReal_finset]
  calc ((Finset.univ.filter fun w : Fin n → Bool => a * n ≤ ∑ j, black (w j)).card : ℝ) *
        (2⁻¹ : ℝ) ^ n
      ≤ Real.exp (-(t * (a * n))) * (1 + Real.exp t) ^ n * (2⁻¹ : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (card_le_chernoff n a ht) (by positivity)
    _ = (Real.exp (-(t * a)) * (1 + Real.exp t) * 2⁻¹) ^ n := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring_nf
    _ = Real.exp (n * (Real.binEntropy a - Real.log 2)) := by
        rw [key, ← Real.exp_nat_mul]

/-- **The mode of the binomial distribution**: for `k ≤ n` and `p = k/n` the term
`C(n, k) pᵏ (1 - p)ⁿ⁻ᵏ` is the largest of the `n + 1` terms of `(p + (1 - p))ⁿ = 1`, so it is at
least `1/(n + 1)`. Consecutive terms satisfy `b(j + 1) (j + 1)(1 - p) = b(j) (n - j) p`, and
`(n - j) p - (j + 1)(1 - p) = k + p - (j + 1)`. -/
theorem one_le_succ_mul_binomial_term {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k)) := by
  set p : ℝ := (k : ℝ) / n with hp
  set b : ℕ → ℝ := fun j => (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) with hb
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hn']; exact_mod_cast hk
  have hnp : (n : ℝ) * p = k := by rw [hp]; field_simp
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    simp only [hb]
    have : 0 ≤ 1 - p := by linarith
    positivity
  -- consecutive terms
  have hstep : ∀ j < n, b (j + 1) * (((j : ℝ) + 1) * (1 - p)) = b j * (((n : ℝ) - j) * p) := by
    intro j hj
    have h1 := Nat.choose_succ_right_eq n j
    have h2 : ((n.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((n.choose j * (n - j) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast [Nat.cast_sub hj.le] at h2
    simp only [hb]
    rw [show n - j = n - (j + 1) + 1 by omega, pow_succ, pow_succ]
    linear_combination (p ^ j * p * (1 - p) ^ (n - (j + 1)) * (1 - p)) * h2
  -- the terms rise up to `k` and fall after it
  have hup : ∀ j < k, b j ≤ b (j + 1) := by
    intro j hj
    have hjn : j < n := by omega
    rcases eq_or_lt_of_le (show 0 ≤ 1 - p by linarith) with hq | hq
    · -- `p = 1`: all terms before `n` vanish
      have : b j = 0 := by
        simp only [hb, ← hq, zero_pow (show n - j ≠ 0 by omega), mul_zero]
      rw [this]
      exact hb0 _
    · have hle : ((j : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - j) * p := by
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
        nlinarith
      have hpos : 0 < ((j : ℝ) + 1) * (1 - p) := mul_pos (by positivity) hq
      have := hstep j hjn
      refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [hb0 j, mul_le_mul_of_nonneg_left hle (hb0 j)]
  have hdown : ∀ j, k ≤ j → j < n → b (j + 1) ≤ b j := by
    intro j hj hjn
    have hq : 0 < 1 - p := by
      have : (k : ℝ) < n := by exact_mod_cast (show k < n by omega)
      rw [hp, sub_pos, div_lt_one hn']
      exact this
    have hle : ((n : ℝ) - j) * p ≤ ((j : ℝ) + 1) * (1 - p) := by
      have : (k : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith
    have hpos : 0 < ((j : ℝ) + 1) * (1 - p) := mul_pos (by positivity) hq
    have := hstep j hjn
    refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [hb0 j, mul_le_mul_of_nonneg_left hle (hb0 j)]
  have hclimb : ∀ d j, j + d ≤ k → b j ≤ b (j + d) := by
    intro d
    induction d with
    | zero => exact fun j _ => le_rfl
    | succ d ih => exact fun j hjd => (ih j (by omega)).trans (hup (j + d) (by omega))
  have hdesc : ∀ d, k + d ≤ n → b (k + d) ≤ b k := by
    intro d
    induction d with
    | zero => exact fun _ => le_rfl
    | succ d ih => exact fun hd => (hdown (k + d) (by omega) (by omega)).trans (ih (by omega))
  have hmax : ∀ j ≤ n, b j ≤ b k := by
    intro j hj
    rcases le_total j k with hjk | hkj
    · have := hclimb (k - j) j (by omega)
      rwa [show j + (k - j) = k by omega] at this
    · have := hdesc (j - k) (by omega)
      rwa [show k + (j - k) = j by omega] at this
  -- the terms sum to `1`
  have hsum : ∑ j ∈ Finset.range (n + 1), b j = 1 := by
    have h := add_pow p (1 - p) n
    rw [add_sub_cancel, one_pow] at h
    calc ∑ j ∈ Finset.range (n + 1), b j
        = ∑ m ∈ Finset.range (n + 1), p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) :=
          Finset.sum_congr rfl fun j _ => by simp only [hb]; ring
      _ = 1 := h.symm
  calc (1 : ℝ) = ∑ j ∈ Finset.range (n + 1), b j := hsum.symm
    _ ≤ ∑ _j ∈ Finset.range (n + 1), b k :=
        Finset.sum_le_sum fun j hj => hmax j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    _ = ((n : ℝ) + 1) * b k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- At least `a n` of `n ≥ 1` fair coins are black with positive probability, for `a ≤ 1`: the word
of ones has probability `2⁻ⁿ`. -/
theorem measureReal_pos (n : ℕ) {a : ℝ} (ha1 : a ≤ 1) :
    0 < (coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)} := by
  have hsub : ({fun _ => true} : Set (Fin n → Bool)) ⊆ {w | a * n ≤ ∑ j, black (w j)} := by
    rintro w rfl
    simp only [Set.mem_ofPred_eq, black, ite_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine lt_of_lt_of_le ?_ (measureReal_mono hsub)
  rw [measureReal_def, LongestRuns.coins_fin_singleton]
  simp

/-- **The lower bound**: with `k = ⌈a n⌉ ≤ n` and `p = k/n`, at least `a n` of `n` fair coins are
black with a probability whose logarithm is at least `n (H(p) - log 2) - log (n + 1)`: exactly `k`
are black with probability `C(n, k)/2ⁿ`, and `log C(n, k) ≥ n H(p) - log (n + 1)` by the mode. -/
theorem log_measureReal_ge {n : ℕ} (hn : 0 < n) {a : ℝ} (ha1 : a ≤ 1) :
    (n : ℝ) * (Real.binEntropy ((⌈a * n⌉₊ : ℕ) / (n : ℝ)) - Real.log 2) - Real.log (n + 1) ≤
      Real.log ((coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)}) := by
  classical
  set k := ⌈a * n⌉₊ with hkdef
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : k ≤ n := Nat.ceil_le.2 (by nlinarith)
  set p : ℝ := (k : ℝ) / n with hp
  have hnp : (n : ℝ) * p = k := by rw [hp]; field_simp
  -- the words with exactly `k` ones
  set S := Finset.univ.filter fun w : Fin n → Bool =>
    (Finset.univ.filter fun j => w j = true).card = k with hS
  have hSsub : (S : Set (Fin n → Bool)) ⊆ {w | a * n ≤ ∑ j, black (w j)} := by
    intro w hw
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
    have : ∑ j, black (w j) = (k : ℝ) := by
      rw [← hw]
      simp [black, Finset.sum_boole]
    rw [this]
    exact Nat.le_ceil _
  have hSmeas : (coins (Fin n)).real S = (n.choose k : ℝ) * (2⁻¹ : ℝ) ^ n := by
    rw [LongestRuns.measureReal_finset, LongestRuns.card_filter_card_eq]
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hpos : 0 < (coins (Fin n)).real S := by rw [hSmeas]; positivity
  refine le_trans ?_ (Real.log_le_log hpos (measureReal_mono hSsub))
  rw [hSmeas, Real.log_mul hC.ne' (by positivity), Real.log_pow, Real.log_inv]
  -- `log C(n, k) ≥ n H(p) - log (n + 1)`, from the mode
  have hpk : p ^ k ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero]
      exact one_ne_zero
    · exact pow_ne_zero _ (div_pos (by exact_mod_cast h) hn').ne'
  have hqk : (1 - p) ^ (n - k) ≠ 0 := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [h, Nat.sub_self, pow_zero]
      exact one_ne_zero
    · refine pow_ne_zero _ (sub_pos.2 ?_).ne'
      rw [hp, div_lt_one hn']
      exact_mod_cast h
  have hmode := Real.log_le_log one_pos (one_le_succ_mul_binomial_term hk hn)
  rw [Real.log_one, Real.log_mul (by positivity) (mul_ne_zero (mul_ne_zero hC.ne' hpk) hqk),
    Real.log_mul (mul_ne_zero hC.ne' hpk) hqk, Real.log_mul hC.ne' hpk, Real.log_pow,
    Real.log_pow] at hmode
  have hH : (n : ℝ) * Real.binEntropy p =
      -((k : ℝ) * Real.log p + ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
    rw [binEntropy_eq, Real.log_inv, Real.log_inv, Nat.cast_sub hk, ← hnp]
    ring
  have e : (n : ℝ) * (Real.binEntropy p - Real.log 2) =
      (n : ℝ) * Real.binEntropy p - n * Real.log 2 := mul_sub _ _ _
  linarith

/-- **Cramér's theorem for fair coins**: for `1/2 ≤ a < 1`,
`(1/n) log P(at least a n of n fair coins are black) → H(a) - log 2`. -/
theorem tendsto_log_measureReal {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => Real.log ((coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)}) / n)
      atTop (𝓝 (Real.binEntropy a - Real.log 2)) := by
  have hup : ∀ᶠ n : ℕ in atTop, Real.log ((coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)}) /
      n ≤ Real.binEntropy a - Real.log 2 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Real.log_le_log (measureReal_pos n ha1.le) (measureReal_le_exp n ha ha1)
    rw [Real.log_exp] at h
    rw [div_le_iff₀ hn']
    linarith
  have hlo : ∀ᶠ n : ℕ in atTop, Real.binEntropy ((⌈a * n⌉₊ : ℕ) / (n : ℝ)) - Real.log 2 -
      Real.log (n + 1) / n ≤
        Real.log ((coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)}) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := log_measureReal_ge hn ha1.le
    rw [le_div_iff₀ hn']
    have e : (Real.binEntropy ((⌈a * n⌉₊ : ℕ) / (n : ℝ)) - Real.log 2 - Real.log (n + 1) / n) * n =
        n * (Real.binEntropy ((⌈a * n⌉₊ : ℕ) / (n : ℝ)) - Real.log 2) - Real.log (n + 1) := by
      field_simp
    linarith
  -- `⌈a n⌉/n → a`, the entropy is continuous, and `log (n + 1)/n → 0`
  have hk : Tendsto (fun n : ℕ => ((⌈a * n⌉₊ : ℕ) : ℝ) / n) atTop (𝓝 a) := by
    have h1 : Tendsto (fun n : ℕ => a + 1 / (n : ℝ)) atTop (𝓝 a) := by
      simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hn']
      exact Nat.le_ceil _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ hn', add_mul, one_div, inv_mul_cancel₀ hn'.ne']
      exact (Nat.ceil_lt_add_one (by positivity)).le
  have hH : Continuous Real.binEntropy := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub']
    fun_prop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, pow_one, one_mul]
    ring_nf
  have hlim := ((hH.tendsto a).comp hk).sub_const (Real.log 2) |>.sub hlog
  rw [sub_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlo hup

/-- **Large deviations of the density of the center column**: for `1/2 ≤ a < 1` and a random
configuration, at least `a n` of the first `n` cells of the center column are black with probability
`e^(-n (log 2 - H(a)) + o(n))`. -/
theorem tendsto_log_measureReal_trace {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => Real.log ((coins ℤ).real
      {x | a * n ≤ ∑ t ∈ Finset.range n, black (trace x t)}) / n) atTop
      (𝓝 (Real.binEntropy a - Real.log 2)) := by
  refine (tendsto_log_measureReal ha ha1).congr fun n => ?_
  have hm : Measurable fun (v : ℕ → Bool) (j : Fin n) => v j := by fun_prop
  have hS : MeasurableSet {w : Fin n → Bool | a * n ≤ ∑ j, black (w j)} :=
    (Set.toFinite _).measurableSet
  have h1 : (coins (Fin n)).real {w | a * n ≤ ∑ j, black (w j)} =
      (coins ℕ).real {v | a * n ≤ ∑ t ∈ Finset.range n, black (v t)} := by
    rw [← map_prefix n, measureReal_def, Measure.map_apply hm hS, measureReal_def]
    congr 2
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [Fin.sum_univ_eq_sum_range (fun t => black (v t)) n]
  have h2 : (coins ℕ).real {v | a * n ≤ ∑ t ∈ Finset.range n, black (v t)} =
      (coins ℤ).real {x | a * n ≤ ∑ t ∈ Finset.range n, black (trace x t)} := by
    rw [measureReal_def, measureReal_def, ← measurePreserving_trace.measure_preimage]
    · rfl
    · exact (measurableSet_le measurable_const (Finset.measurable_sum _ fun t _ =>
        measurable_black.comp (measurable_pi_apply t))).nullMeasurableSet
  rw [h1, h2]

end Rule30Equivalents.LargeDeviations
