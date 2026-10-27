module

public import Rule30Equivalents.LargeDeviations
public import Mathlib.Analysis.SpecialFunctions.Stirling
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
# The local limit theorem for the center column

For a random configuration, the number `N(n)` of black cells among the first `n` cells of the
center column is binomial: `P(N(n) = k) = C(n, k)/2ⁿ` (`measureReal_count_eq_trace`).

* `tendsto_sqrt_mul_choose_div`: **the local limit theorem of de Moivre and Laplace**. If
  `(kₙ - n/2)/√n → x`, then `√n C(n, kₙ)/2ⁿ → √(2/π) e^{-2x²}`, the density at `x` of the normal
  law with mean `0` and variance `1/4`.
* `tendsto_sqrt_mul_measureReal_trace`: so `√n P(N(n) = kₙ) → √(2/π) e^{-2x²}` for the center
  column of a random configuration, and `tendsto_sqrt_mul_measureReal_balanced_trace`: the column
  is exactly balanced at time `2n` with probability `(1 + o(1))/√(πn)`.

The proof writes `C(n, k)/2ⁿ = σ(n)/(σ(k) σ(m)) · √(n/(2km)) · (n/2k)ᵏ (n/2m)ᵐ` with `m = n - k`
(`choose_div_two_pow_eq`) and Stirling's sequence `σ(n) = n!/(√(2n) (n/e)ⁿ) → √π` (Mathlib's
`Stirling.tendsto_stirlingSeq_sqrt_pi`). With `k = n(1 + u)/2`, the logarithm of the last factor
is `-(k log(1 + u) + m log(1 - u)) = -n u²/2 + O(n u³)` (`abs_log_one_add_sub_le`,
`abs_entropy_sub_le`), and `n u²/2 → 2x²`.

Sources: A. de Moivre, *The Doctrine of Chances*, 2nd ed. (1738); P.-S. Laplace, *Théorie
analytique des probabilités* (1812); W. Feller, *An Introduction to Probability Theory and Its
Applications*, vol. 1, 3rd ed., Wiley (1968), chapter VII.
-/

@[expose] public section

namespace Rule30Equivalents.LocalLimit

open MeasureTheory Filter Topology Genericity RandomConfigurations Stirling

theorem tendsto_inv_sqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
  (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

/-- `log(1 + u) = u - u²/2 + O(u³)`. -/
theorem abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * |u| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 2
  have e : (∑ i ∈ Finset.range 2, (-u) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -u) =
      Real.log (1 + u) - (u - u ^ 2 / 2) := by
    simp [Finset.sum_range_succ]
    ring
  rw [e, abs_neg, show 2 + 1 = 3 from rfl] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg (abs_nonneg u) 3]

/-- With `k = n(1 + u)/2` and `m = n(1 - u)/2`, `k log(1 + u) + m log(1 - u) = n u²/2 + O(n u³)`. -/
theorem abs_entropy_sub_le {n u : ℝ} (hn : 0 ≤ n) (hu : |u| ≤ 1 / 2) :
    |n * (1 + u) / 2 * Real.log (1 + u) + n * (1 - u) / 2 * Real.log (1 - u) - n * u ^ 2 / 2| ≤
      2 * n * |u| ^ 3 := by
  have h1 := abs_log_one_add_sub_le hu
  have h2 : |Real.log (1 - u) - (-u - u ^ 2 / 2)| ≤ 2 * |u| ^ 3 := by
    have h := abs_log_one_add_sub_le (u := -u) (by rwa [abs_neg])
    rwa [← sub_eq_add_neg, neg_sq, abs_neg] at h
  have hu' := abs_le.1 (hu.trans (by norm_num : (1 : ℝ) / 2 ≤ 1))
  have hk : 0 ≤ n * (1 + u) / 2 := by nlinarith
  have hm : 0 ≤ n * (1 - u) / 2 := by nlinarith
  have key : n * (1 + u) / 2 * Real.log (1 + u) + n * (1 - u) / 2 * Real.log (1 - u) -
      n * u ^ 2 / 2 = n * (1 + u) / 2 * (Real.log (1 + u) - (u - u ^ 2 / 2)) +
        n * (1 - u) / 2 * (Real.log (1 - u) - (-u - u ^ 2 / 2)) := by ring
  rw [key]
  calc _ ≤ |n * (1 + u) / 2 * (Real.log (1 + u) - (u - u ^ 2 / 2))| +
        |n * (1 - u) / 2 * (Real.log (1 - u) - (-u - u ^ 2 / 2))| := abs_add_le _ _
    _ = n * (1 + u) / 2 * |Real.log (1 + u) - (u - u ^ 2 / 2)| +
        n * (1 - u) / 2 * |Real.log (1 - u) - (-u - u ^ 2 / 2)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk, abs_of_nonneg hm]
    _ ≤ n * (1 + u) / 2 * (2 * |u| ^ 3) + n * (1 - u) / 2 * (2 * |u| ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hk) (mul_le_mul_of_nonneg_left h2 hm)
    _ = 2 * n * |u| ^ 3 := by ring

/-- **Stirling's formula for a binomial coefficient**: with `σ(n) = n!/(√(2n) (n/e)ⁿ)`,
`C(k + m, k)/2^(k+m) = σ(k + m)/(σ(k) σ(m)) · √((k + m)/(2km)) · ((k + m)/2k)ᵏ ((k + m)/2m)ᵐ`. -/
theorem choose_div_two_pow_eq {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    ((k + m).choose k : ℝ) / 2 ^ (k + m) =
      stirlingSeq (k + m) / (stirlingSeq k * stirlingSeq m) *
        √(((k : ℝ) + m) / (2 * k * m)) * ((((k : ℝ) + m) / (2 * k)) ^ k *
          (((k : ℝ) + m) / (2 * m)) ^ m) := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : ((k + m).choose k : ℝ) = ((k + m).factorial : ℝ) / (k.factorial * m.factorial) := by
    rw [eq_div_iff (by positivity)]
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k m)
    rw [Nat.add_sub_cancel_left] at h
    rw [← mul_assoc]
    exact_mod_cast h
  have hs : √(((k : ℝ) + m) / (2 * k * m)) = √((k : ℝ) + m) / (√2 * √(k : ℝ) * √(m : ℝ)) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  simp only [stirlingSeq]
  rw [hfac, hs, Nat.cast_add, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (k : ℝ),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (m : ℝ),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((k : ℝ) + m)]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hk' : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 hK
  have hm' : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.2 hM
  have hn' : (0 : ℝ) < √((k : ℝ) + m) := Real.sqrt_pos.2 (by positivity)
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  simp only [div_pow, mul_pow]
  field_simp
  ring

/-- **The local limit theorem of de Moivre and Laplace**: if `(kₙ - n/2)/√n → x`, then
`√n C(n, kₙ)/2ⁿ → √(2/π) e^{-2x²}`. -/
theorem tendsto_sqrt_mul_choose_div {k : ℕ → ℕ} {x : ℝ}
    (hk : Tendsto (fun n : ℕ => ((k n : ℝ) - n / 2) / √n) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => √n * (n.choose (k n) : ℝ) / 2 ^ n) atTop
      (𝓝 (√(2 / Real.pi) * Real.exp (-2 * x ^ 2))) := by
  set X : ℕ → ℝ := fun n => ((k n : ℝ) - n / 2) / √n with hX
  -- `u = 2X/√n`, so that `k = n (1 + u)/2`
  set u : ℕ → ℝ := fun n => 2 * X n / √n with hu
  have hinv := tendsto_inv_sqrt
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have h := (hk.const_mul 2).mul hinv
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [hu, hX, div_eq_mul_inv]
  have hsq : ∀ n : ℕ, √(n : ℝ) ^ 2 = n := fun n => Real.sq_sqrt (Nat.cast_nonneg n)
  have hku : ∀ n : ℕ, 0 < n → (k n : ℝ) = n * (1 + u n) / 2 := fun n hn => by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : u n = 2 * (((k n : ℝ) - n / 2) / n) := by
      simp only [hu, hX]
      rw [mul_div_assoc, div_div, ← sq, hsq n]
    rw [e]
    field_simp
    ring
  have hev : ∀ᶠ n in atTop, 4 ≤ n ∧ |u n| ≤ 1 / 4 := by
    filter_upwards [eventually_ge_atTop 4,
      hu0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))]
      with n hn hun
    refine ⟨hn, ?_⟩
    simpa [Metric.mem_closedBall, Real.dist_eq] using hun
  -- eventually `0 < k < n`, with `n - k = n (1 - u)/2`
  have hkn : ∀ n : ℕ, 4 ≤ n → |u n| ≤ 1 / 4 → 0 < k n ∧ k n < n := fun n hn hun => by
    have h := hku n (by omega)
    have hun' := abs_le.1 hun
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · have : (0 : ℝ) < k n := by rw [h]; nlinarith
      exact_mod_cast this
    · have : (k n : ℝ) < n := by rw [h]; nlinarith
      exact_mod_cast this
  have hmu : ∀ n : ℕ, 4 ≤ n → |u n| ≤ 1 / 4 → ((n - k n : ℕ) : ℝ) = n * (1 - u n) / 2 :=
    fun n hn hun => by
      rw [Nat.cast_sub (hkn n hn hun).2.le, hku n (by omega)]
      ring
  have hktop : Tendsto k atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono' atTop ?_
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 8)))
    filter_upwards [hev] with n hn
    rw [hku n (by omega)]
    have := abs_le.1 hn.2
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmtop : Tendsto (fun n => n - k n) atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono' atTop ?_
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 8)))
    filter_upwards [hev] with n hn
    rw [hmu n hn.1 hn.2]
    have := abs_le.1 hn.2
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- the three factors
  have h1 : Tendsto (fun n => stirlingSeq n / (stirlingSeq (k n) * stirlingSeq (n - k n)))
      atTop (𝓝 (√Real.pi / (√Real.pi * √Real.pi))) :=
    tendsto_stirlingSeq_sqrt_pi.div ((tendsto_stirlingSeq_sqrt_pi.comp hktop).mul
      (tendsto_stirlingSeq_sqrt_pi.comp hmtop)) (by positivity)
  have h2 : Tendsto (fun n => √(2 / ((1 + u n) * (1 - u n)))) atTop (𝓝 √2) := by
    have hd : Tendsto (fun n => (1 + u n) * (1 - u n)) atTop (𝓝 ((1 + 0) * (1 - 0))) :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add hu0).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hu0)
    have h := ((tendsto_const_nhds (x := (2 : ℝ))).div hd (by norm_num)).sqrt
    simpa using h
  set E : ℕ → ℝ := fun n => n * (1 + u n) / 2 * Real.log (1 + u n) +
    n * (1 - u n) / 2 * Real.log (1 - u n) with hE
  have h3 : Tendsto E atTop (𝓝 (2 * x ^ 2)) := by
    have hX2 : Tendsto (fun n => 2 * X n ^ 2) atTop (𝓝 (2 * x ^ 2)) := (hk.pow 2).const_mul 2
    have hb : Tendsto (fun n => 16 * |X n| ^ 3 * (√(n : ℝ))⁻¹) atTop (𝓝 0) := by
      have h := ((hk.abs.pow 3).const_mul 16).mul hinv
      rwa [mul_zero] at h
    have hdiff : Tendsto (fun n => E n - 2 * X n ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hev] with n hn
      have hn0 : 0 < n := by omega
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
      have hbd := abs_entropy_sub_le (Nat.cast_nonneg n) (hn.2.trans (by norm_num))
      obtain ⟨s, hs_def⟩ : ∃ s, s = √(n : ℝ) := ⟨_, rfl⟩
      have hs0 : 0 < s := hs_def ▸ hs
      have hns : (n : ℝ) = s ^ 2 := by rw [hs_def, hsq n]
      have e1 : (n : ℝ) * u n ^ 2 / 2 = 2 * X n ^ 2 := by
        simp only [hu]
        rw [← hs_def, hns]
        field_simp
      have e2 : 2 * (n : ℝ) * |u n| ^ 3 = 16 * |X n| ^ 3 * (√(n : ℝ))⁻¹ := by
        simp only [hu]
        rw [← hs_def, hns, abs_div, abs_mul, abs_two, abs_of_pos hs0]
        field_simp
        ring
      rw [e1, e2] at hbd
      rw [Real.norm_eq_abs]
      exact hbd
    simpa using hdiff.add hX2
  have hlim := (h1.mul h2).mul ((Real.continuous_exp.tendsto _).comp h3.neg)
  have hval : √Real.pi / (√Real.pi * √Real.pi) * √2 * Real.exp (-(2 * x ^ 2)) =
      √(2 / Real.pi) * Real.exp (-2 * x ^ 2) := by
    have hπ : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), neg_mul]
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with n hn
  obtain ⟨hk0, hkn'⟩ := hkn n hn.1 hn.2
  have hm0 : 0 < n - k n := Nat.sub_pos_of_lt hkn'
  have hKM : k n + (n - k n) = n := Nat.add_sub_cancel' hkn'.le
  have hid := choose_div_two_pow_eq hk0 hm0
  rw [hKM, Nat.cast_sub hkn'.le, add_sub_cancel] at hid
  have hun := abs_le.1 hn.2
  have h1u : 0 < 1 + u n := by linarith
  have h1u' : 0 < 1 - u n := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkr := hku n (by omega)
  have hmr : (n : ℝ) - k n = n * (1 - u n) / 2 := by rw [hkr]; ring
  -- the middle factor
  have hmid : √(n : ℝ) * √((n : ℝ) / (2 * k n * ((n : ℝ) - k n))) =
      √(2 / ((1 + u n) * (1 - u n))) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg n), hmr, hkr]
    congr 1
    field_simp
  -- the last factor
  have hlast : ((n : ℝ) / (2 * k n)) ^ k n * ((n : ℝ) / (2 * ((n : ℝ) - k n))) ^ (n - k n) =
      Real.exp (-E n) := by
    have ha : (n : ℝ) / (2 * k n) = (1 + u n)⁻¹ := by
      rw [hkr]
      field_simp
    have hb : (n : ℝ) / (2 * ((n : ℝ) - k n)) = (1 - u n)⁻¹ := by
      rw [hmr]
      field_simp
    have hexp : ∀ (a : ℝ), 0 < a → ∀ j : ℕ, a⁻¹ ^ j = Real.exp (-((j : ℝ) * Real.log a)) :=
      fun a ha j => by rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log ha, inv_pow]
    rw [ha, hb, hexp _ h1u, hexp _ h1u', ← Real.exp_add, hmu n hn.1 hn.2, hkr]
    congr 1
    simp only [hE]
    ring
  simp only [Function.comp_apply]
  rw [mul_div_assoc, hid, ← hlast, ← hmid]
  ring

/-! ### The center column -/

/-- **The black count is binomial**: exactly `k` of the first `n` cells of the center column of a
random configuration are black with probability `C(n, k)/2ⁿ`. -/
theorem measureReal_count_eq_trace (n k : ℕ) :
    (coins ℤ).real {y | ∑ t ∈ Finset.range n, black (trace y t) = k} =
      (n.choose k : ℝ) / 2 ^ n := by
  classical
  have hm : Measurable fun (v : ℕ → Bool) (j : Fin n) => v j := by fun_prop
  have hS : MeasurableSet {w : Fin n → Bool | ∑ j, black (w j) = k} :=
    (Set.toFinite _).measurableSet
  have h1 : (coins (Fin n)).real {w | ∑ j, black (w j) = k} =
      (coins ℕ).real {v | ∑ t ∈ Finset.range n, black (v t) = k} := by
    rw [← LargeDeviations.map_prefix n, measureReal_def, Measure.map_apply hm hS, measureReal_def]
    congr 2
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [Fin.sum_univ_eq_sum_range (fun t => black (v t)) n]
  have h2 : (coins ℕ).real {v | ∑ t ∈ Finset.range n, black (v t) = k} =
      (coins ℤ).real {y | ∑ t ∈ Finset.range n, black (trace y t) = k} := by
    rw [measureReal_def, measureReal_def, ← measurePreserving_trace.measure_preimage]
    · rfl
    · exact (measurableSet_eq_fun (Finset.measurable_sum _ fun t _ =>
        measurable_black.comp (measurable_pi_apply t)) measurable_const).nullMeasurableSet
  have h3 : {w : Fin n → Bool | ∑ j, black (w j) = k} =
      ((Finset.univ.filter fun w : Fin n → Bool =>
        (Finset.univ.filter fun j => w j = true).card = k : Finset _) : Set (Fin n → Bool)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    have : ∑ j, black (w j) = ((Finset.univ.filter fun j => w j = true).card : ℝ) := by
      simp [black, Finset.sum_boole]
    rw [this]
    exact Nat.cast_inj
  rw [← h2, ← h1, h3, LongestRuns.measureReal_finset, LongestRuns.card_filter_card_eq, inv_pow,
    div_eq_mul_inv]

/-- **The local limit theorem for the center column**: if `(kₙ - n/2)/√n → x`, exactly `kₙ` of the
first `n` cells of the center column of a random configuration are black with probability
`(√(2/π) e^{-2x²} + o(1))/√n`. -/
theorem tendsto_sqrt_mul_measureReal_trace {k : ℕ → ℕ} {x : ℝ}
    (hk : Tendsto (fun n : ℕ => ((k n : ℝ) - n / 2) / √n) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => √n *
      (coins ℤ).real {y | ∑ t ∈ Finset.range n, black (trace y t) = k n}) atTop
      (𝓝 (√(2 / Real.pi) * Real.exp (-2 * x ^ 2))) := by
  refine (tendsto_sqrt_mul_choose_div hk).congr fun n => ?_
  rw [measureReal_count_eq_trace, mul_div_assoc]

/-- **Exact balance**: the first `2n` cells of the center column of a random configuration are half
black with probability `(1 + o(1))/√(πn)`. -/
theorem tendsto_sqrt_mul_measureReal_balanced_trace :
    Tendsto (fun n : ℕ => √(Real.pi * n) *
      (coins ℤ).real {y | ∑ t ∈ Finset.range (2 * n), black (trace y t) = n}) atTop (𝓝 1) := by
  -- `⌊m/2⌋` is within `1/2` of `m/2`
  have hk : Tendsto (fun m : ℕ => (((m / 2 : ℕ) : ℝ) - m / 2) / √m) atTop (𝓝 0) := by
    have hb := (tendsto_inv_sqrt.const_mul (1 / 2 : ℝ))
    rw [mul_zero] at hb
    refine squeeze_zero_norm (fun m => ?_) hb
    have hdm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + ((m % 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod m 2).symm
    have hmod : ((m % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt m two_pos)
    have hmod0 : (0 : ℝ) ≤ ((m % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have habs : |((m / 2 : ℕ) : ℝ) - m / 2| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |((m / 2 : ℕ) : ℝ) - m / 2| / √(m : ℝ) ≤ (1 / 2) / √(m : ℝ) :=
          div_le_div_of_nonneg_right habs (Real.sqrt_nonneg _)
      _ = 1 / 2 * (√(m : ℝ))⁻¹ := div_eq_mul_inv _ _
  have hmul : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n two_pos) tendsto_id
  have h := ((tendsto_sqrt_mul_measureReal_trace hk).comp hmul).const_mul (√(Real.pi / 2))
  have hval : √(Real.pi / 2) * (√(2 / Real.pi) * Real.exp (-2 * 0 ^ 2)) = 1 := by
    rw [← mul_assoc, ← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm Real.pi 2,
      div_self (by positivity), Real.sqrt_one]
    simp
  rw [hval] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Nat.mul_div_cancel_left n two_pos]
  rw [← mul_assoc, ← Real.sqrt_mul (by positivity)]
  congr 2
  push_cast
  field_simp

end Rule30Equivalents.LocalLimit
