module

public import Rule30Equivalents.ProblemTwo
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
# Cesàro means of every order

Write `S⁽ᵏ⁾` for the `k`-fold iterated partial sums of a sequence `a`
(`iterSum`), so that `S⁽¹⁾ n = a 0 + ⋯ + a n`, and `σᵏ n = S⁽ᵏ⁾ n / C(n + k, k)` for its Cesàro
mean of order `k` (`cesaroMean`; `σ¹ n` is the average of `a 0, …, a n`).

* `tendsto_weighted`: **Toeplitz's lemma** for regular weighted means. Nonnegative weights of total
  mass `1` whose mass on every initial segment tends to `0` carry a bounded sequence tending to `L`
  to weighted means tending to `L`.
* `tendsto_cesaroMean_succ`: `σᵏ → L` implies `σᵏ⁺¹ → L`, since `σᵏ⁺¹ n` is a weighted mean of
  `σᵏ 0, …, σᵏ n` with weights `C(m + k, k) / C(n + k + 1, k + 1)` (the hockey-stick identity).
* `tendsto_abel_of_tendsto_cesaroMean`: `σᵏ → L` implies the Abel mean `(1 - x) ∑ aₙ xⁿ → L`, since
  `∑ aₙ xⁿ = (1 - x)ᵏ ∑ S⁽ᵏ⁾ n xⁿ` (Cauchy products with the geometric series) and the weights
  `(1 - x)^(k+1) C(n + k, k) xⁿ` have total mass `1`.
* `tendsto_cesaroMean_iff`: for a bounded nonnegative sequence and every `k ≥ 1`, `σᵏ → L` iff the
  averages tend to `L`. The converse direction goes through the Abel mean and the
  Hardy–Littlewood–Karamata theorem (`Tauberian.tendsto_cesaro_of_tendsto_abel`).
* `problem2_iff_cesaroMean`: **Problem 2 holds iff the Cesàro means of order `k` of the center
  column tend to `1/2`**, for every `k ≥ 1`.
-/

@[expose] public section

namespace Rule30Equivalents.CesaroMeans

open Filter Topology Finset Ruliology.CellularAutomata

/-! ### Toeplitz's lemma -/

/-- **Toeplitz's lemma**: regular weighted means of a bounded convergent sequence converge to its
limit. -/
theorem tendsto_weighted {ι : Type*} {l : Filter ι} {w : ι → ℕ → ℝ} {a : ℕ → ℝ} {L B : ℝ}
    (hw : ∀ᶠ i in l, ∀ n, 0 ≤ w i n) (hsum : ∀ᶠ i in l, HasSum (w i) 1)
    (hhead : ∀ N, Tendsto (fun i => ∑ n ∈ range N, w i n) l (𝓝 0))
    (hB : ∀ n, |a n| ≤ B) (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun i => ∑' n, w i n * a n) l (𝓝 L) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M := B + |L| + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (by positivity)
  have hsmall := (Metric.tendsto_nhds.1 (hhead N)) (ε / (2 * M)) (by positivity)
  filter_upwards [hw, hsum, hsmall] with i hwi hsi hhi
  rw [Real.dist_eq] at hhi ⊢
  have hhi' : ∑ n ∈ range N, w i n < ε / (2 * M) := by
    rw [sub_zero, abs_of_nonneg (sum_nonneg fun n _ => hwi n)] at hhi
    exact hhi
  -- the weighted mean minus `L` is the weighted mean of `a - L`
  have hsumm : Summable fun n => w i n * (a n - L) :=
    Summable.of_norm_bounded (g := fun n => M * w i n) (hsi.summable.mul_left M) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwi n), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (hwi n)
      calc |a n - L| ≤ |a n| + |L| := abs_sub _ _
        _ ≤ B + |L| := by linarith [hB n]
        _ ≤ M := by linarith
  have hdiff : ∑' n, w i n * a n - L = ∑' n, w i n * (a n - L) := by
    have h1 : Summable fun n => w i n * a n := by
      refine (hsumm.add (hsi.summable.mul_right L)).congr fun n => ?_
      ring
    rw [show ∑' n, w i n * (a n - L) = ∑' n, w i n * a n - ∑' n, w i n * L by
      rw [← Summable.tsum_sub h1 (hsi.summable.mul_right L)]
      exact tsum_congr fun n => by ring, tsum_mul_right, hsi.tsum_eq, one_mul]
  rw [hdiff, ← Summable.sum_add_tsum_nat_add N hsumm]
  have hhead_le : |∑ n ∈ range N, w i n * (a n - L)| ≤ M * ∑ n ∈ range N, w i n := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul, abs_of_nonneg (hwi n), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (hwi n)
    calc |a n - L| ≤ |a n| + |L| := abs_sub _ _
      _ ≤ M := by linarith [hB n]
  have htail_le : |∑' n, w i (n + N) * (a (n + N) - L)| ≤ ε / 2 := by
    have htail_s : Summable fun n => w i (n + N) := (summable_nat_add_iff N).2 hsi.summable
    calc |∑' n, w i (n + N) * (a (n + N) - L)|
        ≤ ∑' n, |w i (n + N) * (a (n + N) - L)| := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm ?_).trans_eq rfl
          exact ((summable_nat_add_iff N).2 hsumm).norm
      _ ≤ ∑' n, ε / 2 * w i (n + N) := by
          refine Summable.tsum_le_tsum (fun n => ?_)
            ((summable_nat_add_iff N).2 hsumm).abs (htail_s.mul_left _)
          rw [abs_mul, abs_of_nonneg (hwi _), mul_comm]
          exact mul_le_mul_of_nonneg_right (le_of_lt (by
            have := hN (n + N) (by omega)
            rwa [Real.dist_eq] at this)) (hwi _)
      _ = ε / 2 * ∑' n, w i (n + N) := tsum_mul_left
      _ ≤ ε / 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := Summable.sum_add_tsum_nat_add N hsi.summable
          rw [hsi.tsum_eq] at this
          have h0 : 0 ≤ ∑ n ∈ range N, w i n := sum_nonneg fun n _ => hwi n
          linarith
      _ = ε / 2 := mul_one _
  calc |∑ n ∈ range N, w i n * (a n - L) + ∑' n, w i (n + N) * (a (n + N) - L)|
      ≤ |∑ n ∈ range N, w i n * (a n - L)| + |∑' n, w i (n + N) * (a (n + N) - L)| :=
        abs_add_le _ _
    _ < M * (ε / (2 * M)) + ε / 2 := by
        refine add_lt_add_of_lt_of_le (hhead_le.trans_lt ?_) htail_le
        exact mul_lt_mul_of_pos_left hhi' hM0
    _ = ε := by field_simp; ring

/-! ### Iterated partial sums -/

/-- The partial sums `a 0 + ⋯ + a n`. -/
def psum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ range (n + 1), a m

/-- The `k`-fold iterated partial sums. -/
def iterSum (k : ℕ) (a : ℕ → ℝ) : ℕ → ℝ := psum^[k] a

/-- The Cesàro mean of order `k`. -/
noncomputable def cesaroMean (k : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  iterSum k a n / (n + k).choose k

theorem iterSum_succ (k : ℕ) (a : ℕ → ℝ) : iterSum (k + 1) a = psum (iterSum k a) :=
  Function.iterate_succ_apply' psum k a

/-- The hockey-stick identity: `∑_{m ≤ n} C(m + k, k) = C(n + k + 1, k + 1)`. -/
theorem sum_choose (k : ℕ) : ∀ n : ℕ,
    ∑ m ∈ range (n + 1), ((m + k).choose k : ℝ) = (n + k + 1).choose (k + 1)
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_choose k n, show n + 1 + k + 1 = (n + k + 1) + 1 by ring,
      Nat.choose_succ_succ' (n + k + 1) k, show n + 1 + k = n + k + 1 by ring]
    push_cast
    ring

theorem iterSum_one (k n : ℕ) : iterSum k (fun _ => 1) n = (n + k).choose k := by
  induction k generalizing n with
  | zero => simp [iterSum]
  | succ k ih =>
    rw [iterSum_succ, psum]
    simp only [ih]
    rw [sum_choose k n, show n + (k + 1) = n + k + 1 by ring]

theorem abs_iterSum_le {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) (k n : ℕ) :
    |iterSum k a n| ≤ B * (n + k).choose k := by
  induction k generalizing n with
  | zero => simpa [iterSum] using hB n
  | succ k ih =>
    rw [iterSum_succ, psum]
    calc |∑ m ∈ range (n + 1), iterSum k a m| ≤ ∑ m ∈ range (n + 1), |iterSum k a m| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ range (n + 1), B * (m + k).choose k := sum_le_sum fun m _ => ih m
      _ = B * (n + (k + 1)).choose (k + 1) := by
          rw [← mul_sum, sum_choose k n, show n + (k + 1) = n + k + 1 by ring]

theorem choose_pos (n k : ℕ) : (0 : ℝ) < (n + k).choose k := by
  exact_mod_cast Nat.choose_pos (by omega)

theorem abs_cesaroMean_le {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) (k n : ℕ) :
    |cesaroMean k a n| ≤ B := by
  rw [cesaroMean, abs_div, abs_of_pos (choose_pos n k), div_le_iff₀ (choose_pos n k)]
  exact abs_iterSum_le hB k n

/-! ### Consistency: order `k` gives order `k + 1` -/

theorem tendsto_cesaroMean_succ {a : ℕ → ℝ} {B L : ℝ} (hB : ∀ n, |a n| ≤ B) {k : ℕ}
    (h : Tendsto (cesaroMean k a) atTop (𝓝 L)) :
    Tendsto (cesaroMean (k + 1) a) atTop (𝓝 L) := by
  -- the weights `C(m + k, k) / C(n + k + 1, k + 1)` on `m ≤ n`
  let w : ℕ → ℕ → ℝ := fun n m =>
    if m ≤ n then ((m + k).choose k : ℝ) / (n + k + 1).choose (k + 1) else 0
  have hw0 : ∀ n m, 0 ≤ w n m := fun n m => by
    simp only [w]
    split_ifs <;> positivity
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n + k + 1).choose (k + 1) := fun n => by
    exact_mod_cast Nat.choose_pos (by omega)
  have hsum : ∀ n, HasSum (w n) 1 := by
    intro n
    have : ∑ m ∈ range (n + 1), w n m = 1 := by
      rw [show ∑ m ∈ range (n + 1), w n m =
          ∑ m ∈ range (n + 1), ((m + k).choose k : ℝ) / (n + k + 1).choose (k + 1) from
        sum_congr rfl fun m hm => ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hm)), ← sum_div,
        sum_choose k n, div_self (hpos n).ne']
    rw [← this]
    exact hasSum_sum_of_ne_finset_zero fun m hm => ite_eq_right (by
      rw [mem_range] at hm
      omega)
  have hhead : ∀ N, Tendsto (fun n => ∑ m ∈ range N, w n m) atTop (𝓝 0) := by
    intro N
    -- eventually the head is `(∑_{m < N} C(m + k, k)) / C(n + k + 1, k + 1)`
    have hden : Tendsto (fun n : ℕ => ((n + k + 1).choose (k + 1) : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have : n ≤ (n + k + 1).choose (k + 1) := by
        have h1 : (n + 1).choose n ≤ (n + k + 1).choose n := Nat.choose_le_choose n (by omega)
        have h2 : (n + k + 1).choose (k + 1) = (n + k + 1).choose n := by
          rw [show n + k + 1 = n + (k + 1) by ring]
          exact (Nat.choose_symm_add).symm
        rw [Nat.choose_succ_self_right] at h1
        omega
      exact_mod_cast this
    have := (tendsto_const_nhds (x := ∑ m ∈ range N, ((m + k).choose k : ℝ))).div_atTop hden
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [sum_div]
    refine sum_congr rfl fun m hm => ?_
    simp only [w, ite_eq_left (show m ≤ n by have := mem_range.1 hm; omega)]
  have hmean : ∀ n, cesaroMean (k + 1) a n = ∑' m, w n m * cesaroMean k a m := by
    intro n
    rw [tsum_eq_sum (s := range (n + 1)) fun m hm => by
      simp only [w, ite_eq_right (show ¬ m ≤ n by rw [mem_range] at hm; omega), zero_mul]]
    rw [cesaroMean, iterSum_succ, psum, sum_div, show n + (k + 1) = n + k + 1 by ring]
    refine sum_congr rfl fun m hm => ?_
    simp only [w, ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hm)), cesaroMean]
    have := choose_pos m k
    field_simp
  refine (tendsto_weighted (w := w) (Eventually.of_forall hw0) (Eventually.of_forall hsum)
    hhead (abs_cesaroMean_le hB k) h).congr fun n => (hmean n).symm

/-! ### Order `k` gives the Abel mean -/

/-- Partial sums against the geometric series: `∑ S n xⁿ = (∑ aₙ xⁿ) / (1 - x)`. -/
theorem tsum_psum_mul_pow {a : ℕ → ℝ} {x : ℝ} (hx : |x| < 1)
    (ha : Summable fun n => ‖a n * x ^ n‖) :
    (∑' n, psum a n * x ^ n = (∑' n, a n * x ^ n) * (1 - x)⁻¹) ∧
      Summable fun n => ‖psum a n * x ^ n‖ := by
  have hg : Summable fun n => ‖x ^ n‖ := by
    simpa [norm_pow] using summable_geometric_of_lt_one (abs_nonneg x) hx
  have hterm : ∀ n, ∑ m ∈ range (n + 1), a m * x ^ m * x ^ (n - m) = psum a n * x ^ n := by
    intro n
    rw [psum, sum_mul]
    refine sum_congr rfl fun m hm => ?_
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (mem_range.1 hm))]
  constructor
  · have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha hg
    rw [tsum_geometric_of_abs_lt_one hx] at hprod
    rw [hprod]
    exact tsum_congr fun n => (hterm n).symm
  · exact (summable_norm_sum_mul_range_of_summable_norm ha hg).congr fun n => by rw [hterm]

theorem tsum_iterSum_mul_pow {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) (k : ℕ) :
    (∑' n, a n * x ^ n = (1 - x) ^ k * ∑' n, iterSum k a n * x ^ n) ∧
      Summable fun n => ‖iterSum k a n * x ^ n‖ := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg hx0]
  induction k with
  | zero =>
    refine ⟨by simp [iterSum], ?_⟩
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hx0 hx1).mul_left B)
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact mul_le_mul_of_nonneg_right (by simpa [iterSum] using hB n) (pow_nonneg hx0 n)
  | succ k ih =>
    obtain ⟨h1, h2⟩ := tsum_psum_mul_pow hx ih.2
    refine ⟨?_, ?_⟩
    · rw [iterSum_succ, h1, ih.1, pow_succ]
      have : (1 - x) ≠ 0 := by linarith
      field_simp
    · rw [iterSum_succ]
      exact h2

/-- **Order `k` gives the Abel mean**: if `σᵏ → L` for a bounded sequence, then
`(1 - x) ∑ aₙ xⁿ → L` as `x → 1⁻`. -/
theorem tendsto_abel_of_tendsto_cesaroMean {a : ℕ → ℝ} {B L : ℝ} (hB : ∀ n, |a n| ≤ B) {k : ℕ}
    (h : Tendsto (cesaroMean k a) atTop (𝓝 L)) :
    Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 L) := by
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  -- the weights `(1 - x)^(k+1) C(n + k, k) xⁿ`
  let w : ℝ → ℕ → ℝ := fun x n => (1 - x) ^ (k + 1) * (((n + k).choose k : ℝ) * x ^ n)
  have hw0 : ∀ᶠ x in 𝓝[<] (1 : ℝ), ∀ n, 0 ≤ w x n := by
    filter_upwards [hev] with x hx n
    have : 0 ≤ 1 - x := by linarith [hx.2]
    have : 0 ≤ x := hx.1.le
    positivity
  have hsum : ∀ᶠ x in 𝓝[<] (1 : ℝ), HasSum (w x) 1 := by
    filter_upwards [hev] with x hx
    have hx' : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hx.1]; exact hx.2
    have := (hasSum_choose_mul_geometric_of_norm_lt_one k hx').mul_left ((1 - x) ^ (k + 1))
    have hne : (1 - x) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith [hx.2])
    rwa [mul_one_div, div_self hne] at this
  have hhead : ∀ N, Tendsto (fun x => ∑ n ∈ range N, w x n) (𝓝[<] 1) (𝓝 0) := by
    intro N
    have hc : Continuous fun x : ℝ => ∑ n ∈ range N, w x n := by
      simp only [w]
      fun_prop
    have := hc.tendsto 1
    simp only [w, sub_self, zero_pow (Nat.succ_ne_zero k), zero_mul, sum_const_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hT := tendsto_weighted hw0 hsum hhead (abs_cesaroMean_le hB k) h
  refine hT.congr' ?_
  filter_upwards [hev] with x hx
  obtain ⟨h1, -⟩ := tsum_iterSum_mul_pow hB hx.1.le hx.2 k
  rw [h1, ← mul_assoc, ← pow_succ', ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [w, cesaroMean]
  have := choose_pos n k
  field_simp

/-! ### Cesàro means of every order -/

/-- **Cesàro means of every order agree** on bounded nonnegative sequences. -/
theorem tendsto_cesaroMean_iff {a : ℕ → ℝ} {B L : ℝ} (ha0 : ∀ n, 0 ≤ a n) (hB : ∀ n, |a n| ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (cesaroMean k a) atTop (𝓝 L) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, a n) / N) atTop (𝓝 L) := by
  constructor
  · intro h
    refine Tauberian.tendsto_cesaro_of_tendsto_abel ha0 (fun x hx0 hx1 => ?_)
      (tendsto_abel_of_tendsto_cesaroMean hB h)
    exact (tsum_iterSum_mul_pow hB hx0 hx1 0).2.of_norm.congr fun n => by simp [iterSum]
  · intro h
    -- order `1` is the average of `a 0, …, a n`
    have h1 : Tendsto (cesaroMean 1 a) atTop (𝓝 L) := by
      refine (h.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [Function.comp, cesaroMean, iterSum, Function.iterate_one, psum,
        Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    clear hk
    induction j with
    | zero => exact h1
    | succ j ih => exact tendsto_cesaroMean_succ hB ih

/-- **Density `1/2` through Cesàro means**, for every bit sequence and every order `k ≥ 1`. -/
theorem halfDensity_iff_cesaroMean (b : ℕ → Bool) {k : ℕ} (hk : 1 ≤ k) :
    Symmetry.HalfDensity b ↔
      Tendsto (cesaroMean k fun t => if b t then (1 : ℝ) else 0) atTop (𝓝 (1 / 2)) := by
  rw [ProblemTwo.halfDensity_iff_tendsto, tendsto_cesaroMean_iff (B := 1)
    (fun n => by split_ifs <;> norm_num) (fun n => by split_ifs <;> norm_num) hk]
  refine tendsto_congr fun n => ?_
  rw [ProblemTwo.count_eq_sum]

/-- **Problem 2 through Cesàro means**: Problem 2 holds iff the Cesàro means of order `k` of the
center column tend to `1/2`, for every `k ≥ 1`. -/
theorem problem2_iff_cesaroMean {k : ℕ} (hk : 1 ≤ k) : Rule30Prize.Problem2 ↔
    Tendsto (cesaroMean k fun t => if c t then (1 : ℝ) else 0) atTop (𝓝 (1 / 2)) :=
  halfDensity_iff_cesaroMean c hk

end Rule30Equivalents.CesaroMeans
