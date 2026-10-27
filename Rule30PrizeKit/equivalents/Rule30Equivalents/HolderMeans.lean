module

public import Rule30Equivalents.ProblemTwo
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
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
# Iterated Cesàro means and Hardy's Tauberian theorem

Write `mean u n = (u 0 + ⋯ + u (n-1)) / n` for the Cesàro mean (Mathlib's
convention in `Filter.Tendsto.cesaro`) and `holder k u = mean^[k] u` for the `k`-fold iterated
mean, Hölder's mean of order `k`.

* `tendsto_of_tendsto_mean`: **Hardy's Tauberian theorem** (1910). If the Cesàro means of `s` tend
  to `L` and `|s (n+1) - s n| ≤ K / (n+1)`, then `s` tends to `L`. Average `s` over the block
  `n, …, n + q - 1` with `q ≈ n / M`: the block average is `σ_{n+q} + (n/q)(σ_{n+q} - σ_n)`, which
  tends to `L`, and it differs from `s n` by at most about `K / M`.
* `tendsto_holder_iff`: for a bounded sequence and every `k ≥ 1`, the Hölder means of order `k`
  tend to `L` iff the Cesàro means do. One direction is the regularity of Cesàro means; for the
  other, the mean of a sequence bounded by `B` has increments at most `2B / (n + 1)`
  (`abs_mean_succ_sub_le`), so Hardy's theorem peels off one mean at a time.
* `halfDensity_iff_holder`, `problem2_iff_holder`: **Problem 2 holds iff the Hölder means of order
  `k` of the center column tend to `1/2`**, for every `k ≥ 1`.
-/

@[expose] public section

namespace Rule30Equivalents.HolderMeans

open Filter Topology Finset Ruliology.CellularAutomata

/-- The Cesàro mean of the first `n` terms. -/
noncomputable def mean (u : ℕ → ℝ) (n : ℕ) : ℝ := (n : ℝ)⁻¹ * ∑ i ∈ range n, u i

/-- The `k`-fold iterated Cesàro mean, Hölder's mean of order `k`. -/
noncomputable def holder (k : ℕ) (u : ℕ → ℝ) : ℕ → ℝ := mean^[k] u

theorem sum_range_eq_mul_mean (u : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, u i = n * mean u n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [mean, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem mean_succ (u : ℕ → ℝ) (n : ℕ) :
    mean u (n + 1) = mean u n + (u n - mean u n) / (n + 1) := by
  have h := sum_range_eq_mul_mean u n
  rw [mean, sum_range_succ, h]
  push_cast
  field_simp
  ring

theorem abs_mean_le {u : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |u n| ≤ B) (n : ℕ) : |mean u n| ≤ B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [mean] using hB0
  rw [mean, abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ (by positivity)]
  calc |∑ i ∈ range n, u i| ≤ ∑ i ∈ range n, |u i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, B := sum_le_sum fun i _ => hB i
    _ = n * B := by rw [sum_const, card_range, nsmul_eq_mul]

/-- The mean of a sequence bounded by `B` moves by at most `2B / (n + 1)` at step `n`. -/
theorem abs_mean_succ_sub_le {u : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |u n| ≤ B) (n : ℕ) :
    |mean u (n + 1) - mean u n| ≤ 2 * B / (n + 1) := by
  rw [mean_succ, add_sub_cancel_left, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc |u n - mean u n| ≤ |u n| + |mean u n| := abs_sub _ _
    _ ≤ B + B := add_le_add (hB n) (abs_mean_le hB n)
    _ = 2 * B := by ring

/-- Small increments add up linearly: `|s (n + j) - s n| ≤ j K / (n + 1)`. -/
theorem abs_sub_le_of_increments {s : ℕ → ℝ} {K : ℝ}
    (hK : ∀ n, |s (n + 1) - s n| ≤ K / (n + 1)) (n : ℕ) :
    ∀ j : ℕ, |s (n + j) - s n| ≤ j * K / (n + 1) := by
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hK 0)
    simpa using this
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc |s (n + (j + 1)) - s n| ≤ |s (n + j + 1) - s (n + j)| + |s (n + j) - s n| := by
          rw [← add_assoc]
          exact abs_sub_le _ _ _
      _ ≤ K / (n + 1) + j * K / (n + 1) := by
          refine add_le_add ((hK (n + j)).trans ?_) ih
          refine div_le_div_of_nonneg_left hK0 (by positivity) ?_
          push_cast
          linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      _ = ((j + 1 : ℕ) : ℝ) * K / (n + 1) := by push_cast; ring

/-- **Hardy's Tauberian theorem** for Cesàro means: if the means of `s` tend to `L` and the
increments of `s` are at most `K / (n + 1)`, then `s` tends to `L`. -/
theorem tendsto_of_tendsto_mean {s : ℕ → ℝ} {K L : ℝ}
    (hK : ∀ n, |s (n + 1) - s n| ≤ K / (n + 1)) (h : Tendsto (mean s) atTop (𝓝 L)) :
    Tendsto s atTop (𝓝 L) := by
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hK 0)
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the block length is about `n / M`, with `K / M < ε / 4`
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * K / ε)
  have hM0 : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  have hMpos : 0 < M := by exact_mod_cast hM0
  have hKM : K / M < ε / 4 := by
    rw [div_lt_iff₀ hM0]
    rw [div_lt_iff₀ hε] at hM
    linarith
  set δ := ε / (4 * (2 * M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 h δ hδ0
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 * K / ε)
  refine ⟨N₁ + N₂ + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  set q := n / M + 1 with hq
  have hq0 : (0 : ℝ) < q := by positivity
  -- the block average
  set A := (∑ j ∈ range q, s (n + j)) / q with hA
  have hAeq : A = mean s (n + q) + n / q * (mean s (n + q) - mean s n) := by
    have h1 := sum_range_eq_mul_mean s (n + q)
    rw [sum_range_add, sum_range_eq_mul_mean s n] at h1
    rw [hA, show ∑ j ∈ range q, s (n + j) = ((n + q : ℕ) : ℝ) * mean s (n + q) -
      n * mean s n by linarith]
    push_cast
    field_simp
    ring
  -- `s n` is close to the block average
  have hsA : |s n - A| ≤ q * K / (n + 1) := by
    have hsum : A - s n = (∑ j ∈ range q, (s (n + j) - s n)) / q := by
      rw [hA, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [abs_sub_comm, hsum, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    calc |∑ j ∈ range q, (s (n + j) - s n)| ≤ ∑ j ∈ range q, |s (n + j) - s n| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range q, q * K / (n + 1) := by
          refine sum_le_sum fun j hj => (abs_sub_le_of_increments hK n j).trans ?_
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hK0) hn0.le
          exact_mod_cast (mem_range.1 hj).le
      _ = q * K / (n + 1) * q := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
  have hqK : q * K / (n + 1) ≤ K / M + K / (n + 1) := by
    have hqle : (q : ℝ) ≤ n / M + 1 := by
      rw [hq]
      push_cast
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := M)
      linarith
    calc q * K / (n + 1) ≤ (n / M + 1) * K / (n + 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqle hK0) hn0.le
      _ = K / M * (n / (n + 1)) + K / (n + 1) := by field_simp
      _ ≤ K / M * 1 + K / (n + 1) := by
          gcongr
          rw [div_le_one hn0]
          linarith
      _ = K / M + K / (n + 1) := by rw [mul_one]
  have hnq : (n : ℝ) / q ≤ M := by
    rw [div_le_iff₀ hq0, hq]
    push_cast
    have := Nat.lt_div_mul_add (a := n) hMpos
    have h' : (n : ℝ) < (n / M : ℕ) * M + M := by exact_mod_cast this
    nlinarith
  -- the means at `n` and `n + q` are within `δ` of `L`
  have h1 : |mean s n - L| < δ := hN₁ n (by omega)
  have h2 : |mean s (n + q) - L| < δ := hN₁ (n + q) (le_trans (by omega) (Nat.le_add_right n q))
  have hKn : K / (n + 1) < ε / 4 := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hN₂
    have : (N₂ : ℝ) < n + 1 := by exact_mod_cast (by omega : N₂ < n + 1)
    nlinarith
  rw [Real.dist_eq]
  have hdiff : |mean s (n + q) - mean s n| < 2 * δ := by
    calc |mean s (n + q) - mean s n| ≤ |mean s (n + q) - L| + |L - mean s n| := abs_sub_le _ _ _
      _ = |mean s (n + q) - L| + |mean s n - L| := by rw [abs_sub_comm L]
      _ < δ + δ := add_lt_add h2 h1
      _ = 2 * δ := by ring
  have hAL : |A - L| ≤ δ + M * (2 * δ) := by
    rw [hAeq]
    calc |mean s (n + q) + n / q * (mean s (n + q) - mean s n) - L|
        ≤ |mean s (n + q) - L| + |n / q * (mean s (n + q) - mean s n)| := by
          rw [show mean s (n + q) + n / q * (mean s (n + q) - mean s n) - L =
            (mean s (n + q) - L) + n / q * (mean s (n + q) - mean s n) by ring]
          exact abs_add_le _ _
      _ ≤ δ + M * (2 * δ) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / q)]
          exact add_le_add h2.le (mul_le_mul hnq hdiff.le (abs_nonneg _) hM0.le)
  have hδM : δ + M * (2 * δ) = ε / 4 := by
    rw [hδ]
    field_simp
    ring
  calc |s n - L| ≤ |s n - A| + |A - L| := abs_sub_le _ _ _
    _ ≤ (K / M + K / (n + 1)) + ε / 4 := add_le_add (hsA.trans hqK) (hδM ▸ hAL)
    _ < ε / 4 + ε / 4 + ε / 4 := by linarith
    _ < ε := by linarith

theorem holder_succ (k : ℕ) (u : ℕ → ℝ) : holder (k + 1) u = mean (holder k u) :=
  Function.iterate_succ_apply' mean k u

theorem abs_holder_le {u : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |u n| ≤ B) :
    ∀ k n, |holder k u n| ≤ B
  | 0, n => hB n
  | k + 1, n => by
    rw [holder_succ]
    exact abs_mean_le (abs_holder_le hB k) n

/-- **Hölder means of every order agree with Cesàro means** on bounded sequences. -/
theorem tendsto_holder_iff {u : ℕ → ℝ} {B L : ℝ} (hB : ∀ n, |u n| ≤ B) :
    ∀ k : ℕ, 1 ≤ k → (Tendsto (holder k u) atTop (𝓝 L) ↔ Tendsto (mean u) atTop (𝓝 L))
  | 0, h => absurd h (by norm_num)
  | 1, _ => by rw [holder_succ]; rfl
  | k + 2, _ => by
    have ih := tendsto_holder_iff (L := L) hB (k + 1) (by omega)
    rw [holder_succ]
    constructor
    · intro h
      refine ih.1 (tendsto_of_tendsto_mean (K := 2 * B) (fun n => ?_) h)
      rw [holder_succ]
      exact abs_mean_succ_sub_le (abs_holder_le hB k) n
    · intro h
      have := Filter.Tendsto.cesaro (ih.2 h)
      refine this.congr fun n => ?_
      rfl

/-- **Density `1/2` through Hölder means**, for every bit sequence and every order `k ≥ 1`. -/
theorem halfDensity_iff_holder (b : ℕ → Bool) {k : ℕ} (hk : 1 ≤ k) : Symmetry.HalfDensity b ↔
    Tendsto (holder k fun t => if b t then (1 : ℝ) else 0) atTop (𝓝 (1 / 2)) := by
  rw [ProblemTwo.halfDensity_iff_tendsto, tendsto_holder_iff (B := 1)
    (fun n => by split_ifs <;> norm_num) k hk]
  refine tendsto_congr fun n => ?_
  rw [ProblemTwo.count_eq_sum, mean, div_eq_inv_mul]

/-- **Problem 2 through Hölder means**: Problem 2 holds iff the Hölder means of order `k` of the
center column tend to `1/2`, for every `k ≥ 1`. -/
theorem problem2_iff_holder {k : ℕ} (hk : 1 ≤ k) : Rule30Prize.Problem2 ↔
    Tendsto (holder k fun t => if c t then (1 : ℝ) else 0) atTop (𝓝 (1 / 2)) :=
  halfDensity_iff_holder c hk

end Rule30Equivalents.HolderMeans
