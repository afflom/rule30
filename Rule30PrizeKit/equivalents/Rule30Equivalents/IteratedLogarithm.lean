module

public import Rule30Equivalents.Fluctuations
public import Rule30Equivalents.LongestRuns
public import Mathlib.Probability.BorelCantelli
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
# The law of the iterated logarithm for the center column

For a fair-coin configuration the center trace is a sequence of fair coins
(`RandomConfigurations.measurePreserving_trace`), so `W(n)`, the number of black cells minus the
number of white cells among its first `n`, is a simple random walk (`Fluctuations.walk`).
Khinchin's law of the iterated logarithm pins down its fluctuations:

* `ae_limsup_liminf_walk_trace`: **for almost every configuration, the center column has
  `limsup W(n)/√(2 n log log n) = 1` and `liminf W(n)/√(2 n log log n) = -1`.**
* `ae_clusterPt_walk_trace`: the limit points of `W(n)/√(2 n log log n)` form exactly `[-1, 1]`.
  The walk moves by `±1` while the scale grows, so the ratio cannot jump over a level between its
  visits near `-1` and near `1` (`mapClusterPt_div`).
* `residual_limsup_liminf_walk_div_trace`: in the sense of category the picture is different: for
  a comeager set of configurations `limsup W(n)/n = 1` and `liminf W(n)/n = -1`, the largest
  possible oscillation (`residual_oscillation`).

The upper half, `ae_eventually_two_mul_imbalance_lt`, sharpens
`Fluctuations.ae_eventually_imbalance_lt` from the constant `2` to every constant `c > 1`: along
the scales `⌊cʲ⌋` instead of `2ʲ`, Lévy's maximal inequality and Hoeffding's give summable
probabilities.

The lower half, `ae_frequently_lt_two_mul_imbalance`, needs the fair binomial tail from below at
moderate deviations. Among `2M` fair coins exactly `M + i` are black with probability
`(2M choose M + i)/4^M ≥ exp(-i²/(M - i))/(2√M)` (`centralBinom_mul_exp_le_choose`,
`four_pow_le_two_mul_sqrt_mul_centralBinom`), so at least `M + y` are black with probability at
least `exp(-z²/(M - z))/2`, `z = y + √M + 1` (`le_measureReal_sum_ge`). The windows
`[2bᵏ, 2bᵏ⁺¹)` are independent (`RandomConfigurations.map_windows`), so by the second
Borel–Cantelli lemma (`ae_frequently_window_mem`) the walk gains nearly `√(2 n log log n)`,
`n = 2bᵏ⁺¹`, across infinitely many of them. For a large ratio `b` the walk before the window,
above `-2√(2 n log log n / b)` by the cruder envelope, cannot cancel the gain.
-/

@[expose] public section

namespace Rule30Equivalents.IteratedLogarithm

open MeasureTheory ProbabilityTheory Filter Topology Genericity RandomConfigurations Fluctuations

/-- `log x > 1` for `x ≥ 4`, since `log 2 > 1/2`. -/
theorem one_lt_log_of_four_le {x : ℝ} (hx : 4 ≤ x) : 1 < Real.log x := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
  rw [Real.log_inv] at h
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_le_log (by norm_num) hx
  linarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  calc √(x + y) ≤ √((√x + √y) ^ 2) := Real.sqrt_le_sqrt (by
        nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)])
    _ = √x + √y := Real.sqrt_sq (by positivity)

/-! ### The upper half -/

/-- **The upper half of the law of the iterated logarithm**: for every `c > 1` and almost every
fair-coin sequence, `2 (N(n) - n/2)` stays below `c √(2 n log log n)` from some `n` on. Along the
scales `n_j = ⌊cʲ⌋`, Lévy's inequality and Hoeffding's bound the probability of reaching
`(c/2) √(2 n_j log log n_j)` before time `n_(j+1)` by `2 exp(-c² (n_j/n_(j+1)) log log n_j)`;
the ratio `c² n_j/n_(j+1)` tends to `c > 1`, so these probabilities are summable. -/
theorem ae_eventually_two_mul_imbalance_lt {c : ℝ} (hc : 1 < c) :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ n : ℕ in atTop,
      2 * imbalance v n < c * √(2 * n * Real.log (Real.log n)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ j, N j = ⌊c ^ j⌋₊ := ⟨_, fun _ => rfl⟩
  have hNmono : Monotone N := fun i j hij => by
    rw [hN, hN]
    exact Nat.floor_le_floor (pow_le_pow_right₀ hc.le hij)
  have hNle : ∀ j, (N j : ℝ) ≤ c ^ j := fun j => by
    rw [hN]
    exact Nat.floor_le (by positivity)
  have hNgt : ∀ j, c ^ j - 1 < N j := fun j => by
    rw [hN]
    exact Nat.sub_one_lt_floor _
  have hNtop : Tendsto N atTop atTop := by
    rw [show N = fun j => ⌊c ^ j⌋₊ from funext hN]
    exact tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hc)
  have hlogc : 0 < Real.log c := Real.log_pos hc
  set p : ℝ := (1 + c) / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  set a : ℝ := Real.log c / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  -- from some `j` on: `p N (j + 1) ≤ c² N j`, `a j ≤ log (N j)`, `16 ≤ N j` and `1 ≤ j`
  have hev : ∀ᶠ j : ℕ in atTop, p * N (j + 1) ≤ c ^ 2 * N j ∧ a * j ≤ Real.log (N j) ∧
      16 ≤ N j ∧ 1 ≤ j := by
    have h1 : ∀ᶠ j : ℕ in atTop, max (2 * c / (c - 1)) 17 ≤ c ^ j :=
      (tendsto_pow_atTop_atTop_of_one_lt hc).eventually_ge_atTop _
    have h2 : ∀ᶠ j : ℕ in atTop, 2 * Real.log 2 ≤ j * Real.log c :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hlogc).eventually_ge_atTop _
    filter_upwards [h1, h2, eventually_ge_atTop 1] with j hj1 hj2 hj3
    have hu1 : 2 * c / (c - 1) ≤ c ^ j := (le_max_left _ _).trans hj1
    have hu2 : (17 : ℝ) ≤ c ^ j := (le_max_right _ _).trans hj1
    have hlo := hNgt j
    have hhi := hNle (j + 1)
    rw [pow_succ] at hhi
    refine ⟨?_, ?_, ?_, hj3⟩
    · have hcu : 2 * c ≤ c ^ j * (c - 1) := (div_le_iff₀ (by linarith)).1 hu1
      calc p * N (j + 1) ≤ p * (c ^ j * c) := mul_le_mul_of_nonneg_left hhi (by linarith)
        _ ≤ c ^ 2 * (c ^ j - 1) := by rw [hp]; nlinarith
        _ ≤ c ^ 2 * N j := mul_le_mul_of_nonneg_left hlo.le (by positivity)
    · have hpos : 0 < c ^ j / 2 := by positivity
      calc a * j = j * Real.log c - j * Real.log c / 2 := by rw [ha]; ring
        _ ≤ j * Real.log c - Real.log 2 := by linarith
        _ = Real.log (c ^ j / 2) := by
            rw [Real.log_div (by positivity) two_ne_zero, Real.log_pow]
        _ ≤ Real.log (N j) := Real.log_le_log hpos (by linarith)
    · have : (16 : ℝ) < N j := by linarith
      exact_mod_cast this.le
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  have hJ1 : 1 ≤ J := (hJ J le_rfl).2.2.2
  -- the events: reaching `x (j + J)` before time `N (j + J + 1)`
  set L : ℕ → ℝ := fun j => Real.log (Real.log (N j)) with hL
  set x : ℕ → ℝ := fun j => c / 2 * √(2 * N j * L j) with hx
  set E : ℕ → Set (ℕ → Bool) := fun j =>
    {v | ∃ k ≤ N (j + J + 1), x (j + J) ≤ imbalance v k} with hE
  have hbound : ∀ j : ℕ, (coins ℕ).real (E j) ≤ 2 * ((a * ((j + J : ℕ) : ℝ)) ^ p)⁻¹ := by
    intro j
    obtain ⟨hpN, haN, h16, -⟩ := hJ (j + J) (by omega)
    set i := j + J with hi
    have hNi : (16 : ℝ) ≤ N i := by exact_mod_cast h16
    have hNi1 : (0 : ℝ) < N (i + 1) := by
      have : (16 : ℝ) ≤ N (i + 1) := by exact_mod_cast h16.trans (hNmono (Nat.le_succ i))
      linarith
    have hai : 0 < a * (i : ℝ) := by
      have : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
      positivity
    have hL0 : Real.log (a * i) ≤ L i := Real.log_le_log hai haN
    have hLnn : 0 ≤ L i :=
      Real.log_nonneg (one_lt_log_of_four_le (by linarith)).le
    -- Lévy's inequality and Hoeffding's
    have h1 : (coins ℕ).real (E j) ≤
        2 * (coins ℕ).real {v | x i ≤ imbalance v (N (i + 1))} := by
      have := measure_exists_le_imbalance_le (N (i + 1)) (x i)
      rw [measureReal_def, measureReal_def, ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _))
        this
    have h2 := RandomConfigurations.measureReal_sum_ge_le (N (i + 1))
      (by positivity : 0 ≤ x i)
    have hx2 : x i ^ 2 = c ^ 2 * N i * L i / 2 := by
      simp only [hx]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hexp : -2 * x i ^ 2 / (N (i + 1) : ℝ) ≤ -(p * Real.log (a * i)) := by
      rw [hx2, neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ hNi1]
      calc p * Real.log (a * i) * N (i + 1) ≤ p * L i * N (i + 1) := by gcongr
        _ = L i * (p * N (i + 1)) := by ring
        _ ≤ L i * (c ^ 2 * N i) := mul_le_mul_of_nonneg_left hpN hLnn
        _ = 2 * (c ^ 2 * N i * L i / 2) := by ring
    have hrpow : Real.exp (-(p * Real.log (a * i))) = ((a * i) ^ p)⁻¹ := by
      rw [Real.rpow_def_of_pos hai, ← Real.exp_neg, mul_comm]
    calc (coins ℕ).real (E j) ≤ 2 * (coins ℕ).real {v | x i ≤ imbalance v (N (i + 1))} := h1
      _ ≤ 2 * Real.exp (-2 * x i ^ 2 / (N (i + 1) : ℝ)) := by gcongr; exact h2
      _ ≤ 2 * Real.exp (-(p * Real.log (a * i))) := by gcongr
      _ = 2 * ((a * i) ^ p)⁻¹ := by rw [hrpow]
  have hsum : ∑' j, coins ℕ (E j) ≠ ⊤ := by
    have hsumm : Summable fun j : ℕ => 2 * ((a * ((j + J : ℕ) : ℝ)) ^ p)⁻¹ := by
      have h := (summable_nat_add_iff J).2 (Real.summable_nat_rpow_inv.2 hp1)
      refine (h.mul_left (2 * (a ^ p)⁻¹)).congr fun j => ?_
      rw [Real.mul_rpow ha0.le (Nat.cast_nonneg _), mul_inv]
      ring
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, 2 * ((a * ((j + J : ℕ) : ℝ)) ^ p)⁻¹)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  filter_upwards [ae_eventually_notMem hsum] with v hv
  obtain ⟨J', hJ'⟩ := eventually_atTop.1 hv
  filter_upwards [eventually_ge_atTop (N (J' + J))] with n hn
  have hex : ∃ i, n < N (i + 1) :=
    ((hNtop.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop n).exists
  have hi1 : n < N (Nat.find hex + 1) := Nat.find_spec hex
  have hiJ : J' + J ≤ Nat.find hex := by
    by_contra h
    have : N (Nat.find hex + 1) ≤ N (J' + J) := hNmono (by omega)
    omega
  have hi2 : N (Nat.find hex) ≤ n := by
    obtain ⟨i', hi'⟩ : ∃ i', Nat.find hex = i' + 1 := ⟨Nat.find hex - 1, by omega⟩
    rw [hi']
    exact not_lt.1 (Nat.find_min hex (by omega : i' < Nat.find hex))
  set i := Nat.find hex with hidef
  have hvi := hJ' (i - J) (by omega)
  have hiJ' : i - J + J = i := by omega
  simp only [hE, Set.mem_ofPred_eq, not_exists, not_and, not_le, hiJ'] at hvi
  have hlt : imbalance v n < x i := hvi n hi1.le
  obtain ⟨-, -, h16, -⟩ := hJ i (by omega)
  have hNi : (16 : ℝ) ≤ N i := by exact_mod_cast h16
  have hNn : (N i : ℝ) ≤ n := by exact_mod_cast hi2
  have hlogN : 1 < Real.log (N i) := one_lt_log_of_four_le (by linarith)
  have hL0 : 0 ≤ L i := Real.log_nonneg hlogN.le
  have hLn : L i ≤ Real.log (Real.log n) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by linarith) hNn)
  have hrad : 2 * N i * L i ≤ 2 * n * Real.log (Real.log n) := by
    have : (0 : ℝ) ≤ N i := by positivity
    nlinarith
  calc 2 * imbalance v n < 2 * x i := by linarith
    _ = c * √(2 * N i * L i) := by simp only [hx]; ring
    _ ≤ c * √(2 * n * Real.log (Real.log n)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) hc0.le

/-! ### Fair binomial tails from below -/

/-- `4^M ≤ 2 √M (2M choose M)` for `M ≥ 1`: by induction `16^M ≤ 4M (2M choose M)²`, since
`(M + 1) (2M + 2 choose M + 1) = 2 (2M + 1) (2M choose M)` and `4M (M + 1) ≤ (2M + 1)²`. -/
theorem four_pow_le_two_mul_sqrt_mul_centralBinom {M : ℕ} (hM : 0 < M) :
    (4 : ℝ) ^ M ≤ 2 * √(M : ℝ) * M.centralBinom := by
  have key : ∀ M : ℕ, 0 < M → 16 ^ M ≤ 4 * M * M.centralBinom ^ 2 := by
    intro M hM
    induction M with
    | zero => omega
    | succ M ih =>
      rcases Nat.eq_zero_or_pos M with rfl | hM'
      · norm_num [Nat.centralBinom, Nat.choose]
      · have h := ih hM'
        have hrec := Nat.succ_mul_centralBinom_succ M
        have hid : 16 * (4 * M * M.centralBinom ^ 2) * (M + 1) + 16 * M.centralBinom ^ 2 =
            4 * (2 * (2 * M + 1) * M.centralBinom) ^ 2 := by ring
        have : 16 ^ (M + 1) * (M + 1) ≤ 4 * (M + 1) * (M + 1).centralBinom ^ 2 * (M + 1) := by
          calc 16 ^ (M + 1) * (M + 1) = 16 * 16 ^ M * (M + 1) := by ring
            _ ≤ 16 * (4 * M * M.centralBinom ^ 2) * (M + 1) := by gcongr
            _ ≤ 4 * (2 * (2 * M + 1) * M.centralBinom) ^ 2 := by
                rw [← hid]; exact Nat.le_add_right _ _
            _ = 4 * ((M + 1) * (M + 1).centralBinom) ^ 2 := by rw [hrec]
            _ = 4 * (M + 1) * (M + 1).centralBinom ^ 2 * (M + 1) := by ring
        exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos M)
  have h : ((16 ^ M : ℕ) : ℝ) ≤ ((4 * M * M.centralBinom ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast key M hM
  push_cast at h
  have h' : ((4 : ℝ) ^ M) ^ 2 ≤ (2 * √(M : ℝ) * M.centralBinom) ^ 2 := by
    calc ((4 : ℝ) ^ M) ^ 2 = 16 ^ M := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ 4 * M * M.centralBinom ^ 2 := h
      _ = (2 * √(M : ℝ) * M.centralBinom) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
          ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h'

/-- **Binomial coefficients near the middle**: `(2M choose M) exp(-i²/(M - i)) ≤ (2M choose M + i)`
for `i < M`. Each step multiplies the coefficient by `(M - i)/(M + i + 1)`, which is at least
`exp(-(2i + 1)/(M - i))` since `1 + x ≤ exp x`. -/
theorem centralBinom_mul_exp_le_choose {M : ℕ} : ∀ {i : ℕ}, i < M →
    (M.centralBinom : ℝ) * Real.exp (-((i : ℝ) ^ 2 / (M - i))) ≤ ((2 * M).choose (M + i) : ℝ)
  | 0, _ => by simp [Nat.centralBinom_eq_two_mul_choose]
  | i + 1, hi => by
    have h := centralBinom_mul_exp_le_choose (M := M) (i := i) (by omega)
    have hiM : (i : ℝ) + 1 < M := by exact_mod_cast hi
    have hMi : (0 : ℝ) < M - i := by linarith
    have hMi1 : (0 : ℝ) < M - (i + 1) := by linarith
    have hne : (M : ℝ) - i ≠ 0 := hMi.ne'
    -- `(2M choose M + i + 1) (M + i + 1) = (2M choose M + i) (M - i)`
    have hstep : ((2 * M).choose (M + (i + 1)) : ℝ) * (M + i + 1) =
        ((2 * M).choose (M + i) : ℝ) * (M - i) := by
      have h1 := Nat.choose_succ_right_eq (2 * M) (M + i)
      rw [show 2 * M - (M + i) = M - i by omega] at h1
      have h2 : (((2 * M).choose (M + i + 1) * (M + i + 1) : ℕ) : ℝ) =
          (((2 * M).choose (M + i) * (M - i) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast [Nat.cast_sub (show i ≤ M by omega)] at h2
      rw [← add_assoc]
      linarith
    -- `exp(-(2i + 1)/(M - i)) (M + i + 1) ≤ M - i`
    have hexp : Real.exp (-((2 * i + 1) / (M - i))) * (M + i + 1) ≤ M - i := by
      have h1 := Real.add_one_le_exp ((2 * i + 1) / (M - i))
      have h2 : (M : ℝ) + i + 1 = ((2 * i + 1) / (M - i) + 1) * (M - i) := by
        field_simp
        ring
      have h3 : Real.exp (-((2 * i + 1) / (M - i))) * ((2 * i + 1) / (M - i) + 1) ≤ 1 := by
        calc Real.exp (-((2 * i + 1) / (M - i))) * ((2 * i + 1) / (M - i) + 1)
            ≤ Real.exp (-((2 * i + 1) / (M - i))) * Real.exp ((2 * i + 1) / (M - i)) := by
              gcongr
          _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [h2, ← mul_assoc]
      calc Real.exp (-((2 * i + 1) / (M - i))) * ((2 * i + 1) / (M - i) + 1) * (M - i)
          ≤ 1 * (M - i : ℝ) := mul_le_mul_of_nonneg_right h3 hMi.le
        _ = M - i := one_mul _
    have hmono : Real.exp (-(((i + 1 : ℕ) : ℝ) ^ 2 / (M - (i + 1 : ℕ)))) ≤
        Real.exp (-((i : ℝ) ^ 2 / (M - i))) * Real.exp (-((2 * i + 1) / (M - i))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      push_cast
      have h1 : (i : ℝ) ^ 2 / (M - i) + (2 * i + 1) / (M - i) = ((i : ℝ) + 1) ^ 2 / (M - i) := by
        field_simp
        ring
      have h2 : ((i : ℝ) + 1) ^ 2 / (M - i) ≤ ((i : ℝ) + 1) ^ 2 / (M - (i + 1)) :=
        div_le_div_of_nonneg_left (by positivity) hMi1 (by linarith)
      linarith
    have hpos : (0 : ℝ) < M + i + 1 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    calc (M.centralBinom : ℝ) * Real.exp (-(((i + 1 : ℕ) : ℝ) ^ 2 / (M - (i + 1 : ℕ)))) *
          (M + i + 1)
        ≤ M.centralBinom * (Real.exp (-((i : ℝ) ^ 2 / (M - i))) *
            Real.exp (-((2 * i + 1) / (M - i)))) * (M + i + 1) := by gcongr
      _ = (M.centralBinom * Real.exp (-((i : ℝ) ^ 2 / (M - i)))) *
            (Real.exp (-((2 * i + 1) / (M - i))) * (M + i + 1)) := by ring
      _ ≤ ((2 * M).choose (M + i) : ℝ) * (M - i) :=
          mul_le_mul h hexp (by positivity) (by positivity)
      _ = ((2 * M).choose (M + (i + 1)) : ℝ) * (M + i + 1) := hstep.symm

/-- **The fair binomial tail from below**: among `2M` fair coins at least `M + y` are black with
probability at least `exp(-z²/(M - z))/2`, where `z = y + √M + 1 < M`. Exactly `M + i` are black
with probability `(2M choose M + i)/4^M ≥ exp(-i²/(M - i))/(2√M)`, and more than `√M` integers
`i` lie between `y` and `z`. -/
theorem le_measureReal_sum_ge {M : ℕ} (hM : 0 < M) {y : ℝ} (hy : 0 ≤ y)
    (hz : y + √(M : ℝ) + 1 < M) :
    Real.exp (-((y + √(M : ℝ) + 1) ^ 2 / (M - (y + √(M : ℝ) + 1)))) / 2 ≤
      (coins (Fin (2 * M))).real {u | y ≤ ∑ j, (black (u j) - 1 / 2)} := by
  classical
  set z := y + √(M : ℝ) + 1 with hzdef
  set r := ⌊√(M : ℝ)⌋₊ with hr
  set i₀ := ⌈y⌉₊ with hi₀
  have hsq0 : 0 ≤ √(M : ℝ) := Real.sqrt_nonneg _
  have hr1 : √(M : ℝ) < r + 1 := Nat.lt_floor_add_one _
  have hrle : (r : ℝ) ≤ √(M : ℝ) := Nat.floor_le hsq0
  have hi₀le : (i₀ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  have hyi₀ : y ≤ i₀ := Nat.le_ceil y
  -- the number of black letters
  set ones : (Fin (2 * M) → Bool) → ℕ := fun u =>
    (Finset.univ.filter fun j => u j = true).card with hones
  have hsum : ∀ u : Fin (2 * M) → Bool, ∑ j, (black (u j) - 1 / 2) = (ones u : ℝ) - M := by
    intro u
    rw [Finset.sum_sub_distrib]
    simp only [black, Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hones]
    push_cast
    ring
  -- the words with `M + i₀ + l` black letters, `l ≤ r`
  set A : ℕ → Finset (Fin (2 * M) → Bool) := fun l =>
    Finset.univ.filter fun u => ones u = M + (i₀ + l) with hA
  set T := (Finset.range (r + 1)).biUnion A with hT
  have hTsub : (T : Set (Fin (2 * M) → Bool)) ⊆ {u | y ≤ ∑ j, (black (u j) - 1 / 2)} := by
    intro u hu
    simp only [hT, hA, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio,
      Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
    obtain ⟨l, -, hl⟩ := hu
    rw [Set.mem_ofPred_eq, hsum, hl]
    push_cast
    linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hTcard : T.card = ∑ l ∈ Finset.range (r + 1), (2 * M).choose (M + (i₀ + l)) := by
    rw [hT, Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun l _ => LongestRuns.card_filter_card_eq (2 * M) (M + (i₀ + l))
    · intro l _ l' _ hll'
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu hu'
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
      omega
  have hTmeas : (coins (Fin (2 * M))).real T = T.card * (2⁻¹ : ℝ) ^ (2 * M) :=
    LongestRuns.measureReal_finset _ T
  -- each of these coefficients is at least `(2M choose M) exp(-z²/(M - z))`
  have hzM : 0 < (M : ℝ) - z := by linarith
  have hterm : ∀ l ∈ Finset.range (r + 1),
      (M.centralBinom : ℝ) * Real.exp (-(z ^ 2 / (M - z))) ≤
        ((2 * M).choose (M + (i₀ + l)) : ℝ) := by
    intro l hl
    have hl' : (l : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hiz : ((i₀ + l : ℕ) : ℝ) ≤ z := by push_cast; linarith
    have hiM : i₀ + l < M := by
      have : ((i₀ + l : ℕ) : ℝ) < M := by linarith
      exact_mod_cast this
    refine le_trans ?_ (centralBinom_mul_exp_le_choose hiM)
    have hdiv : ((i₀ + l : ℕ) : ℝ) ^ 2 / (M - ((i₀ + l : ℕ) : ℝ)) ≤ z ^ 2 / (M - z) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) hiz 2) hzM
        (by linarith)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hdiv)) (Nat.cast_nonneg _)
  have hT2 : (r + 1 : ℝ) * M.centralBinom * Real.exp (-(z ^ 2 / (M - z))) ≤ T.card := by
    rw [hTcard]
    push_cast
    calc (r + 1 : ℝ) * M.centralBinom * Real.exp (-(z ^ 2 / (M - z)))
        = ∑ l ∈ Finset.range (r + 1), (M.centralBinom : ℝ) * Real.exp (-(z ^ 2 / (M - z))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ l ∈ Finset.range (r + 1), ((2 * M).choose (M + (i₀ + l)) : ℝ) :=
          Finset.sum_le_sum hterm
  have hcb := four_pow_le_two_mul_sqrt_mul_centralBinom hM
  have h4 : (2⁻¹ : ℝ) ^ (2 * M) = ((4 : ℝ) ^ M)⁻¹ := by
    rw [pow_mul, inv_pow, inv_pow]
    norm_num
  have hhalf : (1 : ℝ) / 2 ≤ √(M : ℝ) * M.centralBinom * (2⁻¹ : ℝ) ^ (2 * M) := by
    rw [h4, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have hE0 : 0 ≤ (M.centralBinom : ℝ) * (2⁻¹ : ℝ) ^ (2 * M) * Real.exp (-(z ^ 2 / (M - z))) :=
    by positivity
  calc Real.exp (-(z ^ 2 / (M - z))) / 2
      = 1 / 2 * Real.exp (-(z ^ 2 / (M - z))) := by ring
    _ ≤ √(M : ℝ) * M.centralBinom * (2⁻¹ : ℝ) ^ (2 * M) * Real.exp (-(z ^ 2 / (M - z))) :=
        mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le
    _ = √(M : ℝ) * ((M.centralBinom : ℝ) * (2⁻¹ : ℝ) ^ (2 * M) *
          Real.exp (-(z ^ 2 / (M - z)))) := by ring
    _ ≤ (r + 1 : ℝ) * ((M.centralBinom : ℝ) * (2⁻¹ : ℝ) ^ (2 * M) *
          Real.exp (-(z ^ 2 / (M - z)))) := mul_le_mul_of_nonneg_right hr1.le hE0
    _ = (r + 1 : ℝ) * M.centralBinom * Real.exp (-(z ^ 2 / (M - z))) * (2⁻¹ : ℝ) ^ (2 * M) := by
        ring
    _ ≤ T.card * (2⁻¹ : ℝ) ^ (2 * M) := mul_le_mul_of_nonneg_right hT2 (by positivity)
    _ = (coins (Fin (2 * M))).real T := hTmeas.symm
    _ ≤ (coins (Fin (2 * M))).real {u | y ≤ ∑ j, (black (u j) - 1 / 2)} :=
        measureReal_mono hTsub

/-! ### Independent windows -/

/-- **The second Borel–Cantelli lemma along disjoint windows**: if the windows
`n k, …, n k + m k - 1` are pairwise disjoint and the probabilities of the events `S k` have an
infinite sum, then almost every fair-coin sequence shows the event `S k` in its `k`-th window for
infinitely many `k`. -/
theorem ae_frequently_window_mem {m n : ℕ → ℕ}
    (hinj : Function.Injective fun p : (k : ℕ) × Fin (m k) => n p.1 + p.2)
    (S : ∀ k, Set (Fin (m k) → Bool)) (hS : ∑' k, coins (Fin (m k)) (S k) = ⊤) :
    ∀ᵐ v ∂(coins ℕ), ∃ᶠ k in atTop, (fun j : Fin (m k) => v (n k + j)) ∈ S k := by
  have hΦ : Measurable fun (v : ℕ → Bool) k (j : Fin (m k)) => v (n k + j) := by fun_prop
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (Set.toFinite _).measurableSet
  let G : ℕ → Set ((k : ℕ) → Fin (m k) → Bool) := fun k => {w | w k ∈ S k}
  have hGm : ∀ k, MeasurableSet (G k) := fun k => measurable_pi_apply k (hSm k)
  have hGμ : ∀ k, (Measure.infinitePi fun k => coins (Fin (m k))) (G k) =
      coins (Fin (m k)) (S k) := fun k => by
    rw [show G k = (fun w => w k) ⁻¹' S k from rfl,
      ← Measure.map_apply (measurable_pi_apply k) (hSm k), Measure.infinitePi_map_eval]
  have hind : iIndepSet G (Measure.infinitePi fun k => coins (Fin (m k))) := by
    rw [iIndepSet_iff_meas_biInter hGm]
    intro s
    have : (⋂ k ∈ s, G k) = Set.pi (s : Set ℕ) S := by
      ext w
      simp [G]
    rw [this, Measure.infinitePi_pi _ fun k _ => hSm k]
    exact Finset.prod_congr rfl fun k _ => (hGμ k).symm
  have h1 : (Measure.infinitePi fun k => coins (Fin (m k))) (limsup G atTop) = 1 :=
    measure_limsup_eq_one hGm hind (by simpa only [hGμ] using hS)
  have hae : ∀ᵐ w ∂(Measure.infinitePi fun k => coins (Fin (m k))), w ∈ limsup G atTop :=
    ae_iff.2 ((prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hGm)).2 h1)
  rw [← map_windows hinj] at hae
  filter_upwards [ae_of_ae_map hΦ.aemeasurable hae] with v hv
  rwa [mem_limsup_iff_frequently_mem] at hv

/-! ### The lower half -/

/-- For `0 ≤ c < 1` there is an integer ratio `b ≥ 2` with `(c + 2/√b)² b/(b - 1) < 1`, since the
left side tends to `c²` as `b → ∞`. -/
theorem exists_ratio {c : ℝ} (hc : c < 1) (hc0 : 0 ≤ c) :
    ∃ b : ℕ, 2 ≤ b ∧ (c + 2 / √(b : ℝ)) ^ 2 * ((b : ℝ) / (b - 1)) < 1 := by
  have h1 : Tendsto (fun b : ℕ => 2 / √(b : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun b : ℕ => (b : ℝ) / (b - 1)) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  have hlim : Tendsto (fun b : ℕ => (c + 2 / √(b : ℝ)) ^ 2 * ((b : ℝ) / (b - 1))) atTop
      (𝓝 (c ^ 2)) := by
    simpa using ((tendsto_const_nhds.add h1).pow 2).mul h2
  have hc2 : c ^ 2 < 1 := by nlinarith
  obtain ⟨b, hbq, hb2⟩ :=
    ((hlim.eventually (gt_mem_nhds hc2)).and (eventually_ge_atTop 2)).exists
  exact ⟨b, hb2, hbq⟩

/-- **A gain in one window**: among `2M` fair coins, at least `M + √M √(q₁ L) - √M - 1` are black
with probability at least `exp(-q₂ L)/2`, if `q₁ < q₂`, `√M + 1 ≤ √M √(q₁ L)` and
`√M √(q₁ L) ≤ (1 - q₁/q₂) M` (`le_measureReal_sum_ge`). -/
theorem exp_le_measureReal_window {M : ℕ} (hM : 0 < M) {q₁ q₂ L : ℝ} (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hL : 0 ≤ L) (hy : √(M : ℝ) + 1 ≤ √(M : ℝ) * √(q₁ * L))
    (hz : √(M : ℝ) * √(q₁ * L) ≤ (1 - q₁ / q₂) * M) :
    Real.exp (-(q₂ * L)) / 2 ≤ (coins (Fin (2 * M))).real
      {u | √(M : ℝ) * √(q₁ * L) - √(M : ℝ) - 1 ≤ ∑ j, (black (u j) - 1 / 2)} := by
  set z := √(M : ℝ) * √(q₁ * L) with hzdef
  have hq₂0 : 0 < q₂ := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hzM : z < M := by
    have h0 : 0 < q₁ / q₂ * M := by positivity
    have : (1 - q₁ / q₂) * M = M - q₁ / q₂ * M := by ring
    linarith
  have h := le_measureReal_sum_ge hM (by linarith : 0 ≤ z - √(M : ℝ) - 1)
    (by linarith : z - √(M : ℝ) - 1 + √(M : ℝ) + 1 < M)
  rw [show z - √(M : ℝ) - 1 + √(M : ℝ) + 1 = z by ring] at h
  refine le_trans ?_ h
  have hz2 : z ^ 2 = M * (q₁ * L) := by
    rw [hzdef, mul_pow, Real.sq_sqrt hMpos.le, Real.sq_sqrt (by positivity)]
  have hexpo : z ^ 2 / (M - z) ≤ q₂ * L := by
    have hpos : 0 < (M : ℝ) - z := by linarith
    rw [div_le_iff₀ hpos, hz2]
    have h1 : q₂ * ((1 - q₁ / q₂) * M) = (q₂ - q₁) * M := by field_simp
    have h2 : q₁ * M ≤ q₂ * (M - z) := by
      have := mul_le_mul_of_nonneg_left hz hq₂0.le
      rw [h1] at this
      linarith
    calc (M : ℝ) * (q₁ * L) = L * (q₁ * M) := by ring
      _ ≤ L * (q₂ * (M - z)) := mul_le_mul_of_nonneg_left h2 hL
      _ = q₂ * L * (M - z) := by ring
  gcongr

/-- `log log (2bᵃ⁺¹) ≤ log (a + 1) + log log (2b)` for `b ≥ 2`, since
`log (2bᵃ⁺¹) ≤ (a + 1) log (2b)`. -/
theorem log_log_le {b : ℝ} (hb : 2 ≤ b) (a : ℕ) :
    Real.log (Real.log (b * (2 * b ^ a))) ≤
      Real.log ((a : ℝ) + 1) + Real.log (Real.log (2 * b)) := by
  have hb0 : 0 < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogN : Real.log (b * (2 * b ^ a)) = Real.log 2 + ((a : ℝ) + 1) * Real.log b := by
    rw [Real.log_mul hb0.ne' (by positivity), Real.log_mul two_ne_zero (by positivity),
      Real.log_pow]
    ring
  have hpos : 0 < Real.log (b * (2 * b ^ a)) := by
    rw [hlogN]
    positivity
  have hle : Real.log (b * (2 * b ^ a)) ≤ ((a : ℝ) + 1) * Real.log (2 * b) := by
    rw [hlogN, Real.log_mul two_ne_zero hb0.ne']
    have e : ((a : ℝ) + 1) * (Real.log 2 + Real.log b) =
        Real.log 2 + ((a : ℝ) + 1) * Real.log b + (a : ℝ) * Real.log 2 := by ring
    have : 0 ≤ (a : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg a) hlog2.le
    linarith
  have h2b : 0 < Real.log (2 * b) := lt_trans one_pos (one_lt_log_of_four_le (by linarith))
  calc Real.log (Real.log (b * (2 * b ^ a)))
      ≤ Real.log (((a : ℝ) + 1) * Real.log (2 * b)) := Real.log_le_log hpos hle
    _ = Real.log ((a : ℝ) + 1) + Real.log (Real.log (2 * b)) :=
        Real.log_mul (by positivity) h2b.ne'

/-- **The threshold beats the target**: `√M √(q L') + √M + 1 ≤ √M √(q₁ L)` when `M ≥ 1`,
`L' ≤ L + C` and `(√q₁ - √q) √L ≥ 2 + √(q C)`. -/
theorem sqrt_mul_le_threshold {M q q₁ L L' C : ℝ} (hM : 1 ≤ M) (hq : 0 ≤ q) (hq₁ : 0 ≤ q₁)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hL' : L' ≤ L + C)
    (hgap : 2 + √(q * C) ≤ (√q₁ - √q) * √L) :
    √M * √(q * L') + √M + 1 ≤ √M * √(q₁ * L) := by
  have h2 : √(q * L') ≤ √q * √L + √(q * C) := by
    calc √(q * L') ≤ √(q * L + q * C) := Real.sqrt_le_sqrt (by
          have := mul_le_mul_of_nonneg_left hL' hq
          linarith)
      _ ≤ √(q * L) + √(q * C) := sqrt_add_le (by positivity) (by positivity)
      _ = √q * √L + √(q * C) := by rw [Real.sqrt_mul hq]
  have hX : 1 ≤ √(q₁ * L) - 1 - √(q * L') := by
    have h3 : (√q₁ - √q) * √L = √q₁ * √L - √q * √L := sub_mul _ _ _
    rw [Real.sqrt_mul hq₁]
    linarith
  have hsM : 1 ≤ √M := Real.one_le_sqrt.2 hM
  have h3 := mul_le_mul_of_nonneg_left hX (Real.sqrt_nonneg M)
  have h4 : √M * (√(q₁ * L) - 1 - √(q * L')) = √M * √(q₁ * L) - √M - √M * √(q * L') := by ring
  linarith

/-- `(c/2 + 1/√b) √(2 · 2bᵃ⁺¹ L) = √(bᵃ (b - 1)) √(q L)` for `q = (c + 2/√b)² b/(b - 1)`. -/
theorem gain_eq {b c L : ℝ} (hb : 1 < b) (hc : 0 ≤ c) (a : ℕ) :
    (c / 2 + 1 / √b) * √(2 * (b * (2 * b ^ a)) * L) =
      √(b ^ a * (b - 1)) * √((c + 2 / √b) ^ 2 * (b / (b - 1)) * L) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hsb : 0 < √b := Real.sqrt_pos.2 hb0
  have hcb : 0 ≤ c / 2 + 1 / √b := by positivity
  rw [← Real.sqrt_sq hcb, ← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- `2bᵃ⁺¹ = 2bᵃ + 2 bᵃ (b - 1)`. -/
theorem two_mul_pow_succ_eq {b : ℕ} (hb : 1 ≤ b) (a : ℕ) :
    2 * b ^ (a + 1) = 2 * b ^ a + 2 * (b ^ a * (b - 1)) := by
  rw [pow_succ, Nat.mul_sub_one]
  have : b ^ a ≤ b ^ a * b := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The windows `[2bᵏ⁺ᴷ, 2bᵏ⁺ᴷ⁺¹)`, `k = 0, 1, …`, are pairwise disjoint. -/
theorem injective_windows {b : ℕ} (hb : 1 ≤ b) (K : ℕ) :
    Function.Injective fun p : (k : ℕ) × Fin (2 * (b ^ (k + K) * (b - 1))) =>
      2 * b ^ (p.1 + K) + p.2 := by
  have hmono : ∀ {a a' : ℕ}, a ≤ a' → 2 * b ^ a ≤ 2 * b ^ a' := fun h =>
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hb h)
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  simp only at h
  have hj := j.2
  have hj' := j'.2
  have hk : k = k' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono (show k + K + 1 ≤ k' + K by omega)
      rw [two_mul_pow_succ_eq hb] at h1
      omega
    · have h1 := hmono (show k' + K + 1 ≤ k + K by omega)
      rw [two_mul_pow_succ_eq hb] at h1
      omega
  subst hk
  rw [Fin.ext (by omega : (j : ℕ) = j')]

/-- **The step after a gain**: if the walk is above `-√(2n L)` at time `n`, and its gain `d` up to
time `bn` is at least `(c/2 + 1/√b) √(2bn L')` with `L ≤ L'`, then at time `bn` twice the
imbalance exceeds `c √(2bn L')`. -/
theorem lt_two_mul_add_of_gain {b c n L L' x d : ℝ} (hb : 0 < b) (hn : 0 ≤ n) (hL : L ≤ L')
    (hx : -√(2 * n * L) < x) (hd : (c / 2 + 1 / √b) * √(2 * (b * n) * L') ≤ d) :
    c * √(2 * (b * n) * L') < 2 * (x + d) := by
  have hsb : 0 < √b := Real.sqrt_pos.2 hb
  have hprev : √(2 * n * L) ≤ √(2 * (b * n) * L') / √b := by
    rw [← Real.sqrt_div' _ hb.le]
    apply Real.sqrt_le_sqrt
    rw [show 2 * (b * n) * L' / b = 2 * n * L' by field_simp]
    have := mul_le_mul_of_nonneg_left hL hn
    linarith
  have e : (c / 2 + 1 / √b) * √(2 * (b * n) * L') =
      c / 2 * √(2 * (b * n) * L') + √(2 * (b * n) * L') / √b := by ring
  linarith

/-- **The windows from some point on**: for `c ≥ 0` and an integer ratio `b ≥ 2` with
`q = (c + 2/√b)² b/(b - 1) < 1` there are `q₂ < 1`, thresholds `thr a` and `K` such that for
`a ≥ K`, among the `2bᵃ(b - 1)` coins of window `a` the black ones exceed half by `thr a` with
probability at least `(a + 1)^(-q₂)/2`, and `thr a ≥ (c/2 + 1/√b) √(2n log log n)`, `n = 2bᵃ⁺¹`.
The thresholds are `√M √(q₁ log (a + 1)) - √M - 1`, `M = bᵃ(b - 1)`, `q < q₁ < q₂ < 1`. -/
theorem exists_thresholds {b : ℕ} {c : ℝ} (hb2 : 2 ≤ b) (hc : 0 ≤ c)
    (hbq : (c + 2 / √(b : ℝ)) ^ 2 * ((b : ℝ) / (b - 1)) < 1) :
    ∃ q₂ : ℝ, q₂ < 1 ∧ ∃ thr : ℕ → ℝ, ∃ K : ℕ, ∀ a ≥ K,
      (((a : ℝ) + 1) ^ q₂)⁻¹ / 2 ≤ (coins (Fin (2 * (b ^ a * (b - 1))))).real
        {u | thr a ≤ ∑ j, (black (u j) - 1 / 2)} ∧
      (c / 2 + 1 / √(b : ℝ)) * √(2 * ((b : ℝ) * (2 * (b : ℝ) ^ a)) *
        Real.log (Real.log ((b : ℝ) * (2 * (b : ℝ) ^ a)))) ≤ thr a := by
  have hb : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (0 : ℝ) < b - 1 := by linarith
  set q : ℝ := (c + 2 / √(b : ℝ)) ^ 2 * ((b : ℝ) / (b - 1)) with hq
  have hq0 : 0 ≤ q := by positivity
  set q₁ : ℝ := (2 * q + 1) / 3 with hq₁
  set q₂ : ℝ := (q + 2) / 3 with hq₂
  have hqq₁ : q < q₁ := by rw [hq₁]; linarith
  have hq₁q₂ : q₁ < q₂ := by rw [hq₁, hq₂]; linarith
  have hq₂1 : q₂ < 1 := by rw [hq₂]; linarith
  have hq₁0 : 0 < q₁ := by rw [hq₁]; linarith
  set δ : ℝ := 1 - q₁ / q₂ with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, sub_pos, div_lt_one (by linarith)]
    exact hq₁q₂
  set C₁ : ℝ := Real.log (Real.log (2 * b)) with hC₁
  have hC₁0 : 0 ≤ C₁ := Real.log_nonneg (one_lt_log_of_four_le (by linarith)).le
  have hsq : 0 < √q₁ - √q := sub_pos.2 (Real.sqrt_lt_sqrt hq0 hqq₁)
  set T : ℝ := ((2 + √(q * C₁)) / (√q₁ - √q)) ^ 2 with hT
  have hev : ∀ᶠ a : ℕ in atTop, T ≤ Real.log ((a : ℝ) + 1) ∧ (a : ℝ) ^ 1 / 2 ^ a ≤ δ ^ 2 := by
    have h1 : Tendsto (fun a : ℕ => Real.log ((a : ℝ) + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    filter_upwards [h1.eventually_ge_atTop T,
      h2.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2))] with a ha1 ha2
    exact ⟨ha1, ha2⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  -- the window lengths `2 M a`, `M a = bᵃ (b - 1)`, and the thresholds
  have hMR : ∀ a, ((b ^ a * (b - 1) : ℕ) : ℝ) = (b : ℝ) ^ a * (b - 1) := fun a => by
    push_cast [Nat.cast_sub (show 1 ≤ b by omega)]
    ring
  have hM1 : ∀ a, (1 : ℝ) ≤ ((b ^ a * (b - 1) : ℕ) : ℝ) := fun a => by
    rw [hMR]
    have : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ (by linarith)
    nlinarith
  obtain ⟨thr, hthr⟩ : ∃ thr : ℕ → ℝ, ∀ a, thr a = √((b ^ a * (b - 1) : ℕ) : ℝ) *
      √(q₁ * Real.log ((a : ℝ) + 1)) - √((b ^ a * (b - 1) : ℕ) : ℝ) - 1 := ⟨_, fun _ => rfl⟩
  -- from `K` on the threshold exceeds `√M √(q log log (2bᵃ⁺¹))`
  have hbeat : ∀ a ≥ K, √((b ^ a * (b - 1) : ℕ) : ℝ) *
      √(q * Real.log (Real.log ((b : ℝ) * (2 * (b : ℝ) ^ a)))) +
        √((b ^ a * (b - 1) : ℕ) : ℝ) + 1 ≤
      √((b ^ a * (b - 1) : ℕ) : ℝ) * √(q₁ * Real.log ((a : ℝ) + 1)) := by
    intro a ha
    obtain ⟨hTa, -⟩ := hK a ha
    have hLa0 : 0 ≤ Real.log ((a : ℝ) + 1) := le_trans (by positivity) hTa
    have hgap : 2 + √(q * C₁) ≤ (√q₁ - √q) * √(Real.log ((a : ℝ) + 1)) := by
      have h1 : √T ≤ √(Real.log ((a : ℝ) + 1)) := Real.sqrt_le_sqrt hTa
      rw [hT, Real.sqrt_sq (by positivity), div_le_iff₀ hsq] at h1
      linarith
    exact sqrt_mul_le_threshold (hM1 a) hq0 hq₁0.le hLa0 hC₁0 (log_log_le hb a) hgap
  -- the probability of a gain in window `a`
  have hP : ∀ a ≥ K, (((a : ℝ) + 1) ^ q₂)⁻¹ / 2 ≤ (coins (Fin (2 * (b ^ a * (b - 1))))).real
      {u | thr a ≤ ∑ j, (black (u j) - 1 / 2)} := by
    intro a ha
    obtain ⟨hTa, hda⟩ := hK a ha
    have hLa0 : 0 ≤ Real.log ((a : ℝ) + 1) := le_trans (by positivity) hTa
    have hMpos : 0 < b ^ a * (b - 1) := by
      have := hM1 a
      exact_mod_cast (show (0 : ℝ) < ((b ^ a * (b - 1) : ℕ) : ℝ) by linarith)
    have hy : √((b ^ a * (b - 1) : ℕ) : ℝ) + 1 ≤
        √((b ^ a * (b - 1) : ℕ) : ℝ) * √(q₁ * Real.log ((a : ℝ) + 1)) := by
      have := hbeat a ha
      have : 0 ≤ √((b ^ a * (b - 1) : ℕ) : ℝ) *
          √(q * Real.log (Real.log ((b : ℝ) * (2 * (b : ℝ) ^ a)))) := by positivity
      linarith
    -- `q₁ log (a + 1) ≤ δ² M a`
    have hla : Real.log ((a : ℝ) + 1) ≤ a := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < a + 1)
      linarith
    have hda' : (a : ℝ) ≤ δ ^ 2 * 2 ^ a := by
      rw [pow_one, div_le_iff₀ (by positivity)] at hda
      linarith
    have hM2 : (2 : ℝ) ^ a ≤ ((b ^ a * (b - 1) : ℕ) : ℝ) := by
      rw [hMR]
      have h1 : (2 : ℝ) ^ a ≤ (b : ℝ) ^ a := pow_le_pow_left₀ (by norm_num) hb a
      have h2 : (1 : ℝ) ≤ b - 1 := by linarith
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) a]
    have hqL : q₁ * Real.log ((a : ℝ) + 1) ≤ δ ^ 2 * ((b ^ a * (b - 1) : ℕ) : ℝ) := by
      have h1 : q₁ * Real.log ((a : ℝ) + 1) ≤ Real.log ((a : ℝ) + 1) :=
        mul_le_of_le_one_left hLa0 (by linarith)
      have h2 := mul_le_mul_of_nonneg_left hM2 (sq_nonneg δ)
      linarith
    have hz : √((b ^ a * (b - 1) : ℕ) : ℝ) * √(q₁ * Real.log ((a : ℝ) + 1)) ≤
        (1 - q₁ / q₂) * ((b ^ a * (b - 1) : ℕ) : ℝ) := by
      calc √((b ^ a * (b - 1) : ℕ) : ℝ) * √(q₁ * Real.log ((a : ℝ) + 1))
          ≤ √((b ^ a * (b - 1) : ℕ) : ℝ) * √(δ ^ 2 * ((b ^ a * (b - 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqL) (Real.sqrt_nonneg _)
        _ = δ * (√((b ^ a * (b - 1) : ℕ) : ℝ) * √((b ^ a * (b - 1) : ℕ) : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ0.le]
            ring
        _ = (1 - q₁ / q₂) * ((b ^ a * (b - 1) : ℕ) : ℝ) := by
            rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    have h := exp_le_measureReal_window hMpos hq₁0 hq₁q₂ hLa0 hy hz
    have hrpow : (((a : ℝ) + 1) ^ q₂)⁻¹ = Real.exp (-(q₂ * Real.log ((a : ℝ) + 1))) := by
      rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_neg, mul_comm]
    rw [hrpow]
    simpa only [← hthr] using h
  refine ⟨q₂, hq₂1, thr, K, fun a ha => ⟨hP a ha, ?_⟩⟩
  rw [gain_eq (by linarith) hc a, ← hq, ← hMR a, hthr]
  linarith [hbeat a ha]

/-- **One window, then the walk**: if the walk is above `-√(2n log log n)` at `n = 2bᵃ` and the
coins of the window `[2bᵃ, 2bᵃ⁺¹)` exceed half by at least `(c/2 + 1/√b) √(2n' log log n')`,
`n' = 2bᵃ⁺¹`, then at `n'` twice the imbalance exceeds `c √(2n' log log n')`. -/
theorem lt_two_mul_imbalance_of_window {v : ℕ → Bool} {b a : ℕ} {c t : ℝ} (hb : 2 ≤ b)
    (hgain : (c / 2 + 1 / √(b : ℝ)) * √(2 * ((b : ℝ) * (2 * (b : ℝ) ^ a)) *
        Real.log (Real.log ((b : ℝ) * (2 * (b : ℝ) ^ a)))) ≤ t)
    (hwin : t ≤ ∑ j : Fin (2 * (b ^ a * (b - 1))), (black (v (2 * b ^ a + j)) - 1 / 2))
    (hprev : -√(2 * ((2 * b ^ a : ℕ) : ℝ) * Real.log (Real.log ((2 * b ^ a : ℕ) : ℝ))) <
      imbalance v (2 * b ^ a)) :
    c * √(2 * ((2 * b ^ (a + 1) : ℕ) : ℝ) * Real.log (Real.log ((2 * b ^ (a + 1) : ℕ) : ℝ))) <
      2 * imbalance v (2 * b ^ (a + 1)) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hsum : ∑ j : Fin (2 * (b ^ a * (b - 1))), (black (v (2 * b ^ a + j)) - 1 / 2) =
      tailImbalance v (2 * b ^ a) (2 * b ^ (a + 1)) := by
    rw [tailImbalance, two_mul_pow_succ_eq (by omega), Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel_left]
    exact Fin.sum_univ_eq_sum_range (fun j => black (v (2 * b ^ a + j)) - 1 / 2) _
  have hle : 2 * b ^ a ≤ 2 * b ^ (a + 1) :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
  rw [imbalance_eq_add v hle]
  have hcast : ((2 * b ^ (a + 1) : ℕ) : ℝ) = (b : ℝ) * ((2 * b ^ a : ℕ) : ℝ) := by
    push_cast
    ring
  have hcast' : ((2 * b ^ a : ℕ) : ℝ) = 2 * (b : ℝ) ^ a := by push_cast; ring
  rw [hcast]
  have hn2 : (2 : ℝ) ≤ ((2 * b ^ a : ℕ) : ℝ) := by
    rw [hcast']
    have : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ (by linarith)
    linarith
  have hbn : ((2 * b ^ a : ℕ) : ℝ) ≤ (b : ℝ) * ((2 * b ^ a : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ b)
      (by linarith : (0 : ℝ) ≤ ((2 * b ^ a : ℕ) : ℝ))
    linarith
  have hLmono : Real.log (Real.log ((2 * b ^ a : ℕ) : ℝ)) ≤
      Real.log (Real.log ((b : ℝ) * ((2 * b ^ a : ℕ) : ℝ))) :=
    Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) hbn)
  refine lt_two_mul_add_of_gain (by linarith) (by linarith) hLmono hprev ?_
  rw [hcast', ← hsum]
  exact hgain.trans hwin

/-- **The lower half of the law of the iterated logarithm**: for every `c < 1` and almost every
fair-coin sequence, `2 (N(n) - n/2)` exceeds `c √(2 n log log n)` for infinitely many `n`.
Take an integer ratio `b` with `(c + 2/√b)² b/(b - 1) < 1` (`exists_ratio`), and the windows
`[2bᵏ, 2bᵏ⁺¹)`. In window `k` the walk gains at least `(c + 2/√b) √(2n log log n)`, `n = 2bᵏ⁺¹`,
with probability at least `(k + 1)^(-q₂)/2` for some `q₂ < 1` (`exists_thresholds`); these sum
to `∞`, so this happens in infinitely many windows (`ae_frequently_window_mem`). Before the window
the walk is above `-2√(2n log log n / b)` (`Fluctuations.ae_eventually_abs_imbalance_lt`,
`lt_two_mul_imbalance_of_window`). -/
theorem ae_frequently_lt_two_mul_imbalance {c : ℝ} (hc : c < 1) :
    ∀ᵐ v ∂(coins ℕ), ∃ᶠ n : ℕ in atTop,
      c * √(2 * n * Real.log (Real.log n)) < 2 * imbalance v n := by
  wlog hc0 : 1 / 2 ≤ c generalizing c with H
  · filter_upwards [H (c := 1 / 2) (by norm_num) le_rfl] with v hv
    exact hv.mono fun n hn => lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)) hn
  obtain ⟨b, hb2, hbq⟩ := exists_ratio hc (by linarith)
  obtain ⟨q₂, hq₂1, thr, K, hK⟩ := exists_thresholds hb2 (by linarith) hbq
  -- the probabilities sum to `∞`
  have hS : ∑' k, coins (Fin (2 * (b ^ (k + K) * (b - 1))))
      {u | thr (k + K) ≤ ∑ j, (black (u j) - 1 / 2)} = ⊤ := by
    by_contra hne
    have hsumm := ENNReal.summable_toReal hne
    have h1 : Summable fun k : ℕ => ((((k + (K + 1) : ℕ) : ℝ)) ^ q₂)⁻¹ := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hsumm.mul_left 2)
      have := (hK (k + K) (by omega)).1
      rw [measureReal_def] at this
      have hcast : (((k + (K + 1) : ℕ) : ℝ)) = ((k + K : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith
    exact absurd (Real.summable_nat_rpow_inv.1 ((summable_nat_add_iff (K + 1)).1 h1))
      (by linarith)
  have hwin := ae_frequently_window_mem (m := fun k => 2 * (b ^ (k + K) * (b - 1)))
    (n := fun k => 2 * b ^ (k + K)) (injective_windows (by omega) K)
    (fun k => {u | thr (k + K) ≤ ∑ j, (black (u j) - 1 / 2)}) hS
  have htop : ∀ s : ℕ, Tendsto (fun k => 2 * b ^ (k + s)) atTop atTop := fun s =>
    tendsto_atTop_mono (fun k => by
      show k ≤ 2 * b ^ (k + s)
      have h1 : k < b ^ k := Nat.lt_pow_self (by omega)
      have h2 : b ^ k ≤ b ^ (k + s) := Nat.pow_le_pow_right (by omega) (Nat.le_add_right k s)
      omega) tendsto_id
  filter_upwards [hwin, ae_eventually_abs_imbalance_lt] with v hv1 hv2
  have hv2' : ∀ᶠ k in atTop,
      -√(2 * ((2 * b ^ (k + K) : ℕ) : ℝ) * Real.log (Real.log ((2 * b ^ (k + K) : ℕ) : ℝ))) <
        imbalance v (2 * b ^ (k + K)) :=
    ((htop K).eventually hv2).mono fun k hk => (abs_lt.1 hk).1
  refine (htop (K + 1)).frequently ((hv1.and_eventually hv2').mono fun k hk => ?_)
  rw [show k + (K + 1) = k + K + 1 by ring]
  exact lt_two_mul_imbalance_of_window hb2 (hK (k + K) (by omega)).2 hk.1 hk.2

/-! ### The law of the iterated logarithm -/

/-- **The bounds behind the law**: for almost every fair-coin sequence and every `k`, the ratio
`W(n)/√(2 n log log n)` lies between `-(1 + 1/(k + 1))` and `1 + 1/(k + 1)` from some `n` on, and
it is at least `1 - 1/(k + 1)` and at most `-(1 - 1/(k + 1))` for infinitely many `n`. These come
from `ae_eventually_two_mul_imbalance_lt` and `ae_frequently_lt_two_mul_imbalance`, applied to the
sequence and to its complement (`Fluctuations.measurePreserving_not`). -/
theorem ae_walk_div_bounds :
    ∀ᵐ v ∂(coins ℕ), ∀ k : ℕ,
      (∀ᶠ n : ℕ in atTop, (walk v n : ℝ) / √(2 * n * Real.log (Real.log n)) ≤
        1 + 1 / ((k : ℝ) + 1)) ∧
      (∀ᶠ n : ℕ in atTop, -(1 + 1 / ((k : ℝ) + 1)) ≤
        (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop, 1 - 1 / ((k : ℝ) + 1) ≤
        (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop, (walk v n : ℝ) / √(2 * n * Real.log (Real.log n)) ≤
        -(1 - 1 / ((k : ℝ) + 1))) := by
  have hk : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hup : ∀ᵐ v ∂(coins ℕ), ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      2 * imbalance v n < (1 + 1 / ((k : ℝ) + 1)) * √(2 * n * Real.log (Real.log n)) :=
    ae_all_iff.2 fun k => ae_eventually_two_mul_imbalance_lt (by linarith [hk k])
  have hlo : ∀ᵐ v ∂(coins ℕ), ∀ k : ℕ, ∃ᶠ n : ℕ in atTop,
      (1 - 1 / ((k : ℝ) + 1)) * √(2 * n * Real.log (Real.log n)) < 2 * imbalance v n :=
    ae_all_iff.2 fun k => ae_frequently_lt_two_mul_imbalance (by linarith [hk k])
  have hflip := measurePreserving_not.quasiMeasurePreserving
  filter_upwards [hup, hlo, hflip.ae hup, hflip.ae hlo] with v h1 h2 h3 h4
  simp only [imbalance_not] at h3 h4
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = √(2 * n * Real.log (Real.log n)) := ⟨_, fun _ => rfl⟩
  simp only [← hg] at h1 h2 h3 h4 ⊢
  have hgpos : ∀ᶠ n : ℕ in atTop, 0 < g n := by
    filter_upwards [eventually_ge_atTop 16] with n hn
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 1 < Real.log n := one_lt_log_of_four_le (by linarith)
    rw [hg]
    exact Real.sqrt_pos.2 (by have := Real.log_pos hl; positivity)
  have hwalk : ∀ n, (walk v n : ℝ) = 2 * imbalance v n := fun n => (two_mul_imbalance v n).symm
  intro k
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [h1 k, hgpos] with n hn hgn
    rw [hwalk, div_le_iff₀ hgn]
    exact hn.le
  · filter_upwards [h3 k, hgpos] with n hn hgn
    rw [hwalk, le_div_iff₀ hgn]
    linarith
  · exact ((h2 k).and_eventually hgpos).mono fun n hn => by
      rw [hwalk, le_div_iff₀ hn.2]
      exact hn.1.le
  · exact ((h4 k).and_eventually hgpos).mono fun n hn => by
      rw [hwalk, div_le_iff₀ hn.2]
      linarith [hn.1]

/-- **Khinchin's law of the iterated logarithm** for fair coins: for almost every fair-coin
sequence, the walk `W(n)`, black minus white among the first `n` coins, has
`limsup W(n)/√(2 n log log n) = 1` and `liminf W(n)/√(2 n log log n) = -1`
(`ae_walk_div_bounds`). -/
theorem ae_limsup_liminf_walk :
    ∀ᵐ v ∂(coins ℕ),
      limsup (fun n : ℕ => (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))) atTop = 1 ∧
      liminf (fun n : ℕ => (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))) atTop = -1 := by
  filter_upwards [ae_walk_div_bounds] with v h
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = (walk v n : ℝ) / √(2 * n * Real.log (Real.log n)) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hu] at h ⊢
  rw [show (fun n => u n) = u from rfl]
  have hbdd : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of_eventually_le (h 0).1
  have hbdd' : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of_eventually_ge (h 0).2.1
  have hcob : IsCoboundedUnder (· ≤ ·) atTop u :=
    isCoboundedUnder_le_of_eventually_le atTop (h 0).2.1
  have hcob' : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_eventually_le atTop (h 0).1
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hε
    exact (limsup_le_of_le hcob (h k).1).trans (by linarith)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hε
    have := le_limsup_of_frequently_le (h k).2.2.1 hbdd
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hε
    have := liminf_le_of_frequently_le (h k).2.2.2 hbdd'
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hε
    have := le_liminf_of_le hcob' (h k).2.1
    linarith

/-- **The law of the iterated logarithm for the center column**: for almost every configuration,
the walk of the center column (black `+1`, white `-1`) has `limsup W(n)/√(2 n log log n) = 1` and
`liminf W(n)/√(2 n log log n) = -1`. So its discrepancy `N(n) - n/2` comes within a factor
`1 + ε` of `±√(n log log n / 2)` infinitely often, and from some `n` on stays within that bound. -/
theorem ae_limsup_liminf_walk_trace :
    ∀ᵐ x ∂(coins ℤ),
      limsup (fun n : ℕ => (walk (trace x) n : ℝ) / √(2 * n * Real.log (Real.log n))) atTop = 1 ∧
      liminf (fun n : ℕ => (walk (trace x) n : ℝ) / √(2 * n * Real.log (Real.log n))) atTop =
        -1 :=
  measurePreserving_trace.quasiMeasurePreserving.ae (p := fun v =>
    limsup (fun n : ℕ => (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))) atTop = 1 ∧
    liminf (fun n : ℕ => (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))) atTop = -1)
    ae_limsup_liminf_walk

/-- **Crossings of a growing scale**: if `W` rises by at most `1` per step, `g` is eventually
positive and nondecreasing and tends to `∞`, `x ≥ 0`, and both `W n < x g n` and `x g n ≤ W n`
happen infinitely often, then `x` is a limit point of `W n / g n`. At the first time `m` after a
time below `x g` with `x g m ≤ W m`, `x ≤ W m / g m < x + 1/g m`. -/
theorem mapClusterPt_div {W g : ℕ → ℝ} {x : ℝ} (hx : 0 ≤ x) (hW : ∀ n, W (n + 1) ≤ W n + 1)
    (hg : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ g (n + 1)) (hgtop : Tendsto g atTop atTop)
    (hlo : ∃ᶠ n in atTop, W n < x * g n) (hhi : ∃ᶠ n in atTop, x * g n ≤ W n) :
    MapClusterPt x atTop fun n => W n / g n := by
  classical
  rw [mapClusterPt_iff_frequently]
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  rw [frequently_atTop]
  intro N
  obtain ⟨N', hN'⟩ := eventually_atTop.1 (hg.and (hgtop.eventually_gt_atTop (1 / ε)))
  obtain ⟨n₁, hn₁, hu₁⟩ := frequently_atTop.1 hlo (max N N')
  obtain ⟨n₂, hn₂, hu₂⟩ := frequently_atTop.1 hhi (n₁ + 1)
  have hex : ∃ m, x * g (n₁ + 1 + m) ≤ W (n₁ + 1 + m) :=
    ⟨n₂ - (n₁ + 1), by rwa [Nat.add_sub_cancel' hn₂]⟩
  have hm := Nat.find_spec hex
  have hprev : W (n₁ + Nat.find hex) < x * g (n₁ + Nat.find hex) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, add_zero]
      exact hu₁
    · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      rw [show n₁ + 1 + (Nat.find hex - 1) = n₁ + Nat.find hex by omega] at this
      exact not_le.1 this
  set m := n₁ + Nat.find hex with hmdef
  rw [show n₁ + 1 + Nat.find hex = m + 1 by omega] at hm
  obtain ⟨⟨-, hgmono⟩, -⟩ := hN' m (by omega)
  obtain ⟨⟨hG, -⟩, hgbig⟩ := hN' (m + 1) (by omega)
  refine ⟨m + 1, by omega, hball ?_⟩
  show W (m + 1) / g (m + 1) ∈ Metric.ball x ε
  have h2 : W (m + 1) < x * g (m + 1) + 1 := by
    have := mul_le_mul_of_nonneg_left hgmono hx
    linarith [hW m]
  have hxW : x ≤ W (m + 1) / g (m + 1) := (le_div_iff₀ hG).2 hm
  have hWx : W (m + 1) / g (m + 1) < x + 1 / g (m + 1) := by
    rw [div_lt_iff₀ hG, add_mul, one_div, inv_mul_cancel₀ hG.ne']
    exact h2
  have hGε : 1 / g (m + 1) < ε := (div_lt_iff₀ hG).2 ((div_lt_iff₀' hε).1 hgbig)
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The limit points of the walk**: for almost every fair-coin sequence the limit points of
`W(n)/√(2 n log log n)` form exactly the interval `[-1, 1]`. The ratio oscillates between
`-1` and `1` (`ae_walk_div_bounds`), and the walk moves by `±1` while the scale grows, so the
ratio passes close to every point in between (`mapClusterPt_div`). -/
theorem ae_clusterPt_walk :
    ∀ᵐ v ∂(coins ℕ), {y | MapClusterPt y atTop fun n : ℕ =>
      (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))} = Set.Icc (-1) 1 := by
  filter_upwards [ae_walk_div_bounds] with v h
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = √(2 * n * Real.log (Real.log n)) := ⟨_, fun _ => rfl⟩
  simp only [← hg] at h ⊢
  -- the scale is eventually positive and nondecreasing, and tends to `∞`
  have hgmono : ∀ᶠ n : ℕ in atTop, 0 < g n ∧ g n ≤ g (n + 1) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 1 < Real.log n := one_lt_log_of_four_le h4
    have hl' : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    have hll : 0 < Real.log (Real.log n) := Real.log_pos hl
    have hll' : Real.log (Real.log n) ≤ Real.log (Real.log ((n : ℝ) + 1)) :=
      Real.log_le_log (by linarith) hl'
    refine ⟨by rw [hg]; exact Real.sqrt_pos.2 (by positivity), ?_⟩
    rw [hg, hg]
    push_cast
    apply Real.sqrt_le_sqrt
    have : (n : ℝ) * Real.log (Real.log n) ≤ ((n : ℝ) + 1) * Real.log (Real.log ((n : ℝ) + 1)) :=
      mul_le_mul (by linarith) hll' hll.le (by linarith)
    linarith
  have hgtop : Tendsto g atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop two_pos
    have h2 : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    rw [show g = fun n : ℕ => √(2 * n * Real.log (Real.log n)) from funext hg]
    exact Real.tendsto_sqrt_atTop.comp (h1.atTop_mul_atTop₀ h2)
  have hgpos : ∀ᶠ n : ℕ in atTop, 0 < g n := hgmono.mono fun n hn => hn.1
  have hstep : ∀ n, (walk v (n + 1) : ℝ) = walk v n + if v n then 1 else -1 := fun n => by
    rw [walk, walk, Finset.sum_range_succ]
    push_cast
    rfl
  -- the points of `[0, 1)` are limit points
  have hpos : ∀ x : ℝ, 0 ≤ x → x < 1 → MapClusterPt x atTop fun n => (walk v n : ℝ) / g n := by
    intro x hx0 hx1
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx1)
    refine mapClusterPt_div (W := fun n => (walk v n : ℝ)) hx0 (fun n => by
      show (walk v (n + 1) : ℝ) ≤ walk v n + 1
      rw [hstep]
      split_ifs <;> linarith) hgmono hgtop ?_ ?_
    · refine ((h 1).2.2.2.and_eventually hgpos).mono fun n hn => ?_
      have h1 := (div_le_iff₀ hn.2).1 hn.1
      have e : -(1 - 1 / (((1 : ℕ) : ℝ) + 1)) = -(1 / 2 : ℝ) := by norm_num
      rw [e] at h1
      have : 0 ≤ x * g n := mul_nonneg hx0 hn.2.le
      linarith [hn.2]
    · refine ((h k).2.2.1.and_eventually hgpos).mono fun n hn => ?_
      have h1 := (le_div_iff₀ hn.2).1 hn.1
      have h2 : x * g n ≤ (1 - 1 / ((k : ℝ) + 1)) * g n :=
        mul_le_mul_of_nonneg_right (by linarith) hn.2.le
      linarith
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {y | MapClusterPt y atTop fun n => (walk v n : ℝ) / g n} := by
    intro x hx
    rcases le_or_gt 0 x with hx0 | hx0
    · exact hpos x hx0 hx.2
    · -- the reflection `W ↦ -W`
      have hx' : 0 ≤ -x := by linarith
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 1 + x by linarith [hx.1])
      have hlo' : ∃ᶠ n in atTop, -(walk v n : ℝ) < -x * g n :=
        ((h 1).2.2.1.and_eventually hgpos).mono fun n hn => by
          have h1 := (le_div_iff₀ hn.2).1 hn.1
          have e : 1 - 1 / (((1 : ℕ) : ℝ) + 1) = 1 / 2 := by norm_num
          rw [e] at h1
          have : 0 < -x * g n := mul_pos (by linarith) hn.2
          linarith [hn.2]
      have hhi' : ∃ᶠ n in atTop, -x * g n ≤ -(walk v n : ℝ) :=
        ((h k).2.2.2.and_eventually hgpos).mono fun n hn => by
          have h1 := (div_le_iff₀ hn.2).1 hn.1
          have h2 : -(1 - 1 / ((k : ℝ) + 1)) * g n ≤ x * g n :=
            mul_le_mul_of_nonneg_right (by linarith) hn.2.le
          linarith
      have hc := mapClusterPt_div (W := fun n => -(walk v n : ℝ)) hx' (fun n => by
        show -(walk v (n + 1) : ℝ) ≤ -(walk v n : ℝ) + 1
        rw [hstep]
        split_ifs <;> linarith) hgmono hgtop hlo' hhi'
      have := hc.continuousAt_comp continuous_neg.continuousAt
      simpa [Function.comp_def, neg_div] using this
  have hclosed : IsClosed {y | MapClusterPt y atTop fun n => (walk v n : ℝ) / g n} :=
    isClosed_setOfPred_clusterPt
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    rw [Set.mem_Icc]
    by_contra hy'
    rcases not_and_or.1 hy' with hy1 | hy1
    · replace hy1 := not_le.1 hy1
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (-1 - y) / 2 by linarith)
      have hfr := hy.frequently (Iio_mem_nhds (show y < -(1 + 1 / ((k : ℝ) + 1)) by linarith))
      obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually (h k).2.1).exists
      have hn1' : (walk v n : ℝ) / g n < -(1 + 1 / ((k : ℝ) + 1)) := hn1
      linarith
    · replace hy1 := not_le.1 hy1
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (y - 1) / 2 by linarith)
      have hfr := hy.frequently (Ioi_mem_nhds (show 1 + 1 / ((k : ℝ) + 1) < y by linarith))
      obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually (h k).1).exists
      have hn1' : 1 + 1 / ((k : ℝ) + 1) < (walk v n : ℝ) / g n := hn1
      linarith
  · rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.2 hsub

/-- **The limit points for the center column**: for almost every configuration the limit points
of `W(n)/√(2 n log log n)`, for the walk of the center column, form exactly the interval
`[-1, 1]`. -/
theorem ae_clusterPt_walk_trace :
    ∀ᵐ x ∂(coins ℤ), {y | MapClusterPt y atTop fun n : ℕ =>
      (walk (trace x) n : ℝ) / √(2 * n * Real.log (Real.log n))} = Set.Icc (-1) 1 :=
  measurePreserving_trace.quasiMeasurePreserving.ae (p := fun v => {y | MapClusterPt y atTop
    fun n : ℕ => (walk v n : ℝ) / √(2 * n * Real.log (Real.log n))} = Set.Icc (-1) 1)
    ae_clusterPt_walk

/-! ### In the sense of category -/

theorem count_le_self (v : ℕ → Bool) (n : ℕ) : count v n ≤ n := by
  unfold count
  exact (List.length_filter_le _ _).trans (List.length_range).le

theorem count_le_of_false {v : ℕ → Bool} {L : ℕ} (h : ∀ t, L ≤ t → v t = false) :
    ∀ n, count v n ≤ L
  | 0 => by simp [count]
  | n + 1 => by
    rw [count_succ]
    by_cases hn : L ≤ n
    · rw [h n hn]
      simpa using count_le_of_false h n
    · have := count_le_self v n
      split_ifs <;> omega

/-- The walk counts ones minus zeros: `W(n) = 2 N(n) - n`. -/
theorem walk_eq_count (v : ℕ → Bool) : ∀ n, walk v n = 2 * (count v n : ℤ) - n
  | 0 => by simp [walk, count]
  | n + 1 => by
    rw [walk, Finset.sum_range_succ, ← walk, walk_eq_count v n, count_succ]
    cases v n <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
      push_cast <;> ring

/-- **Generic sequences oscillate maximally**: for a comeager set of sequences and every `k`, the
frequency of ones is at least `k/(k + 1)`, and at most `1/(k + 1)`, at arbitrarily late times. Each
condition reads finitely many letters, and extending any prefix by a long run of ones, or of zeros,
satisfies it. -/
theorem residual_oscillation : {v : ℕ → Bool | ∀ k N : ℕ,
    (∃ n, N < n ∧ k * n ≤ (k + 1) * count v n) ∧
    (∃ n, N < n ∧ (k + 1) * count v n ≤ n)} ∈ residual (ℕ → Bool) := by
  have hset : {v : ℕ → Bool | ∀ k N : ℕ, (∃ n, N < n ∧ k * n ≤ (k + 1) * count v n) ∧
      (∃ n, N < n ∧ (k + 1) * count v n ≤ n)} =
      (⋂ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, {v | N < n ∧ k * n ≤ (k + 1) * count v n}) ∩
        ⋂ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, {v | N < n ∧ (k + 1) * count v n ≤ n} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
    exact ⟨fun h => ⟨fun k N => (h k N).1, fun k N => (h k N).2⟩,
      fun h k N => ⟨h.1 k N, h.2 k N⟩⟩
  have hopen : ∀ (P : ℕ → ℕ → Prop) (n : ℕ), IsOpen {v : ℕ → Bool | P n (count v n)} :=
    fun P n => by
      rw [isOpen_iff_mem_nhds]
      intro v hv
      refine Filter.mem_of_superset (prefix_mem_nhds v n) fun u hu => ?_
      rw [Set.mem_ofPred_eq, count_congr fun t ht => hu t ht.le]
      exact hv
  rw [hset]
  refine Filter.inter_mem (countable_iInter_mem.2 fun k => countable_iInter_mem.2 fun N =>
    residual_of_dense_open (isOpen_iUnion fun n =>
      hopen (fun n c => N < n ∧ k * n ≤ (k + 1) * c) n) ?_)
    (countable_iInter_mem.2 fun k => countable_iInter_mem.2 fun N =>
      residual_of_dense_open (isOpen_iUnion fun n =>
        hopen (fun n c => N < n ∧ (k + 1) * c ≤ n) n) ?_)
  · rw [dense_iff_inter_open]
    rintro U hU ⟨v, hv⟩
    obtain ⟨L, hL⟩ := exists_prefix_subset (hU.mem_nhds hv)
    -- copy the prefix of `v`, then only ones
    refine ⟨fun t => if t < L then v t else true, hL fun t ht => by simp only [ite_eq_left ht], ?_⟩
    refine Set.mem_iUnion.2 ⟨(k + 1) * (L + N + 1), ?_, ?_⟩
    · nlinarith
    · have h1 := le_count (v := fun t => if t < L then v t else true) (L := L)
        (fun t ht => by simp only [show ¬ t < L by omega, ite_false]) ((k + 1) * (L + N + 1))
      have h2 : (k + 1) * (L + N + 1) ≤
          count (fun t => if t < L then v t else true) ((k + 1) * (L + N + 1)) + L := by omega
      have h3 := Nat.mul_le_mul_left (k + 1) h2
      nlinarith
  · rw [dense_iff_inter_open]
    rintro U hU ⟨v, hv⟩
    obtain ⟨L, hL⟩ := exists_prefix_subset (hU.mem_nhds hv)
    -- copy the prefix of `v`, then only zeros
    refine ⟨fun t => if t < L then v t else false, hL fun t ht => by simp only [ite_eq_left ht], ?_⟩
    refine Set.mem_iUnion.2 ⟨(k + 1) * (L + N + 1), ?_, ?_⟩
    · nlinarith
    · have h1 := count_le_of_false (v := fun t => if t < L then v t else false) (L := L)
        (fun t ht => by simp only [show ¬ t < L by omega, ite_false]) ((k + 1) * (L + N + 1))
      have h2 := Nat.mul_le_mul_left (k + 1) h1
      nlinarith

/-- **In the sense of category the walk oscillates maximally**: for a comeager set of
configurations the walk `W(n)` of the center column has `limsup W(n)/n = 1` and
`liminf W(n)/n = -1`. So `W(n)/√(2 n log log n)` is unbounded above and below, while for almost
every configuration it has limit points exactly `[-1, 1]` (`ae_clusterPt_walk_trace`). -/
theorem residual_limsup_liminf_walk_div_trace :
    {x : ℤ → Bool | limsup (fun n : ℕ => (walk (trace x) n : ℝ) / n) atTop = 1 ∧
      liminf (fun n : ℕ => (walk (trace x) n : ℝ) / n) atTop = -1} ∈ residual (ℤ → Bool) := by
  have h : {v : ℕ → Bool | limsup (fun n : ℕ => (walk v n : ℝ) / n) atTop = 1 ∧
      liminf (fun n : ℕ => (walk v n : ℝ) / n) atTop = -1} ∈ residual (ℕ → Bool) := by
    refine Filter.mem_of_superset residual_oscillation fun v hv => ?_
    simp only [Set.mem_ofPred_eq] at hv ⊢
    -- `W(n)/n = 2 N(n)/n - 1` lies in `[-1, 1]`
    have hW : ∀ n : ℕ, 0 < n → (walk v n : ℝ) / n = 2 * (count v n : ℝ) / n - 1 := fun n hn => by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [walk_eq_count]
      push_cast
      field_simp
    have hle : ∀ n : ℕ, (walk v n : ℝ) / n ≤ 1 := fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have hc : (count v n : ℝ) ≤ n := by exact_mod_cast count_le_self v n
        rw [hW n hn, sub_le_iff_le_add, div_le_iff₀ hn']
        linarith
    have hge : ∀ n : ℕ, -1 ≤ (walk v n : ℝ) / n := fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [hW n hn, le_sub_iff_add_le, le_div_iff₀ hn']
        have : (0 : ℝ) ≤ count v n := Nat.cast_nonneg _
        linarith
    have hfr : ∀ k : ℕ, ∃ᶠ n : ℕ in atTop, 1 - 2 / ((k : ℝ) + 1) ≤ (walk v n : ℝ) / n := fun k =>
      frequently_atTop.2 fun N => by
        obtain ⟨n, hn, hk⟩ := (hv k N).1
        refine ⟨n, hn.le, ?_⟩
        have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hk' : (k : ℝ) * n ≤ ((k : ℝ) + 1) * count v n := by exact_mod_cast hk
        rw [hW n (by omega), le_sub_iff_add_le, le_div_iff₀ hn']
        have e : (1 - 2 / ((k : ℝ) + 1) + 1) * n = 2 * ((k : ℝ) * n) / ((k : ℝ) + 1) := by
          field_simp
          ring
        rw [e, div_le_iff₀ (by positivity)]
        nlinarith
    have hfr' : ∀ k : ℕ, ∃ᶠ n : ℕ in atTop, (walk v n : ℝ) / n ≤ -1 + 2 / ((k : ℝ) + 1) :=
      fun k => frequently_atTop.2 fun N => by
        obtain ⟨n, hn, hk⟩ := (hv k N).2
        refine ⟨n, hn.le, ?_⟩
        have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hk' : ((k : ℝ) + 1) * count v n ≤ n := by exact_mod_cast hk
        rw [hW n (by omega), sub_le_iff_le_add, div_le_iff₀ hn']
        have h2 : 2 * (count v n : ℝ) ≤ 2 / ((k : ℝ) + 1) * n := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith
        linarith
    have hbdd : IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => (walk v n : ℝ) / n :=
      isBoundedUnder_of_eventually_le (Eventually.of_forall hle)
    have hbdd' : IsBoundedUnder (· ≥ ·) atTop fun n : ℕ => (walk v n : ℝ) / n :=
      isBoundedUnder_of_eventually_ge (Eventually.of_forall hge)
    have hcob : IsCoboundedUnder (· ≤ ·) atTop fun n : ℕ => (walk v n : ℝ) / n :=
      isCoboundedUnder_le_of_eventually_le atTop (Eventually.of_forall hge)
    have hcob' : IsCoboundedUnder (· ≥ ·) atTop fun n : ℕ => (walk v n : ℝ) / n :=
      isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hle)
    refine ⟨le_antisymm (limsup_le_of_le hcob (Eventually.of_forall hle)) ?_,
      le_antisymm ?_ (le_liminf_of_le hcob' (Eventually.of_forall hge))⟩
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      have := le_limsup_of_frequently_le (hfr k) hbdd
      have h2 : 2 / ((k : ℝ) + 1) < ε := by
        rw [show 2 / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) by ring]
        linarith
      linarith
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      have := liminf_le_of_frequently_le (hfr' k) hbdd'
      have h2 : 2 / ((k : ℝ) + 1) < ε := by
        rw [show 2 / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) by ring]
        linarith
      linarith
  exact tendsto_residual_of_isOpenMap continuous_trace isOpenMap_trace h

end Rule30Equivalents.IteratedLogarithm
