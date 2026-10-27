module

public import Rule30Equivalents.RandomConfigurations
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
# The longest run of a random sequence

The Erdős–Rényi law: among the first `n` cells of a fair-coin sequence, the longest run of black
cells, and the longest run of white cells, has length `log₂ n (1 + o(1))` almost surely. (For
rule 30's center column the longest runs among the first `10⁷` cells have lengths `22` and `23`,
against `log₂ 10⁷ ≈ 23.3`.)

* `longestRun v β n`: the length of the longest run of color `β` among the first `n` cells, so
  that `m ≤ longestRun v β n` iff such a run of length `m` exists (`le_longestRun_iff`).
* `measure_hasRun_le`: a run of length `m` among the first `n` cells has probability at most
  `(n + 1) 2^-m`, one cylinder for each start (`measure_run`).
* `measureReal_not_hasRun_le`: no run of length `m ≥ 1` among the first `n` cells has probability
  at most `m 2^m / n`. The `⌊n/m⌋` disjoint blocks of length `m` are independent fair words
  (`RandomConfigurations.map_blocks`), so none of them is a run with probability
  `(1 - 2^-m)^⌊n/m⌋ ≤ 1/(1 + ⌊n/m⌋ 2^-m)` (Bernoulli's inequality).
* `ae_eventually_longestRun`: along `n = 2^(qj)` both bounds are summable, and the longest run is
  monotone in `n`. So for almost every sequence and every `q ≥ 2`,
  `(q - 1) ⌊⌊log₂ n⌋/q⌋ ≤ longestRun v β n < (q + 1)(⌊⌊log₂ n⌋/q⌋ + 1)` from some `n` on. Hence
  `ae_tendsto_longestRun`: `longestRun v β n / ⌊log₂ n⌋ → 1`, and
  `ae_tendsto_longestRun_trace`: the same for the center column of almost every configuration.
-/

@[expose] public section

namespace Rule30Equivalents.LongestRuns

open MeasureTheory Filter Topology Genericity RandomConfigurations

/-- `v` has a run of `m` cells of color `β` among its first `n` cells. -/
def HasRun (v : ℕ → Bool) (β : Bool) (m n : ℕ) : Prop :=
  ∃ i, i + m ≤ n ∧ ∀ j < m, v (i + j) = β

open Classical in
/-- The length of the longest run of color `β` among the first `n` cells of `v`. -/
noncomputable def longestRun (v : ℕ → Bool) (β : Bool) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => HasRun v β m n) n

theorem hasRun_zero (v : ℕ → Bool) (β : Bool) (n : ℕ) : HasRun v β 0 n :=
  ⟨0, by omega, fun j hj => absurd hj (by omega)⟩

theorem HasRun.mono {v : ℕ → Bool} {β : Bool} {m n m' n' : ℕ} (h : HasRun v β m n)
    (hm : m' ≤ m) (hn : n ≤ n') : HasRun v β m' n' :=
  let ⟨i, hi, hrun⟩ := h
  ⟨i, by omega, fun j hj => hrun j (by omega)⟩

theorem HasRun.le {v : ℕ → Bool} {β : Bool} {m n : ℕ} (h : HasRun v β m n) : m ≤ n :=
  let ⟨_, hi, _⟩ := h
  by omega

/-- `longestRun v β n` is the largest `m` with a run of length `m`. -/
theorem le_longestRun_iff {v : ℕ → Bool} {β : Bool} {m n : ℕ} :
    m ≤ longestRun v β n ↔ HasRun v β m n := by
  classical
  constructor
  · intro h
    have hspec : HasRun v β (longestRun v β n) n :=
      Nat.findGreatest_spec (P := fun m => HasRun v β m n) (Nat.zero_le n) (hasRun_zero v β n)
    exact hspec.mono h le_rfl
  · intro h
    exact Nat.le_findGreatest h.le h

theorem longestRun_mono (v : ℕ → Bool) (β : Bool) {n n' : ℕ} (h : n ≤ n') :
    longestRun v β n ≤ longestRun v β n' :=
  le_longestRun_iff.2 ((le_longestRun_iff.1 le_rfl).mono le_rfl h)

/-! ### Probabilities -/

/-- A given run has probability `2^-m`. -/
theorem measure_run (β : Bool) (i m : ℕ) :
    coins ℕ {v | ∀ j < m, v (i + j) = β} = 2⁻¹ ^ m :=
  measure_triangular (ι := ℕ) (fun j v => v (i + j)) (fun _ => measurable_pi_apply _)
    (fun j => i + j) (fun j v => by simp)
    (fun j v j' hj' => by rw [Function.update_of_ne (by omega)]) (fun _ => β) m

/-- **A long run is rare**: a run of length `m` among the first `n` cells has probability at most
`(n + 1) 2^-m`. -/
theorem measure_hasRun_le (β : Bool) (m n : ℕ) :
    coins ℕ {v | HasRun v β m n} ≤ (n + 1) * 2⁻¹ ^ m := by
  have hsub : {v | HasRun v β m n} ⊆
      ⋃ i ∈ Finset.range (n + 1), {v | ∀ j < m, v (i + j) = β} := by
    rintro v ⟨i, hi, hrun⟩
    exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (by omega), hrun⟩
  calc coins ℕ {v | HasRun v β m n}
      ≤ ∑ i ∈ Finset.range (n + 1), coins ℕ {v | ∀ j < m, v (i + j) = β} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = (n + 1) * 2⁻¹ ^ m := by
        simp only [measure_run, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- A word of length `m` has probability `2^-m`. -/
theorem coins_fin_singleton (m : ℕ) (w : Fin m → Bool) : coins (Fin m) {w} = 2⁻¹ ^ m := by
  have : ({w} : Set (Fin m → Bool)) = ((Finset.univ : Finset (Fin m)) : Set (Fin m)).pi
      fun j => {w j} := by
    ext u
    simp [funext_iff]
  rw [this, coins_pi, Finset.prod_congr rfl fun j _ => coin_singleton (w j), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- A set of words of length `m` has probability its size times `2⁻ᵐ`. -/
theorem measureReal_finset (m : ℕ) (S : Finset (Fin m → Bool)) :
    (coins (Fin m)).real S = S.card * (2⁻¹ : ℝ) ^ m := by
  rw [measureReal_def, ← sum_measure_singleton,
    Finset.sum_congr rfl fun u _ => coins_fin_singleton m u, Finset.sum_const, nsmul_eq_mul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- The words of length `m` with exactly `t` black letters number `m.choose t`. -/
theorem card_filter_card_eq (m t : ℕ) :
    (Finset.univ.filter fun u : Fin m → Bool =>
      (Finset.univ.filter fun j => u j = true).card = t).card = m.choose t := by
  classical
  have h : m.choose t = (Finset.powersetCard t (Finset.univ : Finset (Fin m))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [h]
  refine Finset.card_nbij' (fun u => Finset.univ.filter fun j => u j = true)
    (fun s j => decide (j ∈ s)) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
    simp [Finset.mem_powersetCard, hu]
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    simp [hs.2]
  · intro u _
    funext j
    simp
  · intro s _
    ext j
    simp

/-- **Bernoulli's inequality, multiplied out**: `(1 - x)^K (1 + K x) ≤ 1` for `0 ≤ x ≤ 1`, since
`1 + K x ≤ (1 + x)^K` and `(1 - x)^K (1 + x)^K = (1 - x²)^K ≤ 1`. -/
theorem one_sub_pow_mul_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (K : ℕ) :
    (1 - x) ^ K * (1 + K * x) ≤ 1 := by
  have h1 : 1 + K * x ≤ (1 + x) ^ K := one_add_mul_le_pow (by linarith) K
  have h2 : (1 - x) ^ K * (1 + x) ^ K ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  calc (1 - x) ^ K * (1 + K * x) ≤ (1 - x) ^ K * (1 + x) ^ K :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) _)
    _ ≤ 1 := h2

/-- **No long run is rare too**: no run of length `m ≥ 1` among the first `n ≥ 1` cells has
probability at most `m 2^m / n`. -/
theorem measureReal_not_hasRun_le (β : Bool) {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    (coins ℕ).real {v | ¬ HasRun v β m n} ≤ m * 2 ^ m / n := by
  set K := n / m with hK
  let S : Set (Fin m → Bool) := {w | w ≠ fun _ => β}
  let B : (ℕ → Bool) → ℕ → Fin m → Bool := fun v k j => v (0 + k * m + j)
  have hB : Measurable B := by fun_prop
  -- the blocks `k m, …, k m + m - 1`, `k < K`, lie among the first `n` cells
  have hsub : {v | ¬ HasRun v β m n} ⊆ B ⁻¹' Set.pi (Finset.range K : Set ℕ) fun _ => S := by
    intro v hv k hk heq
    apply hv
    have hkK : k < K := Finset.mem_range.1 hk
    have hKm : K * m ≤ n := Nat.div_mul_le_self n m
    have hkm : (k + 1) * m ≤ K * m := Nat.mul_le_mul_right m hkK
    rw [add_mul, one_mul] at hkm
    refine ⟨k * m, by omega, fun j hj => ?_⟩
    have := congrFun heq ⟨j, hj⟩
    simpa [B] using this
  have hS : MeasurableSet S := (measurableSet_singleton _).compl
  have hblocks : coins ℕ (B ⁻¹' Set.pi (Finset.range K : Set ℕ) fun _ => S) =
      (1 - 2⁻¹ ^ m) ^ K := by
    rw [← Measure.map_apply hB (MeasurableSet.pi (Set.to_countable _) fun _ _ => hS),
      map_blocks hm 0, Measure.infinitePi_pi _ fun _ _ => hS, Finset.prod_const, Finset.card_range]
    congr 1
    rw [show S = {fun _ => β}ᶜ from rfl, prob_compl_eq_one_sub (measurableSet_singleton _),
      coins_fin_singleton]
  -- Bernoulli's inequality: `(1 - x)^K ≤ 1/(1 + K x)`, with `x = 2^-m`
  set x : ℝ := (1 / 2) ^ m with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hreal : (coins ℕ).real {v | ¬ HasRun v β m n} ≤ (1 - x) ^ K := by
    have h := measureReal_mono (μ := coins ℕ) hsub (measure_ne_top _ _)
    refine h.trans (le_of_eq ?_)
    rw [measureReal_def, hblocks, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le
      (pow_le_one₀ zero_le (by norm_num)) ENNReal.one_ne_top, ENNReal.toReal_one,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, hx, one_div]
  have hbern := one_sub_pow_mul_le hx0.le hx1 K
  -- `1 + K x ≥ n x / m`, since `m K > n - m`
  have hKm : (n : ℝ) < m * K + m := by
    have := Nat.lt_div_mul_add (a := n) hm
    rw [← hK] at this
    exact_mod_cast (by nlinarith [this] : n < m * K + m)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlow : (n : ℝ) * x ≤ m * (1 + K * x) := by nlinarith
  have hpow : x * 2 ^ m = 1 := by rw [hx, ← mul_pow]; norm_num
  calc (coins ℕ).real {v | ¬ HasRun v β m n} ≤ (1 - x) ^ K := hreal
    _ ≤ 1 / (1 + K * x) := by
        rw [le_div_iff₀ (by positivity)]
        exact hbern
    _ ≤ m * 2 ^ m / n := by
        rw [div_le_div_iff₀ (by positivity) hnpos, one_mul]
        calc (n : ℝ) = n * x * 2 ^ m := by rw [mul_assoc, hpow, mul_one]
          _ ≤ m * (1 + K * x) * 2 ^ m := by gcongr
          _ = m * 2 ^ m * (1 + K * x) := by ring

/-! ### Almost surely -/

/-- **The Erdős–Rényi law, in bounds**: for almost every fair-coin sequence and every `q ≥ 2`,
`(q - 1) ⌊⌊log₂ n⌋/q⌋ ≤ longestRun v β n < (q + 1)(⌊⌊log₂ n⌋/q⌋ + 1)` from some `n` on. -/
theorem ae_eventually_longestRun (β : Bool) :
    ∀ᵐ v ∂(coins ℕ), ∀ q : ℕ, 2 ≤ q → ∀ᶠ n in atTop,
      (q - 1) * (Nat.log 2 n / q) ≤ longestRun v β n ∧
        longestRun v β n < (q + 1) * (Nat.log 2 n / q + 1) := by
  refine ae_all_iff.2 fun q => ?_
  rcases Nat.lt_or_ge q 2 with hq | hq
  · exact Eventually.of_forall fun _ h => absurd h (by omega)
  -- the upper events along `2^(q(j+1))`
  have hup : ∑' j : ℕ, coins ℕ {v | HasRun v β ((q + 1) * (j + 1)) (2 ^ (q * (j + 1)))} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' j : ℕ, 2 * (2⁻¹ : ENNReal) ^ j) ?_
      (ENNReal.tsum_le_tsum fun j => ?_)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top
    · refine (measure_hasRun_le β _ _).trans ?_
      have h1 : ((2 ^ (q * (j + 1)) : ℕ) : ENNReal) + 1 ≤ 2 * 2 ^ (q * (j + 1)) := by
        push_cast
        have : (1 : ENNReal) ≤ 2 ^ (q * (j + 1)) := one_le_pow₀ (by norm_num)
        calc (2 : ENNReal) ^ (q * (j + 1)) + 1 ≤ 2 ^ (q * (j + 1)) + 2 ^ (q * (j + 1)) := by
              gcongr
          _ = 2 * 2 ^ (q * (j + 1)) := by ring
      calc ((2 ^ (q * (j + 1)) : ℕ) + 1 : ENNReal) * 2⁻¹ ^ ((q + 1) * (j + 1))
          ≤ 2 * 2 ^ (q * (j + 1)) * 2⁻¹ ^ ((q + 1) * (j + 1)) := by gcongr
        _ = 2 * (2 ^ (q * (j + 1)) * 2⁻¹ ^ (q * (j + 1))) * 2⁻¹ ^ (j + 1) := by
            rw [show (q + 1) * (j + 1) = q * (j + 1) + (j + 1) by ring, pow_add]
            ring
        _ ≤ 2 * 2⁻¹ ^ j := by
            rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow,
              mul_one]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right_of_le_one' (by norm_num)
              (Nat.le_succ j)) zero_le
  -- the lower events along `2^(qj)`
  have hlow : ∑' j : ℕ, coins ℕ {v | ¬ HasRun v β ((q - 1) * j) (2 ^ (q * j))} ≠ ⊤ := by
    have hsumm : Summable fun j : ℕ => ((q - 1 : ℕ) : ℝ) * ((j : ℝ) ^ 1 * (1 / 2) ^ j) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, ((q - 1 : ℕ) : ℝ) * ((j : ℝ) ^ 1 * (1 / 2) ^ j))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hemp : {v | ¬ HasRun v β ((q - 1) * 0) (2 ^ (q * 0))} = ∅ :=
        Set.eq_empty_of_forall_notMem fun v hv => hv (by simpa using hasRun_zero v β _)
      rw [hemp, measure_empty]
      exact zero_le
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ((measureReal_not_hasRun_le β
      (Nat.mul_pos (by omega) hj) (by positivity)).trans (le_of_eq ?_))
    have h2 : ((2 : ℝ) ^ (q * j)) = 2 ^ ((q - 1) * j) * 2 ^ j := by
      rw [← pow_add]
      congr 1
      have : q - 1 + 1 = q := by omega
      calc q * j = (q - 1 + 1) * j := by rw [this]
        _ = (q - 1) * j + j := by ring
    rw [Nat.cast_pow, Nat.cast_ofNat, h2, pow_one, one_div, inv_pow, Nat.cast_mul]
    field_simp
  filter_upwards [ae_eventually_notMem hup, ae_eventually_notMem hlow] with v hv1 hv2 _
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hv1.and hv2)
  -- `n ≥ 2^(qJ)`: with `j = ⌊⌊log₂ n⌋/q⌋ ≥ J`, `2^(qj) ≤ n < 2^(q(j+1))`
  filter_upwards [eventually_ge_atTop (2 ^ (q * J))] with n hn
  set j := Nat.log 2 n / q with hj
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := q * J)
    omega
  have hJj : J ≤ j := by
    rw [hj, Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact Nat.le_log_of_pow_le (by norm_num) hn
  have hlo : 2 ^ (q * j) ≤ n := by
    refine (Nat.pow_le_pow_right (by norm_num) ?_).trans (Nat.pow_log_le_self 2 hn0)
    rw [hj, mul_comm]
    exact Nat.div_mul_le_self _ _
  have hhi : n ≤ 2 ^ (q * (j + 1)) := by
    refine (Nat.lt_pow_succ_log_self (by norm_num) n).le.trans
      (Nat.pow_le_pow_right (by norm_num) ?_)
    have := Nat.lt_div_mul_add (a := Nat.log 2 n) (b := q) (by omega)
    rw [← hj] at this
    rw [Nat.succ_le_iff]
    nlinarith
  obtain ⟨h1, h2⟩ := hJ j hJj
  simp only [not_not] at h1 h2
  constructor
  · exact le_longestRun_iff.2 (h2.mono le_rfl hlo)
  · by_contra hge
    push Not at hge
    exact h1 ((le_longestRun_iff.1 hge).mono le_rfl hhi)

/-- **The Erdős–Rényi law**: for almost every fair-coin sequence the longest run of color `β`
among the first `n` cells has length `⌊log₂ n⌋ (1 + o(1))`. -/
theorem ae_tendsto_longestRun (β : Bool) :
    ∀ᵐ v ∂(coins ℕ),
      Tendsto (fun n : ℕ => (longestRun v β n : ℝ) / Nat.log 2 n) atTop (𝓝 1) := by
  filter_upwards [ae_eventually_longestRun β] with v hv
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- pick `q` with `3/q < ε`
  obtain ⟨q, hq⟩ := exists_nat_gt (3 / ε)
  have hq2 : 2 ≤ q + 2 := by omega
  set Q := q + 2 with hQ
  have hQpos : (0 : ℝ) < Q := by positivity
  have hQε : 3 / (Q : ℝ) < ε := by
    rw [div_lt_iff₀ hQpos]
    have : (3 : ℝ) / ε < Q := by rw [hQ]; push_cast; linarith
    rwa [div_lt_iff₀ hε, mul_comm] at this
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hv Q hq2).and (eventually_ge_atTop (2 ^ (Q * Q))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, hL⟩ := hN n hn
  replace hL : Q * Q ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hL
  set L := Nat.log 2 n
  set j := L / Q
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by positivity) hL
    exact_mod_cast this
  -- `j ≤ L/Q < j + 1`
  have hjQ : (j : ℝ) * Q ≤ L := by exact_mod_cast Nat.div_mul_le_self L Q
  have hjQ' : (L : ℝ) < (j + 1) * Q := by
    have := Nat.lt_div_mul_add (a := L) (b := Q) (by omega)
    have : L < (j + 1) * Q := by rw [add_mul, one_mul]; exact this
    exact_mod_cast this
  have hLQ : (Q : ℝ) * Q ≤ L := by exact_mod_cast hL
  have hr1 : ((Q - 1 : ℕ) : ℝ) * j ≤ longestRun v β n := by exact_mod_cast h1
  have hr2 : (longestRun v β n : ℝ) < (Q + 1 : ℕ) * (j + 1) := by exact_mod_cast h2
  have hQ1 : ((Q - 1 : ℕ) : ℝ) = Q - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hQ1] at hr1
  push_cast at hr2
  rw [Real.dist_eq, abs_lt]
  set R : ℝ := (longestRun v β n : ℝ)
  have hεQ : 3 < ε * Q := by rwa [div_lt_iff₀ hQpos] at hQε
  have h3L : 3 * (L : ℝ) < ε * Q * L := mul_lt_mul_of_pos_right hεQ hLpos
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQQ : (Q : ℝ) ≤ Q * Q := by nlinarith
  constructor
  · -- `R Q ≥ (Q - 1) j Q > (Q - 1)(L - Q) ≥ (1 - ε) L Q`
    have hjQ'' : (L : ℝ) - Q < j * Q := by linarith
    have hA : ((Q : ℝ) - 1) * (L - Q) ≤ ((Q : ℝ) - 1) * (j * Q) :=
      mul_le_mul_of_nonneg_left hjQ''.le (by linarith)
    have hB : ((Q : ℝ) - 1) * j * Q ≤ R * Q := mul_le_mul_of_nonneg_right hr1 hQpos.le
    have hC : (1 - ε) * L < R := by
      have : (1 - ε) * L * Q < R * Q := by nlinarith
      exact lt_of_mul_lt_mul_right this hQpos.le
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hLpos]
    linarith
  · -- `R Q < (Q + 1)(j + 1) Q ≤ (Q + 1)(L + Q) ≤ (1 + ε) L Q`
    have hjQ1 : ((j : ℝ) + 1) * Q ≤ L + Q := by linarith
    have hA : R * Q < ((Q : ℝ) + 1) * (j + 1) * Q := mul_lt_mul_of_pos_right hr2 hQpos
    have hB : ((Q : ℝ) + 1) * ((j + 1) * Q) ≤ ((Q : ℝ) + 1) * (L + Q) :=
      mul_le_mul_of_nonneg_left hjQ1 (by linarith)
    have hC : R < (1 + ε) * L := by
      have : R * Q < (1 + ε) * L * Q := by nlinarith
      exact lt_of_mul_lt_mul_right this hQpos.le
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hLpos]
    linarith

/-- **The Erdős–Rényi law for random center columns**: for almost every configuration the longest
black run, and the longest white run, among the first `n` cells of the center column has length
`⌊log₂ n⌋ (1 + o(1))`. -/
theorem ae_tendsto_longestRun_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ β : Bool,
      Tendsto (fun n : ℕ => (longestRun (trace x) β n : ℝ) / Nat.log 2 n) atTop (𝓝 1) :=
  ae_all_iff.2 fun β => measurePreserving_trace.quasiMeasurePreserving.ae (ae_tendsto_longestRun β)

end Rule30Equivalents.LongestRuns
