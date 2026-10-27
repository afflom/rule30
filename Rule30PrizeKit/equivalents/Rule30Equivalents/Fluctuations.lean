module

public import Rule30Equivalents.BoundedRemainder
public import Mathlib.Probability.Independence.ZeroOne
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
# Fluctuations of the center column of a random configuration

For a fair-coin configuration the center trace is a
sequence of fair coins (`RandomConfigurations.measurePreserving_trace`), so its discrepancy
`N(n) - n/2`, the number of black cells among the first `n` minus `n/2`, is a simple random walk
with steps `±1/2` (`imbalance`).

* `ae_frequently_le_imbalance_trace`: **for almost every configuration and every `K`, the
  discrepancy exceeds `K √n` infinitely often**, and it falls below `-K √n` infinitely often
  (`ae_frequently_imbalance_le_trace`, by exchanging black and white, `measurePreserving_not`).
  The event "`limsup N(n)/√n ≥ K`" (`HighAtScale`) does not depend on finitely many coins
  (`highAtScale_iff_tail`), so it has probability `0` or `1` (Kolmogorov's zero-one law, Mathlib's
  `measure_zero_or_one_of_measurableSet_limsup_atTop`). The central limit theorem
  (`RandomConfigurations.tendstoInDistribution_count`) and the portmanteau theorem give it
  positive probability (`exists_le_measure_le_imbalance`, `measure_highAtScale_ne_zero`).
* `ae_frequently_balanced_trace`: hence **the center column of almost every configuration is
  exactly balanced infinitely often**: `N(n) = n/2` for infinitely many `n`. The walk moves by
  `±1/2`, so between a visit above `0` and a visit below it passes through `0`
  (`exists_eq_zero_of_steps`).
* `ae_oscillating_discrepancy_trace`: the discrepancy is unbounded above and below, which for the
  center column of the single seed would prove Problem 1
  (`BoundedRemainder.problem1_of_oscillating_discrepancy`).
* `ae_eventually_abs_discrepancy_lt_trace`: **the discrepancy stays within `√(2 n log log n)`** from
  some `n` on. `measure_exists_le_imbalance_le` is Lévy's maximal inequality: on the event that `k`
  is the first time the imbalance reaches `x`, flipping the coins `k, …, n - 1`
  (`measurePreserving_flipIco`) preserves the event and negates the later gain, so the imbalance at
  time `n` is still at least `x` on at least half of it. With Hoeffding's inequality, the
  probability of reaching `√(2^(j+1) log log 2^j)` before time `2^(j+1)` is at most
  `2 / (j log 2)²`, a summable sequence (`ae_eventually_imbalance_lt`).

So the fluctuations of a random center column lie between `K √n`, for every `K`, and
`√(2 n log log n)`; the law of the iterated logarithm puts them at `√(n log log n / 2)`
(`IteratedLogarithm.ae_limsup_liminf_walk_trace`). At the
density `1/2` this strengthens `BoundedRemainder.ae_unbounded_remainder_trace`: the remainder is not
even `O(√n)`.
-/

@[expose] public section

namespace Rule30Equivalents.Fluctuations

open MeasureTheory ProbabilityTheory Filter Topology Genericity RandomConfigurations

/-- The imbalance of the first `n` coins: black ones minus `n/2`. -/
noncomputable def imbalance (v : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (black (v k) - 1 / 2)

/-- The imbalance of the coins from `m` up to `n`. -/
noncomputable def tailImbalance (v : ℕ → Bool) (m n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico m n, (black (v k) - 1 / 2)

theorem abs_black_sub_half (b : Bool) : |black b - 1 / 2| = 1 / 2 := by
  cases b <;> norm_num [black]

theorem abs_imbalance_le (v : ℕ → Bool) (m : ℕ) : |imbalance v m| ≤ m / 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun k _ => abs_black_sub_half (v k), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

theorem imbalance_eq_add (v : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    imbalance v n = imbalance v m + tailImbalance v m n := by
  unfold imbalance tailImbalance
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact (Finset.sum_Ico_consecutive _ (Nat.zero_le m) h).symm

/-- "`limsup imbalance(n)/√n ≥ K`", written with countably many quantifiers. -/
def HighAtScale (K : ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ j N : ℕ, ∃ n ≥ N, (K - 1 / (j + 1)) * √n ≤ f n

theorem abs_imbalance_sub_tailImbalance_le (v : ℕ → Bool) (m n : ℕ) :
    |imbalance v n - tailImbalance v m n| ≤ m / 2 := by
  rcases le_total m n with h | h
  · rw [imbalance_eq_add v h, add_sub_cancel_right]
    exact abs_imbalance_le v m
  · rw [tailImbalance, Finset.Ico_eq_empty_of_le h, Finset.sum_empty, sub_zero]
    have : (n : ℝ) ≤ m := by exact_mod_cast h
    exact (abs_imbalance_le v n).trans (by linarith)

/-- `HighAtScale` survives a bounded perturbation, which is negligible against `√n`. -/
theorem HighAtScale.of_le_add {K B : ℝ} {f g : ℕ → ℝ} (h : HighAtScale K f)
    (hfg : ∀ n, f n ≤ g n + B) : HighAtScale K g := by
  intro j N
  -- `√n` eventually dominates `2 (j + 1) B`
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, 2 * ((j : ℝ) + 1) * B ≤ √n := by
    set c := 2 * ((j : ℝ) + 1) * B
    refine ⟨⌈c ^ 2⌉₊, fun n hn => ?_⟩
    rcases le_or_gt c 0 with hc | hc
    · exact hc.trans (Real.sqrt_nonneg _)
    · rw [show c = √(c ^ 2) from (Real.sqrt_sq hc.le).symm]
      exact Real.sqrt_le_sqrt ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  obtain ⟨n, hn, hnK⟩ := h (2 * j + 1) (max N N₀)
  refine ⟨n, (le_max_left _ _).trans hn, ?_⟩
  have hs := hN₀ n ((le_max_right _ _).trans hn)
  have hfg' := hfg n
  have hj : (0 : ℝ) < j + 1 := by positivity
  have key : (1 / ((j : ℝ) + 1) - 1 / (((2 * j + 1 : ℕ) : ℝ) + 1)) * √n ≥ B := by
    have : (1 / ((j : ℝ) + 1) - 1 / (((2 * j + 1 : ℕ) : ℝ) + 1)) = 1 / (2 * ((j : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    rw [this, ge_iff_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith
  nlinarith

/-- Moving finitely many coins does not change `HighAtScale`: the imbalance changes by at most
`m/2`. -/
theorem highAtScale_iff_tail (v : ℕ → Bool) (K : ℝ) (m : ℕ) :
    HighAtScale K (imbalance v) ↔ HighAtScale K (tailImbalance v m) := by
  have h := fun n => abs_le.1 (abs_imbalance_sub_tailImbalance_le v m n)
  exact ⟨fun hf => hf.of_le_add (B := m / 2) fun n => by linarith [(h n).2],
    fun hg => hg.of_le_add (B := m / 2) fun n => by linarith [(h n).1]⟩

/-! ### The zero-one law -/

/-- The σ-algebra of the coin `i`. -/
abbrev coinAlg (i : ℕ) : MeasurableSpace (ℕ → Bool) :=
  MeasurableSpace.comap (fun v => v i) inferInstance

theorem coinAlg_le (i : ℕ) : coinAlg i ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  (measurable_pi_apply i).comap_le

theorem iIndep_coinAlg : iIndep coinAlg (coins ℕ) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => coin) (X := fun _ (b : Bool) => b)
    fun _ => measurable_id
  rw [iIndepFun_iff_iIndep] at h
  exact h

/-- `HighAtScale` for the coins from `m` on is measurable for the coins from `m` on. -/
theorem measurableSet_highAtScale_tail (K : ℝ) (m : ℕ) :
    MeasurableSet[⨆ i ≥ m, coinAlg i] {v | HighAtScale K (tailImbalance v m)} := by
  let : MeasurableSpace (ℕ → Bool) := ⨆ i ≥ m, coinAlg i
  have hk : ∀ k, m ≤ k → Measurable fun v : ℕ → Bool => black (v k) - 1 / 2 := fun k hk => by
    have : Measurable fun v : ℕ → Bool => v k :=
      Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ≥ m) => coinAlg i) k hk)
    exact (measurable_black.comp this).sub measurable_const
  have hsum : ∀ n, Measurable fun v : ℕ → Bool => tailImbalance v m n := fun n =>
    Finset.measurable_sum _ fun k hk' => hk k (Finset.mem_Ico.1 hk').1
  have hset : {v : ℕ → Bool | HighAtScale K (tailImbalance v m)} =
      ⋂ j : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : n ≥ N),
        {v | (K - 1 / ((j : ℝ) + 1)) * √(n : ℝ) ≤ tailImbalance v m n} := by
    ext v
    simp [HighAtScale]
  rw [hset]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => measurableSet_le measurable_const (hsum n)

/-- `HighAtScale K` is a tail event. -/
theorem measurableSet_limsup_highAtScale (K : ℝ) :
    MeasurableSet[limsup coinAlg atTop] {v | HighAtScale K (imbalance v)} := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro m
  rw [show {v : ℕ → Bool | HighAtScale K (imbalance v)} =
    {v | HighAtScale K (tailImbalance v m)} from Set.ext fun v => highAtScale_iff_tail v K m]
  exact measurableSet_highAtScale_tail K m

/-- Kolmogorov's zero-one law for `HighAtScale K`. -/
theorem measure_highAtScale_zero_or_one (K : ℝ) :
    coins ℕ {v | HighAtScale K (imbalance v)} = 0 ∨
      coins ℕ {v | HighAtScale K (imbalance v)} = 1 :=
  measure_zero_or_one_of_measurableSet_limsup_atTop coinAlg_le iIndep_coinAlg
    (measurableSet_limsup_highAtScale K)

/-! ### Positive probability: the central limit theorem -/

theorem imbalance_eq (v : ℕ → Bool) (n : ℕ) :
    imbalance v n = ∑ k ∈ Finset.range n, black (v k) - n / 2 := by
  rw [imbalance, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem measurable_imbalance (n : ℕ) : Measurable fun v : ℕ → Bool => imbalance v n :=
  Finset.measurable_sum _ fun k _ =>
    (measurable_black.comp (measurable_pi_apply k)).sub measurable_const

theorem measurableSet_highAtScale (K : ℝ) :
    MeasurableSet {v : ℕ → Bool | HighAtScale K (imbalance v)} := by
  have h := measurableSet_highAtScale_tail K 0
  have he : ∀ v, tailImbalance v 0 = imbalance v := fun v => funext fun n => by
    rw [tailImbalance, imbalance, Finset.range_eq_Ico]
  simp only [he] at h
  exact (iSup₂_le fun i _ => coinAlg_le i : (⨆ i ≥ 0, coinAlg i) ≤ _) _ h

/-- Exceeding `K` after dividing by `√n` is an imbalance of at least `K √n`. -/
theorem le_imbalance_of_lt {K : ℝ} {n : ℕ} {v : ℕ → Bool}
    (h : K < (√n)⁻¹ * (∑ k ∈ Finset.range n, black (v k) - n * (1 / 2))) :
    K * √n ≤ imbalance v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [imbalance]
  · have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have h' := mul_lt_mul_of_pos_left h hs
    rw [mul_inv_cancel_left₀ hs.ne'] at h'
    rw [imbalance_eq]
    linarith

/-- **The imbalance exceeds `K √n` with probability bounded away from `0`** for all large `n`: by
the central limit theorem (`RandomConfigurations.tendstoInDistribution_count`) and the portmanteau
theorem, at least half the normal tail beyond `K`. -/
theorem exists_le_measure_le_imbalance (K : ℝ) :
    ∃ c : ENNReal, c ≠ 0 ∧ ∀ᶠ n : ℕ in atTop, c ≤ coins ℕ {v | K * √n ≤ imbalance v n} := by
  have hg : gaussianReal 0 (1 / 4) (Set.Ioi K) ≠ 0 := fun h0 => by
    have h := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 / 4 : NNReal) ≠ 0) h0
    rw [Real.volume_Ioi] at h
    exact ENNReal.top_ne_zero h
  refine ⟨gaussianReal 0 (1 / 4) (Set.Ioi K) / 2, (ENNReal.half_pos hg).ne', ?_⟩
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    tendstoInDistribution_count.tendsto (isOpen_Ioi (a := K))
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at hport
  filter_upwards [eventually_lt_of_lt_liminf
    ((ENNReal.half_lt_self hg (measure_ne_top _ _)).trans_le hport)] with n hn
  rw [Measure.map_apply (measurable_centeredSum n) measurableSet_Ioi] at hn
  exact hn.le.trans (measure_mono fun v hv => le_imbalance_of_lt hv)

/-- **`HighAtScale K` has positive probability.** Exceeding `K √n` at some `n ≥ N` is at least as
likely as exceeding it at one such `n`, so its probability stays above the bound of
`exists_le_measure_le_imbalance`, and so does the limit as `N → ∞`. -/
theorem measure_highAtScale_ne_zero (K : ℝ) : coins ℕ {v | HighAtScale K (imbalance v)} ≠ 0 := by
  obtain ⟨c, hc, hev⟩ := exists_le_measure_le_imbalance K
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  let B : ℕ → Set (ℕ → Bool) := fun N => ⋃ n ≥ N, {v | K * √n ≤ imbalance v n}
  have hB : ∀ N, c ≤ coins ℕ (B N) := fun N =>
    (hN₀ _ (le_max_right N N₀)).trans (measure_mono fun v hv =>
      Set.mem_iUnion₂.2 ⟨max N N₀, le_max_left _ _, hv⟩)
  have hBm : ∀ N, MeasurableSet (B N) := fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurableSet_le measurable_const (measurable_imbalance n)
  have hanti : Antitone B := fun N M h v hv => by
    simp only [B, Set.mem_iUnion] at hv ⊢
    obtain ⟨n, hn, hv⟩ := hv
    exact ⟨n, h.trans hn, hv⟩
  have hc' : c ≤ coins ℕ (⋂ N, B N) :=
    ge_of_tendsto (tendsto_measure_iInter_atTop (fun N => (hBm N).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩) (Eventually.of_forall hB)
  have hsub : (⋂ N, B N) ⊆ {v | HighAtScale K (imbalance v)} := fun v hv j N => by
    simp only [B, Set.mem_iInter, Set.mem_iUnion] at hv
    obtain ⟨n, hn, hv⟩ := hv N
    refine ⟨n, hn, le_trans ?_ hv⟩
    have h1 : (0 : ℝ) ≤ 1 / (j + 1) := by positivity
    have h2 := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  exact fun h0 => hc (nonpos_iff_eq_zero.1 (hc'.trans ((measure_mono hsub).trans h0.le)))

theorem ae_highAtScale (K : ℝ) : ∀ᵐ v ∂(coins ℕ), HighAtScale K (imbalance v) := by
  rcases measure_highAtScale_zero_or_one K with h | h
  · exact absurd h (measure_highAtScale_ne_zero K)
  · exact ae_iff.2 ((prob_compl_eq_zero_iff (measurableSet_highAtScale K)).2 h)

/-- **For almost every sequence of fair coins and every `K`, the imbalance exceeds `K √n`
infinitely often.** -/
theorem ae_frequently_le_imbalance :
    ∀ᵐ v ∂(coins ℕ), ∀ K : ℝ, ∃ᶠ n : ℕ in atTop, K * √n ≤ imbalance v n := by
  filter_upwards [ae_all_iff.2 fun m : ℕ => ae_highAtScale ((m : ℝ) + 1)] with v hv K
  refine frequently_atTop.2 fun N => ?_
  obtain ⟨n, hn, h⟩ := hv ⌈K⌉₊ 0 N
  refine ⟨n, hn, le_trans ?_ h⟩
  simp only [Nat.cast_zero, zero_add, div_one, add_sub_cancel_right]
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil K) (Real.sqrt_nonneg _)

/-! ### Symmetry and recurrence -/

theorem coin_map_not : coin.map (fun b => !b) = coin := by
  refine Measure.ext_of_singleton fun b => ?_
  have h : (fun b : Bool => !b) ⁻¹' {b} = {!b} := by
    ext a
    cases a <;> cases b <;> simp
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton b), h, coin_singleton,
    coin_singleton]

/-- Exchanging black and white preserves the fair-coin measure. -/
theorem measurePreserving_not :
    MeasurePreserving (fun (v : ℕ → Bool) k => !v k) (coins ℕ) (coins ℕ) := by
  refine ⟨Measurable.of_eval fun k =>
    (Measurable.of_discrete (f := fun b : Bool => !b)).comp (measurable_pi_apply k), ?_⟩
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => coin) (f := fun _ (b : Bool) => !b)
    fun _ => Measurable.of_discrete
  simp only [coin_map_not] at h
  exact h

theorem imbalance_not (v : ℕ → Bool) (n : ℕ) :
    imbalance (fun k => !v k) n = -imbalance v n := by
  rw [imbalance, imbalance, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases v k <;> norm_num [black]

/-- By symmetry, the imbalance also falls below `-K √n` infinitely often. -/
theorem ae_frequently_imbalance_le :
    ∀ᵐ v ∂(coins ℕ), ∀ K : ℝ, ∃ᶠ n : ℕ in atTop, imbalance v n ≤ -(K * √n) := by
  filter_upwards [measurePreserving_not.quasiMeasurePreserving.ae ae_frequently_le_imbalance]
    with v hv K
  exact (hv K).mono fun n hn => by linarith [imbalance_not v n]

/-- Twice the imbalance, as an integer walk with steps `±1`. -/
def walk (v : ℕ → Bool) (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, if v k then 1 else -1

theorem two_mul_imbalance (v : ℕ → Bool) (n : ℕ) : 2 * imbalance v n = walk v n := by
  rw [imbalance, walk, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  cases v k <;> norm_num [black]

/-- **A discrete intermediate value theorem**: an integer walk whose steps down have size at most
`1`, nonnegative at `a` and nonpositive at `a + d`, vanishes in between. -/
theorem exists_eq_zero_of_steps {f : ℕ → ℤ} (hf : ∀ n, f n - 1 ≤ f (n + 1)) {a : ℕ} :
    ∀ d : ℕ, 0 ≤ f a → f (a + d) ≤ 0 → ∃ n, a ≤ n ∧ n ≤ a + d ∧ f n = 0
  | 0, h0, h1 => ⟨a, le_rfl, le_rfl, le_antisymm h1 h0⟩
  | d + 1, h0, h1 => by
    rw [← Nat.add_assoc] at h1
    by_cases hd : f (a + d) ≤ 0
    · obtain ⟨n, h2, h3, h4⟩ := exists_eq_zero_of_steps hf d h0 hd
      exact ⟨n, h2, by omega, h4⟩
    · have := hf (a + d)
      exact ⟨a + d + 1, by omega, by omega, by omega⟩

/-- The imbalance does not jump over `0`: nonnegative at `a` and nonpositive at a later `b`, it
vanishes in between. -/
theorem exists_imbalance_eq_zero {v : ℕ → Bool} {a b : ℕ} (hab : a ≤ b)
    (ha : 0 ≤ imbalance v a) (hb : imbalance v b ≤ 0) :
    ∃ n, a ≤ n ∧ n ≤ b ∧ imbalance v n = 0 := by
  have hstep : ∀ n, walk v n - 1 ≤ walk v (n + 1) := fun n => by
    rw [walk, walk, Finset.sum_range_succ]
    split_ifs <;> omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h0 : 0 ≤ walk v a := by
    have := two_mul_imbalance v a
    exact_mod_cast (show (0 : ℝ) ≤ walk v a by linarith)
  have h1 : walk v (a + d) ≤ 0 := by
    have := two_mul_imbalance v (a + d)
    exact_mod_cast (show (walk v (a + d) : ℝ) ≤ 0 by linarith)
  obtain ⟨n, h2, h3, h4⟩ := exists_eq_zero_of_steps hstep d h0 h1
  refine ⟨n, h2, h3, ?_⟩
  have := two_mul_imbalance v n
  rw [h4, Int.cast_zero] at this
  linarith

/-- **Almost surely the fair coins are exactly balanced infinitely often**: the imbalance is
`≥ 0` and `≤ 0` infinitely often, and it crosses `0` in between. -/
theorem ae_frequently_imbalance_eq_zero :
    ∀ᵐ v ∂(coins ℕ), ∃ᶠ n in atTop, imbalance v n = 0 := by
  filter_upwards [ae_frequently_le_imbalance, ae_frequently_imbalance_le] with v hhi hlo
  refine frequently_atTop.2 fun N => ?_
  obtain ⟨a, ha, ha'⟩ := frequently_atTop.1 (hhi 0) N
  obtain ⟨b, hb, hb'⟩ := frequently_atTop.1 (hlo 0) a
  obtain ⟨n, h1, -, h3⟩ := exists_imbalance_eq_zero hb (by simpa using ha') (by simpa using hb')
  exact ⟨n, ha.trans h1, h3⟩

/-! ### The envelope `√(n log log n)` -/

/-- Flip the coins `m, …, n - 1`. -/
def flipIco (m n : ℕ) (v : ℕ → Bool) : ℕ → Bool := fun k => if k ∈ Finset.Ico m n then !v k else v k

/-- Flipping a block of coins preserves the fair-coin measure. -/
theorem measurePreserving_flipIco (m n : ℕ) :
    MeasurePreserving (flipIco m n) (coins ℕ) (coins ℕ) := by
  refine ⟨Measurable.of_eval fun k => ?_, ?_⟩
  · by_cases hk : k ∈ Finset.Ico m n
    · simp only [flipIco, hk, ite_true]
      exact (Measurable.of_discrete (f := fun b : Bool => !b)).comp (measurable_pi_apply k)
    · simp only [flipIco, hk, ite_false]
      exact measurable_pi_apply k
  · let f : ℕ → Bool → Bool := fun k => if k ∈ Finset.Ico m n then (fun b => !b) else id
    have hf : flipIco m n = fun v k => f k (v k) := by
      funext v k
      simp only [flipIco, f]
      split_ifs <;> rfl
    have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => coin) (f := f)
      fun _ => Measurable.of_discrete
    have hc : ∀ k, coin.map (f k) = coin := by
      intro k
      simp only [f]
      split_ifs
      · exact coin_map_not
      · exact Measure.map_id
    simp only [hc] at h
    rw [hf]
    exact h

theorem imbalance_flipIco_of_le (v : ℕ → Bool) {m n j : ℕ} (hj : j ≤ m) :
    imbalance (flipIco m n v) j = imbalance v j := by
  unfold imbalance
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [flipIco, Finset.mem_Ico]
  rw [ite_eq_right (by omega)]

theorem tailImbalance_flipIco (v : ℕ → Bool) (m n : ℕ) :
    tailImbalance (flipIco m n v) m n = -tailImbalance v m n := by
  unfold tailImbalance
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [flipIco, ite_eq_left hi]
  cases v i <;> norm_num [black]

/-- **Lévy's maximal inequality**: the imbalance reaches `x` at some time `k ≤ n` with probability
at most twice the probability that it is at least `x` at time `n`. On the event that `k` is the
first such time, flipping the coins `k, …, n - 1` preserves the event and negates the imbalance
gained after `k`, so at least half of the event ends at `x` or above. -/
theorem measure_exists_le_imbalance_le (n : ℕ) (x : ℝ) :
    coins ℕ {v | ∃ k ≤ n, x ≤ imbalance v k} ≤ 2 * coins ℕ {v | x ≤ imbalance v n} := by
  classical
  let A : ℕ → Set (ℕ → Bool) := fun k => {v | x ≤ imbalance v k ∧ ∀ j < k, imbalance v j < x}
  have hAm : ∀ k, MeasurableSet (A k) := fun k => by
    have h2 : MeasurableSet {v : ℕ → Bool | ∀ j < k, imbalance v j < x} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_lt (measurable_imbalance j) measurable_const
    exact (measurableSet_le measurable_const (measurable_imbalance k)).inter h2
  have hBm : ∀ k, MeasurableSet {v : ℕ → Bool | 0 ≤ tailImbalance v k n} := fun k =>
    measurableSet_le measurable_const (Finset.measurable_sum _ fun i _ =>
      (measurable_black.comp (measurable_pi_apply i)).sub measurable_const)
  -- each first time contributes at most twice its part of `{x ≤ S_n}`
  have hk : ∀ k ≤ n, coins ℕ (A k) ≤ 2 * coins ℕ (A k ∩ {v | x ≤ imbalance v n}) := by
    intro k hkn
    have hρA : ∀ v, flipIco k n v ∈ A k ↔ v ∈ A k := fun v => by
      simp only [A, Set.mem_ofPred_eq, imbalance_flipIco_of_le v (le_refl k)]
      exact and_congr_right fun _ => forall₂_congr fun j hj => by
        rw [imbalance_flipIco_of_le v hj.le]
    have htm : Measurable fun v : ℕ → Bool => tailImbalance v k n :=
      Finset.measurable_sum _ fun i _ =>
        (measurable_black.comp (measurable_pi_apply i)).sub measurable_const
    set Bpos := A k ∩ {v | 0 ≤ tailImbalance v k n} with hBpos
    set Bneg := A k ∩ {v | tailImbalance v k n < 0} with hBneg
    have hBnegm : MeasurableSet Bneg := (hAm k).inter (measurableSet_lt htm measurable_const)
    have hunion : A k = Bpos ∪ Bneg := by
      ext v
      simp only [hBpos, hBneg, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hv
        rcases le_or_gt 0 (tailImbalance v k n) with h | h
        · exact Or.inl ⟨hv, h⟩
        · exact Or.inr ⟨hv, h⟩
      · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
    have hdisj' : Disjoint Bpos Bneg := by
      rw [Set.disjoint_left]
      rintro v ⟨-, h1⟩ ⟨-, h2⟩
      simp only [Set.mem_ofPred_eq] at h1 h2
      linarith
    have hsplit : coins ℕ (A k) = coins ℕ Bpos + coins ℕ Bneg := by
      rw [hunion, measure_union hdisj' hBnegm]
    have hneg : coins ℕ Bneg ≤ coins ℕ Bpos := by
      calc coins ℕ Bneg ≤ coins ℕ (flipIco k n ⁻¹' Bpos) := measure_mono fun v hv => by
            simp only [hBpos, hBneg, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
              hρA, tailImbalance_flipIco] at hv ⊢
            exact ⟨hv.1, by linarith [hv.2]⟩
        _ = coins ℕ Bpos := (measurePreserving_flipIco k n).measure_preimage
            ((hAm k).inter (hBm k)).nullMeasurableSet
    have hpos : Bpos ⊆ A k ∩ {v | x ≤ imbalance v n} := fun v hv => by
      refine ⟨hv.1, ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [imbalance_eq_add v hkn]
      have h1 := hv.1.1
      have h2 : 0 ≤ tailImbalance v k n := hv.2
      linarith
    calc coins ℕ (A k) = coins ℕ Bpos + coins ℕ Bneg := hsplit
      _ ≤ coins ℕ Bpos + coins ℕ Bpos := add_le_add le_rfl hneg
      _ = 2 * coins ℕ Bpos := (two_mul _).symm
      _ ≤ 2 * coins ℕ (A k ∩ {v | x ≤ imbalance v n}) :=
        mul_le_mul_of_nonneg_left (measure_mono hpos) zero_le
  -- the first times partition the event
  have hcover : {v | ∃ k ≤ n, x ≤ imbalance v k} ⊆ ⋃ k ∈ Finset.range (n + 1), A k := by
    rintro v ⟨k, hkn, hxk⟩
    have hex : ∃ k, x ≤ imbalance v k := ⟨k, hxk⟩
    refine Set.mem_iUnion₂.2 ⟨Nat.find hex, Finset.mem_range.2 ?_, Nat.find_spec hex,
      fun j hj => not_le.1 (Nat.find_min hex hj)⟩
    have := Nat.find_min' hex hxk
    omega
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint A := by
    intro k _ k' _ hkk'
    rw [Function.onFun, Set.disjoint_left]
    rintro v ⟨hk1, hk2⟩ ⟨hk1', hk2'⟩
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact absurd hk1 (not_le.2 (hk2' k h))
    · exact absurd hk1' (not_le.2 (hk2 k' h))
  calc coins ℕ {v | ∃ k ≤ n, x ≤ imbalance v k}
      ≤ coins ℕ (⋃ k ∈ Finset.range (n + 1), A k) := measure_mono hcover
    _ = ∑ k ∈ Finset.range (n + 1), coins ℕ (A k) := measure_biUnion_finset hdisj fun k _ => hAm k
    _ ≤ ∑ k ∈ Finset.range (n + 1), 2 * coins ℕ (A k ∩ {v | x ≤ imbalance v n}) :=
        Finset.sum_le_sum fun k hk' => hk k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk'))
    _ = 2 * coins ℕ (⋃ k ∈ Finset.range (n + 1), A k ∩ {v | x ≤ imbalance v n}) := by
        rw [← Finset.mul_sum, measure_biUnion_finset
          (hdisj.mono_on fun k _ => Set.inter_subset_left)
          fun k _ => (hAm k).inter (measurableSet_le measurable_const (measurable_imbalance n))]
    _ ≤ 2 * coins ℕ {v | x ≤ imbalance v n} :=
        mul_le_mul_of_nonneg_left (measure_mono (Set.iUnion₂_subset fun k _ =>
          Set.inter_subset_right)) zero_le

/-- **The envelope `√(2 n log log n)` from above**: for almost every fair-coin sequence the
imbalance stays below `√(2 n log log n)` from some `n` on. Along the scales `2^j`, Lévy's
inequality and Hoeffding's give probability at most `2 exp(-2 log log 2^j) = 2 / (j log 2)²` to
reach `√(2^(j+1) log log 2^j)` before time `2^(j+1)`, a summable sequence. -/
theorem ae_eventually_imbalance_lt :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ n : ℕ in atTop, imbalance v n < √(2 * n * Real.log (Real.log n)) := by
  set L : ℕ → ℝ := fun j => Real.log (Real.log ((2 : ℝ) ^ j)) with hL
  set x : ℕ → ℝ := fun j => √(2 * 2 ^ j * L j) with hx
  set E : ℕ → Set (ℕ → Bool) := fun j => {v | ∃ k ≤ 2 ^ (j + 1), x j ≤ imbalance v k} with hE
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog21 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlog2half : 1 / 2 < Real.log 2 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
    rw [Real.log_inv] at this
    linarith
  -- the bound `8 / ((j + 1)² (log 2)²)`
  have hbound : ∀ j, (coins ℕ).real (E j) ≤ 8 / (((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2) := by
    intro j
    rcases Nat.lt_or_ge j 2 with hj | hj
    · refine measureReal_le_one.trans ?_
      rw [le_div_iff₀ (by positivity), one_mul]
      have : ((j : ℝ) + 1) ^ 2 ≤ 4 := by
        have : (j : ℝ) ≤ 1 := by exact_mod_cast (by omega : j ≤ 1)
        nlinarith
      nlinarith [sq_nonneg (Real.log 2)]
    -- `L j = log (j log 2) ≥ 0`
    have hjlog : 1 < (j : ℝ) * Real.log 2 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith
    have hLj : L j = Real.log ((j : ℝ) * Real.log 2) := by
      simp only [hL, Real.log_pow]
    have hL0 : 0 ≤ L j := by rw [hLj]; exact Real.log_nonneg hjlog.le
    -- Lévy and Hoeffding
    have h1 : (coins ℕ).real (E j) ≤ 2 * (coins ℕ).real {v | x j ≤ imbalance v (2 ^ (j + 1))} := by
      have := measure_exists_le_imbalance_le (2 ^ (j + 1)) (x j)
      rw [measureReal_def, measureReal_def, ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)) this
    have h2 := RandomConfigurations.measureReal_sum_ge_le (2 ^ (j + 1))
      (Real.sqrt_nonneg (2 * 2 ^ j * L j))
    have hexp : Real.exp (-2 * (x j) ^ 2 / ((2 ^ (j + 1) : ℕ) : ℝ)) =
        1 / ((j : ℝ) * Real.log 2) ^ 2 := by
      rw [hx]
      simp only
      rw [Real.sq_sqrt (by positivity), hLj]
      push_cast
      rw [show -2 * (2 * 2 ^ j * Real.log ((j : ℝ) * Real.log 2)) / 2 ^ (j + 1) =
        -Real.log (((j : ℝ) * Real.log 2) ^ 2) by rw [Real.log_pow, pow_succ]; field_simp; ring,
        Real.exp_neg, Real.exp_log (by positivity), one_div]
    have hcmp : 2 / ((j : ℝ) * Real.log 2) ^ 2 ≤ 8 / (((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : ((j : ℝ) + 1) ^ 2 ≤ 4 * (j : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
        nlinarith
      nlinarith [sq_nonneg (Real.log 2), mul_pos hlog2 hlog2]
    calc (coins ℕ).real (E j) ≤ 2 * (coins ℕ).real {v | x j ≤ imbalance v (2 ^ (j + 1))} := h1
      _ ≤ 2 * (1 / ((j : ℝ) * Real.log 2) ^ 2) := by
          rw [← hexp]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 / ((j : ℝ) * Real.log 2) ^ 2 := by ring
      _ ≤ 8 / (((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2) := hcmp
  have hsum : ∑' j, coins ℕ (E j) ≠ ⊤ := by
    have hsumm : Summable fun j : ℕ => 8 / (((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2) := by
      have := ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left
        (8 / Real.log 2 ^ 2)
      refine this.congr fun j => ?_
      push_cast
      field_simp
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, 8 / (((j : ℝ) + 1) ^ 2 * Real.log 2 ^ 2))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  filter_upwards [ae_eventually_notMem hsum] with v hv
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hv
  filter_upwards [eventually_ge_atTop (2 ^ (max J 2))] with n hn
  set j := Nat.log 2 n with hj
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := max J 2)
    omega
  have hJj : max J 2 ≤ j := Nat.le_log_of_pow_le (by norm_num) hn
  have hlo : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0
  have hhi : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hvj := hJ j (le_of_max_le_left hJj)
  simp only [hE, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hvj
  refine (hvj n hhi.le).trans_le (Real.sqrt_le_sqrt ?_)
  -- `2^j ≤ n` and `log log 2^j ≤ log log n`
  have hj2 : 2 ≤ j := le_of_max_le_right hJj
  have hpow : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hlo
  have hlogpos : 1 < Real.log ((2 : ℝ) ^ j) := by
    rw [Real.log_pow]
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj2
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
    rw [Real.log_inv] at this
    nlinarith
  have hLle : L j ≤ Real.log (Real.log n) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by positivity) hpow)
  have hL0 : 0 ≤ L j := Real.log_nonneg hlogpos.le
  show 2 * 2 ^ j * L j ≤ 2 * n * Real.log (Real.log n)
  have : (0 : ℝ) ≤ 2 ^ j := by positivity
  nlinarith

/-- **For almost every fair-coin sequence, `|N(n) - n/2| < √(2 n log log n)` from some `n` on**
(by exchanging black and white for the lower side). The law of the iterated logarithm gives the
sharp constant `1/√2` in place of `√2` (`IteratedLogarithm.ae_limsup_liminf_walk`). -/
theorem ae_eventually_abs_imbalance_lt :
    ∀ᵐ v ∂(coins ℕ), ∀ᶠ n : ℕ in atTop, |imbalance v n| < √(2 * n * Real.log (Real.log n)) := by
  filter_upwards [ae_eventually_imbalance_lt,
    measurePreserving_not.quasiMeasurePreserving.ae ae_eventually_imbalance_lt] with v h1 h2
  filter_upwards [h1, h2] with n hn1 hn2
  rw [imbalance_not] at hn2
  exact abs_lt.2 ⟨by linarith, hn1⟩

/-! ### The center column of a random configuration -/

/-- **For almost every configuration and every `K`, infinitely often at least `n/2 + K √n` of the
first `n` cells of the center column are black.** -/
theorem ae_frequently_le_imbalance_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ K : ℝ, ∃ᶠ n : ℕ in atTop,
      K * √n ≤ ∑ k ∈ Finset.range n, black (trace x k) - n / 2 :=
  measurePreserving_trace.quasiMeasurePreserving.ae (p := fun v => ∀ K : ℝ, ∃ᶠ n : ℕ in atTop,
      K * √n ≤ ∑ k ∈ Finset.range n, black (v k) - n / 2)
    (ae_frequently_le_imbalance.mono fun v hv K => (hv K).mono fun n hn => by
      rwa [imbalance_eq] at hn)

/-- … and infinitely often at most `n/2 - K √n`. -/
theorem ae_frequently_imbalance_le_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ K : ℝ, ∃ᶠ n : ℕ in atTop,
      ∑ k ∈ Finset.range n, black (trace x k) - n / 2 ≤ -(K * √n) :=
  measurePreserving_trace.quasiMeasurePreserving.ae (p := fun v => ∀ K : ℝ, ∃ᶠ n : ℕ in atTop,
      ∑ k ∈ Finset.range n, black (v k) - n / 2 ≤ -(K * √n))
    (ae_frequently_imbalance_le.mono fun v hv K => (hv K).mono fun n hn => by
      rwa [imbalance_eq] at hn)

/-- **For almost every configuration the center column is exactly balanced infinitely often**:
for infinitely many `n`, exactly `n/2` of its first `n` cells are black. -/
theorem ae_frequently_balanced_trace :
    ∀ᵐ x ∂(coins ℤ), ∃ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range n, black (trace x k) = n / 2 :=
  measurePreserving_trace.quasiMeasurePreserving.ae
    (p := fun v => ∃ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range n, black (v k) = n / 2)
    (ae_frequently_imbalance_eq_zero.mono fun v hv => hv.mono fun n hn => by
      rw [imbalance_eq] at hn
      linarith)

/-- **For almost every configuration the discrepancy of the center column stays within
`√(2 n log log n)`** from some `n` on. -/
theorem ae_eventually_abs_discrepancy_lt_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ᶠ n : ℕ in atTop,
      |∑ k ∈ Finset.range n, black (trace x k) - n / 2| < √(2 * n * Real.log (Real.log n)) :=
  measurePreserving_trace.quasiMeasurePreserving.ae (p := fun v => ∀ᶠ n : ℕ in atTop,
      |∑ k ∈ Finset.range n, black (v k) - n / 2| < √(2 * n * Real.log (Real.log n)))
    (ae_eventually_abs_imbalance_lt.mono fun v hv => hv.mono fun n hn => by
      rwa [imbalance_eq] at hn)

theorem cast_ones_eq_sum_black (b : ℕ → Bool) (n : ℕ) :
    (BoundedRemainder.ones b n : ℝ) = ∑ k ∈ Finset.range n, black (b k) := by
  rw [BoundedRemainder.ones, Nat.count_eq_card_filter_range, Finset.natCast_card_filter]
  rfl

/-- **The hypotheses of `BoundedRemainder.problem1_of_oscillating_discrepancy` hold for almost
every configuration**: the discrepancy `N(n) - n/2` of the center column is unbounded above and
below. -/
theorem ae_oscillating_discrepancy_trace :
    ∀ᵐ x ∂(coins ℤ), (∀ C : ℝ, ∃ n, C < (BoundedRemainder.ones (trace x) n : ℝ) - n / 2) ∧
      ∀ C : ℝ, ∃ n, (BoundedRemainder.ones (trace x) n : ℝ) - n / 2 < -C := by
  filter_upwards [ae_frequently_le_imbalance_trace, ae_frequently_imbalance_le_trace]
    with x hhi hlo
  have hlarge : ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, C < √n := fun C =>
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  refine ⟨fun C => ?_, fun C => ?_⟩
  · obtain ⟨n, hn, hC⟩ := ((hhi 1).and_eventually (hlarge C)).exists
    exact ⟨n, by rw [cast_ones_eq_sum_black]; linarith⟩
  · obtain ⟨n, hn, hC⟩ := ((hlo 1).and_eventually (hlarge C)).exists
    exact ⟨n, by rw [cast_ones_eq_sum_black]; linarith⟩

end Rule30Equivalents.Fluctuations
