module

public import Rule30Equivalents.Basic
public import Rule30Equivalents.Tauberian
public import Rule30Equivalents.BinaryIrrational
public import Rule30Equivalents.StrongerStatements
public import Rule30Equivalents.Symmetry

/-!
# Prize Problem 2: density 1/2

`Rule30Prize.Problem2` says that the black cells have density `1/2` in the
center column, stated with integers: for every `k > 0`, eventually `k |2 b(n) - n| ≤ n`, where
`b(n)` counts the black cells among `c(0), …, c(n - 1)`. Two equivalent forms:

* `problem2_iff_tendsto`: `b(n) / n → 1/2`, from `halfDensity_iff_tendsto`, which holds for every
  bit sequence;
* `problem2_iff_abel`: the Abel mean `(1 - x) ∑ c(t) xᵗ` tends to `1/2` as `x → 1⁻`. The forward
  direction is Abelian (`Tauberian.tendsto_abel_of_tendsto_cesaro`); the converse is the
  Hardy–Littlewood–Karamata Tauberian theorem (`Tauberian.tendsto_cesaro_of_tendsto_abel`), which
  applies because the coefficients are nonnegative;
* `problem2_iff_simplyNormal`: `x₂ = 0.c(0) c(1) …₂` is simply normal in base `2`. Its binary digits
  are the center column, since `c` has infinitely many `0`s (`binDigit_centerBinary`).

Also `problem2_of_isNormal` (normality of `x₂` gives Problem 2, from `halfDensity_of_isNormal` for
every bit sequence) and
`problem1_of_density_on_progressions`: density `1/2` along every arithmetic progression rules out
an eventually constant residue class, hence gives Problem 1 (the anti-Toeplitz statement).
-/

@[expose] public section

namespace Rule30Equivalents.ProblemTwo

open Filter Topology Ruliology.CellularAutomata

/-- The number of `true` values among `b(0), …, b(n - 1)`, as a sum. -/
theorem count_eq_sum (b : ℕ → Bool) (n : ℕ) :
    (((List.range n).filter b).length : ℝ) =
      ∑ t ∈ Finset.range n, if b t then (1 : ℝ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [List.range_succ, List.filter_append, List.length_append]
    push_cast
    cases h : b n <;> simp [List.filter, h]

/-- `b(n)` is the sum of the center column over `0, …, n - 1`. -/
theorem blackCount_eq_sum (n : ℕ) :
    (Rule30Prize.blackCount n : ℝ) =
      ∑ t ∈ Finset.range n, if Rule30Prize.center t then (1 : ℝ) else 0 :=
  count_eq_sum _ n

theorem le_iff_real (b : ℕ → Bool) (k n : ℕ) :
    k * (2 * (((List.range n).filter b).length : ℤ) - n).natAbs ≤ n ↔
      (k : ℝ) * |2 * (((List.range n).filter b).length : ℝ) - n| ≤ n := by
  have : ((((2 * (((List.range n).filter b).length : ℤ) - n).natAbs : ℕ)) : ℝ) =
      |2 * (((List.range n).filter b).length : ℝ) - n| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    ring_nf
  rw [← this, ← Nat.cast_mul, Nat.cast_le]

theorem abs_sub_half (b : ℕ → Bool) {n : ℕ} (hn : 0 < n) :
    |(((List.range n).filter b).length : ℝ) / n - 1 / 2| =
      |2 * (((List.range n).filter b).length : ℝ) - n| / (2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (((List.range n).filter b).length : ℝ) / n - 1 / 2 =
      (2 * ((List.range n).filter b).length - n) / (2 * n) by field_simp, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]

/-- **Density `1/2` as a limit**, for every bit sequence: the proportion of `true` values among
the first `n` tends to `1/2`. -/
theorem halfDensity_iff_tendsto (b : ℕ → Bool) : Symmetry.HalfDensity b ↔
    Tendsto (fun n : ℕ => (((List.range n).filter b).length : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  constructor
  · intro h2
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    have hk' : (0 : ℝ) < k := lt_trans (by positivity) hk
    obtain ⟨N, hN⟩ := h2 k (by exact_mod_cast hk')
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := (le_iff_real b k n).1 (hN n (by omega))
    rw [Real.dist_eq, abs_sub_half b hn0, div_lt_iff₀ (by positivity)]
    have hεk : 1 < ε * k := by rwa [div_lt_iff₀ hε, mul_comm] at hk
    nlinarith [abs_nonneg (2 * (((List.range n).filter b).length : ℝ) - n)]
  · intro h k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h (1 / (2 * k)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := hN n hn
    rw [Real.dist_eq, abs_sub_half b hn0, div_lt_div_iff₀ (by positivity) (by positivity)] at h1
    rw [le_iff_real]
    nlinarith

/-- **Problem 2 as a limit**: the proportion of black cells tends to `1/2`. -/
theorem problem2_iff_tendsto : Rule30Prize.Problem2 ↔
    Tendsto (fun n : ℕ => (Rule30Prize.blackCount n : ℝ) / n) atTop (𝓝 (1 / 2)) :=
  halfDensity_iff_tendsto c

/-- **Problem 2 as an Abel limit**: `(1 - x) ∑ c(t) xᵗ → 1/2` as `x → 1⁻`. -/
theorem problem2_iff_abel : Rule30Prize.Problem2 ↔
    Tendsto (fun x : ℝ => (1 - x) * ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) * x ^ t)
      (𝓝[<] 1) (𝓝 (1 / 2)) := by
  have hcesaro : Rule30Prize.Problem2 ↔ Tendsto (fun N : ℕ =>
      (∑ t ∈ Finset.range N, if Rule30Prize.center t then (1 : ℝ) else 0) / N) atTop
        (𝓝 (1 / 2)) := by
    rw [problem2_iff_tendsto]
    simp only [blackCount_eq_sum]
  rw [hcesaro]
  constructor
  · intro h
    refine Tauberian.tendsto_abel_of_tendsto_cesaro (B := 1) (fun t => ?_) h
    split_ifs <;> simp
  · intro h
    refine Tauberian.tendsto_cesaro_of_tendsto_abel (fun t => ?_) (fun x hx0 hx1 => ?_) h
    · split_ifs <;> simp
    · refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
        (summable_geometric_of_lt_one hx0 hx1)
      · split_ifs <;> simp [pow_nonneg hx0]
      · split_ifs <;> simp [pow_nonneg hx0]

/-! ### Simple normality of `x₂` -/

/-- The binary digit of `x ≥ 0` at position `t` after the point: `⌊2^(t+1) x⌋ mod 2`. -/
noncomputable def binDigit (x : ℝ) (t : ℕ) : ℕ := ⌊(2 : ℝ) ^ (t + 1) * x⌋₊ % 2

/-- `x` is simply normal in base `2`: the digit `1` has frequency `1/2`. -/
def SimplyNormal2 (x : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (((Finset.range n).filter fun t => binDigit x t = 1).card : ℝ) / n)
    atTop (𝓝 (1 / 2))

/-- The binary digits of `x₂` are the center column. -/
theorem binDigit_centerBinary (t : ℕ) :
    binDigit BinaryIrrational.centerBinary t = if c t then 1 else 0 := by
  have hcb := BinaryIrrational.centerBinary_eq_baseValue
  -- a later digit is `0`, since `c` is not eventually `1`
  obtain ⟨s, hs, hcs⟩ : ∃ s, t + 1 ≤ s ∧ c s = false := by
    by_contra hne
    push Not at hne
    exact Rule30Prize.center_not_eventually_constant
      ⟨t + 1, true, fun s hs => by simpa using hne s hs⟩
  have hshift := BinaryIrrational.pow_mul_baseValue (B := 2) le_rfl c (t + 1)
  have hlt := BinaryIrrational.baseValue_lt_one le_rfl (b := BinaryIrrational.tail c (t + 1))
      (s := s - (t + 1)) (by
    simp only [BinaryIrrational.tail]
    rw [Nat.sub_add_cancel hs]
    exact hcs)
  have hge := BinaryIrrational.baseValue_nonneg (B := 2) le_rfl (BinaryIrrational.tail c (t + 1))
  have hfloor : ⌊(2 : ℝ) ^ (t + 1) * BinaryIrrational.centerBinary⌋₊ =
      BinaryIrrational.lead 2 c (t + 1) := by
    rw [hcb]
    push_cast at hshift
    rw [hshift, Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  rw [binDigit, hfloor]
  simp only [BinaryIrrational.lead]
  cases h : c t <;> simp

/-- **Problem 2 as simple normality**: `x₂` is simply normal in base `2`. -/
theorem problem2_iff_simplyNormal :
    Rule30Prize.Problem2 ↔ SimplyNormal2 BinaryIrrational.centerBinary := by
  rw [problem2_iff_tendsto, SimplyNormal2]
  have : ∀ n, (((Finset.range n).filter fun t =>
      binDigit BinaryIrrational.centerBinary t = 1).card : ℝ) = Rule30Prize.blackCount n := by
    intro n
    rw [blackCount_eq_sum, Finset.sum_boole]
    congr 2
    refine Finset.filter_congr fun t _ => ?_
    rw [binDigit_centerBinary]
    cases h : Rule30Prize.center t <;> simp [c, h]
  simp only [this]

/-- A normal sequence has density `1/2`: the word `1` has frequency `1/2`. -/
theorem halfDensity_of_isNormal {b : ℕ → Bool} (h : StrongerStatements.IsNormal b) :
    Symmetry.HalfDensity b := by
  rw [halfDensity_iff_tendsto]
  have h1 := h 1 fun _ => true
  rw [pow_one, ← one_div] at h1
  refine h1.congr fun n => ?_
  rw [count_eq_sum, Finset.sum_boole]
  congr 3
  refine Finset.filter_congr fun t _ => ?_
  simp

/-- **Normality gives Problem 2**: if every word of length `n` occurs in `c` with frequency
`2⁻ⁿ`, then in particular the black cells have density `1/2`. -/
theorem problem2_of_isNormal (h : StrongerStatements.IsNormal c) : Rule30Prize.Problem2 :=
  halfDensity_of_isNormal h

/-- **Density on progressions gives Problem 1**: if `c` has density `1/2` along every
arithmetic progression, no residue class is eventually constant (anti-Toeplitz). -/
theorem problem1_of_density_on_progressions
    (h : ∀ P r : ℕ, 0 < P → Tendsto (fun n : ℕ =>
      (((Finset.range n).filter fun k => c (r + k * P) = true).card : ℝ) / n) atTop (𝓝 (1 / 2))) :
    Rule30Prize.Problem1 := by
  refine StrongerStatements.problem1_of_anti_toeplitz fun P hP r ⟨K, b, hK⟩ => ?_
  have h1 := h P r hP
  cases b
  · -- eventually white: at most `K` black terms, so the frequency tends to `0`
    have h0 : Tendsto (fun n : ℕ =>
        (((Finset.range n).filter fun k => c (r + k * P) = true).card : ℝ) / n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
        (Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Eventually.of_forall fun n => ?_)
      have hsub : (Finset.range n).filter (fun k => c (r + k * P) = true) ⊆ Finset.range K :=
        fun k hk => by
          rw [Finset.mem_filter] at hk
          rw [Finset.mem_range]
          by_contra hKk
          have := hK k (by omega)
          simp_all
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      gcongr
    have := tendsto_nhds_unique h1 h0
    norm_num at this
  · -- eventually black: at least `n - K` black terms, so the frequency tends to `1`
    have hlin : Tendsto (fun n : ℕ => ((n : ℝ) - K) / n) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).const_sub 1
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    have h0 : Tendsto (fun n : ℕ =>
        (((Finset.range n).filter fun k => c (r + k * P) = true).card : ℝ) / n) atTop (𝓝 1) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlin tendsto_const_nhds ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with n hn
        have hsub : (Finset.range n).filter (fun k => K ≤ k) ⊆
            (Finset.range n).filter (fun k => c (r + k * P) = true) := fun k hk => by
          rw [Finset.mem_filter] at hk ⊢
          exact ⟨hk.1, hK k hk.2⟩
        have hcard : ((Finset.range n).filter (fun k => K ≤ k)).card = n - K := by
          rw [show (Finset.range n).filter (fun k => K ≤ k) = Finset.Ico K n by
            ext k; simp [Finset.mem_Ico, and_comm]]
          exact Nat.card_Ico K n
        have h4 := Finset.card_le_card hsub
        rw [hcard] at h4
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_div_iff_of_pos_right hn']
        have h5 : ((n - K : ℕ) : ℝ) ≤
            (((Finset.range n).filter fun k => c (r + k * P) = true).card : ℝ) := by
          exact_mod_cast h4
        have h3 : (n : ℝ) - K ≤ ((n - K : ℕ) : ℝ) := by
          rcases le_total K n with hKn | hKn
          · rw [Nat.cast_sub hKn]
          · rw [Nat.sub_eq_zero_of_le hKn]
            have : (n : ℝ) ≤ K := by exact_mod_cast hKn
            push_cast
            linarith
        linarith
      · filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_one hn']
        have := Finset.card_filter_le (Finset.range n) (fun k => c (r + k * P) = true)
        rw [Finset.card_range] at this
        exact_mod_cast this
    have := tendsto_nhds_unique h1 h0
    norm_num at this

end Rule30Equivalents.ProblemTwo
