module

public import Rule30Equivalents.Typicality
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
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
# The irrationality exponent of a random center column

The stronger statement "`μ(x₂) = 2`": `x₂ = 0.c(0)c(1)…₂` is irrational and is `p`-Liouville for
no `p > 2` (`ExponentTwo`), that is, for every `p > 2` and `C` only finitely many `n` have an
integer `m` with `0 < |x₂ - m/n| < C/n^p`. It implies Problem 1 (`problem1_of_exponentTwo`), and
together with Dirichlet's theorem (`StrongerStatements.irrExponentGE_two_of_irrational`) it pins
the irrationality exponent at `2`.

* `ae_exponentTwo_trace`: **for almost every configuration the center column satisfies it**, as
  Khinchin's theorem predicts for almost every real number.

The value of the first `k` binary digits is `⌊2ᵏ x₂⌋` or `2ᵏ x₂ - 1` (`pow_mul_baseValue`), and
it determines those digits (`eq_of_lead_eq`), so each of its values has probability at most
`2⁻ᵏ` (`measure_lead_eq_le`). Hence `x₂` lies within `ℓ` of a given point with probability at most
`8ℓ` (`measureReal_abs_sub_lt_le`): a bounded density, without computing the law of `x₂`. For
`n > C + 1` an integer `m` with `|x₂ - m/n| < C/n^p` lies in `[0, n]`, so such an `m` exists with
probability at most `16C n^(1-p)`, summable for `p > 2`, and the Borel–Cantelli lemma applies
(`ae_not_frequently_approx`).
-/

@[expose] public section

namespace Rule30Equivalents.IrrationalityExponent

open MeasureTheory Filter Topology Ruliology.CellularAutomata Genericity RandomConfigurations
  BinaryIrrational

/-- **The irrationality exponent is `2`**: `x` is irrational and is `p`-Liouville for no
`p > 2`. -/
def ExponentTwo (x : ℝ) : Prop := Irrational x ∧ ∀ p > (2 : ℝ), ¬ LiouvilleWith p x

/-- `μ(x₂) = 2` implies Problem 1, through the irrationality of `x₂`. -/
theorem problem1_of_exponentTwo (h : ExponentTwo centerBinary) : Rule30Prize.Problem1 :=
  problem1_iff_irrational_binary.2 h.1

/-- The numeral of the first `k` binary digits determines them. -/
theorem eq_of_lead_eq {b b' : ℕ → Bool} :
    ∀ {k : ℕ}, lead 2 b k = lead 2 b' k → ∀ t < k, b t = b' t
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | k + 1, h, t, ht => by
    simp only [lead] at h
    have hd : (if b k then 1 else 0 : ℕ) = if b' k then 1 else 0 := by
      have h1 : (if b k then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
      have h2 : (if b' k then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
      omega
    have hk : b k = b' k := by
      by_contra hne
      cases hb : b k <;> cases hb' : b' k <;> simp_all
    have h' : lead 2 b k = lead 2 b' k := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | rfl
    · exact eq_of_lead_eq h' t ht'
    · exact hk

/-- Each value of the numeral of the first `k` digits has probability at most `2⁻ᵏ`. -/
theorem measure_lead_eq_le (k j : ℕ) : coins ℕ {v | lead 2 v k = j} ≤ 2⁻¹ ^ k := by
  by_cases hne : ∃ w : ℕ → Bool, lead 2 w k = j
  · obtain ⟨w, hw⟩ := hne
    calc coins ℕ {v | lead 2 v k = j}
        ≤ coins ℕ (Set.pi (Finset.range k : Set ℕ) fun t => {w t}) := measure_mono fun v hv => by
          simp only [Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff]
          exact fun t ht => eq_of_lead_eq (hv.trans hw.symm) t ht
      _ = 2⁻¹ ^ k := by
          rw [coins_pi, Finset.prod_congr rfl fun t _ => coin_singleton (w t), Finset.prod_const,
            Finset.card_range]
  · have : {v : ℕ → Bool | lead 2 v k = j} = ∅ :=
      Set.eq_empty_of_forall_notMem fun v hv => hne ⟨v, hv⟩
    rw [this, measure_empty]
    exact zero_le

/-- **`x₂` has a bounded density**: it lies within `ℓ` of a given point with probability at most
`8ℓ`, for `0 < ℓ ≤ 1/2`. With `2ᵏ ≤ 1/(2ℓ) < 2ᵏ⁺¹`, `2ᵏ x₂` is the numeral of the first `k`
digits plus a number in `[0, 1]` and lies within `1/2` of `2ᵏ y`, so the numeral takes one of
two values. -/
theorem measureReal_abs_sub_lt_le (y : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 2) :
    (coins ℕ).real {v | |baseValue 2 v - y| < ℓ} ≤ 8 * ℓ := by
  set k := Nat.log 2 ⌊1 / (2 * ℓ)⌋₊ with hk
  have h1 : (1 : ℝ) ≤ 1 / (2 * ℓ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hfl : 1 ≤ ⌊1 / (2 * ℓ)⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hpow : 2 ^ k ≤ ⌊1 / (2 * ℓ)⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have hlt : ⌊1 / (2 * ℓ)⌋₊ < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk1 : (2 : ℝ) ^ k * (2 * ℓ) ≤ 1 := by
    have : ((2 ^ k : ℕ) : ℝ) ≤ 1 / (2 * ℓ) :=
      (Nat.cast_le.2 hpow).trans (Nat.floor_le (by positivity))
    push_cast at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hk2 : 1 < (2 : ℝ) ^ (k + 1) * (2 * ℓ) := by
    have h3 : 1 / (2 * ℓ) < ((2 ^ (k + 1) : ℕ) : ℝ) :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hlt)
    push_cast at h3
    rwa [div_lt_iff₀ (by positivity)] at h3
  -- the numeral of the first `k` digits lies in `[a, a + 1]`
  set c := (2 : ℝ) ^ k * y with hc
  set a := ⌈c - 3 / 2⌉₊ with ha
  have hsub : {v | |baseValue 2 v - y| < ℓ} ⊆
      ⋃ j ∈ Finset.Icc a (a + 1), {v : ℕ → Bool | lead 2 v k = j} := by
    intro v hv
    simp only [Set.mem_ofPred_eq, abs_lt] at hv
    obtain ⟨hv1, hv2⟩ := hv
    have hpm := pow_mul_baseValue (le_refl 2) v k
    simp only [Nat.cast_ofNat] at hpm
    have hr0 := baseValue_nonneg (le_refl 2) (tail v k)
    have hr1 := baseValue_le_one (le_refl 2) (tail v k)
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hx1 : (2 : ℝ) ^ k * baseValue 2 v < c + 1 / 2 := by
      have := mul_lt_mul_of_pos_left (show baseValue 2 v < y + ℓ by linarith) h2k
      nlinarith
    have hx2 : c - 1 / 2 < (2 : ℝ) ^ k * baseValue 2 v := by
      have := mul_lt_mul_of_pos_left (show y - ℓ < baseValue 2 v by linarith) h2k
      nlinarith
    have hJ1 : c - 3 / 2 < ((lead 2 v k : ℕ) : ℝ) := by linarith
    have hJ2 : ((lead 2 v k : ℕ) : ℝ) < c + 1 / 2 := by linarith
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc, exists_prop]
    refine ⟨lead 2 v k, ⟨Nat.ceil_le.2 hJ1.le, ?_⟩, rfl⟩
    have h4 : ((lead 2 v k : ℕ) : ℝ) < a + 2 := by
      have := Nat.le_ceil (c - 3 / 2)
      linarith
    have h5 : lead 2 v k < a + 2 := by exact_mod_cast h4
    omega
  have hj : ∀ j, (coins ℕ).real {v : ℕ → Bool | lead 2 v k = j} ≤ (2⁻¹ : ℝ) ^ k := fun j => by
    rw [measureReal_def]
    calc (coins ℕ {v | lead 2 v k = j}).toReal ≤ ((2⁻¹ : ENNReal) ^ k).toReal :=
          ENNReal.toReal_mono (by simp) (measure_lead_eq_le k j)
      _ = (2⁻¹ : ℝ) ^ k := by simp
  calc (coins ℕ).real {v | |baseValue 2 v - y| < ℓ}
      ≤ (coins ℕ).real (⋃ j ∈ Finset.Icc a (a + 1), {v : ℕ → Bool | lead 2 v k = j}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.Icc a (a + 1), (coins ℕ).real {v : ℕ → Bool | lead 2 v k = j} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.Icc a (a + 1), (2⁻¹ : ℝ) ^ k := Finset.sum_le_sum fun j _ => hj j
    _ = 2 * (2⁻¹ : ℝ) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, show a + 1 + 1 - a = 2 by omega, nsmul_eq_mul]
        norm_num
    _ ≤ 8 * ℓ := by
        have h2k : (2⁻¹ : ℝ) ^ k * 2 ^ k = 1 := by
          rw [← mul_pow]
          norm_num
        have hpos : (0 : ℝ) < (2⁻¹ : ℝ) ^ k := by positivity
        rw [pow_succ] at hk2
        nlinarith

/-- **Borel–Cantelli for approximations of order `p > 2`**: for almost every fair-coin sequence
and every `C`, only finitely many `n` have an integer `m` with `|x₂ - m/n| < C/n^p`. For
`n ≥ C + 2` such an `m` lies in `[0, n]`, so it exists with probability at most
`(n + 1) 8C/n^p ≤ 16C n^(1-p)`, summable for `p > 2`. -/
theorem ae_not_frequently_approx {p : ℝ} (hp : 2 < p) (C : ℕ) :
    ∀ᵐ v ∂(coins ℕ), ¬ ∃ᶠ n : ℕ in atTop, ∃ m : ℤ,
      |baseValue 2 v - m / n| < C / (n : ℝ) ^ p := by
  set E : ℕ → Set (ℕ → Bool) := fun i => {v | ∃ m : ℤ,
    |baseValue 2 v - m / ((i + (C + 2) : ℕ) : ℝ)| < C / ((i + (C + 2) : ℕ) : ℝ) ^ p} with hE
  have hbound : ∀ i, (coins ℕ).real (E i) ≤
      16 * C * ((((i + (C + 2) : ℕ) : ℝ)) ^ (p - 1))⁻¹ := by
    intro i
    set n : ℕ := i + (C + 2) with hn
    have hn2 : (C : ℝ) + 2 ≤ n := by
      rw [hn]
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hn0 : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
    have hnp : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ p :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]) hp.le
    rw [Real.rpow_two] at hnp
    have hnp0 : (0 : ℝ) < (n : ℝ) ^ p := by positivity
    rcases Nat.eq_zero_or_pos C with hC0 | hCpos
    · have : E i = ∅ := Set.eq_empty_of_forall_notMem fun v ⟨m, hm⟩ => by
        rw [hC0, Nat.cast_zero, zero_div] at hm
        exact (abs_nonneg _).not_gt hm
      rw [this, measureReal_empty]
      positivity
    have hCR : (0 : ℝ) < C := by exact_mod_cast hCpos
    set ℓ : ℝ := C / (n : ℝ) ^ p with hℓ
    have hℓ0 : 0 < ℓ := by positivity
    -- `ℓ < 1/n ≤ 1/2`
    have hℓn : ℓ < 1 / n := by
      rw [hℓ, div_lt_div_iff₀ hnp0 hn0, one_mul]
      nlinarith
    have hℓ1 : ℓ ≤ 1 / 2 := by
      have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    -- the candidates `m = 0, …, n`
    have hsub : E i ⊆ ⋃ j ∈ Finset.range (n + 1),
        {v : ℕ → Bool | |baseValue 2 v - (j : ℝ) / n| < ℓ} := by
      intro v ⟨m, hm⟩
      have hx0 := baseValue_nonneg (le_refl 2) v
      have hx1 := baseValue_le_one (le_refl 2) v
      rw [abs_lt] at hm
      have h1' : (-1 : ℝ) < m :=
        (div_lt_div_iff_of_pos_right hn0).1 (show -1 / (n : ℝ) < m / n by
          rw [neg_div]
          linarith [hm.2])
      have h2' : (m : ℝ) < n + 1 :=
        (div_lt_div_iff_of_pos_right hn0).1 (show (m : ℝ) / n < (n + 1) / n by
          rw [add_div, div_self hn0.ne']
          linarith [hm.1])
      have hm0 : 0 ≤ m := by
        have : (-1 : ℤ) < m := by exact_mod_cast h1'
        omega
      have hmn : m ≤ n := by
        have : m < (n : ℤ) + 1 := by exact_mod_cast h2'
        omega
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, exists_prop]
      refine ⟨m.toNat, by omega, ?_⟩
      have : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
      rw [this, abs_lt]
      exact ⟨hm.1, hm.2⟩
    calc (coins ℕ).real (E i)
        ≤ (coins ℕ).real (⋃ j ∈ Finset.range (n + 1),
            {v : ℕ → Bool | |baseValue 2 v - (j : ℝ) / n| < ℓ}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            (coins ℕ).real {v : ℕ → Bool | |baseValue 2 v - (j : ℝ) / n| < ℓ} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1), 8 * ℓ :=
          Finset.sum_le_sum fun j _ => measureReal_abs_sub_lt_le _ hℓ0 hℓ1
      _ = (n + 1) * (8 * ℓ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 16 * C * ((n : ℝ) ^ (p - 1))⁻¹ := by
          have hrp : ((n : ℝ) ^ (p - 1))⁻¹ = n / (n : ℝ) ^ p := by
            rw [Real.rpow_sub hn0, Real.rpow_one, inv_div]
          rw [hrp, hℓ]
          have h1 : ((n : ℝ) + 1) * (8 * (C / (n : ℝ) ^ p)) = 8 * C * ((n + 1) / (n : ℝ) ^ p) := by
            ring
          have h2 : ((n : ℝ) + 1) / (n : ℝ) ^ p ≤ 2 * (n / (n : ℝ) ^ p) := by
            rw [← mul_div_assoc]
            exact div_le_div_of_nonneg_right (by linarith) hnp0.le
          nlinarith
  have hsum : ∑' i, coins ℕ (E i) ≠ ⊤ := by
    have hsumm : Summable fun i : ℕ => 16 * C * ((((i + (C + 2) : ℕ) : ℝ)) ^ (p - 1))⁻¹ :=
      ((summable_nat_add_iff (C + 2)).2 (Real.summable_nat_rpow_inv.2 (by linarith))).mul_left _
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' i : ℕ, 16 * C * ((((i + (C + 2) : ℕ) : ℝ)) ^ (p - 1))⁻¹)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hbound i)
  filter_upwards [ae_eventually_notMem hsum] with v hv hfr
  obtain ⟨I, hI⟩ := eventually_atTop.1 hv
  obtain ⟨n, hn, m, hm⟩ := frequently_atTop.1 hfr (I + (C + 2))
  have hn' : n - (C + 2) + (C + 2) = n := by omega
  refine hI (n - (C + 2)) (by omega) ⟨m, ?_⟩
  rw [hn']
  exact hm

/-- For almost every fair-coin sequence, `x₂ = 0.v(0)v(1)…₂` is `p`-Liouville for no `p > 2`. -/
theorem ae_not_liouvilleWith {p : ℝ} (hp : 2 < p) :
    ∀ᵐ v ∂(coins ℕ), ¬ LiouvilleWith p (baseValue 2 v) := by
  filter_upwards [ae_all_iff.2 (ae_not_frequently_approx hp)] with v hv
  rintro ⟨C, hC⟩
  refine hv ⌈C⌉₊ (hC.mono fun n hn => ?_)
  obtain ⟨m, -, hm⟩ := hn
  refine ⟨m, hm.trans_le ?_⟩
  gcongr
  exact Nat.le_ceil C

/-- **For almost every fair-coin sequence `μ(x₂) = 2`**: `x₂` is transcendental, hence irrational
(`Typicality.ae_transcendental_baseValue`), and `p`-Liouville for no `p > 2`
(`ae_not_liouvilleWith` for `p = 2 + 1/(k + 1)`). -/
theorem ae_exponentTwo : ∀ᵐ v ∂(coins ℕ), ExponentTwo (baseValue 2 v) := by
  have h := ae_all_iff.2 fun k : ℕ => ae_not_liouvilleWith (p := 2 + 1 / ((k : ℝ) + 1)) (by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith)
  filter_upwards [h, Typicality.ae_transcendental_baseValue le_rfl] with v hv htr
  refine ⟨htr.irrational, fun p hp hL => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hp)
  exact hv k (hL.mono (by linarith))

/-- **For almost every configuration the center column has `μ(x₂) = 2`.** -/
theorem ae_exponentTwo_trace : ∀ᵐ x ∂(coins ℤ), ExponentTwo (baseValue 2 (trace x)) :=
  measurePreserving_trace.quasiMeasurePreserving.ae ae_exponentTwo

end Rule30Equivalents.IrrationalityExponent
