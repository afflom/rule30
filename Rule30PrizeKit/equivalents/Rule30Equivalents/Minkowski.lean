module

public import Rule30Equivalents.Lagrange
public import Rule30Equivalents.WordForms
public import Rule30Equivalents.BinaryIrrational
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
# Problem 1 through Minkowski's question-mark function

Let `r₁, r₂, …` be the run lengths of the center column (OEIS A327983: 2, 1, 3, 2, 2, 3, 1, 1, …)
and `y = [0; 1, r₁, r₂, …] ≈ 0.7349760786`. By Denjoy's formula
`?([0; a₁, a₂, …]) = 0.0^(a₁ - 1) 1^(a₂) 0^(a₃) …₂` for Minkowski's function, `y = ?⁻¹(x₂)`, because
the center column starts with a black run. Mathlib has no `?`; `questionMark` defines it on the
irrationals of `(0, 1)` by the Denjoy–Salem series `?(x) = 2 ∑_{k ≥ 1} (-1)^(k+1) 2^-(a₁ + ⋯ + a_k)`
over the Gauss-map digits, and `questionMark_yMink` proves `?(y) = x₂`: the digits of `y` are
`1, r₁, r₂, …` (`digit_yMink`), and summing `x₂` run by run (the `k`-th run is black iff `k` is
even, `center_of_mem_run`) gives the same alternating series `∑ (-1)^k 2^-(r₁ + ⋯ + r_k)`
(`partial_sum_eq`).

* `problem1_iff_minkowski_not_quadratic`: Problem 1 holds iff `y` is not a quadratic
  irrational. `y` is the reciprocal of `[1; r₁, r₂, …]`, so it is a quadratic irrational iff that
  number is. By `Lagrange.quadratic_cfValue_iff` this happens iff the run lengths are eventually
  periodic, which by `WordForms.problem1_iff_run_lengths` is the negation of Problem 1.

Sources: H. Minkowski, *Zur Geometrie der Zahlen* (1904); A. Denjoy, *Sur une fonction réelle de
Minkowski*, J. Math. Pures Appl. 17 (1938) 105–151; R. Salem, *On some singular monotonic
functions which are strictly increasing*, Trans. AMS 53 (1943) 427–439.
-/

@[expose] public section

namespace Rule30Equivalents.Minkowski

open Ruliology.CellularAutomata
open Lagrange (cfValue quadratic_cfValue_iff one_le_cfValue)

/-- The run lengths `r₁, r₂, …` of the center column: the first run, then
`WordForms.runLength`. -/
noncomputable def runLen : ℕ → ℕ
  | 0 => Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) 0 + 1
  | k + 1 => WordForms.runLength k

theorem one_le_runLen : ∀ k, 1 ≤ runLen k
  | 0 => by simp [runLen]
  | k + 1 => by
    show 1 ≤ WordForms.runLength k
    rw [WordForms.runLength_eq]
    unfold WordForms.gap WordForms.trueTime
    have := Nat.nth_strictMono WordForms.infinite_changes (show k < k + 1 by omega)
    omega

/-- The digits `1, r₁, r₂, …` of `1 / y`. -/
noncomputable def yDigits (k : ℕ) : ℤ := if k = 0 then 1 else (runLen (k - 1) : ℤ)

theorem one_le_yDigits (k : ℕ) : 1 ≤ yDigits k := by
  unfold yDigits
  split_ifs
  · exact le_rfl
  · exact_mod_cast one_le_runLen (k - 1)

/-- `y = [0; 1, r₁, r₂, …]`, which is `?⁻¹(x₂)` by Denjoy's formula. -/
noncomputable def yMink : ℝ := (cfValue yDigits)⁻¹

theorem quadratic_inv_iff {X : ℝ} (hX : X ≠ 0) :
    (∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * X⁻¹ ^ 2 + B * X⁻¹ + C = 0) ↔
      ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * X ^ 2 + B * X + C = 0 := by
  constructor
  · rintro ⟨A, B, C, hne, h⟩
    refine ⟨C, B, A, fun h0 => hne ?_, ?_⟩
    · simp only [Prod.mk.injEq] at h0 ⊢
      exact ⟨h0.2.2, h0.2.1, h0.1⟩
    · have := congrArg (· * X ^ 2) h
      simp only [zero_mul] at this
      field_simp at this
      linear_combination this
  · rintro ⟨A, B, C, hne, h⟩
    refine ⟨C, B, A, fun h0 => hne ?_, ?_⟩
    · simp only [Prod.mk.injEq] at h0 ⊢
      exact ⟨h0.2.2, h0.2.1, h0.1⟩
    · have := congrArg (· * X⁻¹ ^ 2) h
      simp only [zero_mul] at this
      field_simp at this ⊢
      linear_combination this

/-- **Problem 1 ⟺ `y = ?⁻¹(x₂) = [0; 1, r₁, r₂, …]` is not a quadratic irrational**. -/
theorem problem1_iff_minkowski_not_quadratic : Rule30Prize.Problem1 ↔
    ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * yMink ^ 2 + B * yMink + C = 0 := by
  have hpos : cfValue yDigits ≠ 0 := by linarith [one_le_cfValue one_le_yDigits]
  unfold yMink
  rw [quadratic_inv_iff hpos, quadratic_cfValue_iff one_le_yDigits,
    WordForms.problem1_iff_run_lengths]
  refine not_congr ⟨fun ⟨T, P, hP, h⟩ => ⟨T + 2, P, hP, fun n hn => ?_⟩,
    fun ⟨K, T, hT, h⟩ => ⟨K, T, hT, fun k hk => ?_⟩⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have := h m (by omega)
    simp only [yDigits, show m + 2 + P ≠ 0 by omega, show m + 2 ≠ 0 by omega, ite_false,
      show m + 2 + P - 1 = (m + P) + 1 by omega, show m + 2 - 1 = m + 1 by omega, runLen, this]
  · have := h (k + 2) (by omega)
    simp only [yDigits, show k + 2 + T ≠ 0 by omega, show k + 2 ≠ 0 by omega, ite_false,
      show k + 2 + T - 1 = (k + T) + 1 by omega, show k + 2 - 1 = k + 1 by omega, runLen] at this
    exact_mod_cast this

/-! ### Minkowski's function and Denjoy's formula -/

/-- **Minkowski's question-mark function** on the irrationals of `(0, 1)`, by the Denjoy–Salem
formula: for `x = [0; a₁, a₂, …]`, `?(x) = 2 ∑_{k ≥ 1} (-1)^(k+1) 2^-(a₁ + ⋯ + a_k)`, with the
digits `aᵢ` of the Gauss map (`Lagrange.digit`). -/
noncomputable def questionMark (x : ℝ) : ℝ :=
  2 * ∑' k : ℕ, (-1 : ℝ) ^ k / 2 ^ (∑ i ∈ Finset.range (k + 1), (Lagrange.digit x (i + 1)).toNat)

/-- The digits of `y` are `1, r₁, r₂, …`. -/
theorem digit_yMink (n : ℕ) : Lagrange.digit yMink (n + 1) = yDigits n := by
  have h1 : 1 < cfValue yDigits := by
    rw [Lagrange.cfValue_eq one_le_yDigits]
    have := Lagrange.one_lt_cfValue_shift one_le_yDigits
    have h0 : (yDigits 0 : ℝ) = 1 := by simp [yDigits]
    rw [h0]
    have : 0 < (cfValue (Lagrange.shift yDigits 1))⁻¹ := inv_pos.2 (by linarith)
    linarith
  have hy0 : 0 ≤ yMink := (inv_pos.2 (by linarith)).le
  have hy1 : yMink < 1 := inv_lt_one_of_one_lt₀ h1
  have hg : Lagrange.gauss yMink = cfValue yDigits := by
    unfold Lagrange.gauss
    rw [Int.fract_eq_self.2 ⟨hy0, hy1⟩, yMink, inv_inv]
  rw [add_comm, Lagrange.digit_add, Lagrange.cq_succ, Lagrange.cq_zero, hg,
    Lagrange.digit_cfValue one_le_yDigits]

/-- The center column changes color after time `t`. -/
abbrev ChgAt (t : ℕ) : Prop := Rule30Prize.center t ≠ Rule30Prize.center (t + 1)

/-- The change points of the center column. -/
noncomputable def chg (k : ℕ) : ℕ := Nat.nth ChgAt k

theorem infinite_chg : (Set.ofPred ChgAt).Infinite := by
  convert WordForms.infinite_changes using 1
  ext t
  simp [TransformsSeeds.xorDeriv]

/-- `R_k = r₁ + ⋯ + r_k`, where the `k`-th run (from `0`) starts. -/
noncomputable def runStart (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, runLen j

theorem runStart_add_one (k : ℕ) : runStart (k + 1) = runStart k + runLen k :=
  Finset.sum_range_succ _ _

theorem runStart_succ (k : ℕ) : runStart (k + 1) = chg k + 1 := by
  induction k with
  | zero => simp [runStart, runLen, chg]
  | succ k ih =>
    rw [runStart_add_one, ih]
    show chg k + 1 + WordForms.runLength k = chg (k + 1) + 1
    have hlt : chg k < chg (k + 1) := Nat.nth_strictMono infinite_chg (Nat.lt_succ_self k)
    unfold WordForms.runLength
    rw [← chg, ← chg]
    omega

theorem le_runStart (k : ℕ) : k ≤ runStart k := by
  unfold runStart
  calc k = ∑ _j ∈ Finset.range k, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => one_le_runLen j

/-- The center column is black exactly when an even number of changes precede. -/
theorem center_eq_even (t : ℕ) : Rule30Prize.center t = decide (Even (Nat.count ChgAt t)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hc := Nat.count_succ ChgAt t
    by_cases h : ChgAt t
    · rw [ite_eq_left h] at hc
      have hct : Rule30Prize.center (t + 1) = !Rule30Prize.center t := by
        unfold ChgAt at h
        cases ht : Rule30Prize.center t <;> cases ht' : Rule30Prize.center (t + 1) <;> simp_all
      rw [hct, ih, hc]
      by_cases he : Even (Nat.count ChgAt t) <;> simp [he, Nat.even_add_one]
    · rw [ite_eq_right h, Nat.add_zero] at hc
      have hct : Rule30Prize.center (t + 1) = Rule30Prize.center t := by
        unfold ChgAt at h
        exact (not_not.1 h).symm
      rw [hct, ih, hc]
      simp

/-- On the `k`-th run the center column is black iff `k` is even. -/
theorem center_of_mem_run {k t : ℕ} (h1 : runStart k ≤ t) (h2 : t < runStart (k + 1)) :
    Rule30Prize.center t = decide (Even k) := by
  rw [center_eq_even]
  congr 2
  rw [runStart_succ] at h2
  have hup : Nat.count ChgAt t ≤ k := by
    have := Nat.count_monotone ChgAt (show t ≤ chg k by omega)
    rwa [chg, Nat.count_nth_of_infinite infinite_chg] at this
  have hdown : k ≤ Nat.count ChgAt t := by
    rcases k with _ | k
    · exact Nat.zero_le _
    · rw [runStart_succ] at h1
      have hm : ChgAt (chg k) := Nat.nth_mem_of_infinite infinite_chg k
      have := Nat.count_monotone ChgAt h1
      rwa [Nat.count_succ, ite_eq_left hm, chg, Nat.count_nth_of_infinite infinite_chg] at this
  omega

theorem sum_Ico_inv_two_pow {a b : ℕ} (h : a ≤ b) :
    ∑ t ∈ Finset.Ico a b, 1 / (2 : ℝ) ^ (t + 1) = 1 / 2 ^ a - 1 / 2 ^ b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    field_simp
    ring

/-- Partial sums of `x₂` up to the start of a run. -/
theorem partial_sum_eq (K : ℕ) :
    ∑ t ∈ Finset.range (runStart K), (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1) =
      ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k / 2 ^ runStart k -
        (if Even K then 0 else 1 / 2 ^ runStart K) := by
  induction K with
  | zero => simp [runStart]
  | succ K ih =>
    have hle : runStart K ≤ runStart (K + 1) := by
      rw [runStart_add_one]; omega
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle,
      ← Finset.range_eq_Ico, ih, Finset.sum_range_succ]
    have hblock : ∑ t ∈ Finset.Ico (runStart K) (runStart (K + 1)),
        (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1) =
        if Even K then 1 / 2 ^ runStart K - 1 / 2 ^ runStart (K + 1) else 0 := by
      rw [← sum_Ico_inv_two_pow hle]
      split_ifs with hK
      · refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_Ico] at ht
        rw [center_of_mem_run ht.1 ht.2, decide_eq_true hK, ite_eq_left rfl]
      · refine Finset.sum_eq_zero fun t ht => ?_
        rw [Finset.mem_Ico] at ht
        rw [center_of_mem_run ht.1 ht.2, decide_eq_false hK]
        simp
    rw [hblock]
    rcases Nat.even_or_odd K with hK | hK
    · rw [ite_eq_left hK, ite_eq_left hK, ite_eq_right (by simpa [Nat.even_add_one] using hK),
        hK.neg_one_pow]
      ring
    · rw [ite_eq_right (Nat.not_even_iff_odd.2 hK), ite_eq_right (Nat.not_even_iff_odd.2 hK),
        ite_eq_left (by simpa [Nat.even_add_one] using hK), hK.neg_one_pow]
      ring

/-- **Denjoy's formula for `y`**: `?(y) = x₂`, that is `y = ?⁻¹(x₂)`. -/
theorem questionMark_yMink : questionMark yMink = BinaryIrrational.centerBinary := by
  -- the digit sums are `1 + R_k`
  have hS : ∀ k, ∑ i ∈ Finset.range (k + 1), (Lagrange.digit yMink (i + 1)).toNat =
      runStart k + 1 := fun k => by
    rw [Finset.sum_range_succ', digit_yMink]
    simp only [digit_yMink, yDigits, Nat.add_sub_cancel, ite_eq_right (Nat.succ_ne_zero _),
      Int.toNat_natCast]
    rfl
  -- the alternating series `A = ∑ (-1)^k 2^-R_k`
  set g : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / 2 ^ runStart k
  have hg : Summable g := by
    refine Summable.of_norm_bounded (summable_geometric_two) fun k => ?_
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_pow, abs_two,
      one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (le_runStart k))
  have hq : questionMark yMink = ∑' k, g k := by
    unfold questionMark
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hS, pow_succ]
    simp only [g]
    field_simp
  rw [hq]
  -- `x₂` is the limit of the partial sums at the run starts
  set f : ℕ → ℝ := fun t => (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1)
  have hf : Summable f := by
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      (summable_geometric_two' 1)
    simp only [f]
    split_ifs <;> simp [div_eq_mul_inv, pow_succ]
  have hmono : StrictMono runStart := strictMono_nat_of_lt_succ fun k => by
    rw [runStart_add_one]
    have := one_le_runLen k
    omega
  have h1 : Filter.Tendsto (fun K => ∑ t ∈ Finset.range (runStart K), f t) Filter.atTop
      (nhds (∑' t, f t)) := hf.hasSum.tendsto_sum_nat.comp hmono.tendsto_atTop
  have h2 : Filter.Tendsto (fun K => ∑ k ∈ Finset.range K, g k -
      (if Even K then 0 else 1 / (2 : ℝ) ^ runStart K)) Filter.atTop (nhds (∑' k, g k - 0)) := by
    refine hg.hasSum.tendsto_sum_nat.sub ?_
    refine squeeze_zero_norm (a := fun K => (1 / 2 : ℝ) ^ K) (fun K => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    split_ifs
    · simp
    · show _ ≤ (1 / 2 : ℝ) ^ K
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div_pow]
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (le_runStart K))
  rw [sub_zero] at h2
  refine (tendsto_nhds_unique h1 ?_).symm
  refine h2.congr fun K => ?_
  exact (partial_sum_eq K).symm

end Rule30Equivalents.Minkowski
