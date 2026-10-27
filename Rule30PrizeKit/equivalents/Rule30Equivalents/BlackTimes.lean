module

public import Rule30Equivalents.ProblemTwo
public import Rule30Equivalents.WordForms
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
# Problem 2 through the times of the black cells

Let `τ k` be the time of the `k`-th black cell of a bit sequence
(`WordForms.trueTime`, Mathlib's `Nat.nth`) and `C n` the number of black cells before `n`
(Mathlib's `Nat.count`). They are inverse to each other (`Nat.gc_count_nth`), so a density `L > 0`
of black cells is the same as `τ k / k → 1 / L`:

* `tendsto_count_div_iff`: `C n / n → L` iff `τ k / k → L⁻¹`, for every `L > 0`, when there are
  infinitely many black cells. Along `n = τ k` the ratio `C n / n` is `k / τ k`; in between,
  `τ (k - 1) < n ≤ τ k` with `k = C n` squeezes it.
* `halfDensity_iff_trueTime`, `problem2_iff_trueTime`: **Problem 2 holds iff the `k`-th black cell
  of the center column occurs at time `2k + o(k)`**.
* `problem2_iff_mean_gap`: equivalently, the mean gap between consecutive black cells tends to `2`.
-/

@[expose] public section

namespace Rule30Equivalents.BlackTimes

open Filter Topology Finset Ruliology.CellularAutomata

/-- The number of `true` values before `n`, as a `Nat.count`. -/
theorem length_filter_eq_count (b : ℕ → Bool) (n : ℕ) :
    ((List.range n).filter b).length = Nat.count (fun t => b t = true) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Nat.count_succ]
    cases h : b n <;> simp [h]

/-- **Density through the times of the black cells**: if `p` holds infinitely often, the density
of `p` is `L > 0` iff its `k`-th occurrence is at time `k / L + o(k)`. -/
theorem tendsto_count_div_iff {p : ℕ → Prop} [DecidablePred p] (hinf : (Set.ofPred p).Infinite)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 L) ↔
      Tendsto (fun k : ℕ => (Nat.nth p k : ℝ) / k) atTop (𝓝 L⁻¹) := by
  have hmono : StrictMono (Nat.nth p) := Nat.nth_strictMono hinf
  have hnth : Tendsto (Nat.nth p) atTop atTop := hmono.tendsto_atTop
  constructor
  · intro h
    -- along `n = τ k` the ratio is `k / τ k`
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) / Nat.nth p k) atTop (𝓝 L) := by
      refine (h.comp hnth).congr fun k => ?_
      simp only [Function.comp, Nat.count_nth_of_infinite hinf]
    refine (h1.inv₀ hL.ne').congr fun k => ?_
    rw [inv_div]
  · intro h
    have hcount : Tendsto (Nat.count p) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun K => ⟨Nat.nth p K + 1, fun n hn => ?_⟩
      calc K ≤ K + 1 := Nat.le_succ K
        _ = Nat.count p (Nat.nth p K + 1) := (Nat.count_nth_succ_of_infinite hinf K).symm
        _ ≤ Nat.count p n := Nat.count_monotone p hn
    -- the lower bound `k / τ k`
    have hlow : Tendsto (fun k : ℕ => (k : ℝ) / Nat.nth p k) atTop (𝓝 L) := by
      have := h.inv₀ (inv_ne_zero hL.ne')
      rw [inv_inv] at this
      refine this.congr fun k => ?_
      rw [inv_div]
    -- the upper bound `(k + 1) / (τ k + 1)`
    have hup : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / ((Nat.nth p k : ℝ) + 1)) atTop (𝓝 L) := by
      have hτ : Tendsto (fun k : ℕ => ((Nat.nth p k : ℝ) + 1) / ((k : ℝ) + 1)) atTop
          (𝓝 L⁻¹) := by
        have hk1 : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 1) :=
          tendsto_natCast_div_add_atTop 1
        have hk2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have := (h.mul hk1).add hk2
        rw [mul_one, add_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        field_simp
      have := hτ.inv₀ (inv_ne_zero hL.ne')
      rw [inv_inv] at this
      refine this.congr fun k => ?_
      rw [inv_div]
    -- squeeze `C n / n` between them, with `k = C n`
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hcount)
      (hup.comp (tendsto_sub_atTop_nat 1 |>.comp hcount)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simp only [Function.comp]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hle : (n : ℝ) ≤ Nat.nth p (Nat.count p n) := by
        exact_mod_cast Nat.le_nth_count hinf n
      rcases Nat.eq_zero_or_pos (Nat.count p n) with h0 | h0
      · rw [h0]
        simp
      · have hτ0 : (0 : ℝ) < Nat.nth p (Nat.count p n) := lt_of_lt_of_le hn' hle
        rw [div_le_div_iff₀ hτ0 hn']
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    · filter_upwards [hcount.eventually_ge_atTop 1] with n hn
      simp only [Function.comp]
      have hlt : Nat.nth p (Nat.count p n - 1) < n :=
        Nat.nth_lt_of_lt_count (by omega)
      have hlt' : (Nat.nth p (Nat.count p n - 1) : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      have hk : ((Nat.count p n - 1 : ℕ) : ℝ) + 1 = Nat.count p n := by
        rw [Nat.cast_sub hn]
        push_cast
        ring
      rw [hk]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hlt'

/-- **Density `1/2` through the times of the `true` values**, for every bit sequence with
infinitely many `true` values: the `k`-th one is at time `2k + o(k)`. -/
theorem halfDensity_iff_trueTime {b : ℕ → Bool} (hinf : {t | b t = true}.Infinite) :
    Symmetry.HalfDensity b ↔
      Tendsto (fun k : ℕ => (WordForms.trueTime b k : ℝ) / k) atTop (𝓝 2) := by
  rw [ProblemTwo.halfDensity_iff_tendsto]
  simp only [length_filter_eq_count]
  rw [tendsto_count_div_iff hinf (by norm_num : (0 : ℝ) < 1 / 2), one_div, inv_inv]
  rfl

/-- **Problem 2 through the black cells**: Problem 2 holds iff the `k`-th black cell of the center
column occurs at time `2k + o(k)`. -/
theorem problem2_iff_trueTime : Rule30Prize.Problem2 ↔
    Tendsto (fun k : ℕ => (WordForms.trueTime c k : ℝ) / k) atTop (𝓝 2) :=
  halfDensity_iff_trueTime WordForms.infinite_black

/-- **Problem 2 through the gaps**: Problem 2 holds iff the mean gap between consecutive black
cells of the center column tends to `2`. -/
theorem problem2_iff_mean_gap : Rule30Prize.Problem2 ↔
    Tendsto (fun k : ℕ => (∑ j ∈ range k, (WordForms.gap c j : ℝ)) / k) atTop (𝓝 2) := by
  have hmono : StrictMono (WordForms.trueTime c) := Nat.nth_strictMono WordForms.infinite_black
  have hsum : ∀ k, ∑ j ∈ range k, (WordForms.gap c j : ℝ) =
      WordForms.trueTime c k - WordForms.trueTime c 0 := by
    intro k
    rw [← Finset.sum_range_sub (fun j => (WordForms.trueTime c j : ℝ))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WordForms.gap, Nat.cast_sub (hmono (Nat.lt_succ_self j)).le]
  rw [problem2_iff_trueTime]
  have h0 : Tendsto (fun k : ℕ => (WordForms.trueTime c 0 : ℝ) / k) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  constructor
  · intro h
    have := h.sub h0
    rw [sub_zero] at this
    refine this.congr fun k => ?_
    rw [hsum, sub_div]
  · intro h
    have := h.add h0
    rw [add_zero] at this
    refine this.congr fun k => ?_
    rw [hsum, sub_div, sub_add_cancel]

end Rule30Equivalents.BlackTimes
