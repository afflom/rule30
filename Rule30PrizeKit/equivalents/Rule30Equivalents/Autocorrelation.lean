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
# Autocorrelations of the center column

A bit sequence `b` disagrees with its shift by `τ` at the times `t` with `b t ≠ b (t + τ)`.

* `tendsto_disagreements_of_isNormal`: **in a normal sequence every lag `τ ≥ 1` has disagreement
  frequency exactly `1/2`**. The window `b t, …, b (t + τ)` is each word of length `τ + 1` with
  frequency `2^-(τ+1)`, and half of these words have different first and last letters
  (`card_firstLast_ne`).
* `far_from_periodic_of_isNormal`: so **a normal sequence differs from every periodic sequence at a
  quarter of the times or more**, in lower density. Where `b` agrees with a `P`-periodic `y` at
  both `t` and `t + P`, `b t = y t = y (t + P) = b (t + P)`; the disagreements at lag `P` force
  the disagreements with `y`.
* `ae_tendsto_disagreements_trace`, `ae_far_from_periodic_trace`: hence for almost every
  configuration the center column has disagreement frequency `1/2` at every lag, and stays at
  Besicovitch distance at least `1/4` from every periodic sequence. The same holds with the right
  half fixed, white as for the single seed, and only the left half random
  (`ae_tendsto_disagreements_trace_glue`). For the single seed both statements are open; each
  implies Problem 1 (`StrongerStatements.problem1_of_infinite_disagreements`,
  `StrongerStatements.problem1_of_far_from_periodic`, `ae_infinite_disagreements_trace`).
-/

@[expose] public section

namespace Rule30Equivalents.Autocorrelation

open Filter Topology MeasureTheory StrongerStatements RandomConfigurations Genericity

/-- The number of times `t < n` at which `b` disagrees with its shift by `τ`. -/
def disagreements (b : ℕ → Bool) (τ n : ℕ) : ℕ :=
  ((Finset.range n).filter fun t => b t ≠ b (t + τ)).card

/-- **Half of the words of length `τ + 1` have different first and last letters**: flipping the last
letter exchanges them with the others. -/
theorem card_firstLast_ne (τ : ℕ) (hτ : 0 < τ) :
    (Finset.univ.filter fun w : Fin (τ + 1) → Bool => w 0 ≠ w (Fin.last τ)).card = 2 ^ τ := by
  classical
  have hlast : (0 : Fin (τ + 1)) ≠ Fin.last τ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  let flip : (Fin (τ + 1) → Bool) → (Fin (τ + 1) → Bool) := fun w =>
    Function.update w (Fin.last τ) (!w (Fin.last τ))
  have hflip0 : ∀ w, flip w 0 = w 0 := fun w => Function.update_of_ne hlast _ _
  have hflipl : ∀ w, flip w (Fin.last τ) = !w (Fin.last τ) := fun w => Function.update_self _ _ _
  have hinv : ∀ w, flip (flip w) = w := fun w => by
    funext j
    by_cases hj : j = Fin.last τ
    · subst hj
      rw [hflipl, hflipl, Bool.not_not]
    · simp only [flip, Function.update_of_ne hj]
  have hcard : (Finset.univ.filter fun w : Fin (τ + 1) → Bool => w 0 ≠ w (Fin.last τ)).card =
      (Finset.univ.filter fun w : Fin (τ + 1) → Bool => ¬ w 0 ≠ w (Fin.last τ)).card := by
    refine Finset.card_nbij' flip flip (fun w hw => ?_) (fun w hw => ?_) (fun w _ => hinv w)
      (fun w _ => hinv w)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      rw [hflip0, hflipl]
      cases h0 : w 0 <;> cases hl : w (Fin.last τ) <;> simp_all
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      rw [hflip0, hflipl]
      cases h0 : w 0 <;> cases hl : w (Fin.last τ) <;> simp_all
  have htotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (τ + 1) → Bool))) fun w => w 0 ≠ w (Fin.last τ)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ] at htotal
  omega

/-- **Disagreements of a normal sequence**: at every lag `τ ≥ 1` the frequency of the times with
`b t ≠ b (t + τ)` is `1/2`. -/
theorem tendsto_disagreements_of_isNormal {b : ℕ → Bool} (hb : IsNormal b) {τ : ℕ} (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => (disagreements b τ n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  classical
  set D := Finset.univ.filter fun w : Fin (τ + 1) → Bool => w 0 ≠ w (Fin.last τ) with hD
  -- the disagreements split by the window `b t, …, b (t + τ)`
  have hsplit : ∀ n, (disagreements b τ n : ℝ) / n = ∑ w ∈ D,
      (((Finset.range n).filter fun i => ∀ j : Fin (τ + 1), b (i + j) = w j).card : ℝ) / n := by
    intro n
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.range n).filter fun t => b t ≠ b (t + τ)) (t := D)
      (f := fun t (j : Fin (τ + 1)) => b (t + j)) (by
        intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht
        simp only [hD, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using ht.2)
    rw [← Finset.sum_div, disagreements, hfib]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    congr 2
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, funext_iff]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      have h0 := h.2 0
      have hl := h.2 (Fin.last τ)
      simp only [Fin.val_zero, add_zero, Fin.val_last] at h0 hl
      rw [h0, hl]
      exact (Finset.mem_filter.1 hw).2
  have hlim := tendsto_finsetSum D fun w _ => hb (τ + 1) w
  rw [Finset.sum_const, card_firstLast_ne τ hτ, nsmul_eq_mul] at hlim
  have h12 : ((2 ^ τ : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (τ + 1) = 1 / 2 := by
    push_cast
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, one_mul,
      one_div]
  rw [h12] at hlim
  exact hlim.congr fun n => (hsplit n).symm

/-- A set of naturals whose counting frequency tends to a positive limit is infinite. -/
theorem infinite_of_tendsto_pos {p : ℕ → Prop} [DecidablePred p] {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun n : ℕ => (((Finset.range n).filter p).card : ℝ) / n) atTop (𝓝 a)) :
    {t | p t}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  -- the count stays at most `M + 1`, so the frequency tends to `0`
  have hle : ∀ n, (((Finset.range n).filter p).card : ℝ) ≤ M + 1 := fun n => by
    have : ((Finset.range n).filter p) ⊆ Finset.range (M + 1) := fun t ht => by
      simp only [Finset.mem_filter] at ht
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (hM ht.2))
    exact_mod_cast (Finset.card_le_card this).trans (by simp)
  have h0 : Tendsto (fun n : ℕ => (((Finset.range n).filter p).card : ℝ) / n) atTop (𝓝 0) :=
    squeeze_zero (fun n => by positivity) (fun n => div_le_div_of_nonneg_right (hle n)
      (Nat.cast_nonneg n)) (tendsto_const_div_atTop_nhds_zero_nat _)
  exact ha.ne' (tendsto_nhds_unique h h0)

/-- **A normal sequence differs from every periodic sequence at a quarter of the times or more**,
in lower density: for every `ε > 0`, eventually `#{t < n | b t ≠ y t} ≥ (1/4 - ε) n`. -/
theorem far_from_periodic_of_isNormal {b : ℕ → Bool} (hb : IsNormal b) {y : ℕ → Bool} {P : ℕ}
    (hP : 0 < P) (hy : ∀ t, y (t + P) = y t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 / 4 - ε) * n ≤ ((Finset.range n).filter fun t => b t ≠ y t).card := by
  classical
  let E : ℕ → ℕ := fun n => ((Finset.range n).filter fun t => b t ≠ y t).card
  -- a disagreement at lag `P` is a disagreement with `y` at `t` or at `t + P`
  have hD : ∀ n, disagreements b P n ≤ 2 * E n + P := fun n => by
    have h1 : (Finset.range n).filter (fun t => b t ≠ b (t + P)) ⊆
        (Finset.range n).filter (fun t => b t ≠ y t) ∪
          (Finset.range n).filter (fun t => b (t + P) ≠ y (t + P)) := fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      by_contra hcon
      push Not at hcon
      exact ht.2 (by rw [hcon.1 ht.1, ← hy t, hcon.2 ht.1])
    have h2 : ((Finset.range n).filter (fun t => b (t + P) ≠ y (t + P))).card ≤ E (n + P) := by
      refine Finset.card_le_card_of_injOn (· + P) (fun t ht => ?_)
        (fun _ _ _ _ h => Nat.add_right_cancel h)
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht ⊢
      exact ⟨by omega, ht.2⟩
    have h3 : E (n + P) ≤ E n + P := by
      have : (Finset.range (n + P)).filter (fun t => b t ≠ y t) ⊆
          (Finset.range n).filter (fun t => b t ≠ y t) ∪ Finset.Ico n (n + P) := fun t ht => by
        simp only [Finset.mem_filter, Finset.mem_range] at ht
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        by_cases htn : t < n
        · exact Or.inl ⟨htn, ht.2⟩
        · exact Or.inr ⟨not_lt.1 htn, ht.1⟩
      refine (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans ?_)
      simp [E]
    have h4 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
    simp only [E] at h2 h3
    simp only [disagreements, E]
    omega
  -- the frequency of the disagreements at lag `P` tends to `1/2`
  have hev := (tendsto_disagreements_of_isNormal hb hP).eventually (lt_mem_nhds
    (show 1 / 2 - ε < 1 / 2 by linarith))
  filter_upwards [hev, eventually_ge_atTop (⌈(P : ℝ) / ε⌉₊ + 1)] with n hn hn'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnP : (P : ℝ) / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : _ ≤ n))
  have hPn : (P : ℝ) ≤ ε * n := by rwa [div_le_iff₀ hε, mul_comm] at hnP
  rw [lt_div_iff₀ hnpos] at hn
  have hDn : (disagreements b P n : ℝ) ≤ 2 * E n + P := by exact_mod_cast hD n
  show (1 / 4 - ε) * n ≤ (E n : ℝ)
  nlinarith

/-! ### The center column of a random configuration -/

/-- **For almost every configuration the center column disagrees with each of its shifts half of
the time.** -/
theorem ae_tendsto_disagreements_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ τ, 0 < τ →
      Tendsto (fun n : ℕ => (disagreements (trace x) τ n : ℝ) / n) atTop (𝓝 (1 / 2)) :=
  ae_isNormal_trace.mono fun _ hx _ hτ => tendsto_disagreements_of_isNormal hx hτ

/-- The same with the right half fixed (white, as for the single seed, or any other) and only the
left half random. -/
theorem ae_tendsto_disagreements_trace_glue (R : ℤ → Bool) :
    ∀ᵐ x ∂(coins ℤ), ∀ τ, 0 < τ →
      Tendsto (fun n : ℕ => (disagreements (trace (glue R x)) τ n : ℝ) / n) atTop (𝓝 (1 / 2)) :=
  (ae_isNormal_trace_glue R).mono fun _ hx _ hτ => tendsto_disagreements_of_isNormal hx hτ

/-- **For almost every configuration the center column stays at Besicovitch distance at least
`1/4` from every periodic sequence.** -/
theorem ae_far_from_periodic_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ (y : ℕ → Bool) (P : ℕ), 0 < P → (∀ t, y (t + P) = y t) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (1 / 4 - ε) * n ≤ ((Finset.range n).filter fun t => trace x t ≠ y t).card :=
  ae_isNormal_trace.mono fun _ hx _ _ hP hy _ hε => far_from_periodic_of_isNormal hx hP hy hε

/-- So the hypothesis of `StrongerStatements.problem1_of_infinite_disagreements` holds for almost
every configuration. -/
theorem ae_infinite_disagreements_trace :
    ∀ᵐ x ∂(coins ℤ), ∀ τ, 0 < τ → {t | trace x t ≠ trace x (t + τ)}.Infinite :=
  ae_tendsto_disagreements_trace.mono fun _ hx τ hτ =>
    infinite_of_tendsto_pos (by norm_num : (0 : ℝ) < 1 / 2) (hx τ hτ)

end Rule30Equivalents.Autocorrelation
