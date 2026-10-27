module

public import Rule30Equivalents.UniformMorphic
public import Rule30Equivalents.PerronFrobenius
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Substitutive sequences

A substitution `σ` of a finite alphabet maps each letter to a nonempty word. If `σ(a) = a u` with
`u` nonempty, the words `σⁿ(a)` are prefixes of each other and converge to a fixed point
`x = σ^ω(a)`: `σ(x 0) σ(x 1) ⋯ = x` (`IsFixedPoint`). A sequence `f` is `α`-substitutive
(`IsSubstitutive`) if `f = φ ∘ x` for a coding `φ` and such a fixed point `x` in which every letter
occurs, where `α` is the dominant eigenvalue (`IsDominantEigenvalue`) of the incidence matrix
`M b c = |σ(b)|_c` (`incidence`).

* `isSubstitutive_of_isUniformMorphic`: a fixed point of a `k`-uniform morphism is
  `k`-substitutive, since its incidence matrix has row sums `k` and so dominant eigenvalue `k`
  (`isDominantEigenvalue_of_sum_eq`).
* `isSubstitutive_of_eventuallyPeriodic`: an eventually periodic sequence is `k`-automatic, hence
  `k`-uniformly morphic and `k`-substitutive, for every `k ≥ 2`.
* `problem1_of_not_substitutive`: if the center column is not both `a`- and `b`-substitutive for
  some `a, b ≥ 2`, Problem 1 holds.

Durand's theorem says that for multiplicatively independent Perron numbers `α` and `β`
(`IsPerron`), a sequence is both `α`- and `β`-substitutive iff it is eventually periodic. The
integers `k ≥ 2` are Perron numbers (`isPerron_natCast`), and a primitive incidence matrix has its
Perron root as dominant eigenvalue (`isDominantEigenvalue_of_isPrimitive`).

Sources: F. Durand, *Cobham's theorem for substitutions*, J. Eur. Math. Soc. 13 (2011) 1799–1814;
A. Cobham, *Uniform tag sequences*, Math. Systems Theory 6 (1972) 164–192.
-/

@[expose] public section

namespace Rule30Equivalents.Substitutive

open Ruliology.CellularAutomata Matrix

variable {A : Type*}

/-- The start of the `n`-th block of `σ(x 0) σ(x 1) ⋯`. -/
def start (σ : A → List A) (x : ℕ → A) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (σ (x i)).length

/-- `x` is a fixed point of the substitution `σ`: `σ(x 0) σ(x 1) ⋯ = x`. -/
def IsFixedPoint (σ : A → List A) (x : ℕ → A) : Prop :=
  ∀ n d (hd : d < (σ (x n)).length), x (start σ x n + d) = (σ (x n))[d]

/-- The incidence matrix of `σ`: `M b c = |σ(b)|_c`, the number of occurrences of `c` in `σ(b)`. -/
def incidence [DecidableEq A] (σ : A → List A) : Matrix A A ℝ :=
  Matrix.of fun b c => ((σ b).count c : ℝ)

/-- `α` is the dominant eigenvalue of the real matrix `M`: an eigenvalue of `M`, and at least the
modulus of every complex eigenvalue. -/
def IsDominantEigenvalue [Fintype A] (M : Matrix A A ℝ) (α : ℝ) : Prop :=
  (∃ u : A → ℝ, u ≠ 0 ∧ M *ᵥ u = α • u) ∧
    ∀ (μ : ℂ) (u : A → ℂ), u ≠ 0 → M.map ((↑) : ℝ → ℂ) *ᵥ u = μ • u → ‖μ‖ ≤ α

/-- `f` is `α`-substitutive: `f = φ ∘ x` for a coding `φ` and the fixed point `x = σ^ω(x 0)` of a
substitution `σ` with nonempty images, prolongable on `x 0` (`σ(x 0) = x 0 u` with `u` nonempty),
in which every letter occurs, and `α` is the dominant eigenvalue of the incidence matrix of `σ`. -/
def IsSubstitutive (α : ℝ) (f : ℕ → Bool) : Prop :=
  ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B) (σ : B → List B) (x : ℕ → B) (φ : B → Bool),
    (∀ b, σ b ≠ []) ∧ 1 < (σ (x 0)).length ∧ IsFixedPoint σ x ∧ (∀ b, ∃ n, x n = b) ∧
      IsDominantEigenvalue (incidence σ) α ∧ ∀ n, f n = φ (x n)

/-- A Perron number: a real algebraic integer `α > 1` that exceeds the modulus of each of its other
conjugates. -/
def IsPerron (α : ℝ) : Prop :=
  1 < α ∧ IsIntegral ℤ α ∧ ∀ z : ℂ, Polynomial.aeval z (minpoly ℤ α) = 0 → z ≠ α → ‖z‖ < α

theorem sum_count_eq_length [Fintype A] [DecidableEq A] (l : List A) :
    ∑ c, l.count c = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, ← ih]
    simp [List.count_cons, Finset.sum_add_distrib]

theorem sum_incidence [Fintype A] [DecidableEq A] (σ : A → List A) (b : A) :
    ∑ c, incidence σ b c = (σ b).length := by
  simp only [incidence, of_apply]
  exact_mod_cast sum_count_eq_length (σ b)

/-- **Equal row sums**: a nonnegative matrix whose rows all sum to `k` has dominant eigenvalue `k`,
with eigenvector `(1, …, 1)`; for an eigenvector `u` of `μ`, the row at the largest `‖u a‖` gives
`‖μ‖ ‖u a‖ ≤ k ‖u a‖`. -/
theorem isDominantEigenvalue_of_sum_eq [Fintype A] [Nonempty A] {M : Matrix A A ℝ}
    (hM : ∀ a b, 0 ≤ M a b) {k : ℝ} (hrow : ∀ a, ∑ b, M a b = k) : IsDominantEigenvalue M k := by
  refine ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h (Classical.arbitrary A)), ?_⟩, ?_⟩
  · funext a
    simp [mulVec, dotProduct, hrow]
  · intro μ u hu h
    obtain ⟨a, ha⟩ := Finite.exists_max fun b => ‖u b‖
    have hua : 0 < ‖u a‖ := by
      obtain ⟨b, hb⟩ := Function.ne_iff.1 hu
      exact lt_of_lt_of_le (norm_pos_iff.2 hb) (ha b)
    have e : ∑ b, (M a b : ℂ) * u b = μ * u a := by
      simpa [mulVec, dotProduct] using congrFun h a
    have h1 : ‖μ‖ * ‖u a‖ ≤ k * ‖u a‖ :=
      calc ‖μ‖ * ‖u a‖ = ‖∑ b, (M a b : ℂ) * u b‖ := by rw [e, norm_mul]
        _ ≤ ∑ b, ‖(M a b : ℂ) * u b‖ := norm_sum_le _ _
        _ = ∑ b, M a b * ‖u b‖ := Finset.sum_congr rfl fun b _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hM a b)]
        _ ≤ ∑ b, M a b * ‖u a‖ :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (ha b) (hM a b)
        _ = k * ‖u a‖ := by rw [← Finset.sum_mul, hrow]
    exact le_of_mul_le_mul_right h1 hua

/-- A primitive matrix has its Perron root as dominant eigenvalue. -/
theorem isDominantEigenvalue_of_isPrimitive [Fintype A] [DecidableEq A] [Nonempty A]
    {M : Matrix A A ℝ} (hM : M.IsPrimitive) : ∃ r, 0 < r ∧ IsDominantEigenvalue M r := by
  obtain ⟨r, hr, v, hv, hMv⟩ := PerronFrobenius.exists_eigenvector hM
  refine ⟨r, hr, ⟨v, fun h => (hv (Classical.arbitrary A)).ne' ?_, hMv⟩,
    fun μ u hu h => PerronFrobenius.norm_le_of_mulVec_eq hM hr hv hMv hu h⟩
  simpa using congrFun h (Classical.arbitrary A)

/-- **Uniform morphisms are substitutions**: a `k`-uniformly morphic sequence is `k`-substitutive.
The alphabet is cut down to the letters that occur in the fixed point. -/
theorem isSubstitutive_of_isUniformMorphic {k : ℕ} (hk : 2 ≤ k) {f : ℕ → Bool}
    (hf : UniformMorphic.IsUniformMorphic k f) : IsSubstitutive k f := by
  obtain ⟨A, hA, σ, x, τ, hx, hfx⟩ := hf
  classical
  -- the letters that occur in `x`
  let B := {a : A // ∃ n, x n = a}
  have hσB : ∀ (b : B) (d : Fin k), ∃ n, x n = σ b.1 d := fun b d => by
    obtain ⟨m, hm⟩ := b.2
    exact ⟨k * m + d, by rw [hx, hm]⟩
  let σ' : B → List B := fun b => List.ofFn fun d => ⟨σ b.1 d, hσB b d⟩
  let x' : ℕ → B := fun n => ⟨x n, n, rfl⟩
  have hlen : ∀ b, (σ' b).length = k := fun b => List.length_ofFn
  have hstart : ∀ n, start σ' x' n = k * n := fun n => by
    simp only [start, hlen, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  have : Fintype B := Fintype.ofFinite B
  have : Nonempty B := ⟨x' 0⟩
  refine ⟨B, inferInstance, inferInstance, σ', x', fun b => τ b.1, fun b => ?_, ?_, ?_, ?_, ?_,
    hfx⟩
  · rw [← List.length_pos_iff, hlen]
    omega
  · rw [hlen]
    omega
  · intro n d hd
    have hd' : d < k := hlen (x' n) ▸ hd
    rw [hstart]
    apply Subtype.ext
    simp only [σ', x', List.getElem_ofFn]
    exact hx n ⟨d, hd'⟩
  · rintro ⟨a, n, rfl⟩
    exact ⟨n, rfl⟩
  · refine isDominantEigenvalue_of_sum_eq (fun b c => ?_) fun b => ?_
    · simp only [incidence, of_apply]
      positivity
    · rw [sum_incidence, hlen]

/-- An eventually periodic sequence is `k`-substitutive for every `k ≥ 2`: it is `k`-automatic,
hence `k`-uniformly morphic. -/
theorem isSubstitutive_of_eventuallyPeriodic {k : ℕ} (hk : 2 ≤ k) {f : ℕ → Bool}
    (hf : EventuallyPeriodic f) : IsSubstitutive k f :=
  isSubstitutive_of_isUniformMorphic hk
    ((UniformMorphic.isAutomatic_iff_isUniformMorphic hk f).1
      (Automatic.isAutomatic_of_eventuallyPeriodic hf hk))

/-- The integers `k ≥ 2` are Perron numbers. -/
theorem isPerron_natCast {k : ℕ} (hk : 2 ≤ k) : IsPerron k := by
  have hkZ : (k : ℝ) = algebraMap ℤ ℝ (k : ℤ) := by simp
  refine ⟨by exact_mod_cast hk, hkZ ▸ isIntegral_algebraMap, fun z hz hzk => ?_⟩
  rw [hkZ, minpoly.eq_X_sub_C_of_algebraMap_inj _ Int.cast_injective, map_sub,
    Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hz
  exact absurd (by rw [hz]; simp) hzk

/-- **Substitutions, the sufficient direction**: if the center column is not both `a`-substitutive
and `b`-substitutive for some `a, b ≥ 2`, Problem 1 holds. -/
theorem problem1_of_not_substitutive {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : ¬ (IsSubstitutive a Rule30Prize.center ∧ IsSubstitutive b Rule30Prize.center)) :
    Rule30Prize.Problem1 := fun hep =>
  h ⟨isSubstitutive_of_eventuallyPeriodic ha hep, isSubstitutive_of_eventuallyPeriodic hb hep⟩

/-- **Substitutions, bases 2 and 3**: if the center column is not both `2`-substitutive and
`3`-substitutive, Problem 1 holds. -/
theorem problem1_of_not_substitutive_two_three
    (h : ¬ (IsSubstitutive 2 Rule30Prize.center ∧ IsSubstitutive 3 Rule30Prize.center)) :
    Rule30Prize.Problem1 :=
  problem1_of_not_substitutive (a := 2) (b := 3) le_rfl (by norm_num) (by simpa using h)

end Rule30Equivalents.Substitutive
