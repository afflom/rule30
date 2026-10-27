module

public import Rule30Equivalents.BinaryIrrational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
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
# Problem 1 in every Pisot base `β > 2`

Read the center column as the digits of `x_β = ∑ c(t) β^-(t+1)`. **For every
Pisot number `β > 2`, Problem 1 holds iff `x_β ∉ ℚ(β)`** (`problem1_iff_not_mem_adjoin`); more
generally, a `Bool` sequence is eventually periodic iff its value in base `β` lies in `ℚ(β)`
(`eventuallyPeriodic_iff_mem_adjoin`). A Pisot number is a real algebraic integer `β > 1` whose
other conjugates lie in the open unit disk (`IsPisot`).

**Expansions in a base `β > 2`.** Write `x_t` for the value of the tail `b(t), b(t + 1), …`. Then
`x_{t+1} = β x_t - b(t)` (`BinaryIrrational.tailValue_succ`, which holds in every real base
`β > 1`), and `0 ≤ x_t ≤ 1/(β - 1) < 1`, so the digit `b(t)` is `1` exactly when `β x_t ≥ 1`
(`digit_iff`): the digits are the greedy β-expansion of `x_β`, and finitely many tail values make
`b` eventually periodic (`eventuallyPeriodic_of_finite_tails`).

**Proof** (Bertrand, Schmidt).
* If `b` is eventually periodic, the geometric series puts `x_β` in every field that contains `β`
  (`BinaryIrrational.mem_of_eventuallyPeriodic`).
* If `x_β ∈ K = ℚ(β)`, a number field, then `q x_β` is an algebraic integer for some integer
  `q ≠ 0`, and so is every `q x_t = βᵗ (q x_β) - q (b(0) β^(t-1) + ⋯ + b(t-1))`. An embedding
  `φ : K → ℂ` sends `β` to a conjugate: either `β` itself, and then `φ` is the inclusion and
  `φ(q x_t) = q x_t ∈ [0, q]`; or a conjugate `γ` with `‖γ‖ < 1`, and then
  `‖φ(q x_t)‖ ≤ q (‖φ x_β‖ + 1 / (1 - ‖γ‖))`. Algebraic integers of `K` with all conjugates bounded
  form a finite set (Mathlib's `NumberField.Embeddings.finite_of_norm_le`), so the `x_t` take
  finitely many values.

Sources: K. Schmidt, *On periodic expansions of Pisot numbers and Salem numbers*, Bull. London
Math. Soc. 12 (1980) 269–278; A. Bertrand, *Développements en base de Pisot et répartition
modulo 1*, C. R. Acad. Sci. Paris 285 (1977) 419–421.
-/

@[expose] public section

namespace Rule30Equivalents.PisotNumbers

open Ruliology.CellularAutomata
open BinaryIrrational (value tail lead map_lead value_nonneg value_le tailValue_succ
  pow_mul_value mem_of_eventuallyPeriodic)

/-! ### Expansions in a base `β > 2` -/

variable {β : ℝ}

section Base

variable (hβ : 2 < β)
include hβ

theorem one_lt : (1 : ℝ) < β := one_lt_two.trans hβ

theorem value_lt_one (b : ℕ → Bool) : value β b < 1 := by
  have h := value_le (one_lt hβ) b
  have h2 : 1 / (β - 1) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith

/-- **The greedy digit**: `b(t) = 1` iff `β x_t ≥ 1`. -/
theorem digit_iff (b : ℕ → Bool) (t : ℕ) : b t = true ↔ 1 ≤ β * value β (tail b t) := by
  have h1 := tailValue_succ (one_lt hβ) b t
  have h2 := value_nonneg (one_lt hβ) (tail b (t + 1))
  have h3 := value_lt_one hβ (tail b (t + 1))
  constructor
  · intro h; rw [h] at h1; simp at h1; linarith
  · intro h
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rw [hne] at h1; simp at h1; linarith

/-- **Finitely many tail values give eventual periodicity**: the digit is the greedy one. -/
theorem eventuallyPeriodic_of_finite_tails {b : ℕ → Bool}
    (hfin : (Set.range fun t => value β (tail b t)).Finite) : EventuallyPeriodic b :=
  BinaryIrrational.eventuallyPeriodic_of_finite_tails (one_lt hβ) (fun x => decide (1 ≤ β * x))
    (fun t => Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff]; exact digit_iff hβ b t)) hfin

end Base

/-! ### Pisot numbers -/

/-- A Pisot number: a real algebraic integer `β > 1` whose other conjugates, the other complex
roots of its minimal polynomial, lie in the open unit disk. -/
def IsPisot (β : ℝ) : Prop :=
  IsIntegral ℤ β ∧ 1 < β ∧
    ∀ z : ℂ, Polynomial.aeval z (minpoly ℤ β) = 0 → z ≠ (β : ℂ) → ‖z‖ < 1

/-- **The lattice direction** (Bertrand, Schmidt). If `β > 2` is a Pisot number and the value of
`b` lies in `ℚ(β)`, then `b` is eventually periodic. -/
theorem eventuallyPeriodic_of_mem_adjoin (hP : IsPisot β) (hβ : 2 < β) {b : ℕ → Bool}
    (h : value β b ∈ IntermediateField.adjoin ℚ ({β} : Set ℝ)) : EventuallyPeriodic b := by
  classical
  set K := IntermediateField.adjoin ℚ ({β} : Set ℝ)
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hP.1.tower_top
  have : NumberField K := ⟨⟩
  set βK : K := IntermediateField.AdjoinSimple.gen ℚ β
  set xK : K := ⟨value β b, h⟩
  have hval : ∀ y : K, (K.val : K →+* ℝ) y = y := fun _ => rfl
  -- the tails as elements of `K`
  set xt : ℕ → K := fun t => βK ^ t * xK - lead βK b t
  have hxt : ∀ t, ((xt t : K) : ℝ) = value β (tail b t) := fun t => by
    have e := pow_mul_value (one_lt hβ) b t
    have hl := map_lead (K.val : K →+* ℝ) βK b t
    rw [hval, hval] at hl
    show ((βK ^ t * xK - lead βK b t : K) : ℝ) = _
    push_cast
    rw [hl]
    show β ^ t * value β b - lead β b t = _
    linarith
  -- an integer multiple of `x_β` is an algebraic integer
  obtain ⟨q, hq0, hqint⟩ := exists_integral_multiples ℤ ℚ (L := K) {xK}
  have hqx : IsIntegral ℤ ((q : K) * xK) := by
    have := hqint xK (Finset.mem_singleton_self _)
    rwa [zsmul_eq_mul] at this
  have hβint : IsIntegral ℤ βK := by
    have hinj : Function.Injective ((K.val : K →+* ℝ).toIntAlgHom) := Subtype.val_injective
    exact (isIntegral_algHom_iff _ hinj).1 hP.1
  have hqK : IsIntegral ℤ ((q : ℤ) : K) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K q))
  have hleadint : ∀ t, IsIntegral ℤ (lead βK b t) := fun t => by
    induction t with
    | zero => exact isIntegral_zero
    | succ t ih =>
      refine (hβint.mul ih).add ?_
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  have hint : ∀ t, IsIntegral ℤ ((q : K) * xt t) := fun t => by
    have e : (q : K) * xt t = βK ^ t * ((q : K) * xK) - (q : K) * lead βK b t := by
      simp only [xt]; ring
    rw [e]
    exact ((hβint.pow t).mul hqx).sub (hqK.mul (hleadint t))
  -- the embeddings of `K`: the inclusion, or a conjugate inside the unit disk
  have hroot : ∀ φ : K →+* ℂ, φ βK = (β : ℂ) ∨ ‖φ βK‖ < 1 := by
    intro φ
    have h0 : Polynomial.aeval βK (minpoly ℤ β) = 0 := by
      apply Subtype.val_injective
      have := Polynomial.aeval_algHom_apply ((K.val : K →+* ℝ).toIntAlgHom) βK (minpoly ℤ β)
      rw [show ((K.val : K →+* ℝ).toIntAlgHom) βK = β from rfl, minpoly.aeval] at this
      exact this.symm
    have h1 : Polynomial.aeval (φ βK) (minpoly ℤ β) = 0 := by
      rw [show φ βK = φ.toIntAlgHom βK from rfl, Polynomial.aeval_algHom_apply, h0, map_zero]
    by_cases hb : φ βK = (β : ℂ)
    · exact Or.inl hb
    · exact Or.inr (hP.2.2 _ h1 hb)
  have hreal : ∀ φ : K →+* ℂ, φ βK = (β : ℂ) → ∀ y : K, φ y = ((y : ℝ) : ℂ) := by
    intro φ hφ y
    have := IntermediateField.adjoin_algHom_ext ℚ (φ₁ := φ.toRatAlgHom)
      (φ₂ := (Complex.ofRealHom.comp (K.val : K →+* ℝ)).toRatAlgHom) fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hφ
    exact DFunLike.congr_fun this y
  -- a uniform bound on the conjugates of `q x_t`
  set B : ℝ := |(q : ℝ)| * (1 + ∑ φ : K →+* ℂ,
    (‖φ xK‖ + if ‖φ βK‖ < 1 then 1 / (1 - ‖φ βK‖) else 0))
  have hterm : ∀ φ : K →+* ℂ, 0 ≤ ‖φ xK‖ + if ‖φ βK‖ < 1 then 1 / (1 - ‖φ βK‖) else 0 :=
    fun φ => add_nonneg (norm_nonneg _) (by split_ifs with h1 <;> [exact (one_div_pos.2
      (by linarith)).le; exact le_rfl])
  have hbound : ∀ t (φ : K →+* ℂ), ‖φ ((q : K) * xt t)‖ ≤ B := by
    intro t φ
    rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hsum : ‖φ xK‖ + (if ‖φ βK‖ < 1 then 1 / (1 - ‖φ βK‖) else 0) ≤
        ∑ φ' : K →+* ℂ, (‖φ' xK‖ + if ‖φ' βK‖ < 1 then 1 / (1 - ‖φ' βK‖) else 0) :=
      Finset.single_le_sum (fun φ' _ => hterm φ') (Finset.mem_univ φ)
    rcases hroot φ with hb | hb
    · rw [hreal φ hb, Complex.norm_real, Real.norm_eq_abs, hxt,
        abs_of_nonneg (value_nonneg (one_lt hβ) _)]
      have := value_lt_one hβ (tail b t)
      linarith [hterm φ]
    · rw [ite_eq_left hb] at hsum
      -- `φ(x_t) = γᵗ φ(x_β) - lead γ`
      have e : φ (xt t) = φ βK ^ t * φ xK - lead (φ βK) b t := by
        simp only [xt, map_sub, map_mul, map_pow, map_lead]
      have hγ : 0 ≤ ‖φ βK‖ := norm_nonneg _
      have hne : 1 - ‖φ βK‖ ≠ 0 := by linarith
      have hlead : ∀ s, ‖lead (φ βK) b s‖ ≤ 1 / (1 - ‖φ βK‖) := by
        intro s
        induction s with
        | zero => simp only [lead, norm_zero]; exact (one_div_pos.2 (by linarith)).le
        | succ s ih =>
          rw [lead]
          calc ‖φ βK * lead (φ βK) b s + (if b s then 1 else 0)‖
              ≤ ‖φ βK‖ * ‖lead (φ βK) b s‖ + 1 := by
                refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) ?_)
                split_ifs <;> simp
            _ ≤ ‖φ βK‖ * (1 / (1 - ‖φ βK‖)) + 1 := by gcongr
            _ = 1 / (1 - ‖φ βK‖) := by field_simp; ring
      calc ‖φ (xt t)‖ ≤ ‖φ βK‖ ^ t * ‖φ xK‖ + 1 / (1 - ‖φ βK‖) := by
            rw [e]
            refine (norm_sub_le _ _).trans (add_le_add ?_ (hlead t))
            rw [norm_mul, norm_pow]
        _ ≤ ‖φ xK‖ + 1 / (1 - ‖φ βK‖) := by
            have : ‖φ βK‖ ^ t ≤ 1 := pow_le_one₀ hγ hb.le
            nlinarith [norm_nonneg (φ xK)]
        _ ≤ 1 + ∑ φ' : K →+* ℂ, (‖φ' xK‖ + if ‖φ' βK‖ < 1 then 1 / (1 - ‖φ' βK‖) else 0) := by
            linarith
  -- so the tails take finitely many values
  have hfinK : (Set.range fun t => (q : K) * xt t).Finite :=
    (NumberField.Embeddings.finite_of_norm_le K ℂ B).subset (by
      rintro _ ⟨t, rfl⟩
      exact ⟨hint t, hbound t⟩)
  have hq : (q : K) ≠ 0 := by exact_mod_cast hq0
  have hfin : (Set.range fun t => value β (tail b t)).Finite := by
    have := (hfinK.image fun y => (((q : K)⁻¹ * y : K) : ℝ))
    refine this.subset ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨(q : K) * xt t, ⟨t, rfl⟩, ?_⟩
    show (((q : K)⁻¹ * ((q : K) * xt t) : K) : ℝ) = value β (tail b t)
    rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul, hxt]
  exact eventuallyPeriodic_of_finite_tails hβ hfin

/-- **Schmidt's theorem for `0/1` digits.** For a Pisot number `β > 2`, a `Bool` sequence is
eventually periodic iff its value in base `β` lies in `ℚ(β)`. -/
theorem eventuallyPeriodic_iff_mem_adjoin (hP : IsPisot β) (hβ : 2 < β) (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ value β b ∈ IntermediateField.adjoin ℚ ({β} : Set ℝ) :=
  ⟨fun h => mem_of_eventuallyPeriodic (one_lt hβ)
      (IntermediateField.adjoin ℚ ({β} : Set ℝ)).toSubfield
      (IntermediateField.mem_adjoin_simple_self ℚ β) h,
    eventuallyPeriodic_of_mem_adjoin hP hβ⟩

/-- **Every Pisot base `β > 2`.** Problem 1 holds iff `x_β = ∑ c(t) β^-(t+1)` does not
lie in `ℚ(β)`. -/
theorem problem1_iff_not_mem_adjoin (hP : IsPisot β) (hβ : 2 < β) :
    Rule30Prize.Problem1 ↔ value β c ∉ IntermediateField.adjoin ℚ ({β} : Set ℝ) :=
  not_congr (eventuallyPeriodic_iff_mem_adjoin hP hβ c)

/-- **Any base `β > 2`**, for example a Salem number: if `x_β ∉ ℚ(β)`, Problem 1 holds. For a Salem
number the converse is open (Schmidt's conjecture). -/
theorem problem1_of_not_mem_adjoin (hβ : 2 < β)
    (h : value β c ∉ IntermediateField.adjoin ℚ ({β} : Set ℝ)) : Rule30Prize.Problem1 :=
  fun hep => h (mem_of_eventuallyPeriodic (one_lt hβ)
    (IntermediateField.adjoin ℚ ({β} : Set ℝ)).toSubfield
    (IntermediateField.mem_adjoin_simple_self ℚ β) hep)

end Rule30Equivalents.PisotNumbers
