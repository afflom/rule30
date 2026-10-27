module

public import Rule30Equivalents.DFinite
public import Rule30Equivalents.Transcendence

/-!
# Problem 1 ⟺ the generating function is transcendental over `ℚ(X)`

Let `C(X) = ∑ c(t) Xᵗ`. The library already shows that Problem 1 holds when
`C(X)` is transcendental (`Transcendence.problem1_of_transcendental`). The converse follows from a
classical fact: an algebraic power series is D-finite (Abel; Comtet 1964; Stanley 1980). The D-finite
form (`DFinite.eventuallyPeriodic_of_dFinite`) then gives eventual periodicity. Fatou's
theorem is not needed.

* `exists_dfinite_of_isAlgebraic`: over a field `K` of characteristic zero, a power series `F`
  algebraic over `K[X]` satisfies a linear differential equation with polynomial coefficients, not
  all zero.
  - Let `P` be a nonzero polynomial over `K[X]` of least degree `d` with `P(F) = 0`; then `d ≥ 1`.
  - Differentiating gives `P_Y(F) · F' = −P^∂(F)`, where `P^∂` differentiates the coefficients of
    `P` (`derivative_aeval`). By minimality `P_Y(F) ≠ 0`, and it is algebraic, so
    `P_Y(F) · G(F) = r` for a polynomial `G` and some `r ≠ 0` in `K[X]`. Hence `r F' ∈ K[X][F]`, and
    by induction `r^m F^{(k)} ∈ K[X][F]` for every `k` (`reach_iterate`).
  - A power of the leading coefficient of `P` moves each element of `K[X][F]` into the
    `K[X]`-module spanned by `1, F, …, F^{d-1}` (`mul_aeval_mem_span`). So `F, F', …, F^{(d)}`,
    scaled by nonzero polynomials, are `d + 1` elements of a module spanned by `d` elements, and
    they are linearly dependent over `K[X]`.
* `isAlgebraic_polynomial_of_isAlgebraic`: algebraic over `K(X)` (as a Laurent series) implies
  algebraic over `K[X]` (as a power series).
* `eventuallyPeriodic_iff_isAlgebraic` and `problem1_iff_transcendental`.

Sources: L. Comtet, *Calcul pratique des coefficients de Taylor d'une fonction algébrique*,
Enseign. Math. 10 (1964) 267–270; R. P. Stanley, *Differentiably finite power series*, European J.
Combin. 1 (1980) 175–188, Theorem 2.1.
-/

@[expose] public section

namespace Rule30Equivalents.AlgebraicDFinite

open Ruliology.CellularAutomata Polynomial
open scoped LaurentSeries RatFunc

variable {K : Type*} [Field K]

local notation "δ" => PowerSeries.derivative (R := K)

/-! ### Differentiating `P(F)` -/

theorem algebraMap_eq_coe (a : K[X]) : algebraMap K[X] (PowerSeries K) a = (a : PowerSeries K) := by
  rw [PowerSeries.algebraMap_apply']
  simp

theorem derivative_algebraMap (a : K[X]) :
    δ (algebraMap K[X] (PowerSeries K) a) = algebraMap K[X] (PowerSeries K) (derivative a) := by
  rw [algebraMap_eq_coe, algebraMap_eq_coe, PowerSeries.derivative_coe]

/-- Differentiate the coefficients of a polynomial over `K[X]`. -/
noncomputable def cderiv (P : K[X][X]) : K[X][X] :=
  P.sum fun j a => C (derivative a) * X ^ j

theorem cderiv_add (P Q : K[X][X]) : cderiv (P + Q) = cderiv P + cderiv Q :=
  Polynomial.sum_add_index P Q _ (fun _ => by simp) fun _ _ _ => by simp [add_mul]

theorem cderiv_monomial (j : ℕ) (a : K[X]) : cderiv (monomial j a) = C (derivative a) * X ^ j :=
  Polynomial.sum_monomial_index a _ (by simp)

/-- **The chain rule**: `(P(F))' = P^∂(F) + P_Y(F) · F'`. -/
theorem derivative_aeval (F : PowerSeries K) (P : K[X][X]) :
    δ (aeval F P) = aeval F (cderiv P) + aeval F (derivative P) * δ F := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, cderiv_add, hP, hQ]; ring
  | monomial j a =>
    rw [cderiv_monomial, derivative_monomial, aeval_monomial, aeval_monomial, Derivation.leibniz,
      Derivation.leibniz_pow, derivative_algebraMap]
    simp only [map_mul, aeval_C, aeval_X_pow, smul_eq_mul, nsmul_eq_mul, map_natCast]
    ring

/-! ### Derivatives stay in `K[X][F]` -/

/-- `G` lies in `K[X][F]` up to a power of `r`. -/
def Reach (F : PowerSeries K) (r : K[X]) (G : PowerSeries K) : Prop :=
  ∃ (m : ℕ) (T : K[X][X]), algebraMap K[X] (PowerSeries K) (r ^ m) * G = aeval F T

theorem reach_derivative {F : PowerSeries K} {r : K[X]} {T₁ : K[X][X]}
    (hr : algebraMap K[X] (PowerSeries K) r * δ F = aeval F T₁) {G : PowerSeries K}
    (hG : Reach F r G) : Reach F r (δ G) := by
  obtain ⟨m, T, hT⟩ := hG
  refine ⟨m + 2, C r * cderiv (C r * T) + derivative (C r * T) * T₁ -
    C (r * ((m + 1 : K[X]) * derivative r)) * T, ?_⟩
  have h₁ : algebraMap K[X] (PowerSeries K) (r ^ (m + 1)) * G = aeval F (C r * T) := by
    rw [map_mul, aeval_C, ← hT, pow_succ', map_mul]
    ring
  have h₂ := congrArg δ h₁
  rw [Derivation.leibniz, derivative_algebraMap, derivative_aeval, derivative_pow] at h₂
  simp only [smul_eq_mul, map_mul, map_add, map_sub, map_pow, aeval_C, map_natCast,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_one] at h₂ hT ⊢
  linear_combination algebraMap K[X] (PowerSeries K) r * h₂ +
    aeval F (derivative (C r * T)) * hr -
    algebraMap K[X] (PowerSeries K) r * ((m + 1) * algebraMap K[X] (PowerSeries K) (derivative r)) * hT

theorem reach_iterate {F : PowerSeries K} {r : K[X]} {T₁ : K[X][X]}
    (hr : algebraMap K[X] (PowerSeries K) r * δ F = aeval F T₁) (k : ℕ) :
    Reach F r ((⇑δ)^[k] F) := by
  induction k with
  | zero => exact ⟨0, X, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact reach_derivative hr ih

/-! ### A module spanned by `d` elements -/

/-- A power of the leading coefficient of `P` moves `T(F)` into the `K[X]`-span of
`1, F, …, F^{d-1}`, when `P(F) = 0` and `d = deg P ≥ 1`. -/
theorem mul_aeval_mem_span {F : PowerSeries K} {P : K[X][X]} (hP : aeval F P = 0)
    (hd : P.natDegree ≠ 0) (T : K[X][X]) :
    algebraMap K[X] (PowerSeries K) (P.leadingCoeff ^ T.natDegree) * aeval F T ∈
      Submodule.span K[X] (Set.range fun i : Fin P.natDegree => F ^ (i : ℕ)) := by
  set M := Submodule.span K[X] (Set.range fun i : Fin P.natDegree => F ^ (i : ℕ))
  set φ := algebraMap K[X] (PowerSeries K)
  have hgen : ∀ i : Fin P.natDegree, F ^ (i : ℕ) ∈ M := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have htop : P.leadingCoeff • F ^ P.natDegree =
      -∑ i ∈ Finset.range P.natDegree, P.coeff i • F ^ i := by
    have hsum := hP
    rw [aeval_eq_sum_range, Finset.sum_range_succ] at hsum
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hsum
  have hstep : ∀ G ∈ M, φ P.leadingCoeff * F * G ∈ M := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [mul_assoc, ← pow_succ', ← Algebra.smul_def]
      by_cases hi : (i : ℕ) + 1 < P.natDegree
      · exact Submodule.smul_mem _ _ (hgen ⟨_, hi⟩)
      · rw [show (i : ℕ) + 1 = P.natDegree by omega, htop]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
          (hgen ⟨j, Finset.mem_range.1 hj⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  have hpow : ∀ j, φ (P.leadingCoeff ^ j) * F ^ j ∈ M := by
    intro j
    induction j with
    | zero => simpa using hgen ⟨0, Nat.pos_of_ne_zero hd⟩
    | succ j ih =>
      have h := hstep _ ih
      rwa [show φ P.leadingCoeff * F * (φ (P.leadingCoeff ^ j) * F ^ j) =
        φ (P.leadingCoeff ^ (j + 1)) * F ^ (j + 1) by rw [map_pow, map_pow]; ring] at h
  rw [aeval_eq_sum_range, Finset.mul_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hj' : j ≤ T.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [show φ (P.leadingCoeff ^ T.natDegree) * (T.coeff j • F ^ j) =
      (T.coeff j * P.leadingCoeff ^ (T.natDegree - j)) • (φ (P.leadingCoeff ^ j) * F ^ j) by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, map_pow, map_pow,
      ← pow_sub_mul_pow (φ P.leadingCoeff) hj']
    ring]
  exact Submodule.smul_mem _ _ (hpow j)

/-! ### Algebraic power series are D-finite -/

/-- **Algebraic power series are D-finite** (Abel, Comtet, Stanley): over a field of characteristic
zero, a power series algebraic over `K[X]` satisfies a linear differential equation with
polynomial coefficients, not all zero. -/
theorem exists_dfinite_of_isAlgebraic [CharZero K] {F : PowerSeries K}
    (hF : IsAlgebraic K[X] F) : ∃ (r : ℕ) (q : Fin (r + 1) → K[X]), (∃ i, q i ≠ 0) ∧
      ∑ i : Fin (r + 1), (q i : PowerSeries K) * (⇑δ)^[i] F = 0 := by
  classical
  set φ := algebraMap K[X] (PowerSeries K)
  have hinj : Function.Injective φ := fun a b h => by
    rw [algebraMap_eq_coe, algebraMap_eq_coe] at h
    exact Polynomial.coe_inj.1 h
  -- a nonzero polynomial of least degree with `P(F) = 0`
  have hex : ∃ n, ∃ P : K[X][X], P ≠ 0 ∧ aeval F P = 0 ∧ P.natDegree = n :=
    let ⟨P, hP0, hPF⟩ := hF; ⟨_, P, hP0, hPF, rfl⟩
  obtain ⟨P, hP0, hPF, hPd⟩ := Nat.find_spec hex
  have hmin : ∀ P' : K[X][X], P' ≠ 0 → aeval F P' = 0 → P.natDegree ≤ P'.natDegree :=
    fun P' h0 h => hPd ▸ Nat.find_min' hex ⟨P', h0, h, rfl⟩
  have hd0 : P.natDegree ≠ 0 := by
    intro h0
    have hc := hPF
    rw [eq_C_of_natDegree_eq_zero h0, aeval_C] at hc
    exact hP0 (by rw [eq_C_of_natDegree_eq_zero h0, hinj (hc.trans (map_zero φ).symm), map_zero])
  -- `P_Y(F) ≠ 0`
  have hQ0 : derivative P ≠ 0 := by
    intro h0
    have h := congrArg (fun p => p.coeff (P.natDegree - 1)) h0
    simp only [coeff_derivative, coeff_zero, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd0)] at h
    have hc : (↑(P.natDegree - 1) + 1 : K[X]) ≠ 0 := by
      have e : P.natDegree - 1 + 1 = P.natDegree := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd0)
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, e]
      exact Nat.cast_ne_zero.2 hd0
    exact mul_ne_zero (leadingCoeff_ne_zero.2 hP0) hc h
  have hQF : aeval F (derivative P) ≠ 0 := fun h =>
    absurd (hmin _ hQ0 h) (not_le.2 (natDegree_derivative_lt hd0))
  -- `P_Y(F)` divides a nonzero polynomial inside `K[X][F]`
  have hQalg : IsAlgebraic K[X] (aeval F (derivative P)) :=
    Algebra.isAlgebraic_adjoin_singleton_iff.2 hF _ (aeval_mem_adjoin_singleton K[X] F)
  obtain ⟨t, ht, r, hr0, hrt⟩ :=
    hQalg.exists_nonzero_eq_adjoin_mul (mem_nonZeroDivisors_of_ne_zero hQF)
  have ht' : t ∈ Algebra.adjoin K[X] {F} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (aeval_mem_adjoin_singleton K[X] F)) ht
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ht'
  obtain ⟨G, rfl⟩ := ht'
  -- `r F' ∈ K[X][F]`, hence `r^m F^{(k)} ∈ K[X][F]`
  have hr : φ r * δ F = aeval F (-(G * cderiv P)) := by
    have h := derivative_aeval F P
    rw [hPF, map_zero] at h
    rw [← hrt, map_neg, map_mul]
    linear_combination -(aeval F G) * h
  choose m T hmT using reach_iterate hr
  -- `d + 1` scaled derivatives in a module spanned by `d` elements
  have hmem : ∀ k : Fin (P.natDegree + 1),
      φ (P.leadingCoeff ^ (T k).natDegree * r ^ m k) * (⇑δ)^[k] F ∈
        Submodule.span K[X] (Set.range fun i : Fin P.natDegree => F ^ (i : ℕ)) := by
    intro k
    rw [map_mul, mul_assoc, hmT k]
    exact mul_aeval_mem_span hPF hd0 (T k)
  have hdep : ¬ LinearIndependent K[X] fun k : Fin (P.natDegree + 1) =>
      φ (P.leadingCoeff ^ (T k).natDegree * r ^ m k) * (⇑δ)^[k] F := by
    intro hli
    have h₁ := linearIndependent_le_span' _ hli _ (Set.range_subset_iff.2 hmem)
    have h₂ := Fintype.card_range_le fun i : Fin P.natDegree => F ^ (i : ℕ)
    rw [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_le] at h₁
    rw [Fintype.card_fin] at h₂
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hdep
  refine ⟨P.natDegree, fun k => g k * (P.leadingCoeff ^ (T k).natDegree * r ^ m k),
    ⟨i, mul_ne_zero hi (mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.2 hP0))
      (pow_ne_zero _ hr0))⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, ← algebraMap_eq_coe, map_mul, mul_assoc]

/-! ### The generating function of a `Bool` sequence -/

/-- Algebraic over `K(X)`, as a Laurent series, means algebraic over `K[X]`, as a power series. -/
theorem isAlgebraic_polynomial_of_isAlgebraic {F : PowerSeries K}
    (h : IsAlgebraic (RatFunc K) (F : K⸨X⸩)) : IsAlgebraic K[X] F := by
  have key : ∀ q : K[X][X], HahnSeries.ofPowerSeries ℤ K (aeval F q) = aeval (F : K⸨X⸩) q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n a =>
      rw [aeval_monomial, aeval_monomial, map_mul, map_pow, algebraMap_eq_coe,
        IsScalarTower.algebraMap_apply K[X] (RatFunc K) K⸨X⸩ a]
      congr 1
      exact RatFunc.coe_coe a
  obtain ⟨p, hp0, hp⟩ := (IsFractionRing.isAlgebraic_iff K[X] (RatFunc K) K⸨X⸩).2 h
  refine ⟨p, hp0, HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K) ?_⟩
  rw [map_zero, key, hp]

theorem isDFinite_of_isAlgebraic {b : ℕ → Bool}
    (h : IsAlgebraic (RatFunc ℚ) ((LinearRelations.series ℚ b : PowerSeries ℚ) : ℚ⸨X⸩)) :
    DFinite.IsDFinite b :=
  exists_dfinite_of_isAlgebraic (isAlgebraic_polynomial_of_isAlgebraic h)

/-- A `Bool` sequence is eventually periodic iff its generating function is algebraic over
`ℚ(X)`. -/
theorem eventuallyPeriodic_iff_isAlgebraic (b : ℕ → Bool) : EventuallyPeriodic b ↔
    IsAlgebraic (RatFunc ℚ) ((LinearRelations.series ℚ b : PowerSeries ℚ) : ℚ⸨X⸩) :=
  ⟨Transcendence.isAlgebraic_of_eventuallyPeriodic,
    fun h => DFinite.eventuallyPeriodic_of_dFinite (isDFinite_of_isAlgebraic h)⟩

/-- **Problem 1 ⟺ `∑ c(t) Xᵗ` is transcendental over `ℚ(X)`**. -/
theorem problem1_iff_transcendental : Rule30Prize.Problem1 ↔
    Transcendental (RatFunc ℚ) ((LinearRelations.series ℚ c : PowerSeries ℚ) : ℚ⸨X⸩) :=
  not_congr (eventuallyPeriodic_iff_isAlgebraic c)

end Rule30Equivalents.AlgebraicDFinite
