module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.ComputeDegree

/-!
# A monic polynomial that is small on a notched disk

Szegő's theorem needs, for an arc of the unit circle across which a power series continues, monic
polynomials that are uniformly small on a closed curve around the unit disk with a notch cut out
at the arc: the logarithmic capacity of such a notched disk is below `1`. This file builds them
explicitly from Chebyshev polynomials.

* `norm_eval_T_le`: the Chebyshev polynomial `T_D` satisfies `‖T_D(ℓ)‖ ≤ Rᴰ` whenever `R ≥ 1` and
  `‖ℓ - 1‖ + ‖ℓ + 1‖ ≤ R + R⁻¹`: writing `ℓ = (v + v⁻¹)/2`, `T_D(ℓ) = (vᴰ + v⁻ᴰ)/2` and
  `‖ℓ - 1‖ + ‖ℓ + 1‖ = ‖v‖ + ‖v‖⁻¹` (`norm_sub_one_add_norm_add_one`).
* `arcPoly c D`: with `ℓ(w) = (w² + (1 - c) w + 1)/((1 + c) w)`, the polynomial `wᴰ T_D(ℓ(w))`, of
  degree `2D` and leading coefficient `2ᴰ⁻¹/(1 + c)ᴰ` (`eval_arcPoly`, `leadingCoeff_arcPoly`). On
  the unit circle `ℓ(e^{iθ}) = (2 cos θ + 1 - c)/(1 + c)`, which lies in `[-1, 1]` exactly when
  `cos θ ≤ c`: the polynomial is small on that arc.
* `notchPoly c K D`: the monic polynomial `wᴷᴰ · wᴰ T_D(ℓ(w)) / arcLead c D`, at most
  `2 ((1 + c)/2 · ‖w‖ᴷ⁺¹ · R)ᴰ` in modulus where `‖ℓ(w) - 1‖ + ‖ℓ(w) + 1‖ ≤ R + R⁻¹`
  (`norm_eval_notchPoly_le`). Inside the unit circle that sum is at most `8/‖w‖` (`crude_bound`),
  which the factor `‖w‖ᴷᴰ` beats on a circle of radius `ρ₁ < 1`. Near the arc, where
  `Re w ≤ ‖w‖ cos τ` with `cos τ < c`, it is at most `2 + O((‖w‖ - 1)²)` (`refined_bound`).
* `exists_notch_poly`: for every notch half-angle `0 < τ < π/2` there are radii `ρ₁ < 1 < ρ₂` and
  `q < 1` such that for every `D` some monic polynomial is at most `2 qᴰ` in modulus on the circle
  `‖w‖ = ρ₁` and on the part of the annulus `ρ₁ ≤ ‖w‖ ≤ ρ₂` where `Re w ≤ ‖w‖ cos τ`.

Sources: G. Szegő, *Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten*,
Sitzungsber. Preuss. Akad. Wiss. (1922) 88–91; P. Borwein, T. Erdélyi and F. Littmann,
*Polynomials with coefficients from a finite set*, Trans. Amer. Math. Soc. 360 (2008) 5145–5154,
section 3.
-/

@[expose] public section

namespace Rule30Equivalents.SzegoPolynomial

open Complex Polynomial Polynomial.Chebyshev

/-- `ℓ = (v + v⁻¹)/2` has `‖ℓ - 1‖ + ‖ℓ + 1‖ = ‖v‖ + ‖v‖⁻¹`, by the parallelogram law. -/
theorem norm_sub_one_add_norm_add_one {v : ℂ} (hv : v ≠ 0) :
    ‖(v + v⁻¹) / 2 - 1‖ + ‖(v + v⁻¹) / 2 + 1‖ = ‖v‖ + ‖v‖⁻¹ := by
  have h1 : (v + v⁻¹) / 2 - 1 = (v - 1) ^ 2 / (2 * v) := by field_simp; ring
  have h2 : (v + v⁻¹) / 2 + 1 = (v + 1) ^ 2 / (2 * v) := by field_simp; ring
  have hpar : ‖v - 1‖ ^ 2 + ‖v + 1‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [h1, h2, norm_div, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_two, ← add_div, hpar]
  field_simp

/-- If `x + x⁻¹ ≤ R + R⁻¹` with `x > 0` and `R ≥ 1`, then `x ≤ R`. -/
theorem le_of_add_inv_le {x R : ℝ} (hx : 0 < x) (hR : 1 ≤ R) (h : x + x⁻¹ ≤ R + R⁻¹) : x ≤ R := by
  by_contra hlt
  push Not at hlt
  have hR0 : 0 < R := by linarith
  have hxR : 1 < x * R := by nlinarith
  have : R + R⁻¹ < x + x⁻¹ := by
    rw [← sub_pos]
    have e : x + x⁻¹ - (R + R⁻¹) = (x - R) * (x * R - 1) / (x * R) := by field_simp; ring
    rw [e]
    apply div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  linarith

/-- **The Chebyshev bound**: `‖T_D(ℓ)‖ ≤ Rᴰ` whenever `R ≥ 1` and `‖ℓ - 1‖ + ‖ℓ + 1‖ ≤ R + R⁻¹`. -/
theorem norm_eval_T_le (ℓ : ℂ) (D : ℕ) {R : ℝ} (hR : 1 ≤ R) (h : ‖ℓ - 1‖ + ‖ℓ + 1‖ ≤ R + R⁻¹) :
    ‖(T ℂ (D : ℤ)).eval ℓ‖ ≤ R ^ D := by
  obtain ⟨θ, hθ⟩ := Complex.cos_surjective ℓ
  set v := Complex.exp (θ * I) with hvdef
  have hv : v ≠ 0 := Complex.exp_ne_zero _
  have hvinv : Complex.exp (-θ * I) = v⁻¹ := by rw [hvdef, ← Complex.exp_neg]; ring_nf
  have hℓ : ℓ = (v + v⁻¹) / 2 := by rw [← hθ, Complex.cos, hvinv]
  have hT : (T ℂ (D : ℤ)).eval ℓ = (v ^ D + v⁻¹ ^ D) / 2 := by
    rw [← hθ, T_complex_cos, Complex.cos]
    have e1 : ((D : ℤ) : ℂ) * θ * I = D * (θ * I) := by push_cast; ring
    have e2 : -(((D : ℤ) : ℂ) * θ) * I = D * (-θ * I) := by push_cast; ring
    rw [e1, e2, Complex.exp_nat_mul, Complex.exp_nat_mul, hvinv]
  have hsum := norm_sub_one_add_norm_add_one hv
  rw [← hℓ] at hsum
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hle : ‖v‖ + ‖v‖⁻¹ ≤ R + R⁻¹ := hsum ▸ h
  have h1 : ‖v‖ ≤ R := le_of_add_inv_le hn hR hle
  have h2 : ‖v‖⁻¹ ≤ R := le_of_add_inv_le (inv_pos.2 hn) hR (by rwa [inv_inv, add_comm])
  rw [hT, norm_div, Complex.norm_two]
  calc ‖v ^ D + v⁻¹ ^ D‖ / 2 ≤ (‖v‖ ^ D + ‖v‖⁻¹ ^ D) / 2 := by
        gcongr
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_pow, norm_pow, norm_inv]
    _ ≤ (R ^ D + R ^ D) / 2 := by gcongr
    _ = R ^ D := by ring

/-! ### The polynomial -/

variable {c : ℝ}

/-- `ℓ(w) = (w² + (1 - c) w + 1)/((1 + c) w)`, which maps the arc `cos θ ≤ c` of the unit circle
onto `[-1, 1]`. -/
noncomputable def ell (c : ℝ) (w : ℂ) : ℂ := (w ^ 2 + (1 - c) * w + 1) / ((1 + c) * w)

theorem ell_sub_one (hc : 0 < 1 + c) {w : ℂ} (hw : w ≠ 0) :
    ell c w - 1 = (w ^ 2 - 2 * c * w + 1) / ((1 + c) * w) := by
  have : (1 + c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold ell
  field_simp
  ring

theorem ell_add_one (hc : 0 < 1 + c) {w : ℂ} (hw : w ≠ 0) :
    ell c w + 1 = (w + 1) ^ 2 / ((1 + c) * w) := by
  have : (1 + c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold ell
  field_simp
  ring

/-- The quadratic `w² + (1 - c) w + 1`. -/
noncomputable def quad (c : ℝ) : ℂ[X] := X ^ 2 + C ((1 - c : ℝ) : ℂ) * X + 1

theorem natDegree_quad (c : ℝ) : (quad c).natDegree = 2 := by
  unfold quad
  compute_degree!

theorem monic_quad (c : ℝ) : (quad c).Monic := by
  unfold quad
  monicity!

/-- **The homogenized Chebyshev polynomial** `wᴰ T_D(ℓ(w))`. -/
noncomputable def arcPoly (c : ℝ) (D : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (D + 1), C ((T ℂ (D : ℤ)).coeff k * ((1 + c : ℂ)⁻¹) ^ k) *
    quad c ^ k * X ^ (D - k)

theorem natDegree_T_nat (D : ℕ) : (T ℂ (D : ℤ)).natDegree = D := by
  rw [natDegree_T]
  simp

theorem eval_arcPoly (hc : 0 < 1 + c) (D : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (arcPoly c D).eval w = w ^ D * (T ℂ (D : ℤ)).eval (ell c w) := by
  have h1c : (1 + c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [arcPoly, eval_finsetSum, eval_eq_sum_range' (n := D + 1) (by rw [natDegree_T_nat]; omega),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [eval_mul, eval_C, eval_pow, eval_X, quad, eval_add, eval_one]
  have hp : ((1 + c : ℂ) ^ k) ≠ 0 := pow_ne_zero _ h1c
  have hwk : w ^ k ≠ 0 := pow_ne_zero _ hw
  rw [ell, div_pow, mul_pow, ← pow_sub_mul_pow w hk, inv_pow]
  push_cast
  field_simp

/-- The leading coefficient `2ᴰ⁻¹/(1 + c)ᴰ` of `arcPoly c D`. -/
noncomputable def arcLead (c : ℝ) (D : ℕ) : ℂ := 2 ^ (D - 1) * ((1 + c : ℂ)⁻¹) ^ D

theorem coeff_T_self (D : ℕ) : (T ℂ (D : ℤ)).coeff D = 2 ^ (D - 1) := by
  rw [show (T ℂ (D : ℤ)).coeff D = (T ℂ (D : ℤ)).leadingCoeff by
    rw [Polynomial.leadingCoeff, natDegree_T_nat], leadingCoeff_T]
  simp

theorem arcPoly_eq (c : ℝ) (D : ℕ) : arcPoly c D =
    (∑ k ∈ Finset.range D, C ((T ℂ (D : ℤ)).coeff k * ((1 + c : ℂ)⁻¹) ^ k) * quad c ^ k *
      X ^ (D - k)) + C (arcLead c D) * quad c ^ D := by
  rw [arcPoly, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, coeff_T_self, arcLead]

theorem arcLead_ne_zero (hc : 0 < 1 + c) (D : ℕ) : arcLead c D ≠ 0 := by
  have : (1 + c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold arcLead
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ (inv_ne_zero this))

/-- **`arcPoly c D` has degree `2D` and leading coefficient `arcLead c D`.** -/
theorem leadingCoeff_arcPoly (hc : 0 < 1 + c) (D : ℕ) :
    (arcPoly c D).leadingCoeff = arcLead c D ∧ (arcPoly c D).natDegree = 2 * D := by
  have hL := arcLead_ne_zero hc D
  have htop : (C (arcLead c D) * quad c ^ D).natDegree = 2 * D := by
    rw [natDegree_C_mul hL, (monic_quad c).natDegree_pow, natDegree_quad]
    ring
  have hlc : (C (arcLead c D) * quad c ^ D).leadingCoeff = arcLead c D := by
    rw [leadingCoeff_C_mul_of_isUnit (Ne.isUnit hL), ((monic_quad c).pow D).leadingCoeff, mul_one]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · rw [arcPoly_eq, Finset.range_zero, Finset.sum_empty, zero_add]
    exact ⟨hlc, htop⟩
  have hrest : (∑ k ∈ Finset.range D, C ((T ℂ (D : ℤ)).coeff k * ((1 + c : ℂ)⁻¹) ^ k) *
      quad c ^ k * X ^ (D - k)).natDegree ≤ 2 * D - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hk : k < D := Finset.mem_range.1 hk
    refine (natDegree_mul_le).trans ?_
    have h1 : (C ((T ℂ (D : ℤ)).coeff k * ((1 + c : ℂ)⁻¹) ^ k) * quad c ^ k).natDegree ≤ 2 * k := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [(monic_quad c).natDegree_pow, natDegree_quad]
      omega
    have h2 := natDegree_X_pow_le (R := ℂ) (D - k)
    omega
  have hdeg : (∑ k ∈ Finset.range D, C ((T ℂ (D : ℤ)).coeff k * ((1 + c : ℂ)⁻¹) ^ k) *
      quad c ^ k * X ^ (D - k)).degree < (C (arcLead c D) * quad c ^ D).degree :=
    degree_lt_degree (by rw [htop]; omega)
  rw [arcPoly_eq, leadingCoeff_add_of_degree_lt hdeg, natDegree_add_eq_right_of_degree_lt hdeg]
  exact ⟨hlc, htop⟩

/-- **The monic polynomial** `wᴷᴰ · wᴰ T_D(ℓ(w)) / arcLead`. -/
noncomputable def notchPoly (c : ℝ) (K D : ℕ) : ℂ[X] :=
  C (arcLead c D)⁻¹ * X ^ (K * D) * arcPoly c D

theorem monic_notchPoly (hc : 0 < 1 + c) (K D : ℕ) : (notchPoly c K D).Monic := by
  have hL := arcLead_ne_zero hc D
  have h1 : (C (arcLead c D)⁻¹ * arcPoly c D).Monic := by
    rw [Monic, leadingCoeff_C_mul_of_isUnit (Ne.isUnit (inv_ne_zero hL)),
      (leadingCoeff_arcPoly hc D).1, inv_mul_cancel₀ hL]
  have : notchPoly c K D = X ^ (K * D) * (C (arcLead c D)⁻¹ * arcPoly c D) := by
    unfold notchPoly; ring
  rw [this]
  exact (monic_X_pow _).mul h1

/-- **The size of `notchPoly`**: if `R ≥ 1` and `‖ℓ(w) - 1‖ + ‖ℓ(w) + 1‖ ≤ R + R⁻¹`, then
`‖notchPoly(w)‖ ≤ 2 ((1 + c)/2 · ‖w‖ᴷ⁺¹ · R)ᴰ`. -/
theorem norm_eval_notchPoly_le (hc : 0 < 1 + c) (K D : ℕ) {w : ℂ} (hw : w ≠ 0) {R : ℝ}
    (hR : 1 ≤ R) (h : ‖ell c w - 1‖ + ‖ell c w + 1‖ ≤ R + R⁻¹) :
    ‖(notchPoly c K D).eval w‖ ≤ 2 * ((1 + c) / 2 * ‖w‖ ^ (K + 1) * R) ^ D := by
  have hT := norm_eval_T_le (ell c w) D hR h
  have hL := arcLead_ne_zero hc D
  have hcpos : (0 : ℝ) < 1 + c := hc
  rw [notchPoly, eval_mul, eval_mul, eval_C, eval_pow, eval_X, eval_arcPoly hc D hw]
  have hlead : ‖(arcLead c D)⁻¹‖ ≤ 2 * ((1 + c) / 2) ^ D := by
    rw [arcLead, norm_inv, norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_two]
    have h1c : ‖(1 + c : ℂ)‖ = 1 + c := by
      rw [show (1 + c : ℂ) = ((1 + c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hcpos.le]
    rw [h1c, mul_inv, inv_pow, inv_inv, div_pow]
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · norm_num
    · have : (2 : ℝ) ^ D = 2 * 2 ^ (D - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]
      field_simp
      rfl
  calc ‖(arcLead c D)⁻¹ * w ^ (K * D) * (w ^ D * (T ℂ (D : ℤ)).eval (ell c w))‖
      = ‖(arcLead c D)⁻¹‖ * ‖w‖ ^ (K * D) * (‖w‖ ^ D * ‖(T ℂ (D : ℤ)).eval (ell c w)‖) := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ 2 * ((1 + c) / 2) ^ D * ‖w‖ ^ (K * D) * (‖w‖ ^ D * R ^ D) := by gcongr
    _ = 2 * ((1 + c) / 2 * ‖w‖ ^ (K + 1) * R) ^ D := by
        rw [mul_pow, mul_pow, ← pow_mul, show (K + 1) * D = K * D + D by ring, pow_add]
        ring

/-! ### Growth of `ℓ` -/

theorem norm_one_add_c {c : ℝ} (hc : 0 < 1 + c) : ‖(1 + c : ℂ)‖ = 1 + c := by
  rw [show (1 + c : ℂ) = ((1 + c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg hc.le]

/-- **Crude growth**: for `0 < ‖w‖ ≤ 1` and `0 ≤ c ≤ 1`, `‖ℓ(w) - 1‖ + ‖ℓ(w) + 1‖ ≤ 8/‖w‖`. -/
theorem crude_bound (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {w : ℂ} (hw : w ≠ 0) (ht : ‖w‖ ≤ 1) :
    ‖ell c w - 1‖ + ‖ell c w + 1‖ ≤ 8 / ‖w‖ := by
  have hc : 0 < 1 + c := by linarith
  have ht0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [ell_sub_one hc hw, ell_add_one hc hw, norm_div, norm_div, norm_mul, norm_one_add_c hc,
    ← add_div, div_le_div_iff₀ (by positivity) ht0]
  have e1 : ‖w ^ 2 - 2 * c * w + 1‖ ≤ 4 := by
    calc ‖w ^ 2 - 2 * c * w + 1‖ ≤ ‖w ^ 2‖ + ‖2 * (c : ℂ) * w‖ + ‖(1 : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = ‖w‖ ^ 2 + 2 * c * ‖w‖ + 1 := by
          rw [norm_pow, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
            Real.norm_of_nonneg hc0, norm_one]
      _ ≤ 4 := by nlinarith [norm_nonneg w]
  have e2 : ‖(w + 1) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    have := norm_add_le w 1
    rw [norm_one] at this
    nlinarith [norm_nonneg (w + 1)]
  nlinarith

/-- `√(a² + b²) ≤ a + b²/(2a)` for `a > 0`. -/
theorem sqrt_sq_add_sq_le {a b : ℝ} (ha : 0 < a) : Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b ^ 2 / (2 * a) := by
  have h : 0 ≤ a + b ^ 2 / (2 * a) := by positivity
  rw [show a + b ^ 2 / (2 * a) = Real.sqrt ((a + b ^ 2 / (2 * a)) ^ 2) from (Real.sqrt_sq h).symm]
  apply Real.sqrt_le_sqrt
  have : (a + b ^ 2 / (2 * a)) ^ 2 = a ^ 2 + b ^ 2 + (b ^ 2 / (2 * a)) ^ 2 := by
    field_simp
    ring
  rw [this]
  nlinarith [sq_nonneg (b ^ 2 / (2 * a))]

/-- **Growth near the arc**: with `γ = c - cos τ > 0`, if `1/2 ≤ ‖w‖`, `(‖w‖ - 1)² ≤ γ ‖w‖`
and `Re w ≤ ‖w‖ cos τ`, then `‖ℓ(w) - 1‖ + ‖ℓ(w) + 1‖ ≤ 2 + (4 + 13/γ)(‖w‖ - 1)²`. -/
theorem refined_bound {τ : ℝ} (hτ : 0 < Real.cos τ) (hγ : 0 < c - Real.cos τ) (hc1 : c ≤ 1)
    {w : ℂ} (hw : w ≠ 0) (ht1 : 1 / 2 ≤ ‖w‖)
    (htγ : (‖w‖ - 1) ^ 2 ≤ (c - Real.cos τ) * ‖w‖) (hx : w.re ≤ ‖w‖ * Real.cos τ) :
    ‖ell c w - 1‖ + ‖ell c w + 1‖ ≤ 2 + (4 + 13 / (c - Real.cos τ)) * (‖w‖ - 1) ^ 2 := by
  set t := ‖w‖ with ht
  set γ := c - Real.cos τ with hγdef
  have hc : 0 < 1 + c := by linarith [Real.cos_le_one τ]
  have ht0 : 0 < t := by linarith
  set x := w.re with hxdef
  set y := w.im with hydef
  have hxy : x ^ 2 + y ^ 2 = t ^ 2 := by
    rw [hxdef, hydef, ht, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hxt : |x| ≤ t := by
    rw [ht]
    exact Complex.abs_re_le_norm w
  -- `w² - 2cw + 1 = w (w + w⁻¹ - 2c)`, whose second factor has real part `-a` and imaginary part `b`
  set a := 2 * c - x * (1 + 1 / t ^ 2) with hadef
  set b := y * (1 - 1 / t ^ 2) with hbdef
  have hz : w ^ 2 - 2 * c * w + 1 = w * (w + w⁻¹ - 2 * c) := by
    field_simp
    ring
  have hzre : (w + w⁻¹ - 2 * c).re = -a := by
    simp only [Complex.sub_re, Complex.add_re, Complex.inv_re, Complex.normSq_eq_norm_sq,
      Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im]
    rw [← ht, hadef, ← hxdef]
    ring
  have hzim : (w + w⁻¹ - 2 * c).im = b := by
    simp only [Complex.sub_im, Complex.add_im, Complex.inv_im, Complex.normSq_eq_norm_sq,
      Complex.mul_im, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im]
    rw [← ht, hbdef, ← hydef]
    ring
  -- `a ≥ γ`
  have ha : γ ≤ a := by
    rcases le_or_gt 0 x with hx0 | hx0
    · have h1 : x * (1 + 1 / t ^ 2) ≤ t * Real.cos τ * (1 + 1 / t ^ 2) :=
        mul_le_mul_of_nonneg_right hx (by positivity)
      have h2 : t * Real.cos τ * (1 + 1 / t ^ 2) = Real.cos τ * (2 + (t - 1) ^ 2 / t) := by
        field_simp
        ring
      have h3 : Real.cos τ * ((t - 1) ^ 2 / t) ≤ γ := by
        have hcos1 : Real.cos τ ≤ 1 := Real.cos_le_one τ
        calc Real.cos τ * ((t - 1) ^ 2 / t) ≤ 1 * ((t - 1) ^ 2 / t) := by
              gcongr
          _ ≤ γ := by rw [one_mul, div_le_iff₀ ht0]; linarith
      rw [hadef]
      nlinarith
    · have : x * (1 + 1 / t ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx0.le (by positivity)
      rw [hadef]
      linarith
  have ha0 : 0 < a := lt_of_lt_of_le hγ ha
  -- `‖w² - 2cw + 1‖ ≤ t (a + b²/(2a))`
  have hn1 : ‖w ^ 2 - 2 * c * w + 1‖ ≤ t * (a + b ^ 2 / (2 * a)) := by
    rw [hz, norm_mul, ← ht, Complex.norm_eq_sqrt_sq_add_sq, hzre, hzim, neg_sq]
    exact mul_le_mul_of_nonneg_left (sqrt_sq_add_sq_le ha0) ht0.le
  have hta : t * a ≤ 2 * c * t - 2 * x + (t - 1) ^ 2 := by
    rw [hadef]
    have : t * (2 * c - x * (1 + 1 / t ^ 2)) = 2 * c * t - 2 * x - x * ((t - 1) ^ 2 / t) := by
      field_simp
      ring
    rw [this]
    have h1 : -(x * ((t - 1) ^ 2 / t)) ≤ (t - 1) ^ 2 := by
      have h2 : |x * ((t - 1) ^ 2 / t)| ≤ (t - 1) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (t - 1) ^ 2 / t)]
        calc |x| * ((t - 1) ^ 2 / t) ≤ t * ((t - 1) ^ 2 / t) := by gcongr
          _ = (t - 1) ^ 2 := by field_simp
      linarith [neg_abs_le (x * ((t - 1) ^ 2 / t))]
    linarith
  have htb : t * (b ^ 2 / (2 * a)) ≤ (t - 1) ^ 2 * (25 / (4 * γ)) := by
    have hb2 : b ^ 2 ≤ (t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 2 := by
      rw [hbdef, mul_pow]
      have hy2 : y ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg x]
      have : (1 - 1 / t ^ 2) ^ 2 = (t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 4 := by
        field_simp
        ring
      rw [this]
      calc y ^ 2 * ((t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 4)
          ≤ t ^ 2 * ((t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 4) := by gcongr
        _ = (t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 2 := by field_simp
    have h1 : t * (b ^ 2 / (2 * a)) ≤ t * (b ^ 2 / (2 * γ)) := by
      gcongr
    have h2 : t * (b ^ 2 / (2 * γ)) ≤ t * ((t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 2 / (2 * γ)) := by
      gcongr
    have h3 : t * ((t - 1) ^ 2 * (t + 1) ^ 2 / t ^ 2 / (2 * γ)) =
        (t - 1) ^ 2 * ((t + 1) ^ 2 / (2 * γ * t)) := by
      field_simp
    have h4 : (t + 1) ^ 2 / (2 * γ * t) ≤ 25 / (4 * γ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc t * (b ^ 2 / (2 * a)) ≤ (t - 1) ^ 2 * ((t + 1) ^ 2 / (2 * γ * t)) := by
          rw [← h3]; exact h1.trans h2
      _ ≤ (t - 1) ^ 2 * (25 / (4 * γ)) := by gcongr
  have hw1 : ‖w + 1‖ ^ 2 = t ^ 2 + 2 * x + 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, add_zero, ← hxdef, ← hydef]
    linear_combination hxy
  have hn2 : ‖ell c w + 1‖ = (t ^ 2 + 2 * x + 1) / ((1 + c) * t) := by
    rw [ell_add_one hc hw, norm_div, norm_mul, norm_one_add_c hc, ← ht, norm_pow, hw1]
  rw [ell_sub_one hc hw, norm_div, norm_mul, norm_one_add_c hc, ← ht, hn2, ← add_div,
    div_le_iff₀ (by positivity)]
  have hS : ‖w ^ 2 - 2 * c * w + 1‖ + (t ^ 2 + 2 * x + 1) ≤
      2 * t * (1 + c) + (t - 1) ^ 2 * (2 + 25 / (4 * γ)) := by
    linarith [hn1, hta, htb]
  have hfac : (t - 1) ^ 2 * (2 + 25 / (4 * γ)) ≤
      (4 + 13 / γ) * (t - 1) ^ 2 * ((1 + c) * t) := by
    have hct : 1 / 2 ≤ (1 + c) * t := by nlinarith
    have hγ' : 0 < γ := hγ
    have : 2 + 25 / (4 * γ) ≤ (4 + 13 / γ) * (1 / 2) := by
      rw [show (4 + 13 / γ) * (1 / 2) = 2 + 13 / (2 * γ) by field_simp; ring]
      gcongr ?_ + ?_
      · rfl
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    calc (t - 1) ^ 2 * (2 + 25 / (4 * γ)) ≤ (t - 1) ^ 2 * ((4 + 13 / γ) * (1 / 2)) := by gcongr
      _ ≤ (t - 1) ^ 2 * ((4 + 13 / γ) * ((1 + c) * t)) := by gcongr
      _ = (4 + 13 / γ) * (t - 1) ^ 2 * ((1 + c) * t) := by ring
  linarith [hS, hfac]

/-! ### The polynomial on the notched disk -/

/-- `(1 - s)ᴷ (1 + K s) ≤ 1` for `0 ≤ s ≤ 1`. -/
theorem one_sub_pow_mul_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (K : ℕ) :
    (1 - s) ^ K * (1 + K * s) ≤ 1 := by
  have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ s) K
  calc (1 - s) ^ K * (1 + K * s) ≤ (1 - s) ^ K * (1 + s) ^ K := by
        gcongr
    _ = (1 - s ^ 2) ^ K := by rw [← mul_pow]; ring
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- `R = 1 + (C + 1) s` has `R + R⁻¹ ≥ 2 + C s²` for `0 ≤ s ≤ 1/2`. -/
theorem two_add_le_add_inv {C s : ℝ} (hC : 0 ≤ C) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    2 + C * s ^ 2 ≤ (1 + (C + 1) * s) + (1 + (C + 1) * s)⁻¹ := by
  have hpos : 0 < 1 + (C + 1) * s := by positivity
  rw [← sub_nonneg]
  have e : (1 + (C + 1) * s) + (1 + (C + 1) * s)⁻¹ - (2 + C * s ^ 2) =
      s ^ 2 * ((C + 1) ^ 2 - C * (1 + (C + 1) * s)) / (1 + (C + 1) * s) := by
    field_simp
    ring
  rw [e]
  refine div_nonneg (mul_nonneg (sq_nonneg s) ?_) hpos.le
  nlinarith [mul_nonneg hC hs0, mul_nonneg (mul_nonneg hC hC) hs0]

/-- **A monic polynomial small on a notched disk.** For every notch half-angle `0 < τ < π/2` and
every `ρ₀ < 1 < ρ₃` there are radii `ρ₀ ≤ ρ₁ < 1 < ρ₂ ≤ ρ₃` and `q < 1` such that for every `D` some
monic polynomial is at most `2 qᴰ` in modulus on the circle of radius `ρ₁` and on the part of the
annulus `ρ₁ ≤ ‖w‖ ≤ ρ₂` where `Re w ≤ ‖w‖ cos τ`. -/
theorem exists_notch_poly {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < Real.pi / 2) {ρ₀ ρ₃ : ℝ}
    (hρ₀ : ρ₀ < 1) (hρ₃ : 1 < ρ₃) :
    ∃ ρ₁ ρ₂ q : ℝ, ρ₀ ≤ ρ₁ ∧ 1 / 2 ≤ ρ₁ ∧ ρ₁ < 1 ∧ 1 < ρ₂ ∧ ρ₂ ≤ ρ₃ ∧ 0 < q ∧ q < 1 ∧
      ∀ D : ℕ, ∃ P : ℂ[X], P.Monic ∧
        (∀ w : ℂ, ‖w‖ = ρ₁ → ‖P.eval w‖ ≤ 2 * q ^ D) ∧
        (∀ w : ℂ, ρ₁ ≤ ‖w‖ → ‖w‖ ≤ ρ₂ → w.re ≤ ‖w‖ * Real.cos τ → ‖P.eval w‖ ≤ 2 * q ^ D) := by
  set c := Real.cos (τ / 2) with hcdef
  have hpi := Real.pi_pos
  have hcosτ : 0 < Real.cos τ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hτ1⟩
  have hlt : Real.cos τ < c :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hc1 : c < 1 := by
    rw [hcdef, ← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
  have hc0 : 0 ≤ c := (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
  have hc : 0 < 1 + c := by linarith
  set γ := c - Real.cos τ with hγdef
  have hγ : 0 < γ := by linarith
  have hγ1 : γ ≤ 1 := by linarith
  set C₁ := 4 + 13 / γ with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set κ := C₁ + 1 with hκ
  -- the inner radius
  set ρ₁ := max ρ₀ (max (1 / 2) (1 - γ / 4)) with hρ₁def
  have hρ₁1 : ρ₁ < 1 := max_lt hρ₀ (max_lt (by norm_num) (by linarith))
  have hρ₁h : 1 / 2 ≤ ρ₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hρ₁γ : 1 - γ / 4 ≤ ρ₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  -- the exponent `K`
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 16) hρ₁1
  set K := max n ⌈κ⌉₊ with hKdef
  have hK1 : κ ≤ K + 1 := by
    have : κ ≤ (⌈κ⌉₊ : ℝ) := Nat.le_ceil κ
    have : (⌈κ⌉₊ : ℝ) ≤ K := by exact_mod_cast le_max_right _ _
    linarith
  have hρ₁0 : 0 ≤ ρ₁ := by linarith
  have hK2 : 8 * ρ₁ ^ K ≤ 1 / 2 := by
    have : ρ₁ ^ K ≤ ρ₁ ^ n := pow_le_pow_of_le_one hρ₁0 hρ₁1.le (le_max_left _ _)
    linarith
  -- the outer radius, by continuity at `η = 0`
  set q₂ := (1 + (1 + c) / 2) / 2 with hq₂
  have hq₂c : (1 + c) / 2 < q₂ := by rw [hq₂]; linarith
  have hq₂1 : q₂ < 1 := by rw [hq₂]; linarith
  have hcont : ContinuousAt (fun η : ℝ => (1 + c) / 2 * (1 + η) ^ (K + 1) * (1 + κ * η)) 0 := by
    fun_prop
  have hev : ∀ᶠ η in nhds (0 : ℝ), (1 + c) / 2 * (1 + η) ^ (K + 1) * (1 + κ * η) < q₂ :=
    hcont.eventually (gt_mem_nhds (by simpa using hq₂c))
  obtain ⟨ε, hε, hεη⟩ := Metric.eventually_nhds_iff.1 hev
  set η := min (min (ε / 2) (ρ₃ - 1)) (min (1 / 2) (γ / 4)) with hηdef
  have hη0 : 0 < η :=
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by norm_num) (by linarith))
  have hη3 : η ≤ ρ₃ - 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hηε : η < ε := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hη2 : η ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηγ : η ≤ γ / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hfη : (1 + c) / 2 * (1 + η) ^ (K + 1) * (1 + κ * η) < q₂ :=
    hεη (by rw [Real.dist_eq, sub_zero, abs_of_pos hη0]; exact hηε)
  set q := max (1 / 2) q₂ with hqdef
  refine ⟨ρ₁, 1 + η, q, le_max_left _ _, hρ₁h, hρ₁1, by linarith, by linarith,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), max_lt (by norm_num) hq₂1, fun D => ?_⟩
  refine ⟨notchPoly c K D, monic_notchPoly hc K D, fun w hw => ?_, fun w hw1 hw2 hre => ?_⟩
  · -- the notch arc: the crude bound
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw; linarith
    have hR : (1 : ℝ) ≤ 8 / ρ₁ := by rw [le_div_iff₀ (by linarith)]; linarith
    have hb := norm_eval_notchPoly_le hc K D hw0 hR
      ((crude_bound hc0 hc1.le hw0 (by rw [hw]; exact hρ₁1.le)).trans (by
        rw [hw]; exact le_add_of_nonneg_right (inv_nonneg.2 (by positivity))))
    refine hb.trans ?_
    rw [hw]
    gcongr
    calc (1 + c) / 2 * ρ₁ ^ (K + 1) * (8 / ρ₁) = (1 + c) / 2 * (8 * ρ₁ ^ K) := by
          field_simp
          ring
      _ ≤ 1 * (1 / 2) := by gcongr; linarith
      _ ≤ q := by rw [one_mul]; exact le_max_left _ _
  · -- the annulus away from the notch: the refined bound
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw1; linarith
    set t := ‖w‖ with ht
    have hs : |t - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have htγ : (t - 1) ^ 2 ≤ γ * t := by
      have h1 : (t - 1) ^ 2 ≤ (γ / 4) ^ 2 := by
        rw [← sq_abs]
        have : |t - 1| ≤ γ / 4 := by rw [abs_le]; constructor <;> linarith
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      nlinarith
    have hrb := refined_bound hcosτ (by linarith) hc1.le hw0 (by linarith) htγ hre
    have hR : (1 : ℝ) ≤ 1 + κ * |t - 1| := le_add_of_nonneg_right (by positivity)
    have hb := norm_eval_notchPoly_le hc K D hw0 hR
      (hrb.trans (two_add_le_add_inv hC₁0 (abs_nonneg _) hs |>.trans_eq' (by rw [sq_abs])))
    refine hb.trans ?_
    gcongr
    rcases le_total t 1 with ht1 | ht1
    · -- inside: `t^(K+1) (1 + κ (1 - t)) ≤ 1`
      have h1 := one_sub_pow_mul_le (s := 1 - t) (by linarith) (by linarith) (K + 1)
      rw [show 1 - (1 - t) = t by ring] at h1
      have h2 : t ^ (K + 1) * (1 + κ * |t - 1|) ≤ 1 := by
        rw [abs_of_nonpos (by linarith), show -(t - 1) = 1 - t by ring]
        calc t ^ (K + 1) * (1 + κ * (1 - t)) ≤ t ^ (K + 1) * (1 + ((K + 1 : ℕ) : ℝ) * (1 - t)) := by
              gcongr
              push_cast
              exact hK1
          _ ≤ 1 := h1
      calc (1 + c) / 2 * t ^ (K + 1) * (1 + κ * |t - 1|)
          = (1 + c) / 2 * (t ^ (K + 1) * (1 + κ * |t - 1|)) := by ring
        _ ≤ (1 + c) / 2 * 1 := by gcongr
        _ ≤ q := by rw [mul_one]; exact (hq₂c.le).trans (le_max_right _ _)
    · -- outside: monotone up to `1 + η`
      rw [abs_of_nonneg (by linarith)]
      calc (1 + c) / 2 * t ^ (K + 1) * (1 + κ * (t - 1))
          ≤ (1 + c) / 2 * (1 + η) ^ (K + 1) * (1 + κ * η) := by
            gcongr
            linarith
        _ ≤ q := hfη.le.trans (le_max_right _ _)

end Rule30Equivalents.SzegoPolynomial
