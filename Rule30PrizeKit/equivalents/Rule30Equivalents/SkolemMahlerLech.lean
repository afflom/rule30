module

public import Rule30Equivalents.Strassmann
public import Rule30Equivalents.LinearRelations
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Skolem–Mahler–Lech theorem, and Problem 1 as a zero set over `ℚ`

Problem 1 holds iff the black times of the center column are not the zero set
of any linear recurrence sequence over `ℚ`. The library already has the sufficient direction
(`LinearRelations.problem1_of_not_zero_set`). The converse needs the **Skolem–Mahler–Lech
theorem**: the zero set of a linear recurrence sequence over `ℚ` is eventually periodic.

The proof is the classical `p`-adic one.
* Reduction (`epSet_zeros`, by induction on the order): if the coefficient `a₀` is `0`, the shifted
  sequence solves a shorter recurrence. Otherwise choose an odd prime `p` that divides no
  denominator of the coefficients and initial values, nor the numerator of `a₀`. The state vectors
  `(u(n), …, u(n + d))` are `Aⁿ v` for a companion matrix `A` over `ℤ_[p]` that is invertible
  mod `p`.
* Interpolation (`epSet_zeros_matrix`): `A mod p` has finite order `m`, so `Aᵐ = 1 + p B`
  (`exists_pow_eq_one_add`). For each residue `r`, `u(r + m n) = ∑ₖ (n choose k) pᵏ βₖ`, and
  `n choose k = (n)ₖ / k!` turns this into a power series in `n` whose coefficients tend to `0`,
  since `‖pᵏ / k!‖ ≤ p^{-k/2}` by Legendre's formula (`tendsto_gam`, `psum_coef_natCast`).
* Strassmann's theorem (`Strassmann.eq_zero_of_infinite_natCast_zeros`): for each `r` the zeros
  `n` are finitely many or all of `ℕ`, so the zero set is eventually periodic with period `m`.

* `skolem_mahler_lech`: the zero set of a linear recurrence sequence over `ℚ` is eventually
  periodic.
* `problem1_iff_not_LRS_zero_set`.

Sources: T. Skolem, *Ein Verfahren zur Behandlung gewisser exponentialer Gleichungen*, 8. Skand.
Mat. Kongr. (1934) 163–188; K. Mahler, *Eine arithmetische Eigenschaft der Taylor-Koeffizienten
rationaler Funktionen*, Proc. Akad. Wet. Amsterdam 38 (1935) 50–60; C. Lech, *A note on recurring
series*, Ark. Mat. 2 (1953) 417–421; the exposition of T. Tao, *Structure and Randomness*, §1.9.
-/

@[expose] public section

namespace Rule30Equivalents.SkolemMahlerLech

open Filter Topology Finset Matrix Ruliology.CellularAutomata

/-- An eventually periodic set of natural numbers. -/
def EPSet (Z : Set ℕ) : Prop := ∃ T P, 0 < P ∧ ∀ t, T ≤ t → (t + P ∈ Z ↔ t ∈ Z)

/-- If along each residue class mod `m` the set is finite or everything, it is eventually
periodic. -/
theorem epSet_of_residues {Z : Set ℕ} {m : ℕ} (hm : 0 < m)
    (h : ∀ r, {n | r + m * n ∈ Z}.Finite ∨ ∀ n, r + m * n ∈ Z) : EPSet Z := by
  have h' : ∀ r, ∃ N, ∀ n, N ≤ n → (r + m * (n + 1) ∈ Z ↔ r + m * n ∈ Z) := fun r => by
    rcases h r with hf | ha
    · obtain ⟨N, hN⟩ := hf.bddAbove
      refine ⟨N + 1, fun n hn => ?_⟩
      have h1 : r + m * n ∉ Z := fun hz => by
        have := hN (show n ∈ {n | r + m * n ∈ Z} from hz); omega
      have h2 : r + m * (n + 1) ∉ Z := fun hz => by
        have := hN (show n + 1 ∈ {n | r + m * n ∈ Z} from hz); omega
      simp [h1, h2]
    · exact ⟨0, fun n _ => by simp [ha]⟩
  choose N hN using h'
  refine ⟨m * (range m).sup N, m, hm, fun t ht => ?_⟩
  have hr : t % m < m := Nat.mod_lt _ hm
  have ht' : t % m + m * (t / m) = t := Nat.mod_add_div t m
  have hq : (range m).sup N ≤ t / m := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact ht)
  have := hN (t % m) (t / m) ((Finset.le_sup (Finset.mem_range.2 hr)).trans hq)
  rw [mul_add, mul_one, ← add_assoc, ht'] at this
  exact this

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### `p`-adic estimates -/

theorem norm_natCast_eq {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h := Padic.eq_padicNorm (p := p) (n : ℚ)
  rw [Rat.cast_natCast] at h
  rw [h, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat]
  push_cast
  rfl

theorem norm_rat_eq_one {q : ℚ} (hq : q ≠ 0) (hnum : ¬ (p : ℤ) ∣ q.num) (hden : ¬ p ∣ q.den) :
    ‖(q : ℚ_[p])‖ = 1 := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq, padicValRat,
    padicValInt.eq_zero_of_not_dvd hnum, padicValNat.eq_zero_of_not_dvd hden]
  simp

/-- The coefficients `pᵏ βₖ / k!` of the interpolating series. -/
noncomputable def gam (β : ℕ → ℤ_[p]) (k : ℕ) : ℚ_[p] :=
  (p : ℚ_[p]) ^ k / (k.factorial : ℚ_[p]) * (β k : ℚ_[p])

/-- `‖pᵏ βₖ / k!‖ → 0` for `p ≠ 2`, by Legendre's formula `v_p(k!) ≤ k / 2`. -/
theorem tendsto_gam (hp2 : p ≠ 2) (β : ℕ → ℤ_[p]) : Tendsto (gam β) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hbound : ∀ k, ‖gam β k‖ ≤ ((p : ℝ)⁻¹) ^ (k / 2) := fun k => by
    have hv : 2 * padicValNat p k.factorial ≤ k := by
      have := sub_one_mul_padicValNat_factorial (p := p) k
      have h2 : 2 * padicValNat p k.factorial ≤ (p - 1) * padicValNat p k.factorial :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rw [gam, norm_mul, norm_div, norm_pow, Padic.norm_p,
      norm_natCast_eq (Nat.factorial_ne_zero k)]
    have hβ : ‖(β k : ℚ_[p])‖ ≤ 1 := (β k).2
    calc (p : ℝ)⁻¹ ^ k / (p : ℝ) ^ (-(padicValNat p k.factorial : ℤ)) * ‖(β k : ℚ_[p])‖
        ≤ (p : ℝ)⁻¹ ^ k / (p : ℝ) ^ (-(padicValNat p k.factorial : ℤ)) := by
          exact mul_le_of_le_one_right (div_nonneg (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg p)) k)
            (zpow_nonneg (Nat.cast_nonneg p) _)) hβ
      _ = (p : ℝ) ^ ((padicValNat p k.factorial : ℤ) - k) := by
          rw [inv_pow, ← zpow_natCast, ← zpow_neg, div_eq_mul_inv, ← zpow_neg, ← zpow_add₀
            (by exact_mod_cast hp.out.ne_zero)]
          ring_nf
      _ ≤ (p : ℝ) ^ (-((k / 2 : ℕ) : ℤ)) := zpow_le_zpow_right₀ hp1.le (by omega)
      _ = ((p : ℝ)⁻¹) ^ (k / 2) := by rw [zpow_neg, zpow_natCast, inv_pow]
  refine squeeze_zero_norm hbound ?_
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)).comp
    (Nat.tendsto_div_const_atTop two_ne_zero)

/-! ### From the binomial basis to a power series -/

/-- The power series coefficients of `∑ₖ γₖ (x)ₖ`, where `(x)ₖ` is the falling factorial. -/
noncomputable def coef (γ : ℕ → ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  ∑' k, γ k * (((descPochhammer ℤ k).coeff j : ℤ) : ℚ_[p])

theorem coeff_descPochhammer_eq_zero {k j : ℕ} (h : k < j) : (descPochhammer ℤ k).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree])

theorem norm_term_le (γ : ℕ → ℚ_[p]) (k j : ℕ) (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    ‖γ k * (((descPochhammer ℤ k).coeff j : ℤ) : ℚ_[p]) * x ^ j‖ ≤ ‖γ k‖ := by
  rw [norm_mul, norm_mul, norm_pow]
  calc ‖γ k‖ * ‖(((descPochhammer ℤ k).coeff j : ℤ) : ℚ_[p])‖ * ‖x‖ ^ j ≤ ‖γ k‖ * 1 * 1 := by
        gcongr
        · exact Padic.norm_int_le_one _
        · exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖γ k‖ := by ring

theorem summable_coef_term {γ : ℕ → ℚ_[p]} (hγ : Tendsto γ atTop (𝓝 0)) (j : ℕ) :
    Summable fun k => γ k * (((descPochhammer ℤ k).coeff j : ℤ) : ℚ_[p]) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun k => ?_) (tendsto_zero_iff_norm_tendsto_zero.1 hγ)
  simpa using norm_term_le γ k j 1 (by simp)

theorem tendsto_coef {γ : ℕ → ℚ_[p]} (hγ : Tendsto γ atTop (𝓝 0)) :
    Tendsto (coef γ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 (tendsto_zero_iff_norm_tendsto_zero.1 hγ)) (ε / 2)
    (by linarith)
  refine ⟨K, fun j hj => ?_⟩
  have hb : ‖coef γ j‖ ≤ ε / 2 := by
    refine Strassmann.norm_tsum_le (summable_coef_term hγ j) (by linarith) fun k => ?_
    by_cases hkj : k < j
    · rw [coeff_descPochhammer_eq_zero hkj]; simp; linarith
    · have := hK k (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
      have h1 : ‖γ k * (((descPochhammer ℤ k).coeff j : ℤ) : ℚ_[p])‖ ≤ ‖γ k‖ := by
        simpa using norm_term_le γ k j 1 (by simp)
      exact h1.trans this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- At a natural number `n`, the power series `∑ⱼ coef γ j · nʲ` equals `∑ₖ γₖ (n)ₖ`. -/
theorem psum_coef_natCast {γ : ℕ → ℚ_[p]} (hγ : Tendsto γ atTop (𝓝 0)) (n : ℕ) :
    Strassmann.psum (coef γ) n = ∑' k, γ k * (n.descFactorial k : ℚ_[p]) := by
  set ψ : ℕ → ℕ → ℚ_[p] := fun k j =>
    γ k * (((descPochhammer ℤ k).coeff j : ℤ) : ℚ_[p]) * (n : ℚ_[p]) ^ j
  have hn : ‖(n : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) n
  have hsum : Summable (Function.uncurry ψ) :=
    Strassmann.summable_of_rows (tendsto_zero_iff_norm_tendsto_zero.1 hγ)
      (fun k j => norm_term_le γ k j _ hn) fun k j hkj => by
        simp [ψ, coeff_descPochhammer_eq_zero hkj]
  have hrow : ∀ k, ∑' j, ψ k j = γ k * (n.descFactorial k : ℚ_[p]) := fun k => by
    rw [tsum_eq_sum (s := range (k + 1)) fun j hj => by
      simp [ψ, coeff_descPochhammer_eq_zero (by simpa using hj : k < j)]]
    simp only [ψ, mul_assoc, ← Finset.mul_sum]
    congr 1
    have h := descPochhammer_eval_eq_descFactorial ℤ n k
    rw [Polynomial.eval_eq_sum_range, descPochhammer_natDegree] at h
    have h' := congrArg (fun z : ℤ => (z : ℚ_[p])) h
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h'
    exact h'
  rw [Strassmann.psum, show (∑' k, γ k * (n.descFactorial k : ℚ_[p])) = ∑' k, ∑' j, ψ k j from
    tsum_congr fun k => (hrow k).symm, ← hsum.tsum_comm' (fun k => hsum.prod_factor k)
    fun j => hsum.prod_symm.prod_factor j]
  refine tsum_congr fun j => ?_
  rw [coef, ← (summable_coef_term hγ j).tsum_mul_right]

/-! ### The matrix case -/

/-- A `p`-adic matrix invertible mod `p` has a power `1 + p B`. -/
theorem exists_pow_eq_one_add {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ_[p])
    (hA : IsUnit (A.map PadicInt.toZMod)) :
    ∃ m, 0 < m ∧ ∃ B : Matrix (Fin d) (Fin d) ℤ_[p], A ^ m = 1 + (p : ℤ_[p]) • B := by
  obtain ⟨m, hm, hpow⟩ : ∃ m, 0 < m ∧ (A.map PadicInt.toZMod) ^ m = 1 := by
    refine ⟨orderOf hA.unit, (isOfFinOrder_of_finite hA.unit).orderOf_pos, ?_⟩
    have h := congrArg Units.val (pow_orderOf_eq_one hA.unit)
    rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h
  refine ⟨m, hm, ?_⟩
  have hmap : ∀ i j, PadicInt.toZMod ((A ^ m - 1) i j) = 0 := fun i j => by
    have h1 : (A ^ m).map PadicInt.toZMod = (A.map PadicInt.toZMod) ^ m := by
      simpa using map_pow (PadicInt.toZMod (p := p)).mapMatrix A m
    have h2 := congrFun (congrFun h1 i) j
    rw [hpow, Matrix.map_apply] at h2
    rw [Matrix.sub_apply, map_sub, h2]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have hdiv : ∀ i j, ∃ c, (A ^ m - 1) i j = (p : ℤ_[p]) * c := fun i j => by
    have : (A ^ m - 1) i j ∈ Ideal.span {(p : ℤ_[p])} := by
      rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
      exact hmap i j
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose B hB using hdiv
  refine ⟨Matrix.of B, ?_⟩
  ext i j
  have := hB i j
  rw [Matrix.sub_apply] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← this]
  ring_nf

/-- `((1 + p B)ⁿ w)ᵢ = ∑ₖ (n choose k) pᵏ (Bᵏ w)ᵢ`. -/
theorem mulVec_pow_eq_sum {d : ℕ} (B : Matrix (Fin d) (Fin d) ℤ_[p]) (w : Fin d → ℤ_[p])
    (i : Fin d) (n : ℕ) : ((1 + (p : ℤ_[p]) • B) ^ n *ᵥ w) i =
      ∑ k ∈ range (n + 1), (p : ℤ_[p]) ^ k * n.choose k * (B ^ k *ᵥ w) i := by
  rw [add_comm, (Commute.one_right _).add_pow]
  simp only [one_pow, mul_one, smul_pow]
  rw [show (∑ k ∈ range (n + 1), ((p : ℤ_[p]) ^ k • B ^ k) * (n.choose k : Matrix _ _ ℤ_[p])) =
      ∑ k ∈ range (n + 1), ((p : ℤ_[p]) ^ k * n.choose k) • B ^ k from
    Finset.sum_congr rfl fun k _ => by
      rw [← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, mul_comm]]
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

/-- **The matrix case of Skolem–Mahler–Lech**: for a `p`-adic matrix `A` invertible mod `p`
(`p` odd), the zero set of `n ↦ (Aⁿ v)ᵢ` is eventually periodic. -/
theorem epSet_zeros_matrix (hp2 : p ≠ 2) {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ_[p])
    (hA : IsUnit (A.map PadicInt.toZMod)) (v : Fin d → ℤ_[p]) (i : Fin d) :
    EPSet {n | (A ^ n *ᵥ v) i = 0} := by
  obtain ⟨m, hm, B, hB⟩ := exists_pow_eq_one_add A hA
  refine epSet_of_residues hm fun r => ?_
  set w := A ^ r *ᵥ v
  set β : ℕ → ℤ_[p] := fun k => (B ^ k *ᵥ w) i
  have hγ := tendsto_gam hp2 β
  have hf : ∀ n, (((A ^ (r + m * n) *ᵥ v) i : ℤ_[p]) : ℚ_[p]) =
      ∑' k, gam β k * (n.descFactorial k : ℚ_[p]) := fun n => by
    rw [show r + m * n = m * n + r by ring, pow_add, pow_mul, hB, ← Matrix.mulVec_mulVec,
      mulVec_pow_eq_sum, tsum_eq_sum (s := range (n + 1)) fun k hk => by
        rw [(Nat.descFactorial_eq_zero_iff_lt).2 (by simpa using hk), Nat.cast_zero, mul_zero]]
    rw [PadicInt.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [gam, Nat.descFactorial_eq_factorial_mul_choose]
    have hk : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, Nat.cast_mul]
    field_simp
    simp only [β, w]
  have hdich : {n | (A ^ (r + m * n) *ᵥ v) i = 0}.Finite ∨
      ∀ n, (A ^ (r + m * n) *ᵥ v) i = 0 := by
    by_cases hinf : {n | (A ^ (r + m * n) *ᵥ v) i = 0}.Infinite
    · right
      have hz : {n : ℕ | Strassmann.psum (coef (gam β)) n = 0}.Infinite :=
        hinf.mono fun n hn => by
          simp only [Set.mem_ofPred_eq] at hn ⊢
          rw [psum_coef_natCast hγ, ← hf, hn, PadicInt.coe_zero]
      have h0 := Strassmann.eq_zero_of_infinite_natCast_zeros (tendsto_coef hγ) hz
      intro n
      have h1 := psum_coef_natCast hγ n
      rw [← hf] at h1
      have h2 : Strassmann.psum (coef (gam β)) n = 0 := by simp [Strassmann.psum, h0]
      rw [h2, eq_comm, PadicInt.coe_eq_zero] at h1
      exact h1
    · exact Or.inl (Set.not_infinite.1 hinf)
  simpa only [Set.mem_ofPred_eq] using hdich

/-! ### Recurrences over `ℚ` -/

/-- The companion matrix of `c`: rows shift, and the last row holds the coefficients. -/
def companion {R : Type*} [CommRing R] {d : ℕ} (c : Fin (d + 1) → R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of fun i j => if (i : ℕ) < d then (if (j : ℕ) = i + 1 then 1 else 0) else c j

theorem companion_mulVec_of_lt {R : Type*} [CommRing R] {d : ℕ} (c x : Fin (d + 1) → R)
    (i : Fin (d + 1)) (hi : (i : ℕ) < d) : (companion c *ᵥ x) i = x ⟨i + 1, by omega⟩ := by
  simp only [companion, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_eq_left hi]
  rw [Finset.sum_eq_single ⟨i + 1, by omega⟩ (fun b _ hb => by
    rw [ite_eq_right fun h => hb (Fin.ext h), zero_mul]) (by simp)]
  simp

theorem companion_mulVec_last {R : Type*} [CommRing R] {d : ℕ} (c x : Fin (d + 1) → R) :
    (companion c *ᵥ x) (Fin.last d) = ∑ j, c j * x j := by
  simp [companion, Matrix.mulVec, dotProduct]

theorem map_companion {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (c : Fin (d + 1) → R) : (companion c).map f = companion (f ∘ c) := by
  ext i j
  simp only [companion, Matrix.map_apply, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> simp

/-- A rational number whose denominator is prime to `p`, as a `p`-adic integer. -/
noncomputable def toZp (q : ℚ) (h : ¬ p ∣ q.den) : ℤ_[p] := ⟨q, Padic.norm_rat_le_one h⟩

/-- **Skolem–Mahler–Lech when `a₀ ≠ 0`.** -/
theorem epSet_zeros_of_coeff_ne_zero {d : ℕ} (a : Fin (d + 1) → ℚ) (ha0 : a 0 ≠ 0) (u : ℕ → ℚ)
    (hu : ∀ n, u (n + (d + 1)) = ∑ i, a i * u (n + i)) : EPSet {n | u n = 0} := by
  -- an odd prime dividing no relevant denominator, nor the numerator of `a₀`
  set D := (∏ i, (a i).den) * (∏ i : Fin (d + 1), (u i).den) * (a 0).num.natAbs
  have hnum0 : 0 < (a 0).num.natAbs := Int.natAbs_pos.2 (Rat.num_ne_zero.2 ha0)
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos (Finset.prod_pos fun i _ => (a i).den_pos)
    (Finset.prod_pos fun i _ => (u i).den_pos)) hnum0
  obtain ⟨p, hpD, hp⟩ := Nat.exists_infinite_primes (D + 3)
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have hndvd : ∀ x : ℕ, 0 < x → x ∣ D → ¬ p ∣ x := fun x hx hxD hpx =>
    absurd (Nat.le_of_dvd hx hpx) (not_le.2 ((Nat.le_of_dvd hD hxD).trans_lt (by omega)))
  have ha : ∀ i, ¬ p ∣ (a i).den := fun i => hndvd _ (a i).den_pos
    (((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).mul_right _).mul_right _)
  have hu0 : ∀ i : Fin (d + 1), ¬ p ∣ (u i).den := fun i => hndvd _ (u i).den_pos
    (((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).mul_left _).mul_right _)
  have hnum : ¬ (p : ℤ) ∣ (a 0).num := fun h =>
    hndvd _ hnum0 (dvd_mul_left _ _) (Int.natCast_dvd.1 h)
  -- the companion matrix over `ℤ_[p]`
  set c : Fin (d + 1) → ℤ_[p] := fun j => toZp (a j) (ha j)
  set A := companion c
  set v : Fin (d + 1) → ℤ_[p] := fun i => toZp (u i) (hu0 i)
  have hstate : ∀ n (i : Fin (d + 1)), (((A ^ n *ᵥ v) i : ℤ_[p]) : ℚ_[p]) = (u (n + i) : ℚ_[p]) := by
    intro n
    induction n with
    | zero => intro i; rw [pow_zero, Matrix.one_mulVec]; simp [v, toZp]
    | succ n ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      by_cases hi : (i : ℕ) < d
      · rw [companion_mulVec_of_lt _ _ _ hi, ih]
        show (u (n + ((i : ℕ) + 1)) : ℚ_[p]) = (u (n + 1 + i) : ℚ_[p])
        rw [show n + ((i : ℕ) + 1) = n + 1 + i by omega]
      · obtain rfl : i = Fin.last d := Fin.ext (by simp; omega)
        rw [companion_mulVec_last, PadicInt.coe_sum]
        simp only [PadicInt.coe_mul, ih, Fin.val_last]
        simp only [c, toZp]
        rw [show n + 1 + d = n + (d + 1) by ring, hu n]
        push_cast
        rfl
  -- `A` is invertible mod `p`
  have hc0 : PadicInt.toZMod (c 0) ≠ 0 := by
    intro h
    have hm : c 0 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h
    have hlt : ‖c 0‖ < 1 := PadicInt.mem_nonunits.1 hm
    have h1 : ‖((a 0 : ℚ) : ℚ_[p])‖ = 1 := norm_rat_eq_one ha0 hnum (ha 0)
    exact absurd (h1 ▸ hlt) (lt_irrefl 1)
  have hunit : IsUnit (A.map PadicInt.toZMod) := by
    rw [map_companion]
    refine Matrix.mulVec_injective_iff_isUnit.1 fun x y hxy => ?_
    have hsucc : ∀ j : Fin d, x j.succ = y j.succ := fun j => by
      have := congrFun hxy j.castSucc
      rwa [companion_mulVec_of_lt _ _ _ (by simp), companion_mulVec_of_lt _ _ _ (by simp),
        show (⟨(j.castSucc : ℕ) + 1, _⟩ : Fin (d + 1)) = j.succ from Fin.ext (by simp)] at this
    funext j
    refine Fin.cases ?_ (fun j => hsucc j) j
    have := congrFun hxy (Fin.last d)
    rw [companion_mulVec_last, companion_mulVec_last, Fin.sum_univ_succ, Fin.sum_univ_succ] at this
    simp only [hsucc, add_left_inj] at this
    exact mul_left_cancel₀ hc0 this
  refine (epSet_zeros_matrix hp2 A hunit v 0).imp fun T => ?_
  refine fun ⟨P, hP, h⟩ => ⟨P, hP, fun t ht => ?_⟩
  have key : ∀ n, u n = 0 ↔ (A ^ n *ᵥ v) 0 = 0 := fun n => by
    rw [← PadicInt.coe_eq_zero, hstate n 0]
    simp
  simpa only [Set.mem_ofPred_eq, key] using h t ht

theorem epSet_zeros_aux (d : ℕ) : ∀ (a : Fin d → ℚ) (u : ℕ → ℚ),
    (∀ n, u (n + d) = ∑ i, a i * u (n + i)) → EPSet {n | u n = 0} := by
  induction d with
  | zero =>
    intro a u hu
    have h : ∀ n, u n = 0 := fun n => by simpa using hu n
    exact ⟨0, 1, one_pos, fun t _ => by simp [h]⟩
  | succ d ih =>
    intro a u hu
    by_cases ha0 : a 0 = 0
    · obtain ⟨T, P, hP, hTP⟩ := ih (fun i => a i.succ) (fun n => u (n + 1)) fun n => by
        have := hu n
        rw [Fin.sum_univ_succ, ha0, zero_mul, zero_add] at this
        show u (n + d + 1) = ∑ i : Fin d, a i.succ * u (n + i + 1)
        rw [show n + d + 1 = n + (d + 1) by ring, this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.val_succ, ← add_assoc]
      refine ⟨T + 1, P, hP, fun t ht => ?_⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have := hTP s (by omega)
      simp only [Set.mem_ofPred_eq] at this ⊢
      rwa [show s + 1 + P = s + P + 1 by ring]
    · exact epSet_zeros_of_coeff_ne_zero a ha0 u hu

/-- **The Skolem–Mahler–Lech theorem** over `ℚ`: the zero set of a linear recurrence sequence is
eventually periodic. -/
theorem skolem_mahler_lech (E : LinearRecurrence ℚ) {u : ℕ → ℚ} (hu : E.IsSolution u) :
    EPSet {n | u n = 0} :=
  epSet_zeros_aux E.order E.coeffs u hu

/-- **Problem 1 ⟺ the black times are not the zero set of a linear recurrence sequence over
`ℚ`**. -/
theorem problem1_iff_not_LRS_zero_set : Rule30Prize.Problem1 ↔
    ∀ (E : LinearRecurrence ℚ) (u : ℕ → ℚ), E.IsSolution u → {t | u t = 0} ≠ {t | c t = true} := by
  refine ⟨fun h E u hu hS => h ?_, LinearRelations.problem1_of_not_zero_set ℚ⟩
  obtain ⟨T, P, hP, hTP⟩ := skolem_mahler_lech E hu
  refine ⟨T, P, hP, fun t ht => ?_⟩
  have := hTP t ht
  rw [hS] at this
  simp only [Set.mem_ofPred_eq] at this
  cases h1 : c (t + P) <;> cases h2 : c t <;> simp_all

end Rule30Equivalents.SkolemMahlerLech
