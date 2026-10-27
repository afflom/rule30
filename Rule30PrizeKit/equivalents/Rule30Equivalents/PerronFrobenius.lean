module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination

/-!
# The Perron–Frobenius theorem for primitive matrices

A real square matrix `A` is primitive (`Matrix.IsPrimitive`) if its entries are nonnegative and
some power `A ^ k` has all entries positive.

* `exists_eigenvector`: `A` has an eigenvalue `r > 0` with an eigenvector `v` whose entries are
  all positive. The proof maximizes the Collatz–Wielandt function `cw A x = minᵢ (A x)ᵢ / xᵢ`
  over the compact set of positive vectors `A ^ k x`, `x` in the simplex. At a maximum `x`,
  `A x - r x ≥ 0` must vanish, since otherwise `A ^ k` would make it positive and raise `cw`.
* `tendsto_pow_div`: `A ^ j / r ^ j → v wᵀ` for a left eigenvector `w` with positive entries and
  `w ⬝ᵥ v = 1`. The matrix `B = A / r` fixes `v` and maps every band `m v ≤ x ≤ M v` into itself
  (`InBand.mulVec`), and `B ^ k` shrinks the width `M - m` by a fixed factor `θ < 1`
  (`InBand.contract`), so the columns of `B ^ j` converge to multiples of `v`.
* Consequences: every other complex eigenvalue has modulus `< r` (`norm_lt_of_mulVec_eq`); the
  eigenvectors for `r` are the multiples of `v` (`eq_smul_of_mulVec_eq`); `r` is the only
  eigenvalue with a positive eigenvector (`eq_of_pos_eigenvector`), and the largest `ρ` with
  `ρ x ≤ A x` for a positive `x` (`le_of_smul_le_mulVec`).

Sources: O. Perron, *Zur Theorie der Matrices*, Math. Ann. 64 (1907) 248–263; G. Frobenius,
*Über Matrizen aus nicht negativen Elementen*, Sitzungsber. Preuss. Akad. Wiss. (1912) 456–477;
E. Seneta, *Non-negative Matrices and Markov Chains*, 2nd ed., Springer (2006), chapter 1.
-/

@[expose] public section

namespace Rule30Equivalents.PerronFrobenius

open Matrix Filter Topology

variable {n : Type*} [Fintype n]

/-! ### Nonnegative matrices -/

theorem mulVec_apply_eq_sum (P : Matrix n n ℝ) (x : n → ℝ) (i : n) :
    (P *ᵥ x) i = ∑ j, P i j * x j := by
  simp [mulVec, dotProduct]

/-- A positive matrix maps a nonzero nonnegative vector to a positive one. -/
theorem mulVec_pos {P : Matrix n n ℝ} (hP : ∀ i j, 0 < P i j) {x : n → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx : x ≠ 0) (i : n) : 0 < (P *ᵥ x) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  rw [mulVec_apply_eq_sum]
  exact Finset.sum_pos' (fun l _ => mul_nonneg (hP i l).le (hx0 l))
    ⟨j, Finset.mem_univ j, mul_pos (hP i j) (lt_of_le_of_ne (hx0 j) (Ne.symm hj))⟩

/-- A nonnegative matrix preserves the entrywise order. -/
theorem mulVec_le_mulVec {P : Matrix n n ℝ} (hP : ∀ i j, 0 ≤ P i j) {x y : n → ℝ}
    (h : ∀ j, x j ≤ y j) (i : n) : (P *ᵥ x) i ≤ (P *ᵥ y) i := by
  rw [mulVec_apply_eq_sum, mulVec_apply_eq_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP i j)

section Powers

variable [DecidableEq n]

theorem pow_mulVec_of_mulVec_eq {R : Type*} [CommSemiring R] {A : Matrix n n R} {u : n → R}
    {μ : R} (h : A *ᵥ u = μ • u) (j : ℕ) : A ^ j *ᵥ u = μ ^ j • u := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ]

theorem pow_mulVec_eq {B : Matrix n n ℝ} {v : n → ℝ} (hBv : B *ᵥ v = v) (j : ℕ) :
    B ^ j *ᵥ v = v := by
  have h := pow_mulVec_of_mulVec_eq (A := B) (u := v) (μ := (1 : ℝ)) (by rw [one_smul]; exact hBv) j
  rwa [one_pow, one_smul] at h

end Powers

/-! ### Bands around a positive vector -/

/-- `x` lies in the band `m v ≤ x ≤ M v`. -/
def InBand (v : n → ℝ) (m M : ℝ) (x : n → ℝ) : Prop :=
  ∀ i, m * v i ≤ x i ∧ x i ≤ M * v i

/-- A nonnegative matrix that fixes `v` maps each band around `v` into itself. -/
theorem InBand.mulVec {B : Matrix n n ℝ} (hB : ∀ i j, 0 ≤ B i j) {v : n → ℝ}
    (hBv : B *ᵥ v = v) {m M : ℝ} {x : n → ℝ} (hx : InBand v m M x) : InBand v m M (B *ᵥ x) :=
  fun i => by
    have e : ∀ c : ℝ, (B *ᵥ fun j => c * v j) = fun j => c * v j := fun c => by
      rw [show (fun j => c * v j) = c • v from rfl, mulVec_smul, hBv]
    have h1 := mulVec_le_mulVec hB (fun j => (hx j).1) i
    have h2 := mulVec_le_mulVec hB (fun j => (hx j).2) i
    rw [e] at h1 h2
    exact ⟨h1, h2⟩

section Powers

variable [DecidableEq n]

theorem InBand.pow_mulVec {B : Matrix n n ℝ} (hB : ∀ i j, 0 ≤ B i j) {v : n → ℝ}
    (hBv : B *ᵥ v = v) {m M : ℝ} {x : n → ℝ} (hx : InBand v m M x) (s : ℕ) :
    InBand v m M (B ^ s *ᵥ x) := by
  induction s with
  | zero => simpa using hx
  | succ s ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact ih.mulVec hB hBv

end Powers

theorem card_mul_le_one {Q : Matrix n n ℝ} {v : n → ℝ} (hv : ∀ i, 0 < v i) (hQv : Q *ᵥ v = v)
    {δ : ℝ} (hδ : ∀ i j, δ * v i ≤ Q i j * v j) (i : n) : δ * Fintype.card n ≤ 1 := by
  have hrow : ∑ j, Q i j * v j = v i := by rw [← mulVec_apply_eq_sum, hQv]
  have h : ∑ _j : n, δ * v i ≤ ∑ j, Q i j * v j := Finset.sum_le_sum fun j _ => hδ i j
  rw [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_comm _ δ] at h
  exact (mul_le_iff_le_one_left (hv i)).1 h

/-- **Bands contract**: if `Q` fixes the positive vector `v` and `δ vᵢ ≤ Qᵢⱼ vⱼ` for all `i, j`,
then `Q` maps a band of width `M - m` into a band of width `(1 - δ · #n) (M - m)`: each
`(Q x)ᵢ / vᵢ` is an average of the ratios `xⱼ / vⱼ` with all weights at least `δ`. -/
theorem InBand.contract {Q : Matrix n n ℝ} {v : n → ℝ} (hv : ∀ i, 0 < v i) (hQv : Q *ᵥ v = v)
    {δ : ℝ} (hδ : ∀ i j, δ * v i ≤ Q i j * v j) {m M : ℝ} {x : n → ℝ} (hx : InBand v m M x) :
    ∃ m' M', M' - m' = (1 - δ * Fintype.card n) * (M - m) ∧ InBand v m' M' (Q *ᵥ x) := by
  set t : n → ℝ := fun j => x j / v j with ht
  have hxt : ∀ j, x j = v j * t j := fun j => by
    rw [ht]
    field_simp [(hv j).ne']
  have hrow : ∀ i, ∑ j, Q i j * v j = v i := fun i => by rw [← mulVec_apply_eq_sum, hQv]
  have htm : ∀ j, m ≤ t j := fun j => (le_div_iff₀ (hv j)).2 (hx j).1
  have htM : ∀ j, t j ≤ M := fun j => (div_le_iff₀ (hv j)).2 (hx j).2
  have hQx : ∀ i, (Q *ᵥ x) i = ∑ j, Q i j * v j * t j := fun i => by
    rw [mulVec_apply_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hxt j]; ring
  refine ⟨m + δ * ∑ j, (t j - m), M - δ * ∑ j, (M - t j), ?_, fun i => ⟨?_, ?_⟩⟩
  · have hsum : ∑ j, (t j - m) + ∑ j, (M - t j) = Fintype.card n * (M - m) := by
      rw [← Finset.sum_add_distrib,
        Finset.sum_congr rfl fun j _ => show t j - m + (M - t j) = M - m by ring,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination (-δ) * hsum
  · have h1 : ∑ j, Q i j * v j * t j = m * v i + ∑ j, Q i j * v j * (t j - m) := by
      rw [← hrow i, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : δ * v i * ∑ j, (t j - m) ≤ ∑ j, Q i j * v j * (t j - m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hδ i j) (by linarith [htm j])
    rw [hQx, h1]
    linarith
  · have h1 : ∑ j, Q i j * v j * t j = M * v i - ∑ j, Q i j * v j * (M - t j) := by
      rw [← hrow i, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : δ * v i * ∑ j, (M - t j) ≤ ∑ j, Q i j * v j * (M - t j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hδ i j) (by linarith [htM j])
    rw [hQx, h1]
    linarith

section Powers

variable [DecidableEq n]

theorem InBand.pow_contract {Q : Matrix n n ℝ} {v : n → ℝ} (hv : ∀ i, 0 < v i)
    (hQv : Q *ᵥ v = v) {δ : ℝ} (hδ : ∀ i j, δ * v i ≤ Q i j * v j) {m M : ℝ} {x : n → ℝ}
    (hx : InBand v m M x) (q : ℕ) :
    ∃ m' M', M' - m' = (1 - δ * Fintype.card n) ^ q * (M - m) ∧ InBand v m' M' (Q ^ q *ᵥ x) := by
  induction q with
  | zero => exact ⟨m, M, by ring, by simpa using hx⟩
  | succ q ih =>
    obtain ⟨m', M', hw, h⟩ := ih
    obtain ⟨m'', M'', hw', h'⟩ := h.contract hv hQv hδ
    refine ⟨m'', M'', by rw [hw', hw]; ring, ?_⟩
    rw [pow_succ', ← mulVec_mulVec]
    exact h'

/-- After `j` steps of `B`, a band has shrunk by the factor `(1 - δ · #n) ^ ⌊j / k⌋` when `B ^ k`
satisfies the hypothesis of `InBand.contract`. -/
theorem InBand.pow_width {B : Matrix n n ℝ} (hB : ∀ i j, 0 ≤ B i j) {v : n → ℝ}
    (hv : ∀ i, 0 < v i) (hBv : B *ᵥ v = v) {k : ℕ} {δ : ℝ}
    (hδ : ∀ i j, δ * v i ≤ (B ^ k) i j * v j) {m M : ℝ} {x : n → ℝ} (hx : InBand v m M x)
    (j : ℕ) : ∃ m' M', M' - m' = (1 - δ * Fintype.card n) ^ (j / k) * (M - m) ∧
      InBand v m' M' (B ^ j *ᵥ x) := by
  obtain ⟨m', M', hw, h⟩ :=
    (hx.pow_mulVec hB hBv (j % k)).pow_contract hv (pow_mulVec_eq hBv k) hδ (j / k)
  refine ⟨m', M', hw, ?_⟩
  rwa [mulVec_mulVec, ← pow_mul, ← pow_add, Nat.div_add_mod] at h

end Powers

/-! ### The Collatz–Wielandt function and the Perron eigenvector -/

variable [Nonempty n]

/-- The Collatz–Wielandt function `x ↦ minᵢ (A x)ᵢ / xᵢ`, the largest `ρ` with `ρ x ≤ A x` for a
positive vector `x`. -/
noncomputable def cw (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => (A *ᵥ x) i / x i

theorem cw_mul_le {A : Matrix n n ℝ} {x : n → ℝ} (hx : ∀ i, 0 < x i) (i : n) :
    cw A x * x i ≤ (A *ᵥ x) i :=
  (le_div_iff₀ (hx i)).1 (Finset.inf'_le _ (Finset.mem_univ i))

theorem le_cw {A : Matrix n n ℝ} {x : n → ℝ} (hx : ∀ i, 0 < x i) {ρ : ℝ}
    (h : ∀ i, ρ * x i ≤ (A *ᵥ x) i) : ρ ≤ cw A x :=
  Finset.le_inf' _ _ fun i _ => (le_div_iff₀ (hx i)).2 (h i)

theorem lt_cw {A : Matrix n n ℝ} {x : n → ℝ} (hx : ∀ i, 0 < x i) {ρ : ℝ}
    (h : ∀ i, ρ * x i < (A *ᵥ x) i) : ρ < cw A x :=
  (Finset.lt_inf'_iff _).2 fun i _ => (lt_div_iff₀ (hx i)).2 (h i)

theorem cw_smul (A : Matrix n n ℝ) (x : n → ℝ) {c : ℝ} (hc : 0 < c) : cw A (c • x) = cw A x := by
  unfold cw
  congr 1
  funext i
  rw [mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ hc.ne']

theorem continuousOn_cw (A : Matrix n n ℝ) : ContinuousOn (cw A) {x | ∀ i, 0 < x i} :=
  ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i _ =>
    ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).continuousOn.div
      (continuous_apply i).continuousOn fun _ hx => (hx i).ne'

variable [DecidableEq n]

/-- **Perron's eigenvector**: a primitive matrix has an eigenvalue `r > 0` with an eigenvector whose
entries are all positive. -/
theorem exists_eigenvector {A : Matrix n n ℝ} (hA : A.IsPrimitive) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  obtain ⟨k, hk, hP⟩ := hA.exists_pos_pow
  set P := A ^ k with hPdef
  have hP0 : ∀ i j, 0 ≤ P i j := fun i j => (hP i j).le
  have hcomm : ∀ x, A *ᵥ (P *ᵥ x) = P *ᵥ (A *ᵥ x) := fun x => by
    rw [mulVec_mulVec, mulVec_mulVec, hPdef, ← pow_succ', pow_succ]
  obtain ⟨i₀⟩ := ‹Nonempty n›
  -- the simplex and its image under `P`, a compact set of positive vectors
  set S : Set (n → ℝ) := Set.Icc 0 1 ∩ {x | ∑ i, x i = 1} with hS
  have hSc : IsCompact S := isCompact_Icc.inter_right
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  have hSpos : ∀ x ∈ S, ∀ i, 0 < (P *ᵥ x) i := fun x hx i => by
    obtain ⟨⟨h0, -⟩, h1⟩ := hx
    refine mulVec_pos hP (fun j => h0 j) ?_ i
    rintro rfl
    simp at h1
  have hsingle : Pi.single i₀ (1 : ℝ) ∈ S := by
    refine ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩
    · by_cases h : j = i₀ <;> simp [h]
    · by_cases h : j = i₀ <;> simp [h]
    · simp
  set K := (fun x => P *ᵥ x) '' S with hK
  have hKc : IsCompact K := hSc.image (continuous_const.matrix_mulVec continuous_id)
  have hKpos : ∀ y ∈ K, ∀ i, 0 < y i := by
    rintro _ ⟨x, hx, rfl⟩ i
    exact hSpos x hx i
  obtain ⟨y₀, hy₀K, hmax⟩ := hKc.exists_isMaxOn ⟨_, _, hsingle, rfl⟩
    ((continuousOn_cw A).mono fun y hy => hKpos y hy)
  set r := cw A y₀ with hr
  have hy₀ := hKpos y₀ hy₀K
  have hcw : ∀ i, r * y₀ i ≤ (A *ᵥ y₀) i := fun i => cw_mul_le hy₀ i
  -- `cw` is at most `r` at every positive vector
  have hle : ∀ x : n → ℝ, (∀ i, 0 < x i) → cw A x ≤ r := fun x hx => by
    set s := ∑ i, x i
    have hs : 0 < s := Finset.sum_pos (fun i _ => hx i) Finset.univ_nonempty
    set x' := s⁻¹ • x
    have hx' : ∀ i, 0 < x' i := fun i => mul_pos (inv_pos.2 hs) (hx i)
    have hx'S : x' ∈ S := by
      refine ⟨⟨fun i => (hx' i).le, fun i => ?_⟩, ?_⟩
      · show s⁻¹ * x i ≤ 1
        rw [inv_mul_le_iff₀ hs, mul_one]
        exact Finset.single_le_sum (fun j _ => (hx j).le) (Finset.mem_univ i)
      · show ∑ i, s⁻¹ * x i = 1
        rw [← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    calc cw A x = cw A x' := (cw_smul A x (inv_pos.2 hs)).symm
      _ ≤ cw A (P *ᵥ x') := le_cw (hSpos x' hx'S) fun i => by
          rw [hcomm]
          have h := mulVec_le_mulVec hP0 (fun j => cw_mul_le (A := A) hx' j) i
          rwa [show (fun j => cw A x' * x' j) = cw A x' • x' from rfl, mulVec_smul] at h
      _ ≤ r := isMaxOn_iff.1 hmax _ ⟨x', hx'S, rfl⟩
  -- the maximizer is an eigenvector
  have heig : A *ᵥ y₀ = r • y₀ := by
    by_contra hne
    have hz0 : ∀ i, 0 ≤ (A *ᵥ y₀ - r • y₀) i := fun i => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hcw i]
    have hPy₀ : ∀ i, 0 < (P *ᵥ y₀) i := mulVec_pos hP (fun i => (hy₀ i).le)
      (fun h => by simpa [h] using hy₀ i₀)
    have hlt : r < cw A (P *ᵥ y₀) := lt_cw hPy₀ fun i => by
      have h := mulVec_pos hP hz0 (sub_ne_zero.2 hne) i
      rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hcomm] at h
      linarith
    exact absurd (hle _ hPy₀) (not_le.2 hlt)
  -- the eigenvalue is positive, since `A ^ k y₀ > 0`
  have hrpos : 0 < r := by
    by_contra hr0
    push Not at hr0
    have h0 : A *ᵥ y₀ = 0 := by
      funext i
      have h1 : (A *ᵥ y₀) i = r * y₀ i := by rw [heig]; rfl
      have h2 : 0 ≤ (A *ᵥ y₀) i := by
        rw [mulVec_apply_eq_sum]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hA.nonneg i j) (hy₀ j).le
      have h3 : r * y₀ i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr0 (hy₀ i).le
      simp only [Pi.zero_apply]
      linarith
    have h := mulVec_pos hP (fun i => (hy₀ i).le) (fun h => by simpa [h] using hy₀ i₀) i₀
    rw [hPdef, ← Nat.sub_add_cancel hk, pow_succ, ← mulVec_mulVec, h0, mulVec_zero] at h
    exact lt_irrefl _ h
  exact ⟨r, hrpos, y₀, hy₀, heig⟩

/-! ### Convergence of the powers -/

/-- **Perron–Frobenius, convergence**: if `A` is primitive and `A v = r v` with `r > 0` and `v`
positive, then `A ^ j / r ^ j → v wᵀ` for a positive left eigenvector `w` with `w ⬝ᵥ v = 1`. -/
theorem tendsto_pow_div {A : Matrix n n ℝ} (hA : A.IsPrimitive) {r : ℝ} (hr : 0 < r)
    {v : n → ℝ} (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) :
    ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ w ᵥ* A = r • w ∧ w ⬝ᵥ v = 1 ∧
      Tendsto (fun j : ℕ => (r ^ j)⁻¹ • A ^ j) atTop (𝓝 (vecMulVec v w)) := by
  obtain ⟨k, hk, hP⟩ := hA.exists_pos_pow
  set B : Matrix n n ℝ := r⁻¹ • A with hBdef
  have hB : ∀ i j, 0 ≤ B i j := fun i j => mul_nonneg (inv_nonneg.2 hr.le) (hA.nonneg i j)
  have hBv : B *ᵥ v = v := by
    rw [hBdef, smul_mulVec, hAv, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hBpow : ∀ j : ℕ, B ^ j = (r ^ j)⁻¹ • A ^ j := fun j => by rw [hBdef, smul_pow, inv_pow]
  -- a uniform lower bound for the entries of `B ^ k`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j, δ * v i ≤ (B ^ k) i j * v j := by
    obtain ⟨p, hp⟩ := Finite.exists_min fun p : n × n => (B ^ k) p.1 p.2 * v p.2 / v p.1
    refine ⟨(B ^ k) p.1 p.2 * v p.2 / v p.1, ?_, fun i j => (le_div_iff₀ (hv i)).1 (hp (i, j))⟩
    have : 0 < (B ^ k) p.1 p.2 := by
      rw [hBpow]
      exact mul_pos (inv_pos.2 (pow_pos hr k)) (hP _ _)
    exact div_pos (mul_pos this (hv _)) (hv _)
  set θ := 1 - δ * Fintype.card n with hθ
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hθ0 : 0 ≤ θ := by
    have := card_mul_le_one hv (pow_mulVec_eq hBv k) hδ i₀
    linarith
  have hθ1 : θ < 1 := by
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    have := mul_pos hδ0 this
    linarith
  have htend : ∀ l : n, Tendsto (fun j : ℕ => θ ^ (j / k) * (v l)⁻¹) atTop (𝓝 0) := fun l => by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).comp
      (Nat.tendsto_div_const_atTop hk.ne')).mul_const (v l)⁻¹
  -- the columns of `B ^ j`
  have hcol : ∀ l : n, InBand v 0 (v l)⁻¹ (Pi.single l 1) := fun l i => by
    by_cases h : i = l
    · subst h
      simp [(hv i).ne']
    · rw [Pi.single_eq_of_ne h]
      exact ⟨by simp, mul_nonneg (inv_nonneg.2 (hv l).le) (hv i).le⟩
  have hentry : ∀ (j : ℕ) (i l : n), (B ^ j *ᵥ Pi.single l 1) i = (B ^ j) i l := fun j i l => by
    rw [mulVec_single_one]
    rfl
  have hbound : ∀ (i i' l : n) (j j' : ℕ), j ≤ j' →
      |(B ^ j') i l / v i - (B ^ j) i' l / v i'| ≤ θ ^ (j / k) * (v l)⁻¹ := by
    intro i i' l j j' hjj
    obtain ⟨m', M', hw, h⟩ := (hcol l).pow_width hB hv hBv hδ j
    have h' : InBand v m' M' (B ^ j' *ᵥ Pi.single l 1) := by
      have := h.pow_mulVec hB hBv (j' - j)
      rwa [mulVec_mulVec, ← pow_add, Nat.sub_add_cancel hjj] at this
    have a1 := h' i
    have a2 := h i'
    rw [hentry] at a1 a2
    have b1 : m' ≤ (B ^ j') i l / v i := (le_div_iff₀ (hv i)).2 a1.1
    have b2 : (B ^ j') i l / v i ≤ M' := (div_le_iff₀ (hv i)).2 a1.2
    have b3 : m' ≤ (B ^ j) i' l / v i' := (le_div_iff₀ (hv i')).2 a2.1
    have b4 : (B ^ j) i' l / v i' ≤ M' := (div_le_iff₀ (hv i')).2 a2.2
    rw [sub_zero] at hw
    rw [abs_le]
    constructor <;> linarith
  -- the ratios `(B ^ j)ᵢₗ / vᵢ` converge, to a limit independent of `i`
  have hlim : ∀ i l : n, ∃ ρ, Tendsto (fun j : ℕ => (B ^ j) i l / v i) atTop (𝓝 ρ) :=
    fun i l => cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0'
      (fun j : ℕ => θ ^ (j / k) * (v l)⁻¹)
      (fun j j' hjj => by rw [Real.dist_eq, abs_sub_comm]; exact hbound i i l j j' hjj)
      (htend l))
  choose ρ hρ using hlim
  have hρeq : ∀ i i' l, ρ i l = ρ i' l := fun i i' l => by
    have h1 := ((hρ i l).sub (hρ i' l)).abs
    have h2 : |ρ i l - ρ i' l| ≤ 0 :=
      le_of_tendsto_of_tendsto' h1 (htend l) fun j => hbound i i' l j j le_rfl
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h2)
  set w : n → ℝ := fun l => ρ i₀ l with hwdef
  have hBlim : Tendsto (fun j : ℕ => B ^ j) atTop (𝓝 (vecMulVec v w)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun l => ?_
    have h := (hρ i l).const_mul (v i)
    rw [hρeq i i₀ l] at h
    refine h.congr fun j => ?_
    field_simp [(hv i).ne']
  -- positivity of `w`: from time `k` on, `(B ^ j)ᵢ₀ₗ / vᵢ₀ ≥ δ / vₗ`
  have hwpos : ∀ l, 0 < w l := fun l => by
    have hband : InBand v (δ / v l) (v l)⁻¹ (B ^ k *ᵥ Pi.single l 1) := fun i => by
      refine ⟨?_, ((hcol l).pow_mulVec hB hBv k i).2⟩
      rw [hentry, div_mul_eq_mul_div, div_le_iff₀ (hv l)]
      exact hδ i l
    have hlow : ∀ j, k ≤ j → δ / v l ≤ (B ^ j) i₀ l / v i₀ := fun j hj => by
      have h := (hband.pow_mulVec hB hBv (j - k)) i₀
      rw [mulVec_mulVec, ← pow_add, Nat.sub_add_cancel hj, hentry] at h
      exact (le_div_iff₀ (hv i₀)).2 h.1
    exact lt_of_lt_of_le (div_pos hδ0 (hv l))
      (ge_of_tendsto (hρ i₀ l) (eventually_atTop.2 ⟨k, hlow⟩))
  -- `v wᵀ` is fixed by `B` on the right and fixes `v`
  have hLB : vecMulVec v w * B = vecMulVec v w := by
    have h1 : Tendsto (fun j : ℕ => B ^ j * B) atTop (𝓝 (vecMulVec v w * B)) :=
      ((continuous_id.matrix_mul continuous_const).tendsto _).comp hBlim
    have h2 : Tendsto (fun j : ℕ => B ^ j * B) atTop (𝓝 (vecMulVec v w)) :=
      Tendsto.congr (fun j => pow_succ B j) (hBlim.comp (tendsto_add_atTop_nat 1))
    exact tendsto_nhds_unique h1 h2
  have hLv : vecMulVec v w *ᵥ v = v := by
    have h1 : Tendsto (fun j : ℕ => B ^ j *ᵥ v) atTop (𝓝 (vecMulVec v w *ᵥ v)) :=
      ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp hBlim
    rw [funext fun j => pow_mulVec_eq hBv j] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hwB : w ᵥ* B = w := by
    funext l
    have h := congrFun (congrFun hLB i₀) l
    simp only [mul_apply, vecMulVec_apply] at h
    rw [show ∑ m, v i₀ * w m * B m l = v i₀ * ∑ m, w m * B m l by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring] at h
    simpa [vecMul, dotProduct] using mul_left_cancel₀ (hv i₀).ne' h
  have hwv : w ⬝ᵥ v = 1 := by
    have h := congrFun hLv i₀
    rw [vecMulVec_mulVec] at h
    have h' : v i₀ * (w ⬝ᵥ v) = v i₀ * 1 := by simpa using h
    exact mul_left_cancel₀ (hv i₀).ne' h'
  refine ⟨w, hwpos, ?_, hwv, ?_⟩
  · have hA' : A = r • B := by rw [hBdef, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hA', vecMul_smul, hwB]
  · simpa only [hBpow] using hBlim

/-! ### Consequences -/

/-- **The Perron root is simple**: the eigenvectors for `r` are the multiples of `v`. -/
theorem eq_smul_of_mulVec_eq {A : Matrix n n ℝ} (hA : A.IsPrimitive) {r : ℝ}
    (hr : 0 < r) {v : n → ℝ} (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) {u : n → ℝ}
    (hu : A *ᵥ u = r • u) : ∃ c : ℝ, u = c • v := by
  obtain ⟨w, -, -, -, hlim⟩ := tendsto_pow_div hA hr hv hAv
  have h1 : Tendsto (fun j : ℕ => ((r ^ j)⁻¹ • A ^ j) *ᵥ u) atTop (𝓝 (vecMulVec v w *ᵥ u)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp hlim
  have h2 : ∀ j : ℕ, ((r ^ j)⁻¹ • A ^ j) *ᵥ u = u := fun j => by
    rw [smul_mulVec, pow_mulVec_of_mulVec_eq hu j, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]
  rw [funext h2] at h1
  have hu' : u = vecMulVec v w *ᵥ u := tendsto_nhds_unique tendsto_const_nhds h1
  refine ⟨w ⬝ᵥ u, ?_⟩
  conv_lhs => rw [hu']
  rw [vecMulVec_mulVec, op_smul_eq_smul]

/-- **The Perron root is the only eigenvalue with a positive eigenvector.** -/
theorem eq_of_pos_eigenvector {A : Matrix n n ℝ} (hA : A.IsPrimitive) {r : ℝ}
    (hr : 0 < r) {v : n → ℝ} (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) {ρ : ℝ} {x : n → ℝ}
    (hx : ∀ i, 0 < x i) (hAx : A *ᵥ x = ρ • x) : ρ = r := by
  obtain ⟨w, hw, hwA, -, -⟩ := tendsto_pow_div hA hr hv hAv
  have hpos : 0 < w ⬝ᵥ x := Finset.sum_pos (fun i _ => mul_pos (hw i) (hx i)) Finset.univ_nonempty
  have h : ρ * (w ⬝ᵥ x) = r * (w ⬝ᵥ x) := by
    rw [← smul_eq_mul, ← dotProduct_smul, ← hAx, dotProduct_mulVec, hwA, smul_dotProduct,
      smul_eq_mul]
  exact mul_right_cancel₀ hpos.ne' h

/-- **Collatz–Wielandt**: if `ρ x ≤ A x` for a positive vector `x`, then `ρ ≤ r`. -/
theorem le_of_smul_le_mulVec {A : Matrix n n ℝ} (hA : A.IsPrimitive) {r : ℝ}
    (hr : 0 < r) {v : n → ℝ} (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) {ρ : ℝ} {x : n → ℝ}
    (hx : ∀ i, 0 < x i) (hAx : ∀ i, ρ * x i ≤ (A *ᵥ x) i) : ρ ≤ r := by
  obtain ⟨w, hw, hwA, -, -⟩ := tendsto_pow_div hA hr hv hAv
  have hpos : 0 < w ⬝ᵥ x := Finset.sum_pos (fun i _ => mul_pos (hw i) (hx i)) Finset.univ_nonempty
  have h1 : ρ * (w ⬝ᵥ x) ≤ w ⬝ᵥ (A *ᵥ x) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hAx i) (hw i).le
  have h2 : w ⬝ᵥ (A *ᵥ x) = r * (w ⬝ᵥ x) := by
    rw [dotProduct_mulVec, hwA, smul_dotProduct, smul_eq_mul]
  exact le_of_mul_le_mul_right (h2 ▸ h1) hpos

/-- **Perron–Frobenius, dominance**: every complex eigenvalue of a primitive matrix other than the
Perron root `r` has modulus less than `r`. -/
theorem norm_lt_of_mulVec_eq {A : Matrix n n ℝ} (hA : A.IsPrimitive) {r : ℝ}
    (hr : 0 < r) {v : n → ℝ} (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) {μ : ℂ} {u : n → ℂ}
    (hu0 : u ≠ 0) (hu : A.map ((↑) : ℝ → ℂ) *ᵥ u = μ • u) (hμ : μ ≠ r) : ‖μ‖ < r := by
  obtain ⟨w, -, -, -, hlim⟩ := tendsto_pow_div hA hr hv hAv
  set y := (vecMulVec v w).map ((↑) : ℝ → ℂ) *ᵥ u with hy
  set ζ : ℂ := μ / r with hζ
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hζ1 : ζ ≠ 1 := fun h => hμ ((div_eq_one_iff_eq hr').1 h)
  -- `ζ ^ j • u → y`
  have hseq : Tendsto (fun j : ℕ => ζ ^ j • u) atTop (𝓝 y) := by
    have h1 : Tendsto (fun j : ℕ => ((r ^ j)⁻¹ • A ^ j).map ((↑) : ℝ → ℂ) *ᵥ u) atTop (𝓝 y) :=
      (((continuous_id.matrix_map Complex.continuous_ofReal).matrix_mulVec
        continuous_const).tendsto _).comp hlim
    refine h1.congr fun j => ?_
    have hpow : A.map ((↑) : ℝ → ℂ) ^ j = (A ^ j).map ((↑) : ℝ → ℂ) :=
      (Matrix.map_pow A Complex.ofRealHom j).symm
    have e : ((r ^ j)⁻¹ • A ^ j).map ((↑) : ℝ → ℂ) = ((r : ℂ) ^ j)⁻¹ • A.map (↑) ^ j := by
      rw [hpow]
      ext a b
      simp
    rw [e, smul_mulVec, pow_mulVec_of_mulVec_eq hu j, smul_smul, hζ, div_pow, div_eq_inv_mul]
  by_contra hge
  push Not at hge
  have hζn : 1 ≤ ‖ζ‖ := by
    rw [hζ, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, le_div_iff₀ hr, one_mul]
    exact hge
  -- the limit is fixed by `ζ ≠ 1`, so it vanishes
  have h1 : Tendsto (fun j : ℕ => ζ ^ (j + 1) • u) atTop (𝓝 y) :=
    hseq.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun j : ℕ => ζ ^ (j + 1) • u) atTop (𝓝 (ζ • y)) :=
    (hseq.const_smul ζ).congr fun j => by rw [pow_succ', mul_smul]
  have hy0 : y = 0 := by
    have hfix : ζ • y = y := tendsto_nhds_unique h2 h1
    have : (ζ - 1) • y = 0 := by rw [sub_smul, hfix, one_smul, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hζ1)
  -- but `‖ζ ^ j • u‖ ≥ ‖u‖ > 0`
  rw [hy0] at hseq
  have hnorm : Tendsto (fun j : ℕ => ‖ζ ^ j • u‖) atTop (𝓝 0) := by simpa using hseq.norm
  have hlow : ∀ j : ℕ, ‖u‖ ≤ ‖ζ ^ j • u‖ := fun j => by
    rw [norm_smul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hζn)
  exact hu0 (norm_le_zero_iff.1 (ge_of_tendsto' hnorm hlow))

/-- The Perron root is the spectral radius: every complex eigenvalue has modulus at most `r`. -/
theorem norm_le_of_mulVec_eq {A : Matrix n n ℝ} (hA : A.IsPrimitive) {r : ℝ}
    (hr : 0 < r) {v : n → ℝ} (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) {μ : ℂ} {u : n → ℂ}
    (hu0 : u ≠ 0) (hu : A.map ((↑) : ℝ → ℂ) *ᵥ u = μ • u) : ‖μ‖ ≤ r := by
  by_cases hμ : μ = r
  · rw [hμ, Complex.norm_real, Real.norm_of_nonneg hr.le]
  · exact (norm_lt_of_mulVec_eq hA hr hv hAv hu0 hu hμ).le

end Rule30Equivalents.PerronFrobenius
