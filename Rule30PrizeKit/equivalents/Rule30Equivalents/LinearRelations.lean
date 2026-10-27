module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Rule30Equivalents.Basic
public import Rule30Equivalents.ShiftOrbit
public import Rule30Equivalents.WordsAutomata

/-!
# Problem 1 as the absence of linear relations, over any field

Fix a field `K` (for example `ℚ`, `ℝ`, `ℂ` or `𝔽ₚ`) and read the center column in `K`:
`cK K t = 1` if `c(t)` is black, and `cK K t = 0` otherwise. Each of the following statements is
equivalent to Problem 1. Unless a bullet says otherwise, `K` is an arbitrary field.

## Statements

* **The generating function is not rational** (`problem1_iff_series_not_rational`): no polynomial
  `Q ≠ 0` in `K[X]` makes `Q · ∑ₜ cK(t) Xᵗ` a polynomial. The same holds with `Q(0) ≠ 0`
  (`problem1_iff_series_not_rational_coeff_zero`). Here `K` may be any nontrivial commutative
  ring, such as `ℤ` or `ℤ/4ℤ`: the lowest nonzero coefficient `q` of `Q` need not be invertible,
  since `q · 0 = 0 ≠ q · 1` already makes each bit a function of the bits before it
  (`eventuallyPeriodic_of_mul_eq`, through `WordsAutomata.eventuallyPeriodic_of_determined`).
* **No linear recurrence.** The column solves no Mathlib `LinearRecurrence K`: not from `n = 0`
  (`problem1_iff_no_linearRecurrence`), not eventually, `∀ᶠ n in atTop`
  (`problem1_iff_no_eventual_linearRecurrence`), and no shift `n ↦ cK(n + T)` solves one
  (`problem1_iff_no_linearRecurrence_shift`). Mathlib's recurrences are monic,
  `u (n + d) = ∑_{i < d} aᵢ · u (n + i)`. So the leading coefficient is `1`, and the previous `d`
  terms always determine the next one. Order `d = 0` is allowed; it says that `u` vanishes.
* **Not a torsion element** (`problem1_iff_not_torsion`): let `X` act on sequences as the shift
  `(σ u)(t) = u (t + 1)`. Then `Q(σ) cK ≠ 0` for every nonzero `Q ∈ K[X]`. Equivalently, there is
  no linear relation `∑_{m ≤ d} aₘ · cK(t + m) = 0` (for all `t`) with some `aₘ ≠ 0`. Here the top
  nonzero coefficient plays the role of the leading coefficient.
* **Independent shifts** (`problem1_iff_shifts_linearIndependent`): the shifted sequences
  `t ↦ cK(n + t)`, for `n ∈ ℕ`, are linearly independent in `K^ℕ`. Equivalently, they span an
  infinite-dimensional subspace (`problem1_iff_shift_span_not_finiteDimensional`).
* **Unbounded Hankel rank** (`problem1_iff_hankel_rank_unbounded`): the `n × n` Hankel matrices
  `(cK(i + j))_{i,j<n}` have unbounded rank. No determinants are involved.
* **Kronecker's determinant form** (`problem1_iff_hankel_det`): infinitely many Hankel
  determinants `Hₙ = det (cK(i + j))_{i,j<n}` are nonzero. Over `ℤ` this is
  `problem1_iff_hankel_det_int`, and over `𝔽₂` it is `problem1_iff_hankel_det_zmod_two`. The
  `𝔽₂` form says that `Hₙ` is odd for infinitely many `n` (`problem1_iff_hankel_det_odd`).
  Over `ℤ`, `H₁, …, H₁₂ = 1, -1, -2, 3, 2, -1, 0, 0, -1, -10, 4, 378`, so "`Hₙ ≠ 0` for every
  `n`" is false and "infinitely often" is the right form.
* **Zero sets** (`problem1_iff_not_zero_set`): over a finite field `K`, the set of black times
  `{t | c t}` is not the zero set `{t | u t = 0}` of any solution `u` of a linear recurrence over
  `K`. Over every field the zero-set statement implies Problem 1 (`problem1_of_not_zero_set`).

Each is the specialization to `c` of a theorem about every `b : ℕ → Bool`, for example
`eventuallyPeriodic_iff_rational`, `eventuallyPeriodic_iff_exists_eventually_isSolution`,
`eventuallyPeriodic_iff_exists_aeval_eq_zero`, `eventuallyPeriodic_iff_not_linearIndependent`,
`eventuallyPeriodic_iff_hankel_rank_bounded` and `eventuallyPeriodic_iff_hankel_det`.

## Proof

* Everything reduces to the **window argument** (`eventuallyPeriodic_of_recurrence`). Suppose a
  `0/1` sequence satisfies a monic recurrence `b(t + d) = ∑_{i<d} aᵢ b(t + i)` over `K` from some
  time on. Then it is eventually periodic. Its windows `(b t, …, b (t + d - 1))` lie in the
  finite set `Fin d → Bool`, even when `K` is infinite. Two windows coincide by pigeonhole, and
  the recurrence then repeats everything. The argument uses `0 ≠ 1` in `K`, so that `b` can be
  read back from its image in `K`. It is also the step that needs a nonzero leading coefficient:
  a relation `∑_{m ≤ d} aₘ b(t + m) = 0` with `a_d ≠ 0` is divided by `a_d`
  (`eventuallyPeriodic_of_relation`).
* Conversely, suppose `b` has transient `T` and period `P > 0`. Then `b` satisfies:
  * the recurrence `u(n + T + P) = u(n + T)` of order `T + P`, from `n = 0`;
  * the relation `(X^{T+P} - X^T)(σ) b = 0`;
  * the rationality relation `(1 - X^P) · ∑ b(t) Xᵗ = (a polynomial)`;
  * the shift equality `σ^T b = σ^{T+P} b`, so the shifts are not injective, hence dependent;
  * a bound of at most `T + P` distinct shifts, so the span is finite-dimensional;
  * Hankel rank `≤ T + P`, since every column `(b(i + j))ᵢ` equals `(b(i + m))ᵢ` for some
    `m < T + P`;
  * equal rows `T` and `T + P` in every Hankel matrix of size `n > T + P`, so `Hₙ = 0`.
* **Rational ⇒ periodic.** Suppose `Q · ∑ b(t) Xᵗ = P` with `Q ≠ 0`. For `t > deg P` the
  coefficient of `X^(t + deg Q)` vanishes. This reads `∑_{m ≤ deg Q} Q_{deg Q - m} b(t + m) = 0`, a
  relation whose top nonzero coefficient is the lowest nonzero coefficient of `Q`.
* **Dependent shifts ⇒ periodic.** A nontrivial finite relation `∑_{n ∈ s} gₙ σⁿ b = 0` is such a
  relation, with the largest `n` that has `gₙ ≠ 0` on top.
* **Bounded Hankel rank ⇒ periodic.** Suppose every Hankel matrix has rank `≤ r`. Let
  `Vₙ ⊆ K^{r+1}` be the space of linear relations among the first `r + 1` shifts on the window
  `[0, n)`. The spaces `Vₙ` decrease, so their dimension is eventually minimal, and from then on
  they are all equal. Also `Vₙ ≠ 0` for `n ≥ r + 1`, by rank–nullity: the `r + 1` columns lie in
  the column space of the `n × n` Hankel matrix. A nonzero vector of the common space is a
  relation for all times.
* **Kronecker** (`eventuallyPeriodic_of_hankel_det_eq_zero`). Suppose `Hₙ = 0` for all large `n`,
  and let `r` be the largest size with `H_r ≠ 0` (recall `H₀ = 1`). Solve
  `H_r α = (b(i + r))_{i<r}` and let `A = X^r - ∑ αᵢ Xⁱ`. Then `e = A(σ) b` vanishes on `[0, r)`.
  Suppose `e` does not vanish everywhere, and let `t₀ ≥ r` be its first nonzero value. We show
  `H_{t₀+1} ≠ 0` (`det_hankel_ne_zero_of_error`), which contradicts the choice of `r`.
  * Take `v` with `H_{t₀+1} v = 0`, form `V = ∑ vⱼ Xʲ`, and divide: `V = R + Q · A`.
  * Then `V(σ) b = R(σ) b + Q(σ) e` vanishes on `[0, t₀]`.
  * On `[0, r)` the term `Q(σ) e` sees only values of `e` before `t₀`. So `R(σ) b` vanishes there,
    and since `H_r` is invertible, the coefficients of `R` vanish: `R = 0`.
  * If `Q ≠ 0`, then at time `t₀ - deg Q` the sum `Q(σ) e` has the single nonzero term
    `lead(Q) · e(t₀)`. So `Q = 0`, and hence `v = 0`.

  Therefore `A(σ) b = 0`, a monic recurrence from time `0`. Over `ℤ`, `Hₙ` is nonzero iff its image
  in `ℚ` is nonzero, and `Hₙ` is odd iff its image in `𝔽₂` is nonzero.
* **Zero sets over a finite field.** A solution of a linear recurrence over a finite field is
  eventually periodic. Its windows lie in the finite set `Fin d → K`, and two solutions with the
  same initial window are equal (`LinearRecurrence.eq_iff_eqOn_range_order`). Hence its zero set is
  eventually periodic too. Conversely, if `c` is eventually periodic, then so is `1 - cK`, and its
  zero set is `{t | c t}`.

Special cases:
* Eventually constant sequences need no separate treatment: every argument above holds for every
  `b`.
* The period is always positive: it is `t₂ - t₁` for windows at `t₁ < t₂`.
* There are no digit expansions here, so there are no double-expansion issues.

## Sources

* The `𝔽₂` case of the rational and recurrence forms is `Rule30Equivalents.PowerSeriesF2`, with
  sources there. The window argument follows that file.
* Kronecker's theorem says that an infinite Hankel matrix `(s_{i+j})` has finite rank `r` iff
  `D_r ≠ 0` and `D_j = 0` for all `j > r`, where `D_j` is its leading `j × j` minor. A companion
  theorem says that the matrix has finite rank iff `∑ⱼ sⱼ z^{-j-1}` is a rational function. Both are
  stated as Theorems 1.2 and 1.3 in §1.1 of M. Tyaglov, *Generalized Hurwitz polynomials*,
  arXiv:1005.3032 (2010). Tyaglov attributes the first to L. Kronecker, *Algebraische Reduction der
  Schaaren bilinearer Formen*, S.-B. Akad. Berlin (1890), and the second to F. R. Gantmacher,
  *The Theory of Matrices*, vol. 2, Chelsea (1959). The proofs here are self-contained and work over
  any field. The determinant-free rank argument is standard linear algebra.
* The Skolem–Mahler–Lech theorem gives the converse of `problem1_of_not_zero_set` over `ℚ`; it is
  proved in `SkolemMahlerLech`.
  It says that over a field of characteristic `0`, the zero set of a linear recurrence sequence is a
  finite set plus finitely many arithmetic progressions; see C. Lech, *A note on recurring series*,
  Ark. Mat. 2 (1953) 417–421. The theorem is not in Mathlib, and this file does not prove it.
* `H₁, …, H₁₂` were computed exactly from the first 23 cells of the center column.
-/

@[expose] public section

namespace Rule30Equivalents.LinearRelations

open Ruliology.CellularAutomata
open Finset Polynomial Module
open scoped Matrix

/-- A bit sequence read in `K`: `true ↦ 1`, `false ↦ 0`. -/
def toK (K : Type*) [Zero K] [One K] (b : ℕ → Bool) (t : ℕ) : K := if b t then 1 else 0

/-- The center column of rule 30 read in `K`: `cK K t = 1` if `c t` is black, else `0`. -/
def cK (K : Type*) [Zero K] [One K] (t : ℕ) : K := if c t then 1 else 0

theorem cK_eq_toK (K : Type*) [Zero K] [One K] : cK K = toK K c := rfl

/-- The `n × n` Hankel matrix `(b(i + j))_{0 ≤ i, j < n}` of a bit sequence, over `K`. -/
def hankel (K : Type*) [Zero K] [One K] (b : ℕ → Bool) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => toK K b ((i : ℕ) + (j : ℕ))

/-- With transient `T` and period `P`, rows `T` and `T + P` of every Hankel matrix of size
`n > T + P` coincide, so its determinant vanishes (over any commutative ring). -/
theorem hankel_det_eq_zero {R : Type*} [CommRing R] {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (h : ∀ t, T ≤ t → b (t + P) = b t) {n : ℕ} (hn : T + P < n) : (hankel R b n).det = 0 := by
  refine Matrix.det_zero_of_row_eq (i := ⟨T, by omega⟩) (j := ⟨T + P, hn⟩)
    (by intro h; rw [Fin.mk.injEq] at h; omega) ?_
  funext j
  simp only [hankel, Matrix.of_apply, toK]
  rw [show T + P + (j : ℕ) = T + j + P by omega, h (T + j) (by omega)]

/-! ### Rational generating function over a commutative ring -/

section CommRing

variable {K : Type*} [CommRing K]

/-- Coefficient `t + deg Q` of `Q · φ` for a polynomial `Q`. -/
theorem coeff_coe_mul_add_natDegree {R : Type*} [CommSemiring R] (Q : Polynomial R)
    (φ : PowerSeries R) (t : ℕ) :
    PowerSeries.coeff (t + Q.natDegree) ((Q : PowerSeries R) * φ) =
      ∑ m ∈ range (Q.natDegree + 1),
        Q.coeff (Q.natDegree - m) * PowerSeries.coeff (t + m) φ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (Q : PowerSeries R) * PowerSeries.coeff j φ),
    show (t + Q.natDegree).succ = (Q.natDegree + 1) + t by omega, Finset.sum_range_add]
  have hz : ∑ x ∈ range t, PowerSeries.coeff (Q.natDegree + 1 + x) (Q : PowerSeries R) *
      PowerSeries.coeff (t + Q.natDegree - (Q.natDegree + 1 + x)) φ = 0 :=
    Finset.sum_eq_zero fun x _ => by
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rw [hz, add_zero]
  refine Finset.sum_nbij' (fun m => Q.natDegree - m) (fun m => Q.natDegree - m) ?_ ?_ ?_ ?_ ?_
  · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
  · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
  · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
  · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    rw [Polynomial.coeff_coe, show Q.natDegree - (Q.natDegree - m) = m by omega,
      show t + (Q.natDegree - m) = t + Q.natDegree - m by omega]


/-- The generating function `∑ₜ b(t) Xᵗ ∈ K⟦X⟧`. -/
noncomputable def series (K : Type*) [CommRing K] (b : ℕ → Bool) : PowerSeries K :=
  PowerSeries.mk (toK K b)

@[simp] theorem coeff_series (b : ℕ → Bool) (n : ℕ) :
    PowerSeries.coeff n (series K b) = toK K b n := by
  simp only [series, PowerSeries.coeff_mk]

/-- An eventually periodic sequence has a rational generating function `P / Q` over `K`, with
`Q = 1 - Xᵖ`; in particular `Q(0) ≠ 0`. -/
theorem exists_mul_eq_of_eventuallyPeriodic [Nontrivial K] {b : ℕ → Bool}
    (h : EventuallyPeriodic b) :
    ∃ P Q : K[X], Q.coeff 0 ≠ 0 ∧ (Q : PowerSeries K) * series K b = (P : PowerSeries K) := by
  obtain ⟨T, p, hp, hper⟩ := h
  refine ⟨PowerSeries.trunc (T + p)
    (((1 - Polynomial.X ^ p : K[X]) : PowerSeries K) * series K b), 1 - Polynomial.X ^ p, ?_, ?_⟩
  · rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_X_pow,
      ite_eq_right (by omega), sub_zero]
    exact one_ne_zero
  · refine PowerSeries.ext fun n => ?_
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X, sub_mul,
        one_mul, map_sub, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega), coeff_series,
        coeff_series]
      have hn' := hper (n - p) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hn'
      unfold toK
      rw [hn', sub_self]

/-- If `Q · series b = P` with `Q ≠ 0` over a commutative ring, then `b` is eventually periodic.
Comparing coefficients of `X^(t + deg Q)` for `t > deg P` gives `q · b(t + w) = -∑_{m < w} …` for
the lowest nonzero coefficient `q` of `Q`; since `q · 0 = 0 ≠ q = q · 1`, the bit `b(t + w)` is a
function of the `w` bits before it. No division is needed. -/
theorem eventuallyPeriodic_of_mul_eq {b : ℕ → Bool} {P Q : K[X]} (hQ : Q ≠ 0)
    (h : (Q : PowerSeries K) * series K b = (P : PowerSeries K)) : EventuallyPeriodic b := by
  classical
  set d := Q.natDegree
  set i₀ := Q.natTrailingDegree
  have hkD : i₀ ≤ d := Polynomial.natTrailingDegree_le_natDegree Q
  have hq : Q.coeff i₀ ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ
  set w := d - i₀
  -- each bit from `P.natDegree + 1` on is a function of the `w` bits before it
  have key : ∀ t, P.natDegree + 1 ≤ t → b (t + w) =
      decide (Q.coeff i₀ = -∑ m : Fin w, Q.coeff (d - m) * (if b (t + m) then 1 else 0)) := by
    intro t ht
    have h0 : PowerSeries.coeff (t + d) ((Q : PowerSeries K) * series K b) = 0 := by
      rw [h, Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [coeff_coe_mul_add_natDegree, show d + 1 = (w + 1) + i₀ by omega,
      Finset.sum_range_add, Finset.sum_range_succ] at h0
    have hz : ∑ m ∈ range i₀, Q.coeff (d - (w + 1 + m)) *
        PowerSeries.coeff (t + (w + 1 + m)) (series K b) = 0 :=
      Finset.sum_eq_zero fun m hm => by
        rw [Finset.mem_range] at hm
        rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega), zero_mul]
    rw [hz, add_zero, show d - w = i₀ by omega] at h0
    simp only [coeff_series] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun m => Q.coeff (d - m) * toK K b (t + m)) w] at h0
    show b (t + w) = decide (Q.coeff i₀ = -∑ m : Fin w, Q.coeff (d - m) *
      (if b (t + m) then 1 else 0))
    unfold toK at h0
    cases hb : b (t + w)
    · rw [hb, ite_eq_right (by simp), mul_zero, add_zero] at h0
      rw [h0, neg_zero]
      exact (decide_eq_false hq).symm
    · rw [hb, ite_eq_left rfl, mul_one] at h0
      exact (decide_eq_true (eq_neg_of_add_eq_zero_right h0)).symm
  refine WordsAutomata.eventuallyPeriodic_of_determined (n := w) (T := P.natDegree + 1)
    fun i i' hi hi' hw => ?_
  have hsum : ∑ m : Fin w, Q.coeff (d - m) * (if b (i + m) then (1 : K) else 0) =
      ∑ m : Fin w, Q.coeff (d - m) * (if b (i' + m) then 1 else 0) :=
    Finset.sum_congr rfl fun m _ => by rw [hw m m.isLt]
  rw [key i hi, key i' hi', hsum]

/-- **Rational generating function over any nontrivial commutative ring.** A bit sequence is
eventually periodic iff its generating function over `K` is rational: `Q · ∑ₜ b(t) Xᵗ = P` for
polynomials with `Q ≠ 0`. -/
theorem eventuallyPeriodic_iff_rational [Nontrivial K] (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ P Q : K[X], Q ≠ 0 ∧
      (Q : PowerSeries K) * series K b = (P : PowerSeries K) := by
  constructor
  · intro h
    obtain ⟨P, Q, hQ, hPQ⟩ := exists_mul_eq_of_eventuallyPeriodic (K := K) h
    exact ⟨P, Q, fun h0 => hQ (by rw [h0, Polynomial.coeff_zero]), hPQ⟩
  · rintro ⟨P, Q, hQ, hPQ⟩
    exact eventuallyPeriodic_of_mul_eq hQ hPQ

/-- The same with `Q(0) ≠ 0`. -/
theorem eventuallyPeriodic_iff_rational_coeff_zero [Nontrivial K] (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ P Q : K[X], Q.coeff 0 ≠ 0 ∧
      (Q : PowerSeries K) * series K b = (P : PowerSeries K) := by
  constructor
  · exact exists_mul_eq_of_eventuallyPeriodic
  · rintro ⟨P, Q, hQ, hPQ⟩
    exact eventuallyPeriodic_of_mul_eq (fun h0 => hQ (by rw [h0, Polynomial.coeff_zero])) hPQ

end CommRing

section Field

variable {K : Type*} [Field K]

theorem toK_eq_toK_iff {b b' : ℕ → Bool} {t t' : ℕ} :
    toK K b t = toK K b' t' ↔ b t = b' t' := by
  unfold toK
  cases b t <;> cases b' t' <;> simp

/-! ### The window argument -/

/-- If `b` satisfies an order-`d` recurrence over `K` from time `T` on and the windows of length
`d` at `T ≤ t₁ < t₂` agree, then `b` is eventually periodic with period `t₂ - t₁`. -/
theorem eventuallyPeriodic_of_window_eq {b : ℕ → Bool} {d : ℕ} {a : Fin d → K} {T : ℕ}
    (h : ∀ t, T ≤ t → toK K b (t + d) = ∑ i, a i * toK K b (t + i)) {t₁ t₂ : ℕ}
    (h₁ : T ≤ t₁) (h₁₂ : t₁ < t₂) (h0 : ∀ i < d, b (t₁ + i) = b (t₂ + i)) :
    EventuallyPeriodic b := by
  have step : ∀ n, (∀ i < d, b (t₁ + n + i) = b (t₂ + n + i)) →
      b (t₁ + n + d) = b (t₂ + n + d) := by
    intro n hn
    rw [← toK_eq_toK_iff (K := K), h _ (by omega), h _ (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold toK
    rw [hn j j.isLt]
  have all : ∀ n, ∀ i < d, b (t₁ + n + i) = b (t₂ + n + i) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge (i + 1) d with h' | h'
      · have := ih (i + 1) h'
        rwa [show t₁ + (n + 1) + i = t₁ + n + (i + 1) by omega,
          show t₂ + (n + 1) + i = t₂ + n + (i + 1) by omega]
      · have := step n ih
        rwa [show t₁ + (n + 1) + i = t₁ + n + d by omega,
          show t₂ + (n + 1) + i = t₂ + n + d by omega]
  refine ⟨t₁ + d, t₂ - t₁, by omega, fun t ht => ?_⟩
  have := step (t - (t₁ + d)) (all _)
  rw [show t₁ + (t - (t₁ + d)) + d = t by omega,
    show t₂ + (t - (t₁ + d)) + d = t + (t₂ - t₁) by omega] at this
  exact this.symm

/-- **Window pigeonhole.** A `0/1` sequence satisfying a monic linear recurrence over a field `K`
from some time on is eventually periodic: its windows of length `d` lie in the finite set
`Fin d → Bool`, two of them coincide, and the recurrence repeats everything after them. -/
theorem eventuallyPeriodic_of_recurrence {b : ℕ → Bool} {d : ℕ} {a : Fin d → K} {T : ℕ}
    (h : ∀ t, T ≤ t → toK K b (t + d) = ∑ i, a i * toK K b (t + i)) :
    EventuallyPeriodic b := by
  obtain ⟨x, y, hxy, hw⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => fun i : Fin d => b (T + n + i))
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · exact eventuallyPeriodic_of_window_eq h (t₁ := T + x) (t₂ := T + y) (by omega) (by omega)
      fun i hi => congrFun hw ⟨i, hi⟩
  · exact eventuallyPeriodic_of_window_eq h (t₁ := T + y) (t₂ := T + x) (by omega) (by omega)
      fun i hi => (congrFun hw ⟨i, hi⟩).symm

/-- A linear relation `∑_{m ≤ d} a m · b(t + m) = 0` (for `t ≥ T`) whose top coefficient `a d` is
nonzero makes `b` eventually periodic: dividing by `a d` gives a monic recurrence. -/
theorem eventuallyPeriodic_of_relation {b : ℕ → Bool} {a : ℕ → K} {d T : ℕ} (hd : a d ≠ 0)
    (h : ∀ t, T ≤ t → ∑ m ∈ range (d + 1), a m * toK K b (t + m) = 0) :
    EventuallyPeriodic b := by
  refine eventuallyPeriodic_of_recurrence (d := d) (a := fun i => -(a d)⁻¹ * a i) (T := T)
    fun t ht => ?_
  have h1 := h t ht
  rw [Finset.sum_range_succ] at h1
  show toK K b (t + d) = ∑ i : Fin d, -(a d)⁻¹ * a i * toK K b (t + i)
  rw [Fin.sum_univ_eq_sum_range (fun i => -(a d)⁻¹ * a i * toK K b (t + i)) d]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  linear_combination h1

/-- The same for a relation supported in `[0, N)` with some nonzero coefficient there: the top
nonzero coefficient is used. -/
theorem eventuallyPeriodic_of_relation' {b : ℕ → Bool} {a : ℕ → K} {N T : ℕ}
    (ha : ∃ m < N, a m ≠ 0)
    (h : ∀ t, T ≤ t → ∑ m ∈ range N, a m * toK K b (t + m) = 0) : EventuallyPeriodic b := by
  classical
  set S := (range N).filter (fun m => a m ≠ 0) with hS
  have hne : S.Nonempty := by
    obtain ⟨m, hm, ham⟩ := ha
    exact ⟨m, Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, ham⟩⟩
  have hdS : S.max' hne ∈ S := S.max'_mem hne
  rw [Finset.mem_filter, Finset.mem_range] at hdS
  refine eventuallyPeriodic_of_relation (a := a) (d := S.max' hne) (T := T) hdS.2 fun t ht => ?_
  have hsub : range (S.max' hne + 1) ⊆ range N := Finset.range_subset_range.2 (by omega)
  refine (Finset.sum_subset hsub fun m hm hm' => ?_).trans (h t ht)
  rw [Finset.mem_range] at hm hm'
  have ham : a m = 0 := by
    by_contra hne'
    have := S.le_max' m (Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, hne'⟩)
    omega
  rw [ham, zero_mul]

/-! ### Mathlib's `LinearRecurrence` -/

/-- An eventually periodic sequence solves a Mathlib `LinearRecurrence` from `n = 0`: with
transient `T` and period `P`, `u (n + (T + P)) = u (n + T)`. -/
theorem exists_isSolution_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ E : LinearRecurrence K, E.IsSolution (toK K b) := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨⟨T + P, fun i => if (i : ℕ) = T then 1 else 0⟩, fun n => ?_⟩
  show toK K b (n + (T + P)) =
    ∑ i : Fin (T + P), (if (i : ℕ) = T then (1 : K) else 0) * toK K b (n + i)
  rw [Finset.sum_eq_single (⟨T, by omega⟩ : Fin (T + P))]
  · simp only [ite_true, one_mul]
    unfold toK
    rw [show n + (T + P) = n + T + P by omega, hper (n + T) (by omega)]
  · intro j _ hj
    have hjT : (j : ℕ) ≠ T := fun h => hj (Fin.ext h)
    simp only [hjT, ite_false, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A sequence some shift of which solves a Mathlib `LinearRecurrence` is eventually periodic. -/
theorem eventuallyPeriodic_of_isSolution {b : ℕ → Bool} {E : LinearRecurrence K} {T : ℕ}
    (h : E.IsSolution (fun n => toK K b (n + T))) : EventuallyPeriodic b := by
  refine eventuallyPeriodic_of_recurrence (d := E.order) (a := E.coeffs) (T := T) fun t ht => ?_
  have := h (t - T)
  simp only at this
  rw [show t - T + E.order + T = t + E.order by omega] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show t - T + (i : ℕ) + T = t + i by omega]

/-- **Linear recurrence from `n = 0`.** A bit sequence is eventually periodic iff, read in `K`, it
solves some Mathlib `LinearRecurrence K`. -/
theorem eventuallyPeriodic_iff_exists_isSolution (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ E : LinearRecurrence K, E.IsSolution (toK K b) :=
  ⟨exists_isSolution_of_eventuallyPeriodic, fun ⟨_, hE⟩ =>
    eventuallyPeriodic_of_isSolution (T := 0) hE⟩

/-- **Eventual linear recurrence.** A bit sequence is eventually periodic iff, read in `K`, it
eventually satisfies some Mathlib `LinearRecurrence K`. -/
theorem eventuallyPeriodic_iff_exists_eventually_isSolution (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ E : LinearRecurrence K,
      ∀ᶠ n in Filter.atTop, toK K b (n + E.order) = ∑ i, E.coeffs i * toK K b (n + i) := by
  constructor
  · intro h
    obtain ⟨E, hE⟩ := exists_isSolution_of_eventuallyPeriodic (K := K) h
    exact ⟨E, Filter.Eventually.of_forall hE⟩
  · rintro ⟨E, hE⟩
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hE
    exact eventuallyPeriodic_of_recurrence (a := E.coeffs) (T := T) hT

/-- The same with the shifted sequences `n ↦ b (n + T)` as solutions. -/
theorem eventuallyPeriodic_iff_exists_isSolution_shift (b : ℕ → Bool) :
    EventuallyPeriodic b ↔
      ∃ (E : LinearRecurrence K) (T : ℕ), E.IsSolution (fun n => toK K b (n + T)) :=
  ⟨fun h => (exists_isSolution_of_eventuallyPeriodic h).imp fun _ hE => ⟨0, hE⟩,
    fun ⟨_, _, hE⟩ => eventuallyPeriodic_of_isSolution hE⟩

/-! ### Zero sets of linear recurrence sequences -/

/-- A shift of a solution of a linear recurrence is a solution. -/
theorem isSolution_shift {E : LinearRecurrence K} {u : ℕ → K} (hu : E.IsSolution u) (k : ℕ) :
    E.IsSolution (fun n => u (n + k)) := by
  intro n
  simp only
  rw [show n + E.order + k = n + k + E.order by omega, hu (n + k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show n + (i : ℕ) + k = n + k + i by omega]

/-- Over a finite field every solution of a linear recurrence is eventually periodic: its windows
of length `order` take finitely many values, and two solutions with the same initial window are
equal. -/
theorem isSolution_eventually_periodic [Finite K] {E : LinearRecurrence K} {u : ℕ → K}
    (hu : E.IsSolution u) : ∃ T P : ℕ, 0 < P ∧ ∀ t, T ≤ t → u (t + P) = u t := by
  have heq : ∀ x y, (fun i : Fin E.order => u (x + i)) = (fun i : Fin E.order => u (y + i)) →
      ∀ n, u (n + x) = u (n + y) := by
    intro x y h n
    refine congrFun ((E.eq_iff_eqOn_range_order _ _ (isSolution_shift hu x)
      (isSolution_shift hu y)).2 fun m hm => ?_) n
    rw [Finset.mem_coe, Finset.mem_range] at hm
    have := congrFun h ⟨m, hm⟩
    simp only at this ⊢
    rw [add_comm m x, add_comm m y]
    exact this
  obtain ⟨x, y, hxy, hw⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => fun i : Fin E.order => u (n + i))
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · refine ⟨x, y - x, by omega, fun t ht => ?_⟩
    have := heq x y hw (t - x)
    rw [show t - x + x = t by omega, show t - x + y = t + (y - x) by omega] at this
    exact this.symm
  · refine ⟨y, x - y, by omega, fun t ht => ?_⟩
    have := heq x y hw (t - y)
    rw [show t - y + x = t + (x - y) by omega, show t - y + y = t by omega] at this
    exact this

/-- Over a finite field: if the black times of `b` are the zero set of a linear recurrence
sequence, `b` is eventually periodic. -/
theorem eventuallyPeriodic_of_zero_set [Finite K] {b : ℕ → Bool} {E : LinearRecurrence K}
    {u : ℕ → K} (hu : E.IsSolution u) (hS : {t | u t = 0} = {t | b t = true}) :
    EventuallyPeriodic b := by
  obtain ⟨T, P, hP, h⟩ := isSolution_eventually_periodic hu
  have hS' : ∀ x, u x = 0 ↔ b x = true := fun x => Set.ext_iff.1 hS x
  refine ⟨T, P, hP, fun t ht => ?_⟩
  rw [Bool.eq_iff_iff, ← hS', ← hS', h t ht]

/-- Over any field: the black times of an eventually periodic `b` are the zero set of a linear
recurrence sequence, namely of `1 - b` read in `K`. -/
theorem exists_zero_set_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ (E : LinearRecurrence K) (u : ℕ → K), E.IsSolution u ∧
      {t | u t = 0} = {t | b t = true} := by
  have h' : EventuallyPeriodic (fun t => !b t) := by
    obtain ⟨T, P, hP, hper⟩ := h
    exact ⟨T, P, hP, fun t ht => by simp only [hper t ht]⟩
  obtain ⟨E, hE⟩ := exists_isSolution_of_eventuallyPeriodic (K := K) h'
  refine ⟨E, _, hE, Set.ext fun t => ?_⟩
  simp only [Set.mem_ofPred_eq, toK]
  rcases Bool.eq_false_or_eq_true (b t) with hb | hb <;> simp [hb]

/-! ### Linear independence of the shifts -/

theorem not_linearIndependent_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ¬ LinearIndependent K (fun n : ℕ => fun t : ℕ => toK K b (n + t)) := by
  obtain ⟨T, P, hP, hper⟩ := h
  intro hli
  have := hli.injective (a₁ := T) (a₂ := T + P) (funext fun t => by
    show toK K b (T + t) = toK K b (T + P + t)
    unfold toK
    rw [show T + P + t = T + t + P by omega, hper (T + t) (by omega)])
  omega

theorem eventuallyPeriodic_of_not_linearIndependent {b : ℕ → Bool}
    (h : ¬ LinearIndependent K (fun n : ℕ => fun t : ℕ => toK K b (n + t))) :
    EventuallyPeriodic b := by
  classical
  rw [not_linearIndependent_iff] at h
  obtain ⟨s, g, hsum, i, hi, hgi⟩ := h
  have hrel : ∀ t, ∑ n ∈ s, g n * toK K b (n + t) = 0 := by
    intro t
    have := congrFun hsum t
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  have hs : s ⊆ range (s.sup id + 1) := fun m hm => by
    have := Finset.le_sup (f := id) hm
    rw [Finset.mem_range]
    simp only [id] at this
    omega
  refine eventuallyPeriodic_of_relation' (a := fun m => if m ∈ s then g m else 0)
    (N := s.sup id + 1) (T := 0) ⟨i, Finset.mem_range.1 (hs hi), by simp [hi, hgi]⟩
    fun t _ => ?_
  calc ∑ m ∈ range (s.sup id + 1), (if m ∈ s then g m else 0) * toK K b (t + m)
      = ∑ m ∈ range (s.sup id + 1), if m ∈ s then g m * toK K b (m + t) else 0 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> simp [add_comm]
    _ = ∑ m ∈ s, g m * toK K b (m + t) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hs]
    _ = 0 := hrel t

/-- **Linear independence of the shifts.** A bit sequence is eventually periodic iff its shifts
`n ↦ (t ↦ b(n + t))`, read in `K`, are linearly dependent. -/
theorem eventuallyPeriodic_iff_not_linearIndependent (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ¬ LinearIndependent K (fun n : ℕ => fun t : ℕ => toK K b (n + t)) :=
  ⟨not_linearIndependent_of_eventuallyPeriodic, eventuallyPeriodic_of_not_linearIndependent⟩

/-- **Finite-dimensional span of the shifts.** A bit sequence is eventually periodic iff its
shifts, read in `K`, span a finite-dimensional subspace of `K^ℕ`. -/
theorem eventuallyPeriodic_iff_finiteDimensional_span (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ FiniteDimensional K
      (Submodule.span K (Set.range fun n : ℕ => fun t : ℕ => toK K b (n + t))) := by
  constructor
  · intro h
    apply FiniteDimensional.span_of_finite
    have hfin := (ShiftOrbit.eventuallyPeriodic_iff_finite_shifts b).1 h
    have : (Set.range fun n : ℕ => fun t : ℕ => toK K b (n + t)) =
        (fun f : ℕ → Bool => fun t => toK K f t) ''
          Set.range (fun n : ℕ => fun t => b (n + t)) := by
      rw [← Set.range_comp]
      rfl
    rw [this]
    exact hfin.image _
  · intro h
    by_contra hnot
    have hli : LinearIndependent K (fun n : ℕ => fun t : ℕ => toK K b (n + t)) := by
      by_contra h'
      exact hnot (eventuallyPeriodic_of_not_linearIndependent h')
    exact Module.Finite.not_linearIndependent_of_infinite _ (linearIndependent_span hli)

/-! ### Torsion in the `K[X]`-module of sequences -/

/-- The shift operator `(σ u)(t) = u(t + 1)` on `K`-valued sequences. -/
def shiftₗ (K : Type*) [Field K] : Module.End K (ℕ → K) := LinearMap.funLeft K K (· + 1)

theorem shiftₗ_pow_apply (k : ℕ) (u : ℕ → K) (t : ℕ) : ((shiftₗ K) ^ k) u t = u (t + k) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp only [shiftₗ, LinearMap.funLeft_apply]
    rw [add_assoc]

/-- `Q(σ) u` at time `t` is `∑ₘ Q.coeff m · u(t + m)`. -/
theorem aeval_shiftₗ_apply (Q : K[X]) (u : ℕ → K) (t : ℕ) :
    Polynomial.aeval (shiftₗ K) Q u t = ∑ m ∈ range (Q.natDegree + 1), Q.coeff m * u (t + m) := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, shiftₗ_pow_apply]

/-- **Torsion.** A bit sequence is eventually periodic iff, read in `K`, it is a torsion element of
the `K[X]`-module of sequences in which `X` acts as the shift: `Q(σ) b = 0` for some `Q ≠ 0`. -/
theorem eventuallyPeriodic_iff_exists_aeval_eq_zero (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ Q : K[X], Q ≠ 0 ∧ Polynomial.aeval (shiftₗ K) Q (toK K b) = 0 := by
  constructor
  · rintro ⟨T, P, hP, hper⟩
    refine ⟨Polynomial.X ^ (T + P) - Polynomial.X ^ T, fun h0 => ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · (T + P)) h0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_true, Polynomial.coeff_zero,
        ite_eq_right (show T + P ≠ T by omega), sub_zero] at this
      exact one_ne_zero this
    · funext t
      rw [map_sub, map_pow, map_pow, Polynomial.aeval_X, LinearMap.sub_apply, Pi.sub_apply,
        shiftₗ_pow_apply, shiftₗ_pow_apply, Pi.zero_apply, sub_eq_zero]
      unfold toK
      rw [show t + (T + P) = t + T + P by omega, hper (t + T) (by omega)]
  · rintro ⟨Q, hQ, h0⟩
    refine eventuallyPeriodic_of_relation (a := Q.coeff) (d := Q.natDegree) (T := 0)
      (Polynomial.leadingCoeff_ne_zero.mpr hQ) fun t _ => ?_
    have := congrFun h0 t
    rwa [aeval_shiftₗ_apply] at this

/-! ### Hankel matrices: rank -/

theorem hankel_rank_le {b : ℕ → Bool} {T P : ℕ} (hP : 0 < P)
    (h : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) : (hankel K b n).rank ≤ T + P := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols]
  let F : Finset (Fin n → K) :=
    (Finset.range (T + P)).image (fun m => fun i : Fin n => toK K b ((i : ℕ) + m))
  calc finrank K (Submodule.span K (Set.range (hankel K b n).col))
      ≤ finrank K (Submodule.span K (F : Set (Fin n → K))) := by
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        obtain ⟨m, hm, hm'⟩ := ShiftOrbit.exists_lt_shift_eq hP h j
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, funext fun i => ?_⟩)
        simp only [Matrix.col_apply, hankel, Matrix.of_apply, toK]
        rw [add_comm (i : ℕ) m, add_comm (i : ℕ) j, hm' i]
    _ ≤ F.card := finrank_span_finset_le_card F
    _ ≤ T + P := Finset.card_image_le.trans (by simp)

/-- The `n × (r + 1)` matrix `(b(i + j))_{i < n, j ≤ r}`. Its kernel is the space of linear
relations among the first `r + 1` shifts of `b`, seen on the window `[0, n)`. -/
def window (K : Type*) [Field K] (b : ℕ → Bool) (r n : ℕ) : Matrix (Fin n) (Fin (r + 1)) K :=
  Matrix.of fun i j => toK K b ((i : ℕ) + (j : ℕ))

/-- The relations among the first `r + 1` shifts on the window `[0, n)`. -/
def relations (K : Type*) [Field K] (b : ℕ → Bool) (r n : ℕ) : Submodule K (Fin (r + 1) → K) :=
  LinearMap.ker (window K b r n).mulVecLin

theorem mem_relations {b : ℕ → Bool} {r n : ℕ} {a : Fin (r + 1) → K} :
    a ∈ relations K b r n ↔
      ∀ i : Fin n, ∑ j : Fin (r + 1), toK K b ((i : ℕ) + (j : ℕ)) * a j = 0 := by
  rw [relations, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
  simp only [Matrix.mulVec, dotProduct, window, Matrix.of_apply, Pi.zero_apply]

theorem relations_antitone {b : ℕ → Bool} {r n n' : ℕ} (h : n ≤ n') :
    relations K b r n' ≤ relations K b r n := by
  intro a ha
  rw [mem_relations] at ha ⊢
  intro i
  exact ha ⟨i, by omega⟩

/-- If the `n × n` Hankel matrix has rank `≤ r < n`, the first `r + 1` shifts are dependent on
`[0, n)` (rank–nullity). -/
theorem relations_ne_bot {b : ℕ → Bool} {r n : ℕ} (hn : r + 1 ≤ n)
    (hrank : (hankel K b n).rank ≤ r) : relations K b r n ≠ ⊥ := by
  have h1 : (window K b r n).rank ≤ (hankel K b n).rank := by
    have : window K b r n = (hankel K b n).submatrix id (Fin.castLE hn) := by
      ext i j
      simp [window, hankel]
    rw [this]
    exact Matrix.rank_submatrix_le _ _ _
  have h2 := LinearMap.finrank_range_add_finrank_ker (window K b r n).mulVecLin
  rw [Module.finrank_fin_fun] at h2
  intro hbot
  rw [relations] at hbot
  rw [hbot, finrank_bot] at h2
  have : (window K b r n).rank =
      finrank K (LinearMap.range (window K b r n).mulVecLin) := rfl
  omega

/-- If every Hankel matrix has rank `≤ r`, the first `r + 1` shifts satisfy a nonzero linear
relation at every time. The relation spaces on the windows `[0, n)` decrease with `n`; their
dimension is eventually minimal, from then on the spaces agree, and they are nonzero for
`n ≥ r + 1`. -/
theorem exists_relation_of_hankel_rank_le {b : ℕ → Bool} {r : ℕ}
    (hrank : ∀ n, (hankel K b n).rank ≤ r) :
    ∃ a : Fin (r + 1) → K, a ≠ 0 ∧ ∀ t, ∑ j : Fin (r + 1), toK K b (t + (j : ℕ)) * a j = 0 := by
  classical
  let f : ℕ → ℕ := fun n => finrank K (relations K b r n)
  have hex : ∃ k, ∃ n, f n = k := ⟨f 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hmin : ∀ n, f N ≤ f n := fun n => hN ▸ Nat.find_min' hex ⟨n, rfl⟩
  have hstab : ∀ n, N ≤ n → relations K b r n = relations K b r N := fun n hn =>
    Submodule.eq_of_le_of_finrank_le (relations_antitone hn) (hmin n)
  have hne : relations K b r N ≠ ⊥ := by
    rw [← hstab (max N (r + 1)) (le_max_left _ _)]
    exact relations_ne_bot (le_max_right _ _) (hrank _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨a, ha0, fun t => ?_⟩
  have hmem : a ∈ relations K b r (max N (t + 1)) := by
    rw [hstab _ (le_max_left _ _)]
    exact ha
  exact mem_relations.1 hmem ⟨t, by omega⟩

theorem eventuallyPeriodic_of_hankel_rank_le {b : ℕ → Bool} {r : ℕ}
    (hrank : ∀ n, (hankel K b n).rank ≤ r) : EventuallyPeriodic b := by
  obtain ⟨a, ha0, ha⟩ := exists_relation_of_hankel_rank_le hrank
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha0
  refine eventuallyPeriodic_of_relation' (a := fun m => if h : m < r + 1 then a ⟨m, h⟩ else 0)
    (N := r + 1) (T := 0) ⟨j, j.isLt, by
      show (if h : (j : ℕ) < r + 1 then a ⟨j, h⟩ else 0) ≠ 0
      rw [dite_eq_left j.isLt]
      exact hj⟩ fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => (if h : m < r + 1 then a ⟨m, h⟩ else 0) * toK K b (t + m)) (r + 1)]
  rw [← ha t]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dite_eq_left i.isLt, mul_comm]

/-- **Hankel rank.** A bit sequence is eventually periodic iff the ranks over `K` of its Hankel
matrices `(b(i + j))_{i,j<n}` are bounded. -/
theorem eventuallyPeriodic_iff_hankel_rank_bounded (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ r, ∀ n, (hankel K b n).rank ≤ r := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T + P, hankel_rank_le hP h⟩
  · rintro ⟨r, hr⟩
    exact eventuallyPeriodic_of_hankel_rank_le hr

/-! ### Hankel determinants (Kronecker) -/

/-- `Q(σ) u` at time `t`, for a polynomial whose coefficients vanish from degree `N` on. -/
theorem aeval_shiftₗ_apply_of_coeff {Q : K[X]} {N : ℕ} (hQ : ∀ k, N ≤ k → Q.coeff k = 0)
    (u : ℕ → K) (t : ℕ) :
    Polynomial.aeval (shiftₗ K) Q u t = ∑ m ∈ range N, Q.coeff m * u (t + m) := by
  by_cases h : Q.natDegree < N
  · rw [Polynomial.aeval_eq_sum_range' h]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, shiftₗ_pow_apply]
  · have : Q = 0 := Polynomial.leadingCoeff_eq_zero.1 (hQ _ (not_lt.1 h))
    subst this
    simp

/-- **Kronecker's step.** Let `A` be monic of degree `r`, let `s` be a sequence whose `r × r`
Hankel determinant is nonzero, and let `e = A(σ) s` be the error of the recurrence with
characteristic polynomial `A`. If `e` vanishes before some `t₀ ≥ r` and `e t₀ ≠ 0`, then the
`(t₀ + 1) × (t₀ + 1)` Hankel determinant of `s` is nonzero.

Proof: a vector `v` in the kernel gives a polynomial `V = ∑ⱼ vⱼ Xʲ` of degree `≤ t₀` with
`V(σ) s = 0` on `[0, t₀]`. Divide, `V = R + Q · A` with `deg R < r` and `deg Q ≤ t₀ - r`, so
`V(σ) s = R(σ) s + Q(σ) e`. On `[0, r)` the term `Q(σ) e` only sees `e` before `t₀`, so `R(σ) s`
vanishes there, and the `r × r` determinant forces `R = 0`. If `Q ≠ 0` has degree `D`, then at
time `t₀ - D` only the top coefficient of `Q` meets a nonzero value of `e`, and
`V(σ) s (t₀ - D) = Q_D · e t₀ ≠ 0`. So `Q = 0`, `V = 0` and `v = 0`. -/
theorem det_hankel_ne_zero_of_error {s : ℕ → K} {A : K[X]} (hA : A.Monic) {r t₀ : ℕ}
    (hAr : A.natDegree = r)
    (hr : (Matrix.of fun i j : Fin r => s ((i : ℕ) + (j : ℕ))).det ≠ 0) (hrt : r ≤ t₀)
    (he : ∀ u < t₀, Polynomial.aeval (shiftₗ K) A s u = 0)
    (he0 : Polynomial.aeval (shiftₗ K) A s t₀ ≠ 0) :
    (Matrix.of fun i j : Fin (t₀ + 1) => s ((i : ℕ) + (j : ℕ))).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨V, hV⟩ : ∃ V : K[X], V = ∑ j : Fin (t₀ + 1), Polynomial.monomial (j : ℕ) (v j) :=
    ⟨_, rfl⟩
  -- `V(σ) s` vanishes on `[0, t₀]`.
  have hVs : ∀ i, i < t₀ + 1 → Polynomial.aeval (shiftₗ K) V s i = 0 := by
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this, hV, map_sum]
    simp only [Polynomial.aeval_monomial, LinearMap.coe_sum, Finset.sum_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul,
      shiftₗ_pow_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hVcoeff : ∀ j : Fin (t₀ + 1), V.coeff j = v j := by
    intro j
    rw [hV, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rw [ite_eq_right]
      intro h
      exact hk (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hVdeg : V.natDegree ≤ t₀ := by
    rw [hV]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp j.isLt)
  -- Division by `A`.
  obtain ⟨Q, R, hdiv, hQdeg, hRcoeff⟩ : ∃ Q R : K[X], V = R + Q * A ∧
      Q.natDegree ≤ t₀ - r ∧ ∀ k, r ≤ k → R.coeff k = 0 := by
    refine ⟨V /ₘ A, V %ₘ A, ?_, ?_, fun k hk => ?_⟩
    · rw [mul_comm]
      exact (Polynomial.modByMonic_add_div V A).symm
    · rw [Polynomial.natDegree_divByMonic V hA, hAr]
      omega
    · apply Polynomial.coeff_eq_zero_of_degree_lt
      calc (V %ₘ A).degree < A.degree := Polynomial.degree_modByMonic_lt V hA
        _ = r := by rw [Polynomial.degree_eq_natDegree hA.ne_zero, hAr]
        _ ≤ k := by exact_mod_cast hk
  have hsplit : ∀ i, Polynomial.aeval (shiftₗ K) V s i =
      Polynomial.aeval (shiftₗ K) R s i +
        Polynomial.aeval (shiftₗ K) Q (Polynomial.aeval (shiftₗ K) A s) i := by
    intro i
    rw [hdiv, map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply]
  -- `Q(σ) e` vanishes on `[0, r)`, since it only sees `e` before `t₀` there.
  have hQe_low : ∀ i < r,
      Polynomial.aeval (shiftₗ K) Q (Polynomial.aeval (shiftₗ K) A s) i = 0 := by
    intro i hi
    rw [aeval_shiftₗ_apply]
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [he (i + l) (by omega), mul_zero]
  -- Hence `R(σ) s` vanishes on `[0, r)`, and the `r × r` determinant forces `R = 0`.
  have hR0 : R = 0 := by
    have hker : (Matrix.of fun i j : Fin r => s ((i : ℕ) + (j : ℕ))) *ᵥ
        (fun k : Fin r => R.coeff k) = 0 := by
      funext i
      have h1 := hsplit i
      rw [hVs i (by omega), hQe_low i i.isLt, add_zero,
        aeval_shiftₗ_apply_of_coeff hRcoeff] at h1
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [h1, ← Fin.sum_univ_eq_sum_range (fun m => R.coeff m * s (i + m)) r]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hw : (fun k : Fin r => R.coeff k) = 0 := by
      by_contra hw
      exact hr (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hw, hker⟩)
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < r
    · exact congrFun hw ⟨k, hk⟩
    · exact hRcoeff k (not_lt.1 hk)
  -- If `Q ≠ 0`, its top coefficient meets `e t₀ ≠ 0` at time `t₀ - deg Q`.
  have hQ0 : Q = 0 := by
    by_contra hQ
    have hlc : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have h1 := hsplit (t₀ - Q.natDegree)
    rw [hVs _ (by omega), hR0, map_zero, LinearMap.zero_apply, Pi.zero_apply, zero_add,
      aeval_shiftₗ_apply, Finset.sum_range_succ] at h1
    have hz : ∑ l ∈ range Q.natDegree,
        Q.coeff l * Polynomial.aeval (shiftₗ K) A s (t₀ - Q.natDegree + l) = 0 :=
      Finset.sum_eq_zero fun l hl => by
        rw [Finset.mem_range] at hl
        rw [he _ (by omega), mul_zero]
    rw [hz, zero_add, show t₀ - Q.natDegree + Q.natDegree = t₀ by omega] at h1
    exact mul_ne_zero hlc he0 h1.symm
  apply hv0
  funext j
  rw [← hVcoeff j, hdiv, hR0, hQ0, zero_mul, add_zero, Polynomial.coeff_zero, Pi.zero_apply]

/-- **Kronecker's theorem, the hard direction, for `0/1` sequences.** If the Hankel determinants
of `b` over `K` vanish from some size on, `b` is eventually periodic. Let `r` be the largest size
with a nonzero determinant. Solving the `r × r` system gives a monic recurrence of order `r` that
holds on `[0, r)`; by `det_hankel_ne_zero_of_error`, a first failure at `t₀ ≥ r` would make the
`(t₀ + 1) × (t₀ + 1)` determinant nonzero. So the recurrence holds everywhere. -/
theorem eventuallyPeriodic_of_hankel_det_eq_zero {b : ℕ → Bool} {N : ℕ}
    (h : ∀ n, N ≤ n → (hankel K b n).det = 0) : EventuallyPeriodic b := by
  classical
  have h0 : (hankel K b 0).det ≠ 0 := by
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  obtain ⟨r, hr, hgt⟩ : ∃ r, (hankel K b r).det ≠ 0 ∧ ∀ n, r < n → (hankel K b n).det = 0 := by
    refine ⟨Nat.findGreatest (fun n => (hankel K b n).det ≠ 0) N,
      Nat.findGreatest_spec (P := fun n => (hankel K b n).det ≠ 0) (Nat.zero_le N) h0,
      fun n hn => ?_⟩
    by_contra hne
    by_cases hnN : n ≤ N
    · exact absurd (Nat.le_findGreatest hnN hne) (not_le.2 hn)
    · exact hne (h n (by omega))
  -- Solve `H_r α = (b(i + r))ᵢ`.
  have hunit : IsUnit (hankel K b r).det := isUnit_iff_ne_zero.mpr hr
  obtain ⟨α, hα⟩ : ∃ α : Fin r → K,
      (hankel K b r) *ᵥ α = fun i : Fin r => toK K b ((i : ℕ) + r) :=
    ⟨(hankel K b r)⁻¹ *ᵥ fun i : Fin r => toK K b ((i : ℕ) + r), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]⟩
  -- The characteristic polynomial `A = X^r - ∑ αᵢ Xⁱ`.
  obtain ⟨A, hAdef⟩ : ∃ A : K[X], A = Polynomial.X ^ r -
      ∑ i : Fin r, Polynomial.C (α i) * Polynomial.X ^ (i : ℕ) := ⟨_, rfl⟩
  have hlt : (∑ i : Fin r, Polynomial.C (α i) * Polynomial.X ^ (i : ℕ)).degree <
      (Polynomial.X ^ r : K[X]).degree := by
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt α
  have hA : A.Monic := hAdef ▸ Polynomial.monic_X_pow_sub (Polynomial.degree_sum_fin_lt α)
  have hAr : A.natDegree = r := by
    rw [hAdef]
    exact Polynomial.natDegree_eq_of_degree_eq_some
      ((Polynomial.degree_sub_eq_left_of_degree_lt hlt).trans (Polynomial.degree_X_pow r))
  have hAe : ∀ u, Polynomial.aeval (shiftₗ K) A (toK K b) u =
      toK K b (u + r) - ∑ i : Fin r, α i * toK K b (u + i) := by
    intro u
    rw [hAdef]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
      LinearMap.sub_apply, LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftₗ_pow_apply]
  -- The recurrence holds on `[0, r)` by the choice of `α`.
  have hlow : ∀ u < r, Polynomial.aeval (shiftₗ K) A (toK K b) u = 0 := by
    intro u hu
    rw [hAe, sub_eq_zero]
    have := congrFun hα ⟨u, hu⟩
    simp only [Matrix.mulVec, dotProduct, hankel, Matrix.of_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- It holds everywhere: a first failure would give a nonzero determinant beyond `r`.
  have hall : ∀ u, Polynomial.aeval (shiftₗ K) A (toK K b) u = 0 := by
    by_contra hne
    push Not at hne
    have ht₀ := Nat.find_spec hne
    have hbefore : ∀ u < Nat.find hne, Polynomial.aeval (shiftₗ K) A (toK K b) u = 0 :=
      fun u hu => by
        by_contra h'
        exact Nat.find_min hne hu h'
    have hrt : r ≤ Nat.find hne := by
      by_contra h'
      exact ht₀ (hlow _ (not_le.1 h'))
    exact det_hankel_ne_zero_of_error hA hAr hr hrt hbefore ht₀ (hgt _ (by omega))
  refine eventuallyPeriodic_of_recurrence (d := r) (a := α) (T := 0) fun t _ => ?_
  have := hall t
  rwa [hAe, sub_eq_zero] at this

/-- **Kronecker's criterion for `0/1` sequences.** Over any field `K`, a bit sequence is
eventually periodic iff its Hankel determinants `det (b(i + j))_{i,j<n}` vanish for all large
`n`. -/
theorem eventuallyPeriodic_iff_hankel_det (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ N, ∀ n, N ≤ n → (hankel K b n).det = 0 := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T + P + 1, fun n hn => hankel_det_eq_zero hP h (by omega)⟩
  · rintro ⟨N, hN⟩
    exact eventuallyPeriodic_of_hankel_det_eq_zero hN

end Field

/-- The integer Hankel determinant is nonzero iff the rational one is. -/
theorem hankel_det_int_ne_zero_iff (b : ℕ → Bool) (n : ℕ) :
    (hankel ℤ b n).det ≠ 0 ↔ (hankel ℚ b n).det ≠ 0 := by
  have : hankel ℚ b n = (Int.castRingHom ℚ).mapMatrix (hankel ℤ b n) := by
    ext i j
    simp only [hankel, toK, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [this, ← RingHom.map_det]
  simp

/-- The integer Hankel determinant is odd iff its reduction mod `2` is nonzero. -/
theorem hankel_det_int_odd_iff (b : ℕ → Bool) (n : ℕ) :
    Odd (hankel ℤ b n).det ↔ (hankel (ZMod 2) b n).det ≠ 0 := by
  have : hankel (ZMod 2) b n = (Int.castRingHom (ZMod 2)).mapMatrix (hankel ℤ b n) := by
    ext i j
    simp only [hankel, toK, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [this, ← RingHom.map_det, eq_intCast, Ne, ZMod.intCast_eq_zero_iff_even,
    Int.not_even_iff_odd]

/-! ### Problem 1 -/

/-- **Problem 1 ⇔ the generating function `∑ₜ cK(t) Xᵗ` is not rational over `K`**, for any
field `K`. -/
theorem problem1_iff_series_not_rational (K : Type*) [CommRing K] [Nontrivial K] :
    Rule30Prize.Problem1 ↔
    ¬ ∃ P Q : K[X], Q ≠ 0 ∧
      (Q : PowerSeries K) * PowerSeries.mk (cK K) = (P : PowerSeries K) :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_rational c))

/-- The same with a denominator `Q` that does not vanish at `0`. -/
theorem problem1_iff_series_not_rational_coeff_zero (K : Type*) [CommRing K] [Nontrivial K] :
    Rule30Prize.Problem1 ↔ ¬ ∃ P Q : K[X], Q.coeff 0 ≠ 0 ∧
      (Q : PowerSeries K) * PowerSeries.mk (cK K) = (P : PowerSeries K) :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_iff_rational_coeff_zero c))

/-- **Problem 1 ⇔ the center column solves no Mathlib `LinearRecurrence K`** (from `n = 0`). -/
theorem problem1_iff_no_linearRecurrence (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ∀ E : LinearRecurrence K, ¬ E.IsSolution (cK K) :=
  problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_exists_isSolution c)).trans not_exists)

/-- **Problem 1 ⇔ the center column is not an eventual solution of any Mathlib
`LinearRecurrence K`**: for every recurrence, the relation
`cK(n + order) = ∑ᵢ coeffs i · cK(n + i)` fails for infinitely many `n`. -/
theorem problem1_iff_no_eventual_linearRecurrence (K : Type*) [Field K] :
    Rule30Prize.Problem1 ↔ ∀ E : LinearRecurrence K,
      ¬ ∀ᶠ n in Filter.atTop, cK K (n + E.order) = ∑ i, E.coeffs i * cK K (n + i) :=
  problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_exists_eventually_isSolution c)).trans not_exists)

/-- The eventual form with shifts: no shift `n ↦ cK(n + T)` solves a `LinearRecurrence K`. -/
theorem problem1_iff_no_linearRecurrence_shift (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ∀ (E : LinearRecurrence K) (T : ℕ), ¬ E.IsSolution (fun n => cK K (n + T)) := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_isSolution_shift (K := K)]
  simp only [not_exists]
  rfl

/-- **Problem 1 ⇔ the shifts `t ↦ cK(n + t)` are linearly independent over `K`.** -/
theorem problem1_iff_shifts_linearIndependent (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    LinearIndependent K (fun n : ℕ => fun t : ℕ => cK K (n + t)) := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_not_linearIndependent (K := K),
    not_not]
  rfl

/-- Problem 1 ⇔ the shifts of the center column span an infinite-dimensional subspace of `K^ℕ`. -/
theorem problem1_iff_shift_span_not_finiteDimensional (K : Type*) [Field K] :
    Rule30Prize.Problem1 ↔
      ¬ FiniteDimensional K (Submodule.span K (Set.range fun n : ℕ => fun t : ℕ => cK K (n + t))) :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_iff_finiteDimensional_span c))

/-- **Problem 1 ⇔ the center column is not a torsion element of the `K[X]`-module of sequences**
(with `X` acting as the shift): `Q(σ) cK ≠ 0` for every `Q ≠ 0`. -/
theorem problem1_iff_not_torsion (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ∀ Q : K[X], Q ≠ 0 → Polynomial.aeval (shiftₗ K) Q (cK K) ≠ 0 := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_aeval_eq_zero (K := K)]
  simp only [not_exists, not_and]
  rfl

/-- **Problem 1 ⇔ the Hankel matrices `(cK(i + j))_{i,j<n}` have unbounded rank over `K`.** -/
theorem problem1_iff_hankel_rank_unbounded (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ∀ r : ℕ, ∃ n : ℕ, r ≤ (Matrix.of fun i j : Fin n => cK K ((i : ℕ) + (j : ℕ))).rank := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_hankel_rank_bounded (K := K)]
  constructor
  · intro h r
    by_contra hr
    push Not at hr
    exact h ⟨r, fun n => (hr n).le⟩
  · rintro h ⟨r, hr⟩
    obtain ⟨n, hn⟩ := h (r + 1)
    have := hr n
    change (Matrix.of fun i j : Fin n => cK K ((i : ℕ) + (j : ℕ))).rank ≤ r at this
    omega

/-- **Problem 1 ⇔ infinitely many Hankel determinants `det (cK(i + j))_{i,j<n}` are nonzero**
(Kronecker), over any field `K`. -/
theorem problem1_iff_hankel_det (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ∀ N : ℕ, ∃ n, N ≤ n ∧ (Matrix.of fun i j : Fin n => cK K ((i : ℕ) + (j : ℕ))).det ≠ 0 := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_hankel_det (K := K)]
  simp only [not_exists, not_forall, exists_prop]
  rfl

/-- Kronecker's form over `𝔽₂`. -/
theorem problem1_iff_hankel_det_zmod_two : Rule30Prize.Problem1 ↔
    ∀ N : ℕ, ∃ n, N ≤ n ∧ (Matrix.of fun i j : Fin n => cK (ZMod 2) ((i : ℕ) + (j : ℕ))).det ≠ 0 :=
  problem1_iff_hankel_det (ZMod 2)

/-- **Kronecker's form over `ℤ`**: infinitely many integer Hankel determinants
`Hₙ = det (c(i + j))_{i,j<n}` are nonzero. -/
theorem problem1_iff_hankel_det_int : Rule30Prize.Problem1 ↔
    ∀ N : ℕ, ∃ n, N ≤ n ∧ (Matrix.of fun i j : Fin n => cK ℤ ((i : ℕ) + (j : ℕ))).det ≠ 0 := by
  rw [problem1_iff_hankel_det ℚ]
  exact forall_congr' fun N => exists_congr fun n =>
    and_congr_right fun _ => (hankel_det_int_ne_zero_iff c n).symm

/-- **Problem 1 ⇔ infinitely many integer Hankel determinants `Hₙ` are odd.** -/
theorem problem1_iff_hankel_det_odd : Rule30Prize.Problem1 ↔
    ∀ N : ℕ, ∃ n, N ≤ n ∧ Odd (Matrix.of fun i j : Fin n => cK ℤ ((i : ℕ) + (j : ℕ))).det := by
  rw [problem1_iff_hankel_det_zmod_two]
  exact forall_congr' fun N => exists_congr fun n =>
    and_congr_right fun _ => (hankel_det_int_odd_iff c n).symm

/-- **Zero sets, finite fields.** Over a finite field `K` (for example `𝔽₂`), Problem 1 holds iff
the black times of the center column are not the zero set of any linear recurrence sequence
over `K`. -/
theorem problem1_iff_not_zero_set (K : Type*) [Field K] [Finite K] : Rule30Prize.Problem1 ↔
    ∀ (E : LinearRecurrence K) (u : ℕ → K), E.IsSolution u →
      {t | u t = 0} ≠ {t | c t = true} := by
  rw [problem1_iff_not_eventuallyPeriodic]
  constructor
  · intro h E u hu hS
    exact h (eventuallyPeriodic_of_zero_set hu hS)
  · intro h hep
    obtain ⟨E, u, hu, hS⟩ := exists_zero_set_of_eventuallyPeriodic (K := K) hep
    exact h E u hu hS

/-- **Zero sets, any field.** If the black times of the center column are not the zero set of any
linear recurrence sequence over `K`, Problem 1 holds. Over `ℚ` the converse is the
Skolem–Mahler–Lech theorem (`SkolemMahlerLech.problem1_iff_not_LRS_zero_set`). -/
theorem problem1_of_not_zero_set (K : Type*) [Field K]
    (h : ∀ (E : LinearRecurrence K) (u : ℕ → K), E.IsSolution u →
      {t | u t = 0} ≠ {t | c t = true}) :
    Rule30Prize.Problem1 := by
  rw [problem1_iff_not_eventuallyPeriodic]
  intro hep
  obtain ⟨E, u, hu, hS⟩ := exists_zero_set_of_eventuallyPeriodic (K := K) hep
  exact h E u hu hS

end Rule30Equivalents.LinearRelations
