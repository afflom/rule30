module

public import Rule30Equivalents.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Bound

/-!
# Lagrange's theorem: eventually periodic continued fractions are quadratic irrationals

For an irrational `x`, the *complete quotients* are `x₀ = x` and `xₙ₊₁ = 1 / fract xₙ`, and the
*digits* (partial quotients) are `aₙ = ⌊xₙ⌋`, so `x = [a₀; a₁, a₂, …]`.

* `mobius`: with the continuants `P`, `Q` of the digits, `x (Qₙ₊₁ xₙ + Qₙ) = Pₙ₊₁ xₙ + Pₙ`, and
  `cont_det`: `Pₙ₊₁ Qₙ - Pₙ Qₙ₊₁ = (-1)ⁿ`.
* `abs_mul_sub_le`: `|x Qₙ₊₂ - Pₙ₊₂| ≤ 1 / Qₙ₊₂`, and `eq_of_digit_eq`: two irrationals with the
  same digits are equal.
* `quadratic_of_digit_periodic` (**Euler**): if the digits are eventually periodic, `x` satisfies a
  nontrivial integer quadratic equation. A periodic tail `y` is a fixed point of an integer Möbius
  map, and `x` is an integer Möbius image of `y` with determinant `±1` (`transport`).
* `digit_periodic_of_quadratic` (**Lagrange**): if `x` satisfies a nontrivial integer quadratic
  equation, its digits are eventually periodic. Each complete quotient is a root of an integer
  quadratic whose leading coefficient `F(Pₙ, Qₙ)` is bounded because `Pₙ / Qₙ` approximates `x`, and
  whose discriminant is that of `x`. Finitely many such quadratics have finitely many roots, so two
  complete quotients coincide.
* `digit_periodic_iff`: for an irrational `x`, the digits are eventually periodic iff `x` is a
  quadratic irrational.
* `cfValue b = [b₀; b₁, b₂, …]` for digits `bₖ ≥ 1`: the limit of the convergents
  (`cauchySeq_conv`). `digit_cfValue`: its digits are `b`; `irrational_cfValue`: it is irrational,
  because a rational number reaches an integer complete quotient (`exists_fract_cq_eq_zero`).
  `quadratic_cfValue_iff`: it is a quadratic irrational iff `b` is eventually periodic.
* `problem1_iff_not_quadratic`: Problem 1 holds iff
  `θ = [1 + c(0); 1 + c(1), …]` is not a quadratic irrational.

Sources: G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, §10.12
(Theorems 176 and 177); J.-L. Lagrange (1770); L. Euler (1737).
-/

@[expose] public section

namespace Rule30Equivalents.Lagrange

/-! ### The Gauss map, complete quotients and digits -/

/-- The Gauss map `x ↦ 1 / fract x`. -/
noncomputable def gauss (x : ℝ) : ℝ := (Int.fract x)⁻¹

/-- The complete quotients `x, gauss x, gauss (gauss x), …`. -/
noncomputable def cq (x : ℝ) (n : ℕ) : ℝ := gauss^[n] x

/-- The continued-fraction digits (partial quotients) `⌊xₙ⌋`. -/
noncomputable def digit (x : ℝ) (n : ℕ) : ℤ := ⌊cq x n⌋

theorem cq_zero (x : ℝ) : cq x 0 = x := rfl

theorem cq_succ (x : ℝ) (n : ℕ) : cq x (n + 1) = gauss (cq x n) :=
  Function.iterate_succ_apply' _ _ _

theorem cq_add (x : ℝ) (m n : ℕ) : cq x (m + n) = cq (cq x m) n := by
  unfold cq
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem digit_add (x : ℝ) (m n : ℕ) : digit x (m + n) = digit (cq x m) n := by
  unfold digit
  rw [cq_add]

/-- `xₙ = aₙ + 1 / xₙ₊₁`. -/
theorem cq_eq_digit_add (x : ℝ) (n : ℕ) : cq x n = digit x n + (cq x (n + 1))⁻¹ := by
  rw [cq_succ, gauss, inv_inv, digit]
  exact (Int.floor_add_fract _).symm

section Irrational

variable {x : ℝ} (hx : Irrational x)
include hx

theorem fract_pos : 0 < Int.fract x :=
  lt_of_le_of_ne (Int.fract_nonneg x) fun h => hx.ne_int ⌊x⌋ (by
    have := Int.floor_add_fract x
    rw [← h] at this
    linarith)

theorem irrational_gauss : Irrational (gauss x) := by
  unfold gauss
  have : Irrational (Int.fract x) := by
    rw [Int.fract]
    exact hx.sub_intCast _
  exact this.inv

theorem one_lt_gauss : 1 < gauss x := by
  unfold gauss
  exact one_lt_inv₀ (fract_pos hx) |>.2 (Int.fract_lt_one x)

theorem irrational_cq : ∀ n, Irrational (cq x n)
  | 0 => hx
  | n + 1 => by rw [cq_succ]; exact irrational_gauss (irrational_cq n)

theorem one_lt_cq (n : ℕ) : 1 < cq x (n + 1) := by
  rw [cq_succ]
  exact one_lt_gauss (irrational_cq hx n)

theorem one_le_digit (n : ℕ) : 1 ≤ digit x (n + 1) := by
  unfold digit
  exact Int.le_floor.2 (by exact_mod_cast (one_lt_cq hx n).le)

end Irrational

/-! ### Continuants -/

/-- The numerator continuants: `P 0 = 0`, `P 1 = 1`, `P (n + 2) = a n * P (n + 1) + P n`. -/
def contP (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a n * contP a (n + 1) + contP a n

/-- The denominator continuants: `Q 0 = 1`, `Q 1 = 0`, `Q (n + 2) = a n * Q (n + 1) + Q n`. -/
def contQ (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | n + 2 => a n * contQ a (n + 1) + contQ a n

theorem cont_det (a : ℕ → ℤ) :
    ∀ n, contP a (n + 1) * contQ a n - contP a n * contQ a (n + 1) = (-1) ^ n
  | 0 => by simp [contP, contQ]
  | n + 1 => by
    have ih := cont_det a n
    simp only [contP, contQ] at ih ⊢
    rw [pow_succ]
    linear_combination (-1 : ℤ) * ih

theorem contQ_nonneg {a : ℕ → ℤ} (ha : ∀ n, 1 ≤ a (n + 1)) : ∀ n, 0 ≤ contQ a n
  | 0 => by simp [contQ]
  | 1 => by simp [contQ]
  | 2 => by simp [contQ]
  | n + 3 => by
    have h1 := contQ_nonneg ha (n + 2)
    have h2 := contQ_nonneg ha (n + 1)
    show 0 ≤ a (n + 1) * contQ a (n + 2) + contQ a (n + 1)
    nlinarith [ha n]

theorem contQ_ge_aux {a : ℕ → ℤ} (ha : ∀ n, 1 ≤ a (n + 1)) :
    ∀ n : ℕ, (n : ℤ) + 1 ≤ contQ a (n + 3) ∧ 1 ≤ contQ a (n + 2)
  | 0 => by
    refine ⟨?_, ?_⟩
    · show (0 : ℤ) + 1 ≤ a 1 * (a 0 * 0 + 1) + 0
      have := ha 0
      simp only [mul_zero, zero_add, mul_one, add_zero]
      exact this
    · show (1 : ℤ) ≤ a 0 * 0 + 1
      simp
  | n + 1 => by
    obtain ⟨h1, h3⟩ := contQ_ge_aux ha n
    have h4 : contQ a (n + 3) ≤ a (n + 2) * contQ a (n + 3) := by
      have := ha (n + 1)
      nlinarith
    refine ⟨?_, ?_⟩
    · show ((n + 1 : ℕ) : ℤ) + 1 ≤ a (n + 2) * contQ a (n + 3) + contQ a (n + 2)
      push_cast
      linarith
    · show 1 ≤ contQ a (n + 3)
      omega

/-- `Qₙ₊₃ ≥ n + 1`: the denominators grow. -/
theorem contQ_ge {a : ℕ → ℤ} (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : (n : ℤ) + 1 ≤ contQ a (n + 3) :=
  (contQ_ge_aux ha n).1

theorem one_le_contQ {a : ℕ → ℤ} (ha : ∀ n, 1 ≤ a (n + 1)) (n : ℕ) : 1 ≤ contQ a (n + 2) :=
  (contQ_ge_aux ha n).2

/-! ### The Möbius relation and the approximation bound -/

section Irrational

variable {x : ℝ} (hx : Irrational x)
include hx

/-- **The Möbius relation**: `x (Qₙ₊₁ xₙ + Qₙ) = Pₙ₊₁ xₙ + Pₙ`. -/
theorem mobius : ∀ n, x * ((contQ (digit x) (n + 1) : ℝ) * cq x n + contQ (digit x) n) =
    (contP (digit x) (n + 1) : ℝ) * cq x n + contP (digit x) n
  | 0 => by simp [contP, contQ, cq_zero]
  | n + 1 => by
    have ih := mobius n
    have e := cq_eq_digit_add x n
    have hc : 0 < cq x (n + 1) := lt_trans one_pos (one_lt_cq hx n)
    simp only [contP, contQ]
    push_cast
    rw [e] at ih
    field_simp at ih
    linear_combination ih

/-- **The approximation identity**: `(x Qₙ₊₂ - Pₙ₊₂)(xₙ₊₁ Qₙ₊₂ + Qₙ₊₁) = (-1)ⁿ`. -/
theorem error_mul (n : ℕ) :
    (x * contQ (digit x) (n + 2) - contP (digit x) (n + 2)) *
      (cq x (n + 1) * contQ (digit x) (n + 2) + contQ (digit x) (n + 1)) = (-1) ^ n := by
  have m : x * ((contQ (digit x) (n + 2) : ℝ) * cq x (n + 1) + contQ (digit x) (n + 1)) =
      (contP (digit x) (n + 2) : ℝ) * cq x (n + 1) + contP (digit x) (n + 1) := mobius hx (n + 1)
  have d : contP (digit x) (n + 2) * contQ (digit x) (n + 1) -
      contP (digit x) (n + 1) * contQ (digit x) (n + 2) = (-1) ^ (n + 1) := cont_det (digit x) (n + 1)
  have d' : ((contP (digit x) (n + 2) : ℝ) * contQ (digit x) (n + 1) -
      contP (digit x) (n + 1) * contQ (digit x) (n + 2)) = (-1) ^ (n + 1) := by exact_mod_cast d
  rw [pow_succ] at d'
  linear_combination (contQ (digit x) (n + 2) : ℝ) * m - d'

/-- `|x Qₙ₊₂ - Pₙ₊₂| ≤ 1 / Qₙ₊₂`. -/
theorem abs_mul_sub_le (n : ℕ) :
    |x * contQ (digit x) (n + 2) - contP (digit x) (n + 2)| * contQ (digit x) (n + 2) ≤ 1 := by
  have he := error_mul hx n
  have ha : ∀ k, 1 ≤ digit x (k + 1) := one_le_digit hx
  have hq1 : (1 : ℝ) ≤ contQ (digit x) (n + 2) := by exact_mod_cast one_le_contQ ha n
  have hq0 : (0 : ℝ) ≤ contQ (digit x) (n + 1) := by exact_mod_cast contQ_nonneg ha (n + 1)
  have hc : 1 < cq x (n + 1) := one_lt_cq hx n
  have habs := congrArg abs he
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by nlinarith : (0 : ℝ) < cq x (n + 1) * contQ (digit x) (n + 2) +
      contQ (digit x) (n + 1))] at habs
  nlinarith [abs_nonneg (x * contQ (digit x) (n + 2) - contP (digit x) (n + 2))]

end Irrational

/-- **Two irrationals with the same digits are equal.** -/
theorem eq_of_digit_eq {x y : ℝ} (hx : Irrational x) (hy : Irrational y)
    (h : ∀ n, digit x n = digit y n) : x = y := by
  have hd : digit x = digit y := funext h
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / |x - y|)
  have hax := abs_mul_sub_le hx (n + 1)
  have hay := abs_mul_sub_le hy (n + 1)
  rw [← hd] at hay
  have ha : ∀ k, 1 ≤ digit x (k + 1) := one_le_digit hx
  set q : ℝ := ((contQ (digit x) (n + 1 + 2) : ℤ) : ℝ)
  set p : ℝ := ((contP (digit x) (n + 1 + 2) : ℤ) : ℝ)
  have h3 : (n : ℤ) + 1 ≤ contQ (digit x) (n + 1 + 2) := contQ_ge ha n
  have hq : (n : ℝ) + 1 ≤ q := by
    show ((n : ℤ) : ℝ) + 1 ≤ ((contQ (digit x) (n + 1 + 2) : ℤ) : ℝ)
    exact_mod_cast h3
  have key : |x - y| * q * q ≤ 2 := by
    have : |x - y| * q = |(x * q - p) - (y * q - p)| := by
      rw [show (x * q - p) - (y * q - p) = (x - y) * q by ring, abs_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ q)]
    rw [this]
    calc |(x * q - p) - (y * q - p)| * q ≤ (|x * q - p| + |y * q - p|) * q :=
          mul_le_mul_of_nonneg_right (abs_sub _ _) (by linarith)
      _ ≤ 2 := by nlinarith
  have h2 : 2 < |x - y| * n := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hqq : (n : ℝ) ≤ q * q := by nlinarith
  have h4 : |x - y| * n ≤ |x - y| * (q * q) := mul_le_mul_of_nonneg_left hqq (abs_nonneg _)
  rw [mul_assoc] at key
  linarith

/-! ### Transporting quadratic equations along integer Möbius maps -/

/-- If `y` satisfies `A y² + B y + C = 0` and `x (c y + d) = a y + b` with `a d - b c = ±1`, then
`x` satisfies an integer quadratic equation, nontrivial if the first one is. -/
theorem transport {x y : ℝ} {a b c d A B C : ℤ} (hdet : (a * d - b * c) ^ 2 = 1)
    (hxy : x * (c * y + d) = a * y + b) (hy : (A : ℝ) * y ^ 2 + B * y + C = 0)
    (hne : (A, B, C) ≠ (0, 0, 0)) :
    ∃ A' B' C' : ℤ, (A', B', C') ≠ (0, 0, 0) ∧ (A' : ℝ) * x ^ 2 + B' * x + C' = 0 := by
  have hdetR : ((a : ℝ) * d - b * c) ^ 2 = 1 := by exact_mod_cast hdet
  -- `w = a - c x` satisfies `w (c y + d) = a d - b c` and `w y = d x - b`
  have hw : ((a : ℝ) - c * x) * (c * y + d) = a * d - b * c := by linear_combination -c * hxy
  have hwy : ((a : ℝ) - c * x) * y = d * x - b := by linear_combination -hxy
  refine ⟨A * d ^ 2 - B * c * d + C * c ^ 2, -2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c,
    A * b ^ 2 - B * a * b + C * a ^ 2, ?_, ?_⟩
  · intro h0
    simp only [Prod.mk.injEq] at h0
    obtain ⟨h1, h2, h3⟩ := h0
    apply hne
    have eA : A * (a * d - b * c) ^ 2 = (A * d ^ 2 - B * c * d + C * c ^ 2) * a ^ 2 +
        (-2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c) * a * c +
        (A * b ^ 2 - B * a * b + C * a ^ 2) * c ^ 2 := by ring
    have eB : B * (a * d - b * c) ^ 2 = 2 * (A * d ^ 2 - B * c * d + C * c ^ 2) * a * b +
        (-2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c) * (a * d + b * c) +
        2 * (A * b ^ 2 - B * a * b + C * a ^ 2) * c * d := by ring
    have eC : C * (a * d - b * c) ^ 2 = (A * d ^ 2 - B * c * d + C * c ^ 2) * b ^ 2 +
        (-2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c) * b * d +
        (A * b ^ 2 - B * a * b + C * a ^ 2) * d ^ 2 := by ring
    rw [h1, h2, h3, hdet] at eA eB eC
    simp only [mul_one, zero_mul, mul_zero, add_zero] at eA eB eC
    rw [eA, eB, eC]
  · push_cast
    have := congrArg (fun t => t * ((a : ℝ) - c * x) ^ 2) hy
    simp only [zero_mul] at this
    linear_combination this - (A * y * (a - c * x) + A * (d * x - b) + B * (a - c * x)) * hwy

/-! ### Euler and Lagrange -/

/-- **Euler**: an irrational with eventually periodic digits satisfies a nontrivial integer
quadratic equation. -/
theorem quadratic_of_digit_periodic {x : ℝ} (hx : Irrational x) {K T : ℕ} (hT : 0 < T)
    (hper : ∀ n, K ≤ n → digit x (n + T) = digit x n) :
    ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * x ^ 2 + B * x + C = 0 := by
  set y := cq x K
  have hy : Irrational y := irrational_cq hx K
  -- the tail after `T` more steps has the same digits, hence equals `y`
  have hyT : cq y T = y := by
    refine eq_of_digit_eq (irrational_cq hy T) hy fun n => ?_
    rw [← digit_add, ← digit_add, ← digit_add, show K + (T + n) = K + n + T by omega]
    exact hper _ (by omega)
  -- `y` is a fixed point of an integer Möbius map
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have m := mobius hy (T' + 1)
  rw [hyT] at m
  have hq : 1 ≤ contQ (digit y) (T' + 2) := one_le_contQ (one_le_digit hy) T'
  have hquad : ((contQ (digit y) (T' + 2) : ℤ) : ℝ) * y ^ 2 +
      ((contQ (digit y) (T' + 1) - contP (digit y) (T' + 2) : ℤ) : ℝ) * y +
      ((-contP (digit y) (T' + 1) : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination m
  -- transport to `x`
  have mK := mobius hx K
  have hdet := cont_det (digit x) K
  refine transport (a := contP (digit x) (K + 1)) (b := contP (digit x) K)
    (c := contQ (digit x) (K + 1)) (d := contQ (digit x) K) ?_ mK hquad ?_
  · rw [hdet]
    rw [← pow_mul, show K * 2 = 2 * K by ring, pow_mul]
    norm_num
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

/-- A nonzero integer quadratic has finitely many real roots: at most `r₀` and `-B/A - r₀`. -/
theorem finite_roots {A B C : ℤ} (hA : A ≠ 0) :
    {X : ℝ | (A : ℝ) * X ^ 2 + B * X + C = 0}.Finite := by
  by_cases h : ∃ r₀ : ℝ, (A : ℝ) * r₀ ^ 2 + B * r₀ + C = 0
  · obtain ⟨r₀, hr₀⟩ := h
    refine (Set.toFinite ({r₀, -(B : ℝ) / A - r₀} : Set ℝ)).subset fun X hX => ?_
    simp only [Set.mem_ofPred_eq] at hX
    have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    have h1 : (X - r₀) * ((A : ℝ) * (X + r₀) + B) = 0 := by linear_combination hX - hr₀
    rcases mul_eq_zero.1 h1 with h | h
    · simp [sub_eq_zero.1 h]
    · right
      rw [Set.mem_singleton_iff]
      field_simp
      linear_combination h
  · refine Set.finite_empty.subset fun X hX => ?_
    exact h ⟨X, hX⟩

/-- **Lagrange**: an irrational satisfying a nontrivial integer quadratic equation has eventually
periodic digits. -/
theorem digit_periodic_of_quadratic {x : ℝ} (hx : Irrational x) {A B C : ℤ}
    (hne : (A, B, C) ≠ (0, 0, 0)) (hq : (A : ℝ) * x ^ 2 + B * x + C = 0) :
    ∃ K T, 0 < T ∧ ∀ n, K ≤ n → digit x (n + T) = digit x n := by
  have hA : A ≠ 0 := by
    rintro rfl
    have hB : B ≠ 0 := by
      rintro rfl
      apply hne
      have : (C : ℝ) = 0 := by simpa using hq
      simp [show C = 0 by exact_mod_cast this]
    have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    have hq' : (B : ℝ) * x + C = 0 := by simpa using hq
    apply hx
    refine ⟨((-C : ℤ) : ℚ) / ((B : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff hBR]
    linear_combination (-1 : ℝ) * hq'
  -- the form `F(p, q) = A p² + B p q + C q²`
  set F : ℤ → ℤ → ℤ := fun p q => A * p ^ 2 + B * p * q + C * q ^ 2 with hF
  -- `F` vanishes at no `(p, q)` with `q ≠ 0`: a rational root would make `x` rational
  have hF0 : ∀ p q : ℤ, q ≠ 0 → F p q ≠ 0 := by
    intro p q hq0 hFpq
    apply hx
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    have hr : (A : ℝ) * ((p : ℝ) / q) ^ 2 + B * ((p : ℝ) / q) + C = 0 := by
      have : ((F p q : ℤ) : ℝ) = 0 := by exact_mod_cast hFpq
      simp only [hF] at this
      push_cast at this
      field_simp
      linear_combination this
    have hxr : x ≠ (p : ℝ) / q := fun h => hx ⟨p / q, by push_cast; exact h.symm⟩
    have hsum : (A : ℝ) * (x + (p : ℝ) / q) + B = 0 := by
      have h1 : ((A : ℝ) * (x + (p : ℝ) / q) + B) * (x - (p : ℝ) / q) = 0 := by
        linear_combination hq - hr
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hxr
    have hsum' : (A : ℝ) * (x * q + p) + B * q = 0 := by
      have := congrArg (· * (q : ℝ)) hsum
      simp only [zero_mul] at this
      field_simp at this
      linear_combination this
    refine ⟨((-B * q - A * p : ℤ) : ℚ) / ((A * q : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff (mul_ne_zero hAR hqR)]
    linear_combination (-1 : ℝ) * hsum'
  -- the bound on `F` along the convergents
  set M : ℝ := |(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)| with hM
  have ha : ∀ k, 1 ≤ digit x (k + 1) := one_le_digit hx
  have hFbound : ∀ n, |((F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) : ℤ) : ℝ)| ≤ M := by
    intro n
    have herr := abs_mul_sub_le hx n
    have hq1 : (1 : ℝ) ≤ ((contQ (digit x) (n + 2) : ℤ) : ℝ) := by exact_mod_cast one_le_contQ ha n
    have hval : ((F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) : ℤ) : ℝ) =
        (((contP (digit x) (n + 2) : ℤ) : ℝ) - x * ((contQ (digit x) (n + 2) : ℤ) : ℝ)) *
          (A * (((contP (digit x) (n + 2) : ℤ) : ℝ) + x * ((contQ (digit x) (n + 2) : ℤ) : ℝ)) +
            B * ((contQ (digit x) (n + 2) : ℤ) : ℝ)) := by
      simp only [hF]
      push_cast
      linear_combination (((contQ (digit x) (n + 2) : ℤ) : ℝ) ^ 2) * hq
    generalize ((contP (digit x) (n + 2) : ℤ) : ℝ) = p at hval herr
    generalize ((contQ (digit x) (n + 2) : ℤ) : ℝ) = q at hval herr hq1
    rw [hval, abs_mul]
    have he : |p - x * q| ≤ 1 / q := by
      rw [abs_sub_comm, le_div_iff₀ (by linarith)]
      exact herr
    have h2 : |(A : ℝ) * (p + x * q) + B * q| ≤ (|(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)|) * q := by
      have hp : |p + x * q| ≤ (2 * |x| + 1) * q := by
        have : |p + x * q| ≤ |p - x * q| + 2 * |x| * q := by
          calc |p + x * q| = |(p - x * q) + 2 * x * q| := by ring_nf
            _ ≤ |p - x * q| + |2 * x * q| := abs_add_le _ _
            _ = |p - x * q| + 2 * |x| * q := by
              rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
                abs_of_pos (by linarith : (0 : ℝ) < q)]
        have h1q : 1 / q ≤ q := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        nlinarith
      calc |(A : ℝ) * (p + x * q) + B * q| ≤ |(A : ℝ) * (p + x * q)| + |(B : ℝ) * q| :=
            abs_add_le _ _
        _ = |(A : ℝ)| * |p + x * q| + |(B : ℝ)| * q := by
            rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q)]
        _ ≤ |(A : ℝ)| * ((2 * |x| + 1) * q) + |(B : ℝ)| * q := by
            gcongr
        _ = (|(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)|) * q := by ring
    calc |p - x * q| * |(A : ℝ) * (p + x * q) + B * q|
        ≤ (1 / q) * ((|(A : ℝ)| * (2 * |x| + 1) + |(B : ℝ)|) * q) :=
          mul_le_mul he h2 (abs_nonneg _) (by positivity)
      _ = M := by rw [hM]; field_simp
  -- the quadratic satisfied by the complete quotient `x_{n+1}`
  have hcq : ∀ n, ((F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) : ℤ) : ℝ) *
      cq x (n + 1) ^ 2 +
      ((2 * A * contP (digit x) (n + 2) * contP (digit x) (n + 1) +
        B * (contP (digit x) (n + 2) * contQ (digit x) (n + 1) +
          contP (digit x) (n + 1) * contQ (digit x) (n + 2)) +
        2 * C * contQ (digit x) (n + 2) * contQ (digit x) (n + 1) : ℤ) : ℝ) * cq x (n + 1) +
      ((F (contP (digit x) (n + 1)) (contQ (digit x) (n + 1)) : ℤ) : ℝ) = 0 := by
    intro n
    have m := mobius hx (n + 1)
    simp only [hF]
    push_cast
    set c := cq x (n + 1)
    set p := (contP (digit x) (n + 2) : ℝ)
    set p' := (contP (digit x) (n + 1) : ℝ)
    set q := (contQ (digit x) (n + 2) : ℝ)
    set q' := (contQ (digit x) (n + 1) : ℝ)
    -- substitute `x (q c + q') = p c + p'` into `A x² + B x + C = 0`
    linear_combination (q * c + q') ^ 2 * hq -
      (A * (x * (q * c + q') + (p * c + p')) + B * (q * c + q')) * m
  -- the discriminant is invariant
  have hdisc : ∀ n,
      (2 * A * contP (digit x) (n + 2) * contP (digit x) (n + 1) +
        B * (contP (digit x) (n + 2) * contQ (digit x) (n + 1) +
          contP (digit x) (n + 1) * contQ (digit x) (n + 2)) +
        2 * C * contQ (digit x) (n + 2) * contQ (digit x) (n + 1)) ^ 2 -
      4 * F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) *
        F (contP (digit x) (n + 1)) (contQ (digit x) (n + 1)) = B ^ 2 - 4 * A * C := by
    intro n
    have d := cont_det (digit x) (n + 1)
    have d2 : (contP (digit x) (n + 2) * contQ (digit x) (n + 1) -
        contP (digit x) (n + 1) * contQ (digit x) (n + 2)) ^ 2 = 1 := by
      rw [d, ← pow_mul]
      exact Even.neg_one_pow ⟨n + 1, by ring⟩
    simp only [hF]
    linear_combination (B ^ 2 - 4 * A * C) * d2
  -- the coefficients are bounded integers, so the complete quotients take finitely many values
  obtain ⟨N, hN⟩ := exists_nat_gt M
  set D := B ^ 2 - 4 * A * C
  set R : ℤ := N + |D| + 4 * N * N
  have hFint : ∀ n, -(N : ℤ) ≤ F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) ∧
      F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) ≤ N := by
    intro n
    have b := hFbound n
    have : |((F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) : ℤ) : ℝ)| < (N : ℝ) := by
      linarith
    rw [abs_lt] at this
    constructor
    · have := this.1
      exact_mod_cast this.le
    · exact_mod_cast this.2.le
  have hbox : ∀ n, 1 ≤ n →
      (-(N : ℤ) ≤ F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) ∧
        F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2)) ≤ N) ∧
      (-(N : ℤ) ≤ F (contP (digit x) (n + 1)) (contQ (digit x) (n + 1)) ∧
        F (contP (digit x) (n + 1)) (contQ (digit x) (n + 1)) ≤ N) ∧
      (-R ≤ 2 * A * contP (digit x) (n + 2) * contP (digit x) (n + 1) +
        B * (contP (digit x) (n + 2) * contQ (digit x) (n + 1) +
          contP (digit x) (n + 1) * contQ (digit x) (n + 2)) +
        2 * C * contQ (digit x) (n + 2) * contQ (digit x) (n + 1) ∧
       2 * A * contP (digit x) (n + 2) * contP (digit x) (n + 1) +
        B * (contP (digit x) (n + 2) * contQ (digit x) (n + 1) +
          contP (digit x) (n + 1) * contQ (digit x) (n + 2)) +
        2 * C * contQ (digit x) (n + 2) * contQ (digit x) (n + 1) ≤ R) := by
    intro n hn
    have i1 := hFint n
    have i2 := hFint (n - 1)
    rw [show n - 1 + 2 = n + 1 by omega] at i2
    refine ⟨i1, i2, ?_⟩
    have hd := hdisc n
    set β := 2 * A * contP (digit x) (n + 2) * contP (digit x) (n + 1) +
        B * (contP (digit x) (n + 2) * contQ (digit x) (n + 1) +
          contP (digit x) (n + 1) * contQ (digit x) (n + 2)) +
        2 * C * contQ (digit x) (n + 2) * contQ (digit x) (n + 1)
    set f1 := F (contP (digit x) (n + 2)) (contQ (digit x) (n + 2))
    set f2 := F (contP (digit x) (n + 1)) (contQ (digit x) (n + 1))
    have hb : β ^ 2 = D + 4 * f1 * f2 := by linarith
    have hf : f1 * f2 ≤ (N : ℤ) * N := by nlinarith [i1.1, i1.2, i2.1, i2.2]
    have hD : D ≤ |D| := le_abs_self D
    have hβ1 := Int.le_self_sq β
    have hβ2 := Int.le_self_sq (-β)
    rw [neg_sq] at hβ2
    have hN0 : (0 : ℤ) ≤ N := by exact_mod_cast Nat.zero_le N
    constructor <;> nlinarith
  -- the finite set of candidate values
  set box := (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-R) R ×ˢ Finset.Icc (-(N : ℤ)) N).filter
    fun t => t.1 ≠ 0
  set S : Set ℝ := ⋃ t ∈ box, {X : ℝ | (t.1 : ℝ) * X ^ 2 + t.2.1 * X + t.2.2 = 0}
  have hS : S.Finite := Set.Finite.biUnion box.finite_toSet fun t ht => by
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, box] at ht
    exact finite_roots ht.2
  have hmem : ∀ n, cq x (n + 2) ∈ S := by
    intro n
    obtain ⟨b1, b2, b3⟩ := hbox (n + 1) (by omega)
    simp only [S, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨⟨F (contP (digit x) (n + 1 + 2)) (contQ (digit x) (n + 1 + 2)),
      2 * A * contP (digit x) (n + 1 + 2) * contP (digit x) (n + 1 + 1) +
        B * (contP (digit x) (n + 1 + 2) * contQ (digit x) (n + 1 + 1) +
          contP (digit x) (n + 1 + 1) * contQ (digit x) (n + 1 + 2)) +
        2 * C * contQ (digit x) (n + 1 + 2) * contQ (digit x) (n + 1 + 1),
      F (contP (digit x) (n + 1 + 1)) (contQ (digit x) (n + 1 + 1))⟩, ?_, ?_⟩
    · simp only [box, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨b1, b3, b2⟩, hF0 _ _ (by
        have := one_le_contQ ha (n + 1)
        omega)⟩
    · exact hcq (n + 1)
  obtain ⟨i, j, hij, hEq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun n => cq x (n + 2)) hmem hS
  refine ⟨i + 2, j - i, by omega, fun n hn => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = i + 2 + s := ⟨n - (i + 2), by omega⟩
  rw [show i + 2 + s + (j - i) = j + 2 + s by omega, digit_add, digit_add]
  have hEq' : cq x (i + 2) = cq x (j + 2) := hEq
  rw [hEq']

/-- **Euler–Lagrange**: the digits of an irrational are eventually periodic iff it satisfies a
nontrivial integer quadratic equation. -/
theorem digit_periodic_iff {x : ℝ} (hx : Irrational x) :
    (∃ K T, 0 < T ∧ ∀ n, K ≤ n → digit x (n + T) = digit x n) ↔
      ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * x ^ 2 + B * x + C = 0 := by
  constructor
  · rintro ⟨K, T, hT, hper⟩
    exact quadratic_of_digit_periodic hx hT hper
  · rintro ⟨A, B, C, hne, hq⟩
    exact digit_periodic_of_quadratic hx hne hq


/-! ### Rational numbers have terminating expansions -/

theorem fract_div_eq (m : ℤ) {d : ℕ} (hd : 0 < d) :
    Int.fract ((m : ℝ) / d) = ((m % (d : ℤ) : ℤ) : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  rw [Int.fract_eq_iff]
  refine ⟨div_nonneg (by exact_mod_cast Int.emod_nonneg m (by omega)) hdR.le, ?_, m / d, ?_⟩
  · rw [div_lt_one hdR]
    exact_mod_cast Int.emod_lt_of_pos m hd'
  · have h := Int.mul_ediv_add_emod m (d : ℤ)
    have : (d : ℝ) * ((m / (d : ℤ) : ℤ) : ℝ) + ((m % (d : ℤ) : ℤ) : ℝ) = m := by exact_mod_cast h
    rw [← sub_div, div_eq_iff hdR.ne']
    linear_combination (-1 : ℝ) * this

/-- **A rational number reaches an integer complete quotient** (Euclid's algorithm terminates). -/
theorem exists_fract_cq_eq_zero : ∀ (d : ℕ) (m : ℤ), 0 < d →
    ∃ n, Int.fract (cq ((m : ℝ) / d) n) = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m hd
    by_cases h0 : m % (d : ℤ) = 0
    · exact ⟨0, by rw [cq_zero, fract_div_eq m hd, h0]; simp⟩
    · have hr : 0 < m % (d : ℤ) := lt_of_le_of_ne (Int.emod_nonneg m (by exact_mod_cast hd.ne'))
        (Ne.symm h0)
      obtain ⟨r, hr'⟩ : ∃ r : ℕ, (r : ℤ) = m % (d : ℤ) := ⟨(m % (d : ℤ)).toNat, Int.toNat_of_nonneg hr.le⟩
      have hrd : r < d := by
        have := Int.emod_lt_of_pos m (by exact_mod_cast hd : (0 : ℤ) < d)
        omega
      have hr0 : 0 < r := by omega
      obtain ⟨n, hn⟩ := ih r hrd (d : ℤ) hr0
      refine ⟨n + 1, ?_⟩
      have hg : gauss ((m : ℝ) / d) = ((d : ℤ) : ℝ) / r := by
        rw [gauss, fract_div_eq m hd, ← hr', inv_div]
        push_cast
        ring
      rw [show n + 1 = 1 + n by omega, cq_add, show cq ((m : ℝ) / d) 1 = gauss ((m : ℝ) / d) from
        cq_succ _ 0, hg]
      exact hn

/-! ### Continued fractions with prescribed digits -/

/-- A digit sequence shifted by `n`. -/
def shift (b : ℕ → ℤ) (n : ℕ) : ℕ → ℤ := fun k => b (n + k)

theorem shift_shift (b : ℕ → ℤ) (m n : ℕ) : shift (shift b m) n = shift b (m + n) := by
  funext k
  simp [shift, Nat.add_assoc]

/-- The continuants of `b` from those of its shift: `[b₀; b₁, …] = b₀ + 1 / [b₁; …]`. -/
theorem cont_shift (b : ℕ → ℤ) : ∀ m,
    (contP b (m + 1) = b 0 * contP (shift b 1) m + contQ (shift b 1) m ∧
      contQ b (m + 1) = contP (shift b 1) m) ∧
    (contP b (m + 2) = b 0 * contP (shift b 1) (m + 1) + contQ (shift b 1) (m + 1) ∧
      contQ b (m + 2) = contP (shift b 1) (m + 1))
  | 0 => by simp [contP, contQ]
  | m + 1 => by
    obtain ⟨h1, h2⟩ := cont_shift b m
    refine ⟨h2, ?_, ?_⟩
    · show b (m + 1) * contP b (m + 2) + contP b (m + 1) =
        b 0 * (shift b 1 m * contP (shift b 1) (m + 1) + contP (shift b 1) m) +
          (shift b 1 m * contQ (shift b 1) (m + 1) + contQ (shift b 1) m)
      rw [h2.1, h1.1, show shift b 1 m = b (m + 1) by simp [shift, Nat.add_comm]]
      ring
    · show b (m + 1) * contQ b (m + 2) + contQ b (m + 1) =
        shift b 1 m * contP (shift b 1) (m + 1) + contP (shift b 1) m
      rw [h2.2, h1.2, show shift b 1 m = b (m + 1) by simp [shift, Nat.add_comm]]

section Digits

variable {b : ℕ → ℤ} (hb : ∀ k, 1 ≤ b k)
include hb

theorem one_le_contP : ∀ m, 1 ≤ contP b (m + 2) ∧ 0 ≤ contP b (m + 1)
  | 0 => ⟨by simpa [contP] using hb 0, by simp [contP]⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := one_le_contP m
    refine ⟨?_, ?_⟩
    · show 1 ≤ b (m + 1) * contP b (m + 2) + contP b (m + 1)
      nlinarith [hb (m + 1)]
    · show 0 ≤ contP b (m + 2)
      omega

/-- The convergents `[b₀; b₁, …, b_K]`. -/
noncomputable def conv (b : ℕ → ℤ) (K : ℕ) : ℝ := (contP b (K + 2) : ℝ) / contQ b (K + 2)

theorem shift_ge : ∀ n k, 1 ≤ shift b n k := fun n k => hb (n + k)

theorem conv_succ (K : ℕ) : conv b (K + 1) = b 0 + (conv (shift b 1) K)⁻¹ := by
  have hb' : ∀ k, 1 ≤ shift b 1 k := fun k => hb (1 + k)
  obtain ⟨-, h⟩ := cont_shift b (K + 1)
  have hP := (one_le_contP hb' K).1
  unfold conv
  rw [show K + 1 + 2 = K + 1 + 2 from rfl, h.1, h.2]
  have : (0 : ℝ) < contP (shift b 1) (K + 2) := by exact_mod_cast hP
  have hQ : (0 : ℝ) < contQ (shift b 1) (K + 2) := by
    exact_mod_cast one_le_contQ (fun k => hb' (k + 1)) K
  rw [inv_div]
  push_cast
  field_simp

theorem one_le_conv : ∀ K, 1 ≤ conv b K := by
  intro K
  induction K generalizing b with
  | zero =>
    unfold conv
    simp [contP, contQ]
    exact_mod_cast hb 0
  | succ K ih =>
    rw [conv_succ hb]
    have := ih (b := shift b 1) (fun k => hb (1 + k))
    have : 0 < (conv (shift b 1) K)⁻¹ := inv_pos.2 (by linarith)
    have := hb 0
    have : (1 : ℝ) ≤ b 0 := by exact_mod_cast hb 0
    linarith

theorem abs_conv_succ_sub (K : ℕ) :
    |conv b (K + 1) - conv b K| = 1 / ((contQ b (K + 3) : ℝ) * contQ b (K + 2)) := by
  have ha : ∀ n, 1 ≤ b (n + 1) := fun n => hb (n + 1)
  have hq2 : (0 : ℝ) < contQ b (K + 2) := by exact_mod_cast one_le_contQ ha K
  have hq3 : (0 : ℝ) < contQ b (K + 3) := by exact_mod_cast one_le_contQ ha (K + 1)
  have hdet : contP b (K + 3) * contQ b (K + 2) - contP b (K + 2) * contQ b (K + 3) =
      (-1) ^ (K + 2) := cont_det b (K + 2)
  have hdetR : (contP b (K + 3) : ℝ) * contQ b (K + 2) - contP b (K + 2) * contQ b (K + 3) =
      (-1) ^ (K + 2) := by exact_mod_cast hdet
  have key : (contP b (K + 3) : ℝ) * contQ b (K + 2) - contQ b (K + 3) * contP b (K + 2) =
      (-1) ^ (K + 2) := by linear_combination hdetR
  unfold conv
  rw [show K + 1 + 2 = K + 3 from rfl, div_sub_div _ _ hq3.ne' hq2.ne', key, abs_div, abs_pow,
    abs_neg, abs_one, one_pow, abs_of_pos (mul_pos hq3 hq2)]

theorem cauchySeq_conv : CauchySeq (conv b) := by
  have ha : ∀ n, 1 ≤ b (n + 1) := fun n => hb (n + 1)
  refine cauchySeq_of_summable_dist ?_
  have hsum : Summable fun K : ℕ => 2 * ((1 : ℝ) / ((K + 1 : ℝ) ^ 2)) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    exact ((summable_nat_add_iff 1).2 this |>.congr fun K => by push_cast; ring_nf).mul_left 2
  refine Summable.of_nonneg_of_le (fun K => dist_nonneg) (fun K => ?_) hsum
  rw [dist_comm, Real.dist_eq, abs_conv_succ_sub hb K]
  have h3 : (K : ℝ) + 1 ≤ contQ b (K + 3) := by exact_mod_cast contQ_ge ha K
  have h2 : (1 : ℝ) ≤ contQ b (K + 2) := by exact_mod_cast one_le_contQ ha K
  have h2' : (K : ℝ) ≤ contQ b (K + 2) := by
    rcases K with _ | k
    · simp only [Nat.cast_zero]
      linarith
    · have := contQ_ge ha k
      have h' : ((k : ℤ) : ℝ) + 1 ≤ ((contQ b (k + 1 + 2) : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h' ⊢
      linarith
  have hpos : (0 : ℝ) < (contQ b (K + 3) : ℝ) * contQ b (K + 2) :=
    mul_pos (by have := (Nat.cast_nonneg K : (0 : ℝ) ≤ K); linarith) (by linarith)
  rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
  have e1 : ((K : ℝ) + 1) * contQ b (K + 2) ≤ (contQ b (K + 3) : ℝ) * contQ b (K + 2) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  nlinarith

/-- The value `[b₀; b₁, b₂, …]` of the continued fraction with digits `b`. -/
noncomputable def cfValue (b : ℕ → ℤ) : ℝ := Filter.limUnder Filter.atTop (conv b)

theorem tendsto_conv : Filter.Tendsto (conv b) Filter.atTop (nhds (cfValue b)) :=
  (cauchySeq_conv hb).tendsto_limUnder

theorem one_le_cfValue : 1 ≤ cfValue b :=
  ge_of_tendsto (tendsto_conv hb) (Filter.Eventually.of_forall (one_le_conv hb))

theorem cfValue_eq : cfValue b = b 0 + (cfValue (shift b 1))⁻¹ := by
  have hb' : ∀ k, 1 ≤ shift b 1 k := fun k => hb (1 + k)
  have h1 : Filter.Tendsto (fun K => conv b (K + 1)) Filter.atTop (nhds (cfValue b)) :=
    (tendsto_conv hb).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun K => (b 0 : ℝ) + (conv (shift b 1) K)⁻¹) Filter.atTop
      (nhds ((b 0 : ℝ) + (cfValue (shift b 1))⁻¹)) :=
    ((tendsto_conv hb').inv₀ (by linarith [one_le_cfValue hb'])).const_add _
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun K => ?_
  rw [conv_succ hb]

theorem one_lt_cfValue_shift : 1 < cfValue (shift b 1) := by
  have hb' : ∀ k, 1 ≤ shift b 1 k := fun k => hb (1 + k)
  have hb'' : ∀ k, 1 ≤ shift (shift b 1) 1 k := fun k => hb' (1 + k)
  rw [cfValue_eq hb']
  have := one_le_cfValue hb''
  have : 0 < (cfValue (shift (shift b 1) 1))⁻¹ := inv_pos.2 (by linarith)
  have : (1 : ℝ) ≤ shift b 1 0 := by exact_mod_cast hb' 0
  linarith

theorem floor_cfValue : ⌊cfValue b⌋ = b 0 := by
  rw [cfValue_eq hb, Int.floor_intCast_add, add_eq_left, Int.floor_eq_zero_iff]
  have h := one_lt_cfValue_shift hb
  refine ⟨(inv_pos.2 (by linarith)).le, ?_⟩
  exact inv_lt_one_of_one_lt₀ h

theorem gauss_cfValue : gauss (cfValue b) = cfValue (shift b 1) := by
  have h := one_lt_cfValue_shift hb
  unfold gauss
  rw [Int.fract, floor_cfValue hb, cfValue_eq hb]
  simp

theorem cq_cfValue : ∀ n, cq (cfValue b) n = cfValue (shift b n)
  | 0 => by
    rw [cq_zero]
    congr 1
    funext k
    simp [shift]
  | n + 1 => by
    rw [cq_succ, cq_cfValue n, gauss_cfValue (shift_ge hb n), shift_shift]

/-- **The digits of `[b₀; b₁, …]` are `b`.** -/
theorem digit_cfValue (n : ℕ) : digit (cfValue b) n = b n := by
  unfold digit
  rw [cq_cfValue hb, floor_cfValue (shift_ge hb n)]
  simp [shift]

/-- `[b₀; b₁, …]` is irrational: its expansion never reaches an integer. -/
theorem irrational_cfValue : Irrational (cfValue b) := by
  rintro ⟨q, hq⟩
  have hq' : (q : ℝ) = (q.num : ℝ) / q.den := by
    rw [Rat.cast_def]
  obtain ⟨n, hn⟩ := exists_fract_cq_eq_zero q.den q.num q.den_pos
  rw [← hq', hq, cq_cfValue hb, cfValue_eq (shift_ge hb n), Int.fract_intCast_add] at hn
  have h := one_lt_cfValue_shift (shift_ge hb n)
  rw [Int.fract_eq_self.2 ⟨(inv_pos.2 (by linarith)).le, inv_lt_one_of_one_lt₀ h⟩] at hn
  exact (inv_pos.2 (by linarith : (0 : ℝ) < cfValue (shift (shift b n) 1))).ne' hn

/-- **Euler–Lagrange for prescribed digits**: `[b₀; b₁, …]` with all `bₖ ≥ 1` satisfies a nontrivial
integer quadratic equation iff `b` is eventually periodic. -/
theorem quadratic_cfValue_iff :
    (∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * cfValue b ^ 2 + B * cfValue b + C = 0) ↔
      ∃ K T, 0 < T ∧ ∀ n, K ≤ n → b (n + T) = b n := by
  rw [← digit_periodic_iff (irrational_cfValue hb)]
  simp only [digit_cfValue hb]

end Digits


/-! ### Problem 1 -/

open Ruliology.CellularAutomata

/-- `θ = [1 + c(0); 1 + c(1), 1 + c(2), …] = 2.3693419984…`, the continued fraction whose partial
quotients are `2` at the black cells of the center column and `1` at the white cells. -/
noncomputable def theta : ℝ := cfValue fun n => 1 + if c n then 1 else 0

/-- **Problem 1 ⟺ `θ` is not a quadratic irrational**. By Euler–Lagrange, the
digits `1 + c(t)` of `θ` are eventually periodic iff `θ` satisfies a nontrivial integer quadratic
equation; `θ` is never rational. -/
theorem problem1_iff_not_quadratic : Rule30Prize.Problem1 ↔
    ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * theta ^ 2 + B * theta + C = 0 := by
  unfold theta
  rw [quadratic_cfValue_iff fun n => by split_ifs <;> norm_num]
  constructor
  · rintro hP ⟨K, T, hT, hper⟩
    refine hP ⟨K, T, hT, fun t ht => ?_⟩
    have := hper t ht
    show c (t + T) = c t
    cases h1 : c (t + T) <;> cases h2 : c t <;> simp_all
  · rintro h ⟨T, P, hP, hper⟩
    refine h ⟨T, P, hP, fun n hn => ?_⟩
    have : c (n + P) = c n := hper n hn
    simp [this]

end Rule30Equivalents.Lagrange
