module

public import Rule30Equivalents.BinaryIrrational
public import Rule30Equivalents.ShiftOrbit
public import Rule30Equivalents.BlackTimes
public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Problem 1 in number theory: continued fractions, approximation, the circle, long division

Let `x₂ = centerBinary = 0.c(0) c(1) c(2) …₂ = ∑ₜ c(t) / 2^(t+1)` be the center column of rule 30
read as a binary number. Problem 1 holds iff `x₂` is irrational
(`BinaryIrrational.problem1_iff_irrational_binary`). So every characterization of irrational
numbers gives a form of Problem 1. This file proves the ones below for every real number, or for
every digit sequence, and then specializes them to the center column.

## Statements

**Problem 1 holds iff**

* `problem1_iff_cf_not_terminates`: the regular continued fraction of `x₂` (`GenContFract.of`)
  does not terminate;
* `problem1_iff_dirichlet`: infinitely many rationals `q` satisfy `|x₂ - q| < 1 / den(q)²`;
* `problem1_iff_liouvilleWith_two`: `LiouvilleWith 2 x₂`, i.e. for some `C`, infinitely many
  denominators `n` have a numerator `m` with `x₂ ≠ m / n` and `|x₂ - m / n| < C / n²`; the same
  holds for every exponent `1 < p ≤ 2` (`problem1_iff_liouvilleWith`);
* `problem1_iff_infinite_order`, `problem1_iff_addOrderOf_eq_zero`: `x₂` has infinite order in the
  circle `AddCircle 1 = ℝ/ℤ`;
* `problem1_iff_dense_multiples`: the multiples `n x₂ mod 1`, `n : ℤ`, are dense in the circle;
* `problem1_iff_doubling_not_preperiodic`: `x₂ mod 1` is not a preperiodic point of the doubling map
  `y ↦ 2y` of the circle. The doubling map shifts binary digits: its `n`-th iterate sends `x₂` to
  `0.c(n) c(n+1) …₂ mod 1` (`iterate_doubling_centerBinary`). Read the other way, `c(t)` is black
  iff `2^t x₂ mod 1 > 1/2` (`center_iff_fract`), so **Problem 2 holds iff** the doubling orbit of
  `x₂` lies in `(1/2, 1)` with frequency `1/2` (`problem2_iff_doubling`), and **`c` is normal iff**
  the doubling orbit visits every dyadic interval `[k/2^m, (k+1)/2^m)` with frequency `2^-m`
  (`isNormal_iff_doubling`, Borel and Wall);
* `problem1_iff_not_rational_digits` (**no real numbers**): there are no natural numbers `p` and
  `q > 0` with `c(t) = decide (⌊2^(t+1) p / q⌋ mod 2 = 1)` for every `t`, i.e. the center column is
  not the sequence of binary digits of a fraction. `problem1_iff_not_rational_digits_base` says the
  same in every base `B ≥ 2` (the digit `⌊B^(t+1) p / q⌋ mod B` is `c(t) ∈ {0, 1}` for every `t`),
  and `problem1_iff_not_rational_decimal_digits` is base 10.

**General statements**

* For every real `x`: `irrational_iff_not_terminates`, `irrational_iff_infinite_rat_approx`,
  `irrational_iff_liouvilleWith_two`, `irrational_iff_liouvilleWith` (`1 < p ≤ 2`),
  `irrational_iff_not_isOfFinAddOrder`, `irrational_iff_addOrderOf_eq_zero`,
  `irrational_iff_denseRange_zsmul`, and `irrational_iff_not_preperiodic_mul` (the map `y ↦ k y`
  of the circle, `k ≥ 2`).
* In every additive commutative group, for `k ≥ 2`, a point is preperiodic under `y ↦ k • y` iff
  it has finite order (`isOfFinAddOrder_iff_preperiodic`).
* For every `b : ℕ → Bool` and base `B ≥ 2`, with `x = 0.b(0) b(1) …` in base `B`: `b` is
  eventually periodic iff the continued fraction of `x` terminates
  (`eventuallyPeriodic_iff_terminates`), iff `x` has only finitely many approximations
  `|x - q| < 1 / den(q)²` (`eventuallyPeriodic_iff_finite_rat_approx`), iff `¬ LiouvilleWith 2 x`
  (`eventuallyPeriodic_iff_not_liouvilleWith_two`), iff `x` has finite order in `ℝ/ℤ`
  (`eventuallyPeriodic_iff_isOfFinAddOrder`), iff `x mod 1` is preperiodic under `y ↦ B y`
  (`eventuallyPeriodic_iff_preperiodic_mul`).
* Long division (`exists_digits_iff`): `b(t) = decide (⌊2^(t+1) p / q⌋ mod 2 = 1)` for all `t`, for
  some `p` and `q > 0`, iff `b` is eventually periodic and not eventually `true`. In base `B ≥ 3`
  the second condition disappears (`exists_digits_base_iff`).

## Proof

* Continued fractions, good approximations, finite order and dense multiples: Mathlib proves each
  characterization of irrationality (`GenContFract.terminates_iff_rat`,
  `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`,
  `AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div`, `AddCircle.denseRange_zsmul_coe_iff`).
  Combined with `BinaryIrrational`, each becomes a form of Problem 1.
* `LiouvilleWith 2`. Mathlib proves `LiouvilleWith p x → Irrational x` for `p > 1`; its docstring
  says the converse for `1 < p ≤ 2` "is not formalized yet". We prove it from Dirichlet's theorem
  (`exists_rat_approx_den_ge`). An irrational `x` has infinitely many approximations
  `|x - q| < 1 / den(q)²`. Only finitely many rationals with denominator `< N` lie within `1` of
  `x`, so for every `N` there is such a `q` with `den(q) ≥ N`. Taking `n = den(q)`, `m = num(q)` and
  `C = 1` gives `LiouvilleWith 2 x`, and `LiouvilleWith.mono` lowers the exponent.
* Preperiodic points. If `k^(m+P) • x = k^m • x` with `P > 0`, then `(k^(m+P) - k^m) • x = 0`
  and `k^(m+P) - k^m > 0`. Conversely, if `x` has order `N > 0`, the orbit `k^j • x` lies in the
  finite set `{0, x, …, (N - 1) • x}`, so two iterates coincide.
* Long division in base `B`, with the remainders `r_t = B^t p mod q` (`rem`):
  `⌊B^(t+1) p / q⌋ mod B = ⌊B r_t / q⌋` (`digit_eq`) and `r_(t+1) = B r_t mod q` (`rem_succ`).
  The remainders take at most `q` values, so two of them coincide, and from then on remainders
  and digits repeat (`eventuallyPeriodic_of_digits`). In base 2, if the digits were `1` from time
  `T` on, then `q - r_t` would double at every step, but it stays between `1` and `q`
  (`not_eventually_true_of_digits`). Conversely, if `b` is eventually periodic, then
  `x = 0.b(0) b(1) …` in base `B` is a fraction `p / q` (`BinaryIrrational`), and
  `B^(t+1) x = N_(t+1) + x_(t+1)`, where `N_(t+1)` is the number with base-`B` digits
  `b(0) … b(t)` and `x_(t+1) = 0.b(t+1) b(t+2) …`. If `x_(t+1) < 1`, then
  `⌊B^(t+1) p / q⌋ = N_(t+1)`, whose last digit is `b(t)` (`exists_digits_of_eventuallyPeriodic`).
  Here `x_(t+1) < 1` holds if some later digit is `0` (`baseValue_lt_one`, `tail_lt_one`), and
  always in base `B ≥ 3` (`baseValue_lt_one_of_three_le`).

## Special cases

* **Dyadic rationals** have two binary expansions, `0.0111…₂ = 0.1000…₂`. The real-number forms
  do not see this: both expansions are eventually periodic, and their common value is rational.
  For a dyadic rational, long division produces only the expansion that ends in `0`s, so the
  eventually periodic sequence `0111…` (value `1/2`) is not of the form `⌊2^(t+1) p / q⌋ mod 2`.
  That is why `exists_digits_iff` requires "not eventually `true`". For the center column this
  holds, since `c` is not eventually constant (`Rule30Prize.center_not_eventually_constant`). In
  base `B ≥ 3` the digits `0, 1` never reach `B - 1`, and the problem does not arise.
* **Positive periods.** `EventuallyPeriodic` requires a period `P > 0`, `Function.periodicPts` a
  period `n > 0` and `IsOfFinAddOrder` an order `n > 0`; with `0` allowed, every point would
  qualify. In the long-division forms the denominator must be positive. Allowing `q = 0` would
  change nothing: Lean's `n / 0 = 0` only gives the all-`0` sequence, which `p = 0, q = 1` also
  gives.
* **Exponents.** Every real number is `LiouvilleWith 1` (`liouvilleWith_one`), hence
  `LiouvilleWith p` for `p ≤ 1`, so `problem1_iff_liouvilleWith` needs `1 < p`. For `p > 2`,
  `LiouvilleWith p x` is a non-trivial condition on irrational numbers which, by the
  Thue–Siegel–Roth theorem, forces `x` to be transcendental (Mathlib's docstring). So
  `LiouvilleWith p x₂` with `p > 2` implies Problem 1, but irrationality alone does not give it:
  it fails for every algebraic irrational number.

## Sources

* The Mathlib theorems used, all checked here: `GenContFract.terminates_iff_rat`
  (`Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean`), Dirichlet's theorem
  `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` and its converse
  (`Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`), `LiouvilleWith` and the remark on
  the missing converse quoted above
  (`Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean`),
  `AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div`
  (`Mathlib/Topology/Instances/AddCircle/Defs.lean`) and `AddCircle.denseRange_zsmul_coe_iff`
  (`Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean`, "irrational rotation is minimal").
* The classical facts, as stated on Wikipedia: "Simple continued fraction"
  (the expansion is finite iff the number is rational; for rationals it is Euclid's algorithm);
  "Dirichlet's approximation theorem" (an irrational `α` has infinitely many `p/q` with
  `|α - p/q| < 1/q²`); "Irrationality measure" (every irrational number has irrationality exponent
  at least 2, a consequence of Dirichlet's theorem); "Irrational rotation" (the orbits of an
  irrational rotation are dense); "Dyadic transformation" (the doubling map shifts binary digits;
  rational points have eventually periodic orbits, irrational points do not); "Repeating decimal"
  (long division: only finitely many remainders occur, so one repeats, and then the digits repeat;
  a terminating expansion has a second one ending in repeated `9`s).
-/

@[expose] public section

namespace Rule30Equivalents.NumberTheory

open Ruliology.CellularAutomata BinaryIrrational

/-! ### Irrationality of a real number -/

/-- **Continued fractions**: a real number is irrational iff its regular continued fraction does
not terminate. -/
theorem irrational_iff_not_terminates (x : ℝ) :
    Irrational x ↔ ¬ (GenContFract.of x).Terminates := by
  rw [GenContFract.terminates_iff_rat, Irrational, Set.mem_range]
  exact not_congr (exists_congr fun q => eq_comm)

/-- **Dirichlet**: a real number is irrational iff it has infinitely many rational approximations
`|x - q| < 1 / den(q)²` (Mathlib's theorem, turned around). -/
theorem irrational_iff_infinite_rat_approx (x : ℝ) :
    Irrational x ↔ {q : ℚ | |x - q| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
  (Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational x).symm

/-- An irrational number has approximations `|x - q| < 1 / den(q)²` with arbitrarily large
denominators: only finitely many rationals with denominator `< N` lie within `1` of `x`. -/
theorem exists_rat_approx_den_ge {x : ℝ} (hx : Irrational x) (N : ℕ) :
    ∃ q : ℚ, N ≤ q.den ∧ |x - q| < 1 / (q.den : ℝ) ^ 2 := by
  by_contra! h
  apply Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (|x| + 1) * N ≤ K := exists_nat_ge _
  refine (((Set.finite_Icc (-(K : ℤ)) K).prod (Set.finite_Iio N)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ) / z.2)).subset ?_
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq
  have hden : q.den < N := by
    by_contra hge
    exact (h q (not_lt.1 hge)).not_gt hq
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have h1 : |x - q| < 1 := hq.trans_le (by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ hd)
  have hq1 : |(q : ℝ)| ≤ |x| + 1 := by
    have := abs_sub_abs_le_abs_sub (q : ℝ) x
    rw [abs_sub_comm] at this
    linarith
  have hnum : |(q.num : ℝ)| ≤ K := by
    have e : (q.num : ℝ) = q * q.den := by exact_mod_cast (Rat.mul_den_eq_num q).symm
    rw [e, abs_mul, Nat.abs_cast]
    calc |(q : ℝ)| * q.den ≤ (|x| + 1) * N :=
          mul_le_mul hq1 (by exact_mod_cast hden.le) (by positivity) (by positivity)
      _ ≤ K := hK
  rw [abs_le] at hnum
  refine ⟨(q.num, q.den), Set.mk_mem_prod (Set.mem_Icc.2 ⟨?_, ?_⟩) (Set.mem_Iio.2 hden), ?_⟩
  · exact_mod_cast hnum.1
  · exact_mod_cast hnum.2
  · exact Rat.num_div_den q

/-- **Irrational numbers are `LiouvilleWith 2`**, and conversely: for some `C` (here `C = 1`),
infinitely many denominators `n` have a numerator `m` with `x ≠ m / n` and
`|x - m / n| < C / n²`. -/
theorem irrational_iff_liouvilleWith_two (x : ℝ) : Irrational x ↔ LiouvilleWith 2 x := by
  refine ⟨fun hx => ⟨1, Filter.frequently_atTop.2 fun N => ?_⟩, fun h => h.irrational one_lt_two⟩
  obtain ⟨q, hN, hq⟩ := exists_rat_approx_den_ge hx N
  refine ⟨q.den, hN, q.num, ?_, ?_⟩
  · rw [← Rat.cast_def]
    exact hx.ne_rat q
  · rw [← Rat.cast_def, Real.rpow_two]
    exact hq

/-- For every exponent `1 < p ≤ 2`, a real number is irrational iff it is `LiouvilleWith p`. -/
theorem irrational_iff_liouvilleWith {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (x : ℝ) :
    Irrational x ↔ LiouvilleWith p x :=
  ⟨fun hx => ((irrational_iff_liouvilleWith_two x).1 hx).mono hp2, fun h => h.irrational hp1⟩

/-- A real number is irrational iff it has infinite order in the circle `ℝ/ℤ`. -/
theorem irrational_iff_not_isOfFinAddOrder (x : ℝ) :
    Irrational x ↔ ¬ IsOfFinAddOrder (x : AddCircle (1 : ℝ)) := by
  rw [AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div, div_one, Irrational, Set.mem_range,
    not_exists]

/-- The same with `addOrderOf`, which is `0` for elements of infinite order. -/
theorem irrational_iff_addOrderOf_eq_zero (x : ℝ) :
    Irrational x ↔ addOrderOf (x : AddCircle (1 : ℝ)) = 0 := by
  rw [addOrderOf_eq_zero_iff, irrational_iff_not_isOfFinAddOrder]

/-- **Irrational rotations**: a real number is irrational iff its integer multiples are dense in
the circle `ℝ/ℤ`. -/
theorem irrational_iff_denseRange_zsmul (x : ℝ) :
    Irrational x ↔ DenseRange (· • (x : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) := by
  rw [AddCircle.denseRange_zsmul_coe_iff, div_one]

/-- In an additive commutative group, for `k ≥ 2`, a point is preperiodic under `y ↦ k • y` iff
it has finite order. -/
theorem isOfFinAddOrder_iff_preperiodic {G : Type*} [AddCommGroup G] {k : ℕ} (hk : 2 ≤ k)
    (x : G) :
    IsOfFinAddOrder x ↔
      ∃ m, (fun y : G => k • y)^[m] x ∈ Function.periodicPts (fun y : G => k • y) := by
  classical
  constructor
  · intro hx
    have hmem : ∀ j, k ^ j • x ∈
        (((Finset.range (addOrderOf x)).image (fun n : ℕ => n • x) : Finset G) : Set G) := by
      intro j
      rw [Finset.coe_image]
      refine ⟨k ^ j % addOrderOf x, ?_, mod_addOrderOf_nsmul x _⟩
      exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hx.addOrderOf_pos))
    obtain ⟨i, j, hij, heq⟩ := (Finset.finite_toSet _).exists_lt_map_eq_of_forall_mem hmem
    refine ⟨i, Function.mk_mem_periodicPts (n := j - i) (by omega) ?_⟩
    show (fun y : G => k • y)^[j - i] ((fun y : G => k • y)^[i] x) = (fun y : G => k • y)^[i] x
    rw [smul_iterate_apply, smul_iterate_apply, smul_smul, ← pow_add, Nat.sub_add_cancel hij.le,
      heq]
  · rintro ⟨m, hm⟩
    obtain ⟨P, hP, hper⟩ := Function.mem_periodicPts.1 hm
    have e : k ^ (P + m) • x = k ^ m • x := by
      have : (fun y : G => k • y)^[P] ((fun y : G => k • y)^[m] x) =
          (fun y : G => k • y)^[m] x := hper
      rwa [smul_iterate_apply, smul_iterate_apply, smul_smul, ← pow_add] at this
    have hlt : k ^ m < k ^ (P + m) := Nat.pow_lt_pow_right (by omega) (by omega)
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨k ^ (P + m) - k ^ m, by omega, ?_⟩
    rw [sub_nsmul x hlt.le, e, add_neg_cancel]

/-- For `k ≥ 2`, a real number is irrational iff it is not a preperiodic point of the map
`y ↦ k y` of the circle `ℝ/ℤ`. -/
theorem irrational_iff_not_preperiodic_mul {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    Irrational x ↔ ∀ m, (fun y : AddCircle (1 : ℝ) => k • y)^[m] (x : AddCircle (1 : ℝ)) ∉
      Function.periodicPts (fun y : AddCircle (1 : ℝ) => k • y) := by
  rw [irrational_iff_not_isOfFinAddOrder, isOfFinAddOrder_iff_preperiodic hk, not_exists]

/-! ### Digit sequences -/

section DigitSequences

variable {B : ℕ} (hB : 2 ≤ B)
include hB

/-- **Multiplication by the base shifts the digits**: in the circle `ℝ/ℤ`,
`B · 0.b(0) b(1) b(2) … = 0.b(1) b(2) …`. -/
theorem nsmul_coe_baseValue (b : ℕ → Bool) :
    B • (baseValue B b : AddCircle (1 : ℝ)) = (baseValue B (tail b 1) : AddCircle (1 : ℝ)) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_baseValue hB b, AddCircle.coe_add]
  have h0 : (((if b 0 then 1 else 0 : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
    split_ifs
    · exact AddCircle.coe_period (1 : ℝ)
    · exact AddCircle.coe_zero (1 : ℝ)
  rw [h0, zero_add]

/-- The `n`-th iterate of `y ↦ B y` sends `0.b(0) b(1) …` to the tail `0.b(n) b(n+1) …`. -/
theorem iterate_nsmul_coe_baseValue (b : ℕ → Bool) (n : ℕ) :
    (fun y : AddCircle (1 : ℝ) => B • y)^[n] (baseValue B b : AddCircle (1 : ℝ)) =
      (baseValue B (tail b n) : AddCircle (1 : ℝ)) := by
  induction n with
  | zero =>
    have h : tail b 0 = b := funext fun s => by simp [tail]
    rw [Function.iterate_zero_apply, h]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, nsmul_coe_baseValue hB, tail_tail_one]

/-- `BinaryIrrational.eventuallyPeriodic_iff_not_irrational`, with `baseValue`. -/
theorem eventuallyPeriodic_iff_not_irrational_baseValue (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ¬ Irrational (baseValue B b) :=
  eventuallyPeriodic_iff_not_irrational hB b

/-- A digit sequence is eventually periodic iff the continued fraction of its value terminates. -/
theorem eventuallyPeriodic_iff_terminates (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ (GenContFract.of (baseValue B b)).Terminates := by
  rw [eventuallyPeriodic_iff_not_irrational_baseValue hB, irrational_iff_not_terminates, not_not]

/-- A digit sequence is eventually periodic iff its value has only finitely many approximations
`|x - q| < 1 / den(q)²`. -/
theorem eventuallyPeriodic_iff_finite_rat_approx (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ {q : ℚ | |baseValue B b - q| < 1 / (q.den : ℝ) ^ 2}.Finite := by
  rw [eventuallyPeriodic_iff_not_irrational_baseValue hB, irrational_iff_infinite_rat_approx,
    Set.not_infinite]

/-- A digit sequence is eventually periodic iff its value is not `LiouvilleWith 2`. -/
theorem eventuallyPeriodic_iff_not_liouvilleWith_two (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ¬ LiouvilleWith 2 (baseValue B b) := by
  rw [eventuallyPeriodic_iff_not_irrational_baseValue hB, irrational_iff_liouvilleWith_two]

/-- A digit sequence is eventually periodic iff its value has finite order in `ℝ/ℤ`. -/
theorem eventuallyPeriodic_iff_isOfFinAddOrder (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ IsOfFinAddOrder (baseValue B b : AddCircle (1 : ℝ)) := by
  rw [eventuallyPeriodic_iff_not_irrational_baseValue hB, irrational_iff_not_isOfFinAddOrder,
    not_not]

/-- A digit sequence is eventually periodic iff its value is a preperiodic point of the map
`y ↦ B y` of the circle `ℝ/ℤ`. -/
theorem eventuallyPeriodic_iff_preperiodic_mul (b : ℕ → Bool) :
    EventuallyPeriodic b ↔
      ∃ m, (fun y : AddCircle (1 : ℝ) => B • y)^[m] (baseValue B b : AddCircle (1 : ℝ)) ∈
        Function.periodicPts (fun y : AddCircle (1 : ℝ) => B • y) := by
  rw [eventuallyPeriodic_iff_isOfFinAddOrder hB, isOfFinAddOrder_iff_preperiodic hB]

end DigitSequences

/-! ### Digits of a fraction, by long division -/

section LongDivision

variable {B p q : ℕ}

/-- The remainder `B^t p mod q` after `t` steps of the long division of `p` by `q` in base `B`. -/
def rem (B p q t : ℕ) : ℕ := B ^ t * p % q

theorem rem_lt (hq : 0 < q) (t : ℕ) : rem B p q t < q := Nat.mod_lt _ hq

/-- The next remainder: `r_(t+1) = B r_t mod q`. -/
theorem rem_succ (B p q t : ℕ) : rem B p q (t + 1) = B * rem B p q t % q := by
  simp only [rem]
  rw [pow_succ, mul_comm (B ^ t) B, mul_assoc, Nat.mul_mod B (B ^ t * p) q,
    Nat.mul_mod B (B ^ t * p % q) q, Nat.mod_mod]

/-- One step of long division: `⌊B^(t+1) p / q⌋ = B ⌊B^t p / q⌋ + ⌊B r_t / q⌋`. -/
theorem pow_succ_mul_div_eq (hq : 0 < q) (t : ℕ) :
    B ^ (t + 1) * p / q = B * (B ^ t * p / q) + B * rem B p q t / q := by
  have h := Nat.div_add_mod (B ^ t * p) q
  have e : B ^ (t + 1) * p = B * rem B p q t + q * (B * (B ^ t * p / q)) := by
    calc B ^ (t + 1) * p = B * (B ^ t * p) := by ring
      _ = B * (q * (B ^ t * p / q) + B ^ t * p % q) := by rw [h]
      _ = _ := by simp only [rem]; ring
  rw [e, Nat.add_mul_div_left _ _ hq]
  ring

/-- **The digits of `p / q`**: the base-`B` digit `⌊B^(t+1) p / q⌋ mod B` is `⌊B r_t / q⌋`. -/
theorem digit_eq (hB : 0 < B) (hq : 0 < q) (t : ℕ) :
    B ^ (t + 1) * p / q % B = B * rem B p q t / q := by
  have hr : B * rem B p q t / q < B := by
    rw [Nat.div_lt_iff_lt_mul hq]
    exact (Nat.mul_lt_mul_left hB).2 (rem_lt hq t)
  rw [pow_succ_mul_div_eq hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- **Long division is eventually periodic.** If `b t` says whether the `t`-th base-`B` digit of
`p / q` is `1`, then `b` is eventually periodic: the remainders take at most `q` values, and each
remainder determines the next one and the next digit. -/
theorem eventuallyPeriodic_of_digits (hB : 0 < B) (hq : 0 < q) {b : ℕ → Bool}
    (h : ∀ t, b t = decide (B ^ (t + 1) * p / q % B = 1)) : EventuallyPeriodic b := by
  have hb : ∀ t, b t = decide (B * rem B p q t / q = 1) := fun t => by rw [h, digit_eq hB hq]
  obtain ⟨i, j, hij, heq⟩ :=
    (Set.finite_Iio q).exists_lt_map_eq_of_forall_mem (f := rem B p q) (rem_lt hq)
  have key : ∀ k, rem B p q (i + k) = rem B p q (j + k) := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih => rw [← Nat.add_assoc, ← Nat.add_assoc, rem_succ, rem_succ, ih]
  exact ShiftOrbit.eventuallyPeriodic_of_shift_eq hij fun k => by rw [hb, hb, key]

/-- **Binary long division never ends in `1 1 1 …`.** If the binary digits of `p / q` were `1`
from time `T` on, the gaps `q - r_t` would double at every step, but they stay between `1`
and `q`. -/
theorem not_eventually_true_of_digits (hq : 0 < q) {b : ℕ → Bool}
    (h : ∀ t, b t = decide (2 ^ (t + 1) * p / q % 2 = 1)) :
    ¬ ∃ T, ∀ t, T ≤ t → b t = true := by
  have hb : ∀ t, b t = decide (2 * rem 2 p q t / q = 1) := fun t => by
    rw [h, digit_eq two_pos hq]
  rintro ⟨T, hT⟩
  have hge : ∀ t, T ≤ t → q ≤ 2 * rem 2 p q t := by
    intro t ht
    have h1 : 2 * rem 2 p q t / q = 1 := by
      have := hT t ht
      rw [hb] at this
      exact of_decide_eq_true this
    by_contra hlt
    rw [Nat.div_eq_of_lt (not_le.1 hlt)] at h1
    exact absurd h1 (by norm_num)
  have hstep : ∀ t, T ≤ t → q - rem 2 p q (t + 1) = 2 * (q - rem 2 p q t) := by
    intro t ht
    have h1 := hge t ht
    have h2 := rem_lt (B := 2) (p := p) hq t
    rw [rem_succ, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hpow : ∀ k, 2 ^ k ≤ q - rem 2 p q (T + k) := by
    intro k
    induction k with
    | zero =>
      have := rem_lt (B := 2) (p := p) hq T
      simp only [pow_zero, Nat.add_zero]
      omega
    | succ k ih =>
      rw [← Nat.add_assoc, hstep _ (by omega), pow_succ]
      omega
  have h1 := hpow q
  have h2 := rem_lt (B := 2) (p := p) hq (T + q)
  have h3 := @Nat.lt_two_pow_self q
  omega

/-- In base `B ≥ 3`, `0.b(0) b(1) … < 1` for every `b`. -/
theorem baseValue_lt_one_of_three_le (hB : 3 ≤ B) (b : ℕ → Bool) : baseValue B b < 1 := by
  have hB' : (3 : ℝ) ≤ B := by exact_mod_cast hB
  have h := Summable.tsum_lt_tsum_of_nonneg (i := 0) (term_nonneg (β := (B : ℝ)) (by linarith) b)
    (term_le_two (B := B) (by omega) b) ?_ (summable_geometric_two' 1)
  · rwa [tsum_geometric_two' 1] at h
  · rw [zero_add, pow_one, pow_zero, div_one]
    split_ifs
    · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    · rw [zero_div]
      norm_num

/-- **An eventually periodic sequence is the digit sequence of a fraction**, provided that every
tail value `0.b(t) b(t+1) …` is `< 1`: the fraction `p / q = 0.b(0) b(1) …` in base `B` has
`⌊B^(t+1) p / q⌋ mod B = b(t)` for every `t`. -/
theorem exists_digits_of_eventuallyPeriodic (hB : 2 ≤ B) {b : ℕ → Bool}
    (hb : EventuallyPeriodic b) (htail : ∀ t, baseValue B (tail b t) < 1) :
    ∃ p q : ℕ, 0 < q ∧ ∀ t, B ^ (t + 1) * p / q % B = if b t then 1 else 0 := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational (not_irrational_of_eventuallyPeriodic hB b hb)
  have hr0 : 0 ≤ r := by
    have := baseValue_nonneg hB b
    rw [hr] at this
    exact_mod_cast this
  refine ⟨r.num.toNat, r.den, r.pos, fun t => ?_⟩
  have hp : ((r.num.toNat : ℕ) : ℝ) = r.num := by
    have := Int.toNat_of_nonneg (Rat.num_nonneg.2 hr0)
    exact_mod_cast this
  have e := pow_mul_baseValue hB b (t + 1)
  have hlt := htail (t + 1)
  have hge := baseValue_nonneg hB (tail b (t + 1))
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hx : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
  have hdiv : B ^ (t + 1) * r.num.toNat / r.den = lead B b (t + 1) := by
    apply Nat.div_eq_of_lt_le
    · have : ((lead B b (t + 1) : ℕ) : ℝ) * r.den ≤ (B : ℝ) ^ (t + 1) * r.num.toNat := by
        rw [hp, ← hx, ← hr]
        nlinarith [mul_nonneg hge hq.le]
      exact_mod_cast this
    · have : (B : ℝ) ^ (t + 1) * r.num.toNat < (((lead B b (t + 1) : ℕ) : ℝ) + 1) * r.den := by
        rw [hp, ← hx, ← hr]
        nlinarith [mul_lt_mul_of_pos_right hlt hq]
      exact_mod_cast this
  rw [hdiv]
  simp only [lead]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt]
  split_ifs <;> omega

/-- `decide ((if x then 1 else 0) = 1) = x`. -/
theorem decide_ite_eq_one (x : Bool) : decide ((if x then 1 else 0 : ℕ) = 1) = x := by
  cases x <;> rfl

/-- **Binary digits of fractions**: `b(t) = decide (⌊2^(t+1) p / q⌋ mod 2 = 1)` for all `t`, for
some `p` and `q > 0`, iff `b` is eventually periodic and not eventually `true`. The second
condition excludes the expansions `… 0 1 1 1 …` of dyadic rationals, which long division never
produces. -/
theorem exists_digits_iff (b : ℕ → Bool) :
    (∃ p q : ℕ, 0 < q ∧ ∀ t, b t = decide (2 ^ (t + 1) * p / q % 2 = 1)) ↔
      EventuallyPeriodic b ∧ ¬ ∃ T, ∀ t, T ≤ t → b t = true := by
  constructor
  · rintro ⟨p, q, hq, h⟩
    exact ⟨eventuallyPeriodic_of_digits two_pos hq h, not_eventually_true_of_digits hq h⟩
  · rintro ⟨hb, h1⟩
    obtain ⟨p, q, hq, h⟩ := exists_digits_of_eventuallyPeriodic le_rfl hb (tail_lt_one le_rfl h1)
    exact ⟨p, q, hq, fun t => by rw [h t, decide_ite_eq_one]⟩

/-- **Base-`B` digits of fractions, `B ≥ 3`**: `⌊B^(t+1) p / q⌋ mod B = b(t)` for all `t`, for some
`p` and `q > 0`, iff `b` is eventually periodic. -/
theorem exists_digits_base_iff (hB : 3 ≤ B) (b : ℕ → Bool) :
    (∃ p q : ℕ, 0 < q ∧ ∀ t, B ^ (t + 1) * p / q % B = if b t then 1 else 0) ↔
      EventuallyPeriodic b := by
  constructor
  · rintro ⟨p, q, hq, h⟩
    exact eventuallyPeriodic_of_digits (B := B) (p := p) (by omega) hq fun t => by
      rw [h t, decide_ite_eq_one]
  · intro hb
    exact exists_digits_of_eventuallyPeriodic (by omega) hb fun t =>
      baseValue_lt_one_of_three_le hB _

end LongDivision

/-! ### Problem 1 -/

/-- The center column is not eventually `true` (`Rule30Prize.center_not_eventually_constant`). -/
theorem center_not_eventually_true : ¬ ∃ T, ∀ t, T ≤ t → c t = true := fun ⟨T, hT⟩ =>
  Rule30Prize.center_not_eventually_constant ⟨T, true, hT⟩

/-- The doubling map shifts the binary digits of `x₂`: its `n`-th iterate sends `x₂ mod 1` to
`0.c(n) c(n+1) …₂ mod 1`. -/
theorem iterate_doubling_centerBinary (n : ℕ) :
    (fun y : AddCircle (1 : ℝ) => 2 • y)^[n] (centerBinary : AddCircle (1 : ℝ)) =
      (baseValue 2 (tail c n) : AddCircle (1 : ℝ)) := by
  rw [centerBinary_eq_baseValue]
  exact iterate_nsmul_coe_baseValue le_rfl c n

/-- **Problem 1 as an infinite continued fraction**: the regular continued fraction of
`x₂ = 0.c(0) c(1) c(2) …₂` does not terminate. -/
theorem problem1_iff_cf_not_terminates :
    Rule30Prize.Problem1 ↔ ¬ (GenContFract.of centerBinary).Terminates :=
  problem1_iff_irrational_binary.trans (irrational_iff_not_terminates _)

/-- **Problem 1 via Dirichlet**: infinitely many rationals `q` satisfy `|x₂ - q| < 1 / den(q)²`. -/
theorem problem1_iff_dirichlet :
    Rule30Prize.Problem1 ↔ {q : ℚ | |centerBinary - q| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
  problem1_iff_irrational_binary.trans (irrational_iff_infinite_rat_approx _)

/-- **Problem 1 as `LiouvilleWith 2`**: for some `C`, infinitely many denominators `n` have a
numerator `m` with `x₂ ≠ m / n` and `|x₂ - m / n| < C / n²`. -/
theorem problem1_iff_liouvilleWith_two : Rule30Prize.Problem1 ↔ LiouvilleWith 2 centerBinary :=
  problem1_iff_irrational_binary.trans (irrational_iff_liouvilleWith_two _)

/-- The same for every exponent `1 < p ≤ 2`. -/
theorem problem1_iff_liouvilleWith {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    Rule30Prize.Problem1 ↔ LiouvilleWith p centerBinary :=
  problem1_iff_irrational_binary.trans (irrational_iff_liouvilleWith hp1 hp2 _)

/-- **Problem 1 on the circle**: `x₂` has infinite order in `ℝ/ℤ`. -/
theorem problem1_iff_infinite_order :
    Rule30Prize.Problem1 ↔ ¬ IsOfFinAddOrder (centerBinary : AddCircle (1 : ℝ)) :=
  problem1_iff_irrational_binary.trans (irrational_iff_not_isOfFinAddOrder _)

/-- The same with `addOrderOf`. -/
theorem problem1_iff_addOrderOf_eq_zero :
    Rule30Prize.Problem1 ↔ addOrderOf (centerBinary : AddCircle (1 : ℝ)) = 0 :=
  problem1_iff_irrational_binary.trans (irrational_iff_addOrderOf_eq_zero _)

/-- **Problem 1 as a dense rotation orbit**: the multiples `n x₂ mod 1`, `n : ℤ`, are dense in
`ℝ/ℤ`. -/
theorem problem1_iff_dense_multiples : Rule30Prize.Problem1 ↔
    DenseRange (· • (centerBinary : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) :=
  problem1_iff_irrational_binary.trans (irrational_iff_denseRange_zsmul _)

/-- **Problem 1 for the doubling map**: `x₂ mod 1` is not a preperiodic point of `y ↦ 2y` on
`ℝ/ℤ`. -/
theorem problem1_iff_doubling_not_preperiodic : Rule30Prize.Problem1 ↔
    ∀ m, (fun y : AddCircle (1 : ℝ) => 2 • y)^[m] (centerBinary : AddCircle (1 : ℝ)) ∉
      Function.periodicPts (fun y : AddCircle (1 : ℝ) => 2 • y) :=
  problem1_iff_irrational_binary.trans (irrational_iff_not_preperiodic_mul le_rfl _)

/-- **The doubling map shifts the digits of `x₂`**: `2^t x₂ mod 1` is the tail value
`0.c(t) c(t+1) …₂`, which is below `1` because `c` is not eventually black. -/
theorem fract_pow_mul_centerBinary (t : ℕ) :
    Int.fract (2 ^ t * centerBinary) = baseValue 2 (tail c t) := by
  have hpow := pow_mul_baseValue (B := 2) le_rfl c t
  have hlt := tail_lt_one (B := 2) le_rfl center_not_eventually_true t
  have hnn := baseValue_nonneg (B := 2) le_rfl (tail c t)
  rw [Nat.cast_ofNat] at hpow
  rw [centerBinary_eq_baseValue, hpow, add_comm, Int.fract_add_natCast,
    Int.fract_eq_self.2 ⟨hnn, hlt⟩]

/-- **The doubling map reads the center column**: `c(t)` is black iff `2^t x₂ mod 1` lies in the
upper half `(1/2, 1)` of the circle. -/
theorem center_iff_fract (t : ℕ) : c t = true ↔ 1 / 2 < Int.fract (2 ^ t * centerBinary) := by
  have hinf : ∀ T, ∃ s, T ≤ s ∧ c s = true := fun T => by
    obtain ⟨s, hs, hTs⟩ := WordForms.infinite_black.exists_gt T
    exact ⟨s, hTs.le, hs⟩
  have hd := digit_iff (B := 2) le_rfl c hinf t
  rw [Nat.cast_ofNat] at hd
  rw [fract_pow_mul_centerBinary, hd]
  constructor <;> intro h <;> linarith

open Filter Topology in
/-- **Problem 2 for the doubling map**: Problem 2 holds iff the orbit of `x₂` under the doubling
map `y ↦ 2y mod 1` lies in the upper half `(1/2, 1)` of the circle with frequency `1/2`. -/
theorem problem2_iff_doubling : Rule30Prize.Problem2 ↔
    Tendsto (fun n : ℕ => (((Finset.range n).filter fun t =>
      1 / 2 < Int.fract (2 ^ t * centerBinary)).card : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  rw [ProblemTwo.problem2_iff_tendsto]
  refine tendsto_congr fun n => ?_
  congr 2
  rw [show Rule30Prize.blackCount n = ((List.range n).filter c).length from rfl,
    BlackTimes.length_filter_eq_count, Nat.count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr fun t _ => center_iff_fract t)

/-! ### Normality and the doubling map -/

/-- A binary numeral of `m` digits is below `2^m`. -/
theorem lead_lt (b : ℕ → Bool) : ∀ m, lead 2 b m < 2 ^ m
  | 0 => by simp [lead]
  | m + 1 => by
    have := lead_lt b m
    simp only [lead, pow_succ]
    split_ifs <;> omega

/-- A binary numeral depends only on its digits. -/
theorem lead_congr {b b' : ℕ → Bool} : ∀ {m}, (∀ j < m, b j = b' j) → lead 2 b m = lead 2 b' m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lead]
    rw [lead_congr fun j hj => h j (by omega), h m (by omega)]

/-- A binary numeral determines its digits. -/
theorem eq_of_lead_eq {b b' : ℕ → Bool} :
    ∀ {m}, lead 2 b m = lead 2 b' m → ∀ j < m, b j = b' j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, h, j, hj => by
    simp only [lead] at h
    have hd : b m = b' m := by
      cases hb : b m <;> cases hb' : b' m
      · rfl
      · rw [hb, hb'] at h
        simp only [Bool.false_eq_true, ite_false, ite_true, add_zero] at h
        omega
      · rw [hb, hb'] at h
        simp only [Bool.false_eq_true, ite_false, ite_true, add_zero] at h
        omega
      · rfl
    rw [hd] at h
    have hl : lead 2 b m = lead 2 b' m := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact eq_of_lead_eq hl j hj
    · exact hd

/-- The binary numeral `w(0) … w(m-1)` of a word. -/
def num {m : ℕ} (w : Fin m → Bool) : ℕ :=
  lead 2 (fun j => if h : j < m then w ⟨j, h⟩ else false) m

theorem num_injective (m : ℕ) : Function.Injective (num (m := m)) := fun w w' h => by
  funext j
  have := eq_of_lead_eq h j.1 j.2
  simpa [j.2] using this

/-- **Words of `c` are dyadic intervals of the doubling orbit**: the word `w` occurs in `c` at `t`
iff `2^t x₂ mod 1` lies in the dyadic interval `[num w / 2^m, (num w + 1) / 2^m)`. -/
theorem occurs_iff_fract (t : ℕ) {m : ℕ} (w : Fin m → Bool) :
    (∀ j : Fin m, c (t + j) = w j) ↔
      Int.fract (2 ^ t * centerBinary) ∈ Set.Ico ((num w : ℝ) / 2 ^ m) ((num w + 1) / 2 ^ m) := by
  rw [fract_pow_mul_centerBinary]
  have hpow := pow_mul_baseValue (B := 2) le_rfl (tail c t) m
  have htt : tail (tail c t) m = tail c (t + m) := funext fun s => by
    simp only [tail]
    congr 1
    ring
  have hlt := tail_lt_one (B := 2) le_rfl center_not_eventually_true (t + m)
  have hnn := baseValue_nonneg (B := 2) le_rfl (tail c (t + m))
  rw [htt, Nat.cast_ofNat] at hpow
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  rw [Set.mem_Ico, div_le_iff₀ h2m, lt_div_iff₀ h2m, mul_comm, hpow]
  -- both sides say that the numeral of the next `m` digits is `num w`
  have hword : (∀ j : Fin m, c (t + j) = w j) ↔ lead 2 (tail c t) m = num w := by
    constructor
    · intro h
      exact lead_congr fun j hj => by
        simp only [tail, dite_eq_left hj]
        rw [add_comm]
        exact h ⟨j, hj⟩
    · intro h j
      have := eq_of_lead_eq h j.1 j.2
      simp only [tail, dite_eq_left j.2] at this
      rw [add_comm]
      exact this
  rw [hword]
  constructor
  · intro h
    constructor <;> rw [h] <;> linarith
  · rintro ⟨h1, h2⟩
    have h1' : (num w : ℝ) < ((lead 2 (tail c t) m : ℕ) : ℝ) + 1 := by linarith
    have h2' : ((lead 2 (tail c t) m : ℕ) : ℝ) < num w + 1 := by linarith
    have h1'' : num w < lead 2 (tail c t) m + 1 := by exact_mod_cast h1'
    have h2'' : lead 2 (tail c t) m < num w + 1 := by exact_mod_cast h2'
    omega

open Filter Topology in
/-- **Normality and the doubling map** (Borel, Wall): the center column is normal iff the orbit of
`x₂` under the doubling map visits every dyadic interval `[k/2^m, (k+1)/2^m)` with frequency
`2^-m`. -/
theorem isNormal_iff_doubling : StrongerStatements.IsNormal c ↔
    ∀ m k : ℕ, k < 2 ^ m → Tendsto (fun N : ℕ => (((Finset.range N).filter fun t =>
      Int.fract (2 ^ t * centerBinary) ∈ Set.Ico ((k : ℝ) / 2 ^ m) ((k + 1) / 2 ^ m)).card : ℝ) /
        N) atTop (𝓝 ((2 : ℝ)⁻¹ ^ m)) := by
  have hcount : ∀ {m : ℕ} (w : Fin m → Bool) (N : ℕ),
      ((Finset.range N).filter fun t => ∀ j : Fin m, c (t + j) = w j) =
        (Finset.range N).filter fun t => Int.fract (2 ^ t * centerBinary) ∈
          Set.Ico ((num w : ℝ) / 2 ^ m) ((num w + 1) / 2 ^ m) := fun w N =>
    Finset.filter_congr fun t _ => occurs_iff_fract t w
  constructor
  · intro h m k hk
    -- every `k < 2^m` is the numeral of a word
    let f : (Fin m → Bool) → Fin (2 ^ m) := fun w => ⟨num w, lead_lt _ m⟩
    have hf : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2
      ⟨fun w w' hww => num_injective m (congrArg Fin.val hww), by simp⟩
    obtain ⟨w, hw⟩ := hf.2 ⟨k, hk⟩
    have hwk : num w = k := congrArg Fin.val hw
    have := h m w
    simp only [hcount, hwk] at this
    exact this
  · intro h m w
    have := h m (num w) (lead_lt _ m)
    simp only [hcount]
    exact this

/-- **Problem 1 without real numbers**: the center column is not the sequence of binary digits
`⌊2^(t+1) p / q⌋ mod 2` of a fraction `p / q`. -/
theorem problem1_iff_not_rational_digits : Rule30Prize.Problem1 ↔
    ¬ ∃ p q : ℕ, 0 < q ∧ ∀ t, c t = decide (2 ^ (t + 1) * p / q % 2 = 1) := by
  rw [exists_digits_iff, problem1_iff_not_eventuallyPeriodic]
  simp only [center_not_eventually_true, not_false_eq_true, and_true]

/-- **Problem 1 without real numbers, in base `B ≥ 2`**: there is no fraction `p / q` whose
base-`B` digits `⌊B^(t+1) p / q⌋ mod B` are `c(0), c(1), c(2), …` (as `0`/`1`). -/
theorem problem1_iff_not_rational_digits_base {B : ℕ} (hB : 2 ≤ B) : Rule30Prize.Problem1 ↔
    ¬ ∃ p q : ℕ, 0 < q ∧ ∀ t, B ^ (t + 1) * p / q % B = if c t then 1 else 0 := by
  rw [problem1_iff_not_eventuallyPeriodic]
  constructor
  · rintro hc ⟨p, q, hq, h⟩
    exact hc (eventuallyPeriodic_of_digits (B := B) (p := p) (by omega) hq fun t => by
      rw [h t, decide_ite_eq_one])
  · intro h hc
    exact h (exists_digits_of_eventuallyPeriodic hB hc (tail_lt_one hB center_not_eventually_true))

/-- **Problem 1 without real numbers, in decimal**: no fraction `p / q` has the decimal digits
`c(0), c(1), c(2), …`. -/
theorem problem1_iff_not_rational_decimal_digits : Rule30Prize.Problem1 ↔
    ¬ ∃ p q : ℕ, 0 < q ∧ ∀ t, 10 ^ (t + 1) * p / q % 10 = if c t then 1 else 0 :=
  problem1_iff_not_rational_digits_base (by norm_num)

end Rule30Equivalents.NumberTheory
