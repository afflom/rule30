module

public import Rule30Equivalents.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Multiplicity

/-!
# Problem 1 as the irrationality of a 2-adic number

Read the center column `c(0), c(1), c(2), …` of rule 30 as the digits of a 2-adic integer, lowest
digit first: `α₂ = ∑ₜ c(t) 2ᵗ ∈ ℤ₂` (with `true = 1`, `false = 0`). **Problem 1 holds iff `α₂` is
not a rational number.** The same holds for the `p`-adic integer `∑ₜ c(t) pᵗ`, for every prime
`p`, and it can be said with integers alone, for every base `p ≥ 2`.

## Statements

Write `S(n) = ∑_{t<n} x(t) pᵗ` for the first `n` digits of a bit sequence `x` read in base `p`,
lowest digit first (`partialSum p x n`; for the center column, `S p n`). A fraction `a / b` with
`b ≠ 0` *matches* the first `n` digits if `pⁿ ∣ b · S(n) - a`.

* `eventuallyPeriodic_iff_exists_pow_dvd`: for every `x : ℕ → Bool` and every natural `p ≥ 2`,
  `x` is eventually periodic iff some fraction matches all prefixes:
  `∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a`. The denominator can be taken
  not divisible by `p` (`eventuallyPeriodic_iff_exists_pow_dvd_not_dvd`).
* `problem1_iff_no_pow_dvd` (any `p ≥ 2`) and `problem1_iff_padic_int` (`p` prime):
  `Problem1 ↔ ¬ ∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * S p n - a`.
  `problem1_iff_no_odd_fraction`: the same for `p = 2` with `b` odd, i.e. `c` is not the 2-adic
  expansion of any fraction with odd denominator.
* `eventuallyPeriodic_iff_fcsr`: `x` is eventually periodic iff some feedback-with-carry shift
  register (FCSR) generates it (`FCSRGenerates r g M x`: `r` cells, taps `g`, integer memory `M`).
  So `problem1_iff_no_fcsr`: no FCSR generates the center column. Klapper and Goresky prove the
  same equivalence through 2-adic numbers: FCSR outputs are the 2-adic expansions of the fractions
  whose denominator is the connection integer.
* `eventuallyPeriodic_iff_exists_rat`: for every prime `p` and every `x`, `x` is eventually periodic
  iff the `p`-adic integer `padicValue p x = ∑' t, x(t) pᵗ ∈ ℤ_[p]` is rational in `ℚ_[p]`. So
  `problem1_iff_padicValue_irrational`: `Problem1 ↔ ∀ q : ℚ, (padicValue p c : ℚ_[p]) ≠ q`, and for
  `p = 2`, `problem1_iff_padic_irrational`: `Problem1 ↔ ∀ q : ℚ, (α₂ : ℚ_[2]) ≠ q`, where
  `α₂ = ∑' t, (if c t then 1 else 0) * 2 ^ t`.
* `eventuallyPeriodic_iff_bounded_height`: `x` is eventually periodic iff one height bound `B`
  serves every prefix: for each `n` a fraction `a / b` with `b ≠ 0`, `|a| ≤ B` and `|b| ≤ B`
  matches the first `n` digits (also with `p ∤ b`: `eventuallyPeriodic_iff_bounded_height_not_dvd`).
  So `problem1_iff_padic_complexity` and, for `p = 2`, `problem1_iff_two_adic_complexity`:
  `Problem1 ↔ ∀ B : ℕ, ∃ n, ¬ ∃ a b : ℤ, b ≠ 0 ∧ |a| ≤ B ∧ |b| ≤ B ∧ (2 : ℤ) ^ n ∣ b * S 2 n - a`.
  With `b` odd (`problem1_iff_two_adic_complexity_odd`) this says exactly that the 2-adic
  complexity profile of the center column in Klapper and Goresky's sense is unbounded. Their
  2-adic complexity of a prefix of length `n` is `log₂` of the least `max(|a|, |b|)` over the
  fractions `a / b`, `b` odd, whose 2-adic expansion starts with that prefix.

## Proof

* (→) If `x(t + P) = x(t)` for `t ≥ T`, with `P > 0`, let `S'` be the partial sums of the purely
  periodic tail `y(t) = x(T + t)`. Then `S'(P + k) = S'(P) + pᴾ · S'(k)`, so
  `pᵏ ∣ (pᴾ - 1) · S'(k) + S'(P)` for every `k` (`pow_dvd_of_periodic`): the geometric series
  `∑ y(t) pᵗ = -S'(P) / (pᴾ - 1)`, read modulo `pᵏ`. With `b = pᴾ - 1` and
  `a = b · S(T) - pᵀ · S'(P)`, this gives `p^(T+k) ∣ b · S(T + k) - a`. The congruences *descend*
  (`pow_dvd_of_le`): a fraction that matches `n` digits matches every shorter prefix. And
  `p ∤ pᴾ - 1` because `P > 0` and `p ≥ 2`.
* (←) First divide out the power of `p` in `b`: if `b = pᵏ b'` with `p ∤ b'`, then `pᵏ ∣ a`, and
  `a / pᵏ` over `b'` still matches every prefix (`exists_not_dvd_of_pow_dvd`). Now let `p ∤ b`. The
  remainders `rₙ = (a - b · S(n)) / pⁿ` are integers with `rₙ = p · rₙ₊₁ + b · x(n)`. So
  `2 |rₙ₊₁| ≤ |rₙ| + |b|`, and from some point on `|rₙ| ≤ |b|`. Since `p ∤ b`, `x(n) = 1` iff
  `p ∣ rₙ - b`: the remainder `rₙ` determines the digit `x(n)` and the next remainder `rₙ₊₁`. By
  pigeonhole `rᵢ = rⱼ` for some `i < j` in the bounded range, and then `x` has period `j - i` from
  `i` on (`eventuallyPeriodic_of_pow_dvd`).
* `p`-adic form. Splitting off `n` digits, `α = S(n) + pⁿ α'` in `ℤ_[p]` (`padicValue_eq_add`).
  So `b · α = a` iff `pⁿ ∣ b · S(n) - a` in `ℤ_[p]` for every `n`, because an element of `ℤ_[p]`
  divisible by every `pⁿ` is `0`. For integers, divisibility by `pⁿ` in `ℤ_[p]` is divisibility
  in `ℤ` (`PadicInt.pow_p_dvd_int_iff`). Finally `α = a / b` in `ℚ_[p]` iff `b · α = a`.
* Complexity. There are finitely many pairs of height at most `B`. If every prefix is matched by
  one of them, then, since the congruences descend, a single pair matches every prefix: otherwise
  each pair fails at some length, and the pair matching the longest of these lengths fails there.
* FCSRs. An eventually periodic sequence is generated with memory `0` and a single tap
  (`fcsr_of_eventuallyPeriodic`). Conversely the feedback sum lies in `[0, r]`, so
  `2 |M (n + 1)| ≤ |M n| + r + 1` and the memory ends up in `[-(r + 1), r + 1]`. Then the register
  has finitely many states (cells, memory), each state determines the next bit and the next
  state, and by pigeonhole a state repeats (`eventuallyPeriodic_of_fcsr`).

## Special cases

* No double expansions: the `p`-adic expansion is unique. In `ℝ`, `0.0111…₂ = 0.1000…₂`; in `ℤ₂`,
  `0 + 2 + 4 + ⋯ = -2` and `1 + 0 + 0 + ⋯ = 1` are different. So, unlike the binary real number of
  `BinaryIrrational`, no case split on eventually constant sequences is needed; they are covered
  (`1, 1, 1, …` is `-1/(p-1)`). The general theorems hold for every bit sequence, so
  `Rule30Prize.center_not_eventually_constant` is not used.
* `p ≥ 2` is needed. For `p = 1` every congruence `1ⁿ ∣ …` holds. For `p = 0` the congruences say
  only `b · x(0) = a`. In both cases the right-hand side holds for every sequence.
* `P > 0` (as in `EventuallyPeriodic`) is what makes `b = pᴾ - 1` nonzero; with `P = 0` allowed,
  every sequence would count as eventually periodic.

## Sources

* The classical theorem that a `p`-adic number is rational iff its `p`-adic expansion is
  eventually periodic: K. Conrad, *The p-adic expansion of rational numbers*, expository note
  (kconrad.math.uconn.edu/blurbs/gradnumthy/rationalsinQp.pdf), Theorem 3.1. For `ℤ_p`, `ℚ_p` and
  `p`-adic expansions in general: F. Q. Gouvêa, *p-adic Numbers: An Introduction*, 2nd ed.,
  Universitext, Springer, 1997 (cited as a general reference; we did not check which section
  treats periodic expansions).
* A. Klapper and M. Goresky, *Feedback shift registers, 2-adic span, and combiners with memory*,
  J. Cryptology 10 (1997) 111–147. Numbering as in the preprint on Klapper's web page: Theorem 2.1
  (the rationals with odd denominator are exactly the 2-adic numbers with eventually periodic bit
  sequences), Definition 3.1 (the FCSR), Proposition 3.2 (the memory enters a bounded range),
  Theorem 4.1 and Corollary 4.2 (FCSR outputs are the 2-adic expansions of `p / q`, `q` the
  connection integer, and every eventually periodic sequence is one), §9 "Complexity Profile" (the
  2-adic complexity of a finite sequence), §10 (the rational approximation algorithm, the 2-adic
  analogue of Berlekamp–Massey).
-/

@[expose] public section

namespace Rule30Equivalents.TwoAdic

open Ruliology.CellularAutomata
open Finset

/-! ### Partial sums -/

/-- `partialSum p x n = ∑_{t < n} x(t) pᵗ` (with `true = 1`, `false = 0`): the first `n` digits of
`x` read in base `p`, lowest digit first. -/
def partialSum (p : ℕ) (x : ℕ → Bool) (n : ℕ) : ℤ :=
  ∑ t ∈ range n, (if x t then 1 else 0) * (p : ℤ) ^ t

theorem partialSum_succ (p : ℕ) (x : ℕ → Bool) (n : ℕ) :
    partialSum p x (n + 1) = partialSum p x n + (if x n then 1 else 0) * (p : ℤ) ^ n := by
  unfold partialSum
  rw [sum_range_succ]

/-- Splitting the digits at position `m`: `S(m + k) = S(m) + pᵐ · S'(k)`, where `S'` are the
partial sums of the tail `x(m), x(m + 1), …`. -/
theorem partialSum_add (p : ℕ) (x : ℕ → Bool) (m k : ℕ) :
    partialSum p x (m + k) =
      partialSum p x m + (p : ℤ) ^ m * partialSum p (fun t => x (m + t)) k := by
  simp only [partialSum]
  rw [sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [pow_add]
  ring

/-- The digits from position `m` on change the partial sums only by multiples of `pᵐ`. -/
theorem pow_dvd_partialSum_sub (p : ℕ) (x : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    (p : ℤ) ^ m ∣ partialSum p x n - partialSum p x m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [partialSum_add, add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- A congruence modulo `pᵐ` only sees the first `m` digits: if `pᵐ ∣ b · S(n) - a` with
`m ≤ n`, then `pᵐ ∣ b · S(m) - a`. -/
theorem pow_dvd_of_le_of_pow_dvd {p : ℕ} {x : ℕ → Bool} {a b : ℤ} {m n : ℕ}
    (h : (p : ℤ) ^ m ∣ b * partialSum p x n - a) (hmn : m ≤ n) :
    (p : ℤ) ^ m ∣ b * partialSum p x m - a := by
  have e : b * partialSum p x m - a =
      (b * partialSum p x n - a) - b * (partialSum p x n - partialSum p x m) := by ring
  rw [e]
  exact dvd_sub h (dvd_mul_of_dvd_right (pow_dvd_partialSum_sub p x hmn) b)

/-- **The congruences descend**: a fraction `a / b` that matches the first `n` digits matches
every shorter prefix. -/
theorem pow_dvd_of_le {p : ℕ} {x : ℕ → Bool} {a b : ℤ} {m n : ℕ}
    (h : (p : ℤ) ^ n ∣ b * partialSum p x n - a) (hmn : m ≤ n) :
    (p : ℤ) ^ m ∣ b * partialSum p x m - a :=
  pow_dvd_of_le_of_pow_dvd ((pow_dvd_pow _ hmn).trans h) hmn

/-! ### Eventually periodic ⇒ one fraction matches every prefix -/

/-- A purely periodic sequence `y` with period `P`: `pᵏ ∣ (pᴾ - 1) · S(k) + S(P)` for every `k`.
This is the geometric series `∑ y(t) pᵗ = -S(P) / (pᴾ - 1)`, read modulo `pᵏ`. -/
theorem pow_dvd_of_periodic (p : ℕ) {y : ℕ → Bool} {P : ℕ} (hy : ∀ t, y (P + t) = y t)
    (k : ℕ) : (p : ℤ) ^ k ∣ ((p : ℤ) ^ P - 1) * partialSum p y k + partialSum p y P := by
  have e := partialSum_add p y P k
  rw [show (fun t => y (P + t)) = y from funext hy] at e
  have h := pow_dvd_partialSum_sub p y (show k ≤ P + k by omega)
  rw [e] at h
  have e2 : partialSum p y P + (p : ℤ) ^ P * partialSum p y k - partialSum p y k =
      ((p : ℤ) ^ P - 1) * partialSum p y k + partialSum p y P := by ring
  rwa [e2] at h

/-- (→) If `x` has transient `T` and period `P > 0`, the fraction `a / b` with `b = pᴾ - 1` and
`a = b · S(T) - pᵀ · S'(P)`, where `S'` are the partial sums of the periodic tail, matches every
prefix. Its denominator is not divisible by `p`. -/
theorem exists_pow_dvd_of_eventuallyPeriodic {p : ℕ} (hp : 2 ≤ p) {x : ℕ → Bool}
    (h : EventuallyPeriodic x) :
    ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hy : ∀ t, x (T + (P + t)) = x (T + t) := fun t => by
    rw [show T + (P + t) = T + t + P by omega]
    exact hper (T + t) (by omega)
  refine ⟨((p : ℤ) ^ P - 1) * partialSum p x T -
      (p : ℤ) ^ T * partialSum p (fun t => x (T + t)) P, (p : ℤ) ^ P - 1, ?_, fun n => ?_⟩
  · intro hdvd
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_pow_self (p : ℤ) hP.ne') hdvd
      rwa [sub_sub_cancel] at this
    have := Int.le_of_dvd one_pos h1
    omega
  · have hd := pow_dvd_of_periodic p (y := fun t => x (T + t)) (P := P) hy n
    have e := partialSum_add p x T n
    have hTn : (p : ℤ) ^ (T + n) ∣ ((p : ℤ) ^ P - 1) * partialSum p x (T + n) -
        (((p : ℤ) ^ P - 1) * partialSum p x T -
          (p : ℤ) ^ T * partialSum p (fun t => x (T + t)) P) := by
      rw [e, pow_add]
      have e2 : ((p : ℤ) ^ P - 1) * (partialSum p x T +
            (p : ℤ) ^ T * partialSum p (fun t => x (T + t)) n) -
          (((p : ℤ) ^ P - 1) * partialSum p x T -
            (p : ℤ) ^ T * partialSum p (fun t => x (T + t)) P) =
          (p : ℤ) ^ T * (((p : ℤ) ^ P - 1) * partialSum p (fun t => x (T + t)) n +
            partialSum p (fun t => x (T + t)) P) := by ring
      rw [e2]
      exact mul_dvd_mul_left _ hd
    exact pow_dvd_of_le hTn (by omega)

/-! ### One fraction matches every prefix ⇒ eventually periodic -/

/-- `|u - v · e| ≤ |u| + |v|` for a digit `e ∈ {0, 1}`. -/
theorem abs_sub_mul_ite_le (u v : ℤ) (e : Bool) :
    |u - v * (if e then 1 else 0)| ≤ |u| + |v| := by
  cases e
  · rw [ite_eq_right Bool.false_ne_true, mul_zero, sub_zero]
    exact le_add_of_nonneg_right (abs_nonneg v)
  · rw [ite_eq_left rfl, mul_one, sub_eq_add_neg]
    calc |u + -v| ≤ |u| + |-v| := abs_add_le _ _
      _ = |u| + |v| := by rw [abs_neg]

/-- (←) If `p ∤ b` and the fraction `a / b` matches every prefix of `x`, then `x` is eventually
periodic. The remainders `rₙ = (a - b · S(n)) / pⁿ` satisfy `rₙ = p · rₙ₊₁ + b · x(n)`; they
shrink until `|rₙ| ≤ |b|`, and since `p ∤ b` each `rₙ` determines `x(n)` and `rₙ₊₁`. -/
theorem eventuallyPeriodic_of_pow_dvd {p : ℕ} (hp : 2 ≤ p) {x : ℕ → Bool} {a b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (h : ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a) :
    EventuallyPeriodic x := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  -- The remainders `rₙ = (a - b · S(n)) / pⁿ`.
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℤ, ∀ n, r n * (p : ℤ) ^ n = a - b * partialSum p x n :=
    ⟨fun n => (a - b * partialSum p x n) / (p : ℤ) ^ n, fun n =>
      Int.ediv_mul_cancel (by rw [← neg_sub]; exact dvd_neg.2 (h n))⟩
  -- `rₙ = p · rₙ₊₁ + b · x(n)`.
  have hrec : ∀ n, r n = (p : ℤ) * r (n + 1) + b * (if x n then 1 else 0) := by
    intro n
    have h1 := hr n
    have h2 := hr (n + 1)
    rw [partialSum_succ, pow_succ] at h2
    have h3 : (p : ℤ) ^ n * (r n - ((p : ℤ) * r (n + 1) + b * (if x n then 1 else 0))) = 0 := by
      linear_combination h1 - h2
    have := (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hp0)
    linarith
  -- The remainders shrink: `2 |rₙ₊₁| ≤ |rₙ| + |b|`.
  have hstep : ∀ n, 2 * |r (n + 1)| ≤ |r n| + |b| := by
    intro n
    have e : (p : ℤ) * r (n + 1) = r n - b * (if x n then 1 else 0) := by linarith [hrec n]
    have h1 : |(p : ℤ) * r (n + 1)| ≤ |r n| + |b| := by
      rw [e]
      exact abs_sub_mul_ite_le _ _ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p)] at h1
    nlinarith [abs_nonneg (r (n + 1))]
  -- So `|rₙ| ≤ |b|` from some point on.
  have hbound : ∀ n, |r n| ≤ |b| ∨ |r n| + n ≤ |r 0| := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      have h1 := hstep n
      have h2 := abs_nonneg (r (n + 1))
      have h3 := abs_nonneg b
      push_cast
      omega
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n, N ≤ n → r n ∈ Set.Icc (-|b|) |b| := by
    refine ⟨(r 0).natAbs + 1, fun n hn => Set.mem_Icc.2 (abs_le.1 ?_)⟩
    have h1 := hbound n
    have h2 : ((r 0).natAbs : ℤ) = |r 0| := Int.natCast_natAbs (r 0)
    have h3 : ((r 0).natAbs : ℤ) + 1 ≤ n := by exact_mod_cast hn
    have h4 := abs_nonneg (r n)
    omega
  -- Pigeonhole: two remainders in the bounded range coincide.
  obtain ⟨i, j, hij, hrij⟩ := (Set.finite_Icc (-|b|) |b|).exists_lt_map_eq_of_forall_mem
    (f := fun k => r (N + k)) (fun k => hN (N + k) (by omega))
  -- Since `p ∤ b`, the remainder `rₙ` determines the digit `x(n)`.
  have hdig : ∀ n, x n = true ↔ (p : ℤ) ∣ r n - b := by
    intro n
    have e := hrec n
    cases hxn : x n
    · rw [hxn, ite_eq_right Bool.false_ne_true, mul_zero, add_zero] at e
      simp only [Bool.false_eq_true, false_iff]
      intro hd
      apply hb
      have := dvd_sub (⟨r (n + 1), e⟩ : (p : ℤ) ∣ r n) hd
      rwa [sub_sub_cancel] at this
    · rw [hxn, ite_eq_left rfl, mul_one] at e
      simp only [true_iff]
      exact ⟨r (n + 1), by linarith⟩
  -- So the remainders, and with them the digits, repeat from `N + i` on with period `j - i`.
  have hk : ∀ k, r (N + i + k) = r (N + j + k) := by
    intro k
    induction k with
    | zero => simpa using hrij
    | succ k ih =>
      have hx : x (N + i + k) = x (N + j + k) := by
        rw [Bool.eq_iff_iff, hdig, hdig, ih]
      have e1 := hrec (N + i + k)
      have e2 := hrec (N + j + k)
      rw [hx, ih] at e1
      show r (N + i + k + 1) = r (N + j + k + 1)
      exact mul_left_cancel₀ hp0 (by linear_combination e2 - e1)
  refine ⟨N + i, j - i, by omega, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [show N + i + k + (j - i) = N + j + k by omega, Bool.eq_iff_iff, hdig, hdig, hk k]

/-- Dividing out the power of `p` in `b`: if `b ≠ 0` and `a / b` matches every prefix, then so
does a fraction `a' / b'` with `p ∤ b'`. -/
theorem exists_not_dvd_of_pow_dvd {p : ℕ} (hp : 2 ≤ p) {x : ℕ → Bool} {a b : ℤ} (hb : b ≠ 0)
    (h : ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a) :
    ∃ a' b' : ℤ, ¬ (p : ℤ) ∣ b' ∧ ∀ n, (p : ℤ) ^ n ∣ b' * partialSum p x n - a' := by
  have hfin : FiniteMultiplicity (p : ℤ) b :=
    Int.finiteMultiplicity_iff.mpr ⟨by rw [Int.natAbs_natCast]; omega, hb⟩
  obtain ⟨b', hbb', hb'⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  generalize multiplicity (p : ℤ) b = k at hbb'
  subst hbb'
  have hka : (p : ℤ) ^ k ∣ a := by
    have := dvd_sub (dvd_mul_of_dvd_left (dvd_mul_right ((p : ℤ) ^ k) b') (partialSum p x k))
      (h k)
    rwa [sub_sub_cancel] at this
  obtain ⟨a', rfl⟩ := hka
  have hpk : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show p ≠ 0 by omega))
  refine ⟨a', b', hb', fun n => pow_dvd_of_le_of_pow_dvd (n := k + n) ?_ (by omega)⟩
  have h1 := h (k + n)
  rw [pow_add, show (p : ℤ) ^ k * b' * partialSum p x (k + n) - (p : ℤ) ^ k * a' =
    (p : ℤ) ^ k * (b' * partialSum p x (k + n) - a') by ring] at h1
  exact (mul_dvd_mul_iff_left hpk).mp h1

/-! ### The equivalences for an arbitrary bit sequence -/

/-- **Eventually periodic iff one fraction matches every prefix.** For every base `p ≥ 2`, a bit
sequence `x` is eventually periodic iff there are integers `a` and `b ≠ 0` with
`pⁿ ∣ b · S(n) - a` for every `n`, where `S(n) = ∑_{t<n} x(t) pᵗ`. In `p`-adic language: the
`p`-adic integer `∑ x(t) pᵗ` equals the fraction `a / b`. -/
theorem eventuallyPeriodic_iff_exists_pow_dvd {p : ℕ} (hp : 2 ≤ p) (x : ℕ → Bool) :
    EventuallyPeriodic x ↔ ∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := exists_pow_dvd_of_eventuallyPeriodic hp h
    exact ⟨a, b, fun h0 => hb (by rw [h0]; exact dvd_zero _), hab⟩
  · rintro ⟨a, b, hb, hab⟩
    obtain ⟨a', b', hb', hab'⟩ := exists_not_dvd_of_pow_dvd hp hb hab
    exact eventuallyPeriodic_of_pow_dvd hp hb' hab'

/-- The same with a denominator not divisible by `p`. -/
theorem eventuallyPeriodic_iff_exists_pow_dvd_not_dvd {p : ℕ} (hp : 2 ≤ p) (x : ℕ → Bool) :
    EventuallyPeriodic x ↔
      ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a :=
  ⟨exists_pow_dvd_of_eventuallyPeriodic hp,
    fun ⟨_, _, hb, hab⟩ => eventuallyPeriodic_of_pow_dvd hp hb hab⟩

/-- **Bounded `p`-adic complexity.** For every base `p ≥ 2`, `x` is eventually periodic iff one
height bound `B` serves every prefix: for each `n` some fraction `a / b` with `b ≠ 0`, `|a| ≤ B`
and `|b| ≤ B` matches the first `n` digits. -/
theorem eventuallyPeriodic_iff_bounded_height {p : ℕ} (hp : 2 ≤ p) (x : ℕ → Bool) :
    EventuallyPeriodic x ↔ ∃ B : ℕ, ∀ n, ∃ a b : ℤ, b ≠ 0 ∧ |a| ≤ B ∧ |b| ≤ B ∧
      (p : ℤ) ^ n ∣ b * partialSum p x n - a := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := (eventuallyPeriodic_iff_exists_pow_dvd hp x).1 h
    refine ⟨max a.natAbs b.natAbs, fun n => ⟨a, b, hb, ?_, ?_, hab n⟩⟩
    · rw [← Int.natCast_natAbs]
      exact_mod_cast le_max_left _ _
    · rw [← Int.natCast_natAbs]
      exact_mod_cast le_max_right _ _
  · rintro ⟨B, hB⟩
    rw [eventuallyPeriodic_iff_exists_pow_dvd hp]
    by_contra hne
    -- Each pair of integers fails at some length.
    have hbad : ∀ z : ℤ × ℤ, ∃ n, z.2 ≠ 0 → ¬ (p : ℤ) ^ n ∣ z.2 * partialSum p x n - z.1 := by
      intro z
      by_contra hall
      push Not at hall
      exact hne ⟨z.1, z.2, (hall 0).1, fun n => (hall n).2⟩
    choose bad hbad using hbad
    -- The pair of height `≤ B` that matches the longest of these lengths fails there.
    obtain ⟨a, b, hb, ha, hb', hdvd⟩ :=
      hB ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).sup bad)
    have hmem : (a, b) ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B :=
      Finset.mem_product.2 ⟨Finset.mem_Icc.2 (abs_le.1 ha), Finset.mem_Icc.2 (abs_le.1 hb')⟩
    exact hbad (a, b) hb (pow_dvd_of_le hdvd (Finset.le_sup hmem))

/-- The same with the denominator not divisible by `p`; for `p = 2` this asks for an odd
denominator, as in Klapper and Goresky's 2-adic complexity. -/
theorem eventuallyPeriodic_iff_bounded_height_not_dvd {p : ℕ} (hp : 2 ≤ p) (x : ℕ → Bool) :
    EventuallyPeriodic x ↔ ∃ B : ℕ, ∀ n, ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ |a| ≤ B ∧ |b| ≤ B ∧
      (p : ℤ) ^ n ∣ b * partialSum p x n - a := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := exists_pow_dvd_of_eventuallyPeriodic hp h
    refine ⟨max a.natAbs b.natAbs, fun n => ⟨a, b, hb, ?_, ?_, hab n⟩⟩
    · rw [← Int.natCast_natAbs]
      exact_mod_cast le_max_left _ _
    · rw [← Int.natCast_natAbs]
      exact_mod_cast le_max_right _ _
  · rintro ⟨B, hB⟩
    refine (eventuallyPeriodic_iff_bounded_height hp x).2 ⟨B, fun n => ?_⟩
    obtain ⟨a, b, hb, ha, hb', hdvd⟩ := hB n
    exact ⟨a, b, fun h0 => hb (by rw [h0]; exact dvd_zero _), ha, hb', hdvd⟩

/-! ### Feedback-with-carry shift registers -/

/-- `FCSRGenerates r g M x`: the feedback-with-carry shift register with `r` cells and taps
`g : Fin r → Bool`, started with the cells `x(0), …, x(r - 1)`, outputs `x`, and `M n` is its
memory before step `n`. At step `n` the cells hold `x(n), …, x(n + r - 1)`. The register adds the
tapped cells and the memory as integers, `σ = ∑ᵢ gᵢ · x(n + i) + M n`. The parity of `σ` is the new
bit `x(n + r)` and `⌊σ / 2⌋` is the new memory: `σ = 2 · M (n + 1) + x(n + r)`.

This is Klapper and Goresky's register (Definition 3.1, steps A1–A4). Tap `g i` reads the cell
`r - i` steps back from the new bit, so their tap `q_k` is `g (r - k)`. They also require the
farthest tap `q_r = g 0` to be on; we do not, which only allows more registers. -/
def FCSRGenerates (r : ℕ) (g : Fin r → Bool) (M : ℕ → ℤ) (x : ℕ → Bool) : Prop :=
  ∀ n, (∑ i : Fin r, (if g i then 1 else 0) * (if x (n + i) then 1 else 0) : ℤ) + M n =
    2 * M (n + 1) + (if x (n + r) then 1 else 0)

/-- A digit `0` or `1`, as an integer. -/
theorem digit_eq_zero_or_one (u : Bool) :
    (if u then (1 : ℤ) else 0) = 0 ∨ (if u then (1 : ℤ) else 0) = 1 := by
  cases u <;> simp

/-- The integer digit `0` or `1` determines the bit. -/
theorem digit_inj {u v : Bool} (h : (if u then (1 : ℤ) else 0) = if v then 1 else 0) : u = v := by
  cases u <;> cases v <;> simp_all

/-- An eventually periodic sequence is generated by a feedback-with-carry shift register, even
one with memory `0`: if `x(t + P) = x(t)` for `t ≥ T`, take `T + P` cells and the single tap that
reads the cell `P` steps back. -/
theorem fcsr_of_eventuallyPeriodic {x : ℕ → Bool} (h : EventuallyPeriodic x) :
    ∃ (r : ℕ) (g : Fin r → Bool) (M : ℕ → ℤ), FCSRGenerates r g M x := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T + P, fun i => decide ((i : ℕ) = T), fun _ => 0, fun n => ?_⟩
  rw [Finset.sum_eq_single (⟨T, by omega⟩ : Fin (T + P))]
  · have e : x (n + (T + P)) = x (n + T) := by
      rw [← add_assoc]
      exact hper (n + T) (by omega)
    simp [e]
  · intro j _ hj
    have : (j : ℕ) ≠ T := fun h => hj (Fin.ext h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The output of a feedback-with-carry shift register is eventually periodic. The memory shrinks
until `|M n| ≤ r + 1` (`2 |M (n + 1)| ≤ |M n| + r + 1`). From then on the register has finitely
many states (cells, memory), each state determines the next one and the next bit, and by
pigeonhole a state repeats. -/
theorem eventuallyPeriodic_of_fcsr {r : ℕ} {g : Fin r → Bool} {M : ℕ → ℤ} {x : ℕ → Bool}
    (h : FCSRGenerates r g M x) : EventuallyPeriodic x := by
  -- The feedback sum `W n = ∑ᵢ gᵢ · x(n + i)` lies in `[0, r]`.
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℤ, ∀ n,
      W n = ∑ i : Fin r, (if g i then 1 else 0) * (if x (n + i) then 1 else 0) :=
    ⟨_, fun _ => rfl⟩
  have h' : ∀ n, W n + M n = 2 * M (n + 1) + (if x (n + r) then 1 else 0) := fun n => by
    rw [hW]
    exact h n
  have hW0 : ∀ n, 0 ≤ W n := fun n => by
    rw [hW]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hWr : ∀ n, W n ≤ r := fun n => by
    rw [hW]
    calc ∑ i : Fin r, (if g i then (1 : ℤ) else 0) * (if x (n + i) then 1 else 0)
        ≤ ∑ _i : Fin r, (1 : ℤ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = r := by simp
  -- The memory shrinks: `2 |M (n + 1)| ≤ |M n| + r + 1`.
  have hstep : ∀ n, 2 * |M (n + 1)| ≤ |M n| + (r + 1) := by
    intro n
    have e := h' n
    have w0 := hW0 n
    have w1 := hWr n
    have b := digit_eq_zero_or_one (x (n + r))
    have a1 := le_abs_self (M n)
    have a2 := neg_abs_le (M n)
    rcases abs_cases (M (n + 1)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  -- So `|M n| ≤ r + 1` from some point on.
  have hbound : ∀ n, |M n| ≤ r + 1 ∨ |M n| + n ≤ |M 0| := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      have h1 := hstep n
      have h2 := abs_nonneg (M (n + 1))
      push_cast
      omega
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n, N ≤ n → M n ∈ Set.Icc (-((r : ℤ) + 1)) ((r : ℤ) + 1) := by
    refine ⟨(M 0).natAbs + 1, fun n hn => Set.mem_Icc.2 (abs_le.1 ?_)⟩
    have h1 := hbound n
    have h2 : ((M 0).natAbs : ℤ) = |M 0| := Int.natCast_natAbs (M 0)
    have h3 : ((M 0).natAbs : ℤ) + 1 ≤ n := by exact_mod_cast hn
    have h4 := abs_nonneg (M n)
    omega
  -- Each state (cells, memory) determines the next bit and the next memory.
  have hdet : ∀ n n', (∀ l : Fin r, x (n + l) = x (n' + l)) → M n = M n' →
      x (n + r) = x (n' + r) ∧ M (n + 1) = M (n' + 1) := by
    intro n n' hw hm
    have hWeq : W n = W n' := by
      rw [hW, hW]
      exact Finset.sum_congr rfl fun l _ => by rw [hw l]
    have e1 := h' n
    have e2 := h' n'
    rw [hWeq, hm] at e1
    have b1 := digit_eq_zero_or_one (x (n + r))
    have b2 := digit_eq_zero_or_one (x (n' + r))
    have key : (if x (n + r) then (1 : ℤ) else 0) = (if x (n' + r) then 1 else 0) ∧
        M (n + 1) = M (n' + 1) := by omega
    exact ⟨digit_inj key.1, key.2⟩
  -- Pigeonhole on the states from time `N` on.
  have hfin : ((Set.univ : Set (Fin r → Bool)) ×ˢ
      Set.Icc (-((r : ℤ) + 1)) ((r : ℤ) + 1)).Finite :=
    Set.finite_univ.prod (Set.finite_Icc _ _)
  obtain ⟨i, j, hij, hf⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun k => ((fun l : Fin r => x (N + k + l)), M (N + k)))
    (fun k => Set.mem_prod.2 ⟨Set.mem_univ _, hN (N + k) (by omega)⟩)
  obtain ⟨hw, hM⟩ := Prod.ext_iff.1 hf
  -- From the repeated state on, everything repeats.
  have hk : ∀ k, (∀ l : Fin r, x (N + i + k + l) = x (N + j + k + l)) ∧
      M (N + i + k) = M (N + j + k) := by
    intro k
    induction k with
    | zero => exact ⟨fun l => by simpa using congrFun hw l, by simpa using hM⟩
    | succ k ih =>
      obtain ⟨hx, hm⟩ := hdet (N + i + k) (N + j + k) ih.1 ih.2
      refine ⟨fun l => ?_, hm⟩
      by_cases hl : (l : ℕ) + 1 < r
      · rw [show N + i + (k + 1) + l = N + i + k + ((l : ℕ) + 1) by omega,
          show N + j + (k + 1) + l = N + j + k + ((l : ℕ) + 1) by omega]
        exact ih.1 ⟨l + 1, hl⟩
      · rw [show N + i + (k + 1) + l = N + i + k + r by omega,
          show N + j + (k + 1) + l = N + j + k + r by omega]
        exact hx
  refine ⟨N + i + r, j - i, by omega, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  have := (hdet (N + i + k) (N + j + k) (hk k).1 (hk k).2).1
  rw [show N + i + r + k + (j - i) = N + j + k + r by omega,
    show N + i + r + k = N + i + k + r by omega]
  exact this.symm

/-- **Feedback-with-carry shift registers.** A bit sequence is eventually periodic iff some
feedback-with-carry shift register generates it (Klapper and Goresky, Theorem 4.1 and
Corollary 4.2). -/
theorem eventuallyPeriodic_iff_fcsr (x : ℕ → Bool) :
    EventuallyPeriodic x ↔ ∃ (r : ℕ) (g : Fin r → Bool) (M : ℕ → ℤ), FCSRGenerates r g M x :=
  ⟨fcsr_of_eventuallyPeriodic, fun ⟨_, _, _, h⟩ => eventuallyPeriodic_of_fcsr h⟩

/-! ### The `p`-adic integer `∑ x(t) pᵗ` -/

/-- The `p`-adic integer `∑ₜ x(t) pᵗ ∈ ℤ_[p]`, whose `p`-adic digits are `x(0), x(1), …`. -/
noncomputable def padicValue (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) : ℤ_[p] :=
  ∑' t, (if x t then (1 : ℤ_[p]) else 0) * (p : ℤ_[p]) ^ t

/-- The series defining `padicValue p x` converges: its terms have norm at most `p⁻ᵗ`. -/
theorem summable_padicValue (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) :
    Summable (fun t => (if x t then (1 : ℤ_[p]) else 0) * (p : ℤ_[p]) ^ t) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Summable.of_norm_bounded (g := fun t => ((p : ℝ)⁻¹) ^ t)
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)) fun t => ?_
  rw [norm_mul, norm_pow, PadicInt.norm_p]
  exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one _)

/-- Splitting off the first `n` digits: `α = S(n) + pⁿ · α'`, where `α'` is the `p`-adic integer
with digits `x(n), x(n + 1), …`. -/
theorem padicValue_eq_add (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) (n : ℕ) :
    padicValue p x = (partialSum p x n : ℤ_[p]) +
      (p : ℤ_[p]) ^ n * padicValue p (fun t => x (t + n)) := by
  simp only [padicValue]
  rw [← (summable_padicValue p x).sum_add_tsum_nat_add n,
    ← (summable_padicValue p (fun t => x (t + n))).tsum_mul_left]
  congr 1
  · simp [partialSum]
  · refine tsum_congr fun t => ?_
    simp only [pow_add]
    ring

/-- `pⁿ ∣ α - S(n)` in `ℤ_[p]`: the `p`-adic integer and its first `n` digits agree modulo `pⁿ`. -/
theorem pow_dvd_padicValue_sub (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ padicValue p x - (partialSum p x n : ℤ_[p]) := by
  rw [padicValue_eq_add p x n, add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- An element of `ℤ_[p]` divisible by every power of `p` is `0`. -/
theorem eq_zero_of_forall_pow_dvd (p : ℕ) [Fact p.Prime] {z : ℤ_[p]}
    (h : ∀ n, (p : ℤ_[p]) ^ n ∣ z) : z = 0 := by
  by_contra hz
  have := (PadicInt.mem_span_pow_iff_le_valuation z hz (z.valuation + 1)).1
    (Ideal.mem_span_singleton.2 (h _))
  omega

/-- `b · α = a` in `ℤ_[p]` iff the fraction `a / b` matches every prefix of `x`. -/
theorem mul_padicValue_eq_iff (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) (a b : ℤ) :
    (b : ℤ_[p]) * padicValue p x = a ↔ ∀ n, (p : ℤ) ^ n ∣ b * partialSum p x n - a := by
  constructor
  · intro h n
    refine (PadicInt.pow_p_dvd_int_iff (p := p) n _).1 ?_
    have e : ((b * partialSum p x n - a : ℤ) : ℤ_[p]) =
        -((b : ℤ_[p]) * (padicValue p x - (partialSum p x n : ℤ_[p]))) := by
      push_cast
      linear_combination h
    rw [e, dvd_neg]
    exact dvd_mul_of_dvd_right (pow_dvd_padicValue_sub p x n) _
  · intro h
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd p fun n => ?_
    have e : (b : ℤ_[p]) * padicValue p x - a =
        (b : ℤ_[p]) * (padicValue p x - (partialSum p x n : ℤ_[p])) +
          ((b * partialSum p x n - a : ℤ) : ℤ_[p]) := by
      push_cast
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right (pow_dvd_padicValue_sub p x n) _)
      ((PadicInt.pow_p_dvd_int_iff n _).2 (h n))

/-- `α` is rational, as an element of `ℚ_[p]`, iff `b · α = a` for integers `a` and `b ≠ 0`. -/
theorem exists_rat_iff (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) :
    (∃ q : ℚ, (padicValue p x : ℚ_[p]) = q) ↔
      ∃ a b : ℤ, b ≠ 0 ∧ (b : ℤ_[p]) * padicValue p x = a := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.num, q.den, by exact_mod_cast q.den_nz, PadicInt.ext ?_⟩
    rw [PadicInt.coe_mul, PadicInt.coe_intCast, PadicInt.coe_intCast, hq]
    exact_mod_cast q.den_mul_eq_num
  · rintro ⟨a, b, hb, h⟩
    refine ⟨a / b, ?_⟩
    have h' : (((b : ℤ_[p]) * padicValue p x : ℤ_[p]) : ℚ_[p]) = ((a : ℤ_[p]) : ℚ_[p]) := by
      rw [h]
    rw [PadicInt.coe_mul, PadicInt.coe_intCast, PadicInt.coe_intCast] at h'
    have hb' : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, eq_div_iff hb', mul_comm]
    exact h'

/-- **Eventually periodic iff `p`-adically rational.** For every prime `p`, a bit sequence `x` is
eventually periodic iff the `p`-adic integer `∑ x(t) pᵗ` is a rational number. -/
theorem eventuallyPeriodic_iff_exists_rat (p : ℕ) [Fact p.Prime] (x : ℕ → Bool) :
    EventuallyPeriodic x ↔ ∃ q : ℚ, (padicValue p x : ℚ_[p]) = q := by
  rw [exists_rat_iff, eventuallyPeriodic_iff_exists_pow_dvd (Fact.out : p.Prime).two_le]
  simp only [mul_padicValue_eq_iff]

/-! ### Problem 1 -/

/-- `S p n = ∑_{t<n} c(t) pᵗ`: the first `n` cells of the center column read in base `p`, lowest
digit first. -/
def S (p n : ℕ) : ℤ := ∑ t ∈ range n, (if c t then 1 else 0) * (p : ℤ) ^ t

/-- `S` is `partialSum` for the center column. -/
theorem S_eq_partialSum (p n : ℕ) : S p n = partialSum p c n := rfl

/-- **Problem 1 in integers, base `p ≥ 2`**: no fraction `a / b` matches every prefix of the
center column read in base `p`, i.e. there are no integers `a`, `b ≠ 0` with
`pⁿ ∣ b · ∑_{t<n} c(t) pᵗ - a` for all `n`. -/
theorem problem1_iff_no_pow_dvd {p : ℕ} (hp : 2 ≤ p) :
    Rule30Prize.Problem1 ↔ ¬ ∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * S p n - a :=
  problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_iff_exists_pow_dvd hp c))

/-- **Problem 1, `p`-adic integer form**, for a prime `p`. -/
theorem problem1_iff_padic_int (p : ℕ) (hp : p.Prime) :
    Rule30Prize.Problem1 ↔ ¬ ∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * S p n - a :=
  problem1_iff_no_pow_dvd hp.two_le

/-- **Problem 1, odd denominators**: the center column is not the 2-adic expansion of any fraction
`a / b` with `b` odd (Klapper and Goresky's Theorem 2.1 reading; compare `problem1_iff_no_fcsr`). -/
theorem problem1_iff_no_odd_fraction :
    Rule30Prize.Problem1 ↔ ¬ ∃ a b : ℤ, Odd b ∧ ∀ n, (2 : ℤ) ^ n ∣ b * S 2 n - a := by
  have h := problem1_iff_not_eventuallyPeriodic.trans
    (not_congr (eventuallyPeriodic_iff_exists_pow_dvd_not_dvd (p := 2) le_rfl c))
  rw [Nat.cast_ofNat] at h
  simp only [← even_iff_two_dvd, Int.not_even_iff_odd] at h
  exact h

/-- **Problem 1, `p`-adic form, every prime `p`**: the center column read as the `p`-adic integer
`∑ c(t) pᵗ` is not a rational number. -/
theorem problem1_iff_padicValue_irrational (p : ℕ) [Fact p.Prime] :
    Rule30Prize.Problem1 ↔ ∀ q : ℚ, (padicValue p c : ℚ_[p]) ≠ q :=
  problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_exists_rat p c)).trans not_exists)

/-- `α₂ = ∑ₜ c(t) 2ᵗ ∈ ℤ₂`: the center column of rule 30 read as a 2-adic integer, lowest digit
first. -/
noncomputable def α₂ : ℤ_[2] := ∑' t, (if c t then (1 : ℤ_[2]) else 0) * 2 ^ t

theorem α₂_eq_padicValue : α₂ = padicValue 2 c := by
  simp only [α₂, padicValue, Nat.cast_ofNat]

/-- **Problem 1 as 2-adic irrationality**: the 2-adic integer `α₂ = ∑ c(t) 2ᵗ` is not rational. -/
theorem problem1_iff_padic_irrational : Rule30Prize.Problem1 ↔ ∀ q : ℚ, (α₂ : ℚ_[2]) ≠ q := by
  rw [α₂_eq_padicValue]
  exact problem1_iff_padicValue_irrational 2

/-- **Problem 1 as feedback-with-carry shift registers**: no FCSR, of any size, with any taps and
any memory, generates the center column. -/
theorem problem1_iff_no_fcsr : Rule30Prize.Problem1 ↔
    ∀ (r : ℕ) (g : Fin r → Bool) (M : ℕ → ℤ), ¬ FCSRGenerates r g M c := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_fcsr]
  simp only [not_exists]

/-- **Problem 1 as unbounded `p`-adic complexity**, for every base `p ≥ 2`: for every bound `B`
some prefix of the center column, read in base `p`, is matched by no fraction of height at most
`B`. -/
theorem problem1_iff_padic_complexity {p : ℕ} (hp : 2 ≤ p) : Rule30Prize.Problem1 ↔
    ∀ B : ℕ, ∃ n, ¬ ∃ a b : ℤ, b ≠ 0 ∧ |a| ≤ B ∧ |b| ≤ B ∧ (p : ℤ) ^ n ∣ b * S p n - a :=
  problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_bounded_height hp c)).trans
      (not_exists.trans (forall_congr' fun _ => not_forall)))

/-- **Problem 1 as unbounded 2-adic complexity.** -/
theorem problem1_iff_two_adic_complexity : Rule30Prize.Problem1 ↔
    ∀ B : ℕ, ∃ n, ¬ ∃ a b : ℤ, b ≠ 0 ∧ |a| ≤ B ∧ |b| ≤ B ∧ (2 : ℤ) ^ n ∣ b * S 2 n - a := by
  have h := problem1_iff_padic_complexity (p := 2) le_rfl
  rw [Nat.cast_ofNat] at h
  exact h

/-- **Problem 1 as unbounded 2-adic complexity, Klapper–Goresky form**: with odd denominators,
`¬ ∃ a b, Odd b ∧ |a| ≤ B ∧ |b| ≤ B ∧ 2ⁿ ∣ b · S(n) - a` says that the 2-adic complexity of the
prefix of length `n` exceeds `log₂ B`. So Problem 1 holds iff the 2-adic complexity profile of the
center column is unbounded. -/
theorem problem1_iff_two_adic_complexity_odd : Rule30Prize.Problem1 ↔
    ∀ B : ℕ, ∃ n, ¬ ∃ a b : ℤ, Odd b ∧ |a| ≤ B ∧ |b| ≤ B ∧ (2 : ℤ) ^ n ∣ b * S 2 n - a := by
  have h := problem1_iff_not_eventuallyPeriodic.trans
    ((not_congr (eventuallyPeriodic_iff_bounded_height_not_dvd (p := 2) le_rfl c)).trans
      (not_exists.trans (forall_congr' fun _ => not_forall)))
  rw [Nat.cast_ofNat] at h
  simp only [← even_iff_two_dvd, Int.not_even_iff_odd] at h
  exact h

end Rule30Equivalents.TwoAdic
