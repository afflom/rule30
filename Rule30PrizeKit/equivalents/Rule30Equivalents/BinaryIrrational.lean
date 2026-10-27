module

public import Rule30Equivalents.ShiftOrbit
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Problem 1 as the irrationality of a real number

Read the center column `c(0), c(1), c(2), …` of rule 30 as the digits after the point of a binary
number, `centerBinary = 0.c(0) c(1) c(2) …₂ = ∑ₜ c(t) / 2^(t+1)` (with `true = 1`, `false = 0`).
**Problem 1 holds iff this number is irrational.** The same is true in every base `B ≥ 2`: for
example Problem 1 holds iff the decimal number `0.c(0) c(1) c(2) …₁₀`, whose digits are all `0`
or `1`, is irrational.

## Statements

* `eventuallyPeriodic_iff_not_irrational`: for every `b : ℕ → Bool` and every natural `B ≥ 2`,
  `EventuallyPeriodic b ↔ ¬ Irrational (∑' t, (if b t then 1 else 0) / B ^ (t + 1))`;
  `irrational_iff_not_eventuallyPeriodic` is the contrapositive.
* `problem1_iff_irrational_base`: `Problem1` iff `0.c(0) c(1) c(2) …` in base `B` is irrational.
* `problem1_iff_irrational_binary`: `Problem1 ↔ Irrational centerBinary` (base 2).
* `problem1_iff_irrational_decimal`: `Problem1 ↔ Irrational centerDecimal` (base 10).

## Proof

Let `x_t = ∑' s, b(t + s) / B^(s+1)` be the value of the tail from position `t`
(`baseValue B (tail b t)`). Comparison with `∑ 1/2^(s+1) = 1` gives `0 ≤ x_t ≤ 1`. Splitting off
the first term gives `B x_t = b(t) + x_(t+1)` (`mul_baseValue`), and so `B^t x_0 = N_t + x_t`, where
`N_t` is the natural number with base-`B` digits `b(0) … b(t-1)` (`pow_mul_baseValue`).

* (→) If `b(t + P) = b(t)` for `t ≥ T`, the tail from `T` is purely periodic, so `x_(T+P) = x_T`
  and `B^P x_T = N' + x_T` for a natural number `N'`. This is the geometric series:
  `x_T = N' / (B^P - 1)`. Then `x_0 = (N_T + x_T) / B^T` is rational.
* (←) If `x_0 = p/q`, then `q x_t = B^t p - q N_t` is an integer in `[0, q]`. So the tails take
  finitely many values, and `x_i = x_j` for some `i < j` by pigeonhole. If only finitely many
  digits are `1`, `b` is eventually `0`, hence eventually periodic. Otherwise every `x_t` is
  positive, so `b(t) = 1` iff `B x_t > 1` (`digit_iff`): a `1` gives `B x_t = 1 + x_(t+1) > 1`, a
  `0` gives `B x_t = x_(t+1) ≤ 1`. The tail value thus determines the next digit and, through
  `x_(t+1) = B x_t - b(t)`, the next tail value. By induction `x_(i+k) = x_(j+k)` and
  `b(i+k) = b(j+k)` for all `k`, so `b` has period `j - i` from `i` on.

Everything except the digit rule holds in every real base `β > 1`: the value `value β b`, the
shift `β^t x_0 = N_t + x_t` (`pow_mul_value`, with `N_t = lead β b t`), the geometric series
(`mem_of_eventuallyPeriodic`: an eventually periodic `b` has its value in every subfield of `ℝ`
containing `β`) and the pigeonhole step (`eventuallyPeriodic_of_finite_tails`: finitely many tail
values give eventual periodicity once the tail value determines the digit).
`PisotNumbers` uses them for Pisot bases.

The case split takes care of double expansions. In base 2, `0.0111…₂ = 0.1000…₂`: equal tail
values need not have equal digits. That only happens for eventually constant sequences, and when
infinitely many digits are `1` the tail value does determine the digit. For `B ≥ 3` the digits
`0, 1` never reach `B - 1`, and the expansion is always unique.

## Source

The classical theorem that a real number is rational iff its expansion in an integer base is
eventually periodic. For decimal fractions it goes back to J. Wallis, *A Treatise of Algebra*
(1685), J. H. Lambert and L. Euler in the eighteenth century, and C. F. Gauss, *Disquisitiones
Arithmeticae* (1801), art. 312 ff.; see L. E. Dickson, *History of the Theory of Numbers*, vol. I
(1919), ch. VI. A textbook treatment for an arbitrary base is G. H. Hardy and E. M. Wright,
*An Introduction to the Theory of Numbers* (1938), ch. IX.
-/

@[expose] public section

namespace Rule30Equivalents.BinaryIrrational

open Ruliology.CellularAutomata

/-! ### Expansions in a real base `β > 1` -/

/-- The value `0.b(0) b(1) b(2) …` of the digits `b` in a real base `β`, with digit `1` for `true`
and `0` for `false`. -/
noncomputable def value (β : ℝ) (b : ℕ → Bool) : ℝ :=
  ∑' t, (if b t then (1 : ℝ) else 0) / β ^ (t + 1)

/-- The tail `b(t), b(t + 1), …` of a sequence. -/
def tail (b : ℕ → Bool) (t : ℕ) : ℕ → Bool := fun s => b (s + t)

/-- The first `t` digits `b(0) … b(t - 1)` read as a numeral in base `x`, an element of a
semiring: `lead x b (t + 1) = x · lead x b t + b(t)`. -/
def lead {R : Type*} [Semiring R] (x : R) (b : ℕ → Bool) : ℕ → R
  | 0 => 0
  | t + 1 => x * lead x b t + (if b t then 1 else 0)

theorem map_lead {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (x : R) (b : ℕ → Bool) :
    ∀ t, f (lead x b t) = lead (f x) b t
  | 0 => map_zero f
  | t + 1 => by
    rw [lead, lead, map_add, map_mul, map_lead f x b t]
    split_ifs <;> simp

/-- The first digit of the tail from `t` is `b t`. -/
theorem tail_zero_apply (b : ℕ → Bool) (t : ℕ) : tail b t 0 = b t := by
  simp [tail]

/-- Dropping one more digit from the tail from `t` gives the tail from `t + 1`. -/
theorem tail_tail_one (b : ℕ → Bool) (t : ℕ) : tail (tail b t) 1 = tail b (t + 1) := by
  funext s
  simp only [tail]
  congr 1
  omega

section RealBase
variable {β : ℝ} (hβ : 1 < β)
include hβ

theorem term_nonneg (b : ℕ → Bool) (t : ℕ) :
    0 ≤ (if b t then (1 : ℝ) else 0) / β ^ (t + 1) := by
  have : (0 : ℝ) < β ^ (t + 1) := pow_pos (by linarith) _
  split_ifs <;> positivity

theorem term_le (b : ℕ → Bool) (t : ℕ) :
    (if b t then (1 : ℝ) else 0) / β ^ (t + 1) ≤ (β⁻¹) ^ (t + 1) := by
  rw [inv_pow, ← one_div]
  have : (0 : ℝ) < β ^ (t + 1) := pow_pos (by linarith) _
  split_ifs
  · exact le_refl _
  · rw [zero_div]; positivity

theorem summable_geom : Summable fun t : ℕ => (β⁻¹) ^ (t + 1) := by
  have h := summable_geometric_of_lt_one (inv_nonneg.2 (by linarith)) (inv_lt_one_of_one_lt₀ hβ)
  exact h.comp_injective (add_left_injective 1)

/-- The series defining `value β b` converges. -/
theorem summable_term (b : ℕ → Bool) :
    Summable fun t => (if b t then (1 : ℝ) else 0) / β ^ (t + 1) :=
  Summable.of_nonneg_of_le (term_nonneg hβ b) (term_le hβ b) (summable_geom hβ)

theorem value_nonneg (b : ℕ → Bool) : 0 ≤ value β b := tsum_nonneg (term_nonneg hβ b)

/-- `∑ β^-(t+1) = 1 / (β - 1)`. -/
theorem tsum_geom : ∑' t : ℕ, (β⁻¹) ^ (t + 1) = 1 / (β - 1) := by
  have h : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  have hs := tsum_geometric_of_lt_one (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ β)) h
  have : ∑' t : ℕ, (β⁻¹) ^ (t + 1) = β⁻¹ * ∑' t : ℕ, (β⁻¹) ^ t := by
    rw [← tsum_mul_left]; congr 1; funext t; ring
  rw [this, hs]
  have hb : β ≠ 0 := by linarith
  have h1 : β - 1 ≠ 0 := by linarith
  have h2 : 1 - β⁻¹ ≠ 0 := by linarith
  field_simp

theorem value_le (b : ℕ → Bool) : value β b ≤ 1 / (β - 1) := by
  rw [← tsum_geom hβ]
  exact (summable_term hβ b).tsum_le_tsum (term_le hβ b) (summable_geom hβ)

/-- A single digit `1` makes the value positive. -/
theorem value_pos (b : ℕ → Bool) {s : ℕ} (hs : b s = true) : 0 < value β b := by
  refine (summable_term hβ b).tsum_pos (term_nonneg hβ b) s ?_
  have : (0 : ℝ) < β := by linarith
  simp only [hs, ite_true]
  positivity

/-- Peeling off the first digit: `β · 0.b₀b₁b₂… = b₀ + 0.b₁b₂…`. -/
theorem mul_value (b : ℕ → Bool) :
    β * value β b = (if b 0 then 1 else 0) + value β (tail b 1) := by
  have hb : β ≠ 0 := by linarith
  have e : value β (tail b 1) = ∑' n, (if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1) := rfl
  rw [e, value, (summable_term hβ b).tsum_eq_zero_add]
  have h : ∀ n : ℕ, (if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1 + 1) =
      β⁻¹ * ((if b (n + 1) then (1 : ℝ) else 0) / β ^ (n + 1)) := by
    intro n; rw [pow_succ]; field_simp
  simp only [h, tsum_mul_left]
  field_simp
  ring

/-- One step of the digit dynamics: `x_{t+1} = β x_t - b(t)`. -/
theorem tailValue_succ (b : ℕ → Bool) (t : ℕ) :
    value β (tail b (t + 1)) = β * value β (tail b t) - (if b t then 1 else 0) := by
  have h1 := mul_value hβ (tail b t)
  rw [tail_tail_one, tail_zero_apply] at h1
  linarith

/-- Shifting by `t` digits: `βᵗ · 0.b₀b₁… = (b₀ … b_{t-1})_β + 0.b_t b_{t+1}…`. -/
theorem pow_mul_value (b : ℕ → Bool) : ∀ t, β ^ t * value β b = lead β b t + value β (tail b t)
  | 0 => by simp only [pow_zero, one_mul, lead, zero_add]; rfl
  | t + 1 => by
    rw [pow_succ, mul_comm (β ^ t) β, mul_assoc, pow_mul_value b t, mul_add,
      tailValue_succ hβ b t, lead]
    ring

/-- **The periodic direction** (geometric series). An eventually periodic digit sequence has its
value in every subfield of `ℝ` that contains `β`. -/
theorem mem_of_eventuallyPeriodic (F : Subfield ℝ) (hF : β ∈ F) {b : ℕ → Bool}
    (h : EventuallyPeriodic b) : value β b ∈ F := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hlead : ∀ (b' : ℕ → Bool) t, lead β b' t ∈ F := fun b' t => by
    induction t with
    | zero => exact F.zero_mem
    | succ t ih =>
      exact F.add_mem (F.mul_mem hF ih) (by split_ifs; exacts [F.one_mem, F.zero_mem])
  have htail : tail (tail b T) P = tail b T := by
    funext s; simp only [tail]; rw [show s + P + T = s + T + P by omega]; exact hper _ (by omega)
  have e1 := pow_mul_value hβ (tail b T) P
  rw [htail] at e1
  have e2 := pow_mul_value hβ b T
  have hβP : (1 : ℝ) < β ^ P := one_lt_pow₀ hβ hP.ne'
  have hβT : (0 : ℝ) < β ^ T := pow_pos (by linarith) T
  have hx : value β (tail b T) = lead β (tail b T) P / (β ^ P - 1) := by
    rw [eq_div_iff (by linarith)]; linarith
  have hv : value β b = (lead β b T + value β (tail b T)) / β ^ T := by
    rw [eq_div_iff hβT.ne']; linarith
  rw [hv, hx]
  exact F.div_mem (F.add_mem (hlead b T)
    (F.div_mem (hlead _ P) (F.sub_mem (F.pow_mem hF P) F.one_mem))) (F.pow_mem hF T)

/-- **Finitely many tail values give eventual periodicity**, as soon as the tail value determines
the digit: then it also determines the next tail value (`tailValue_succ`). -/
theorem eventuallyPeriodic_of_finite_tails {b : ℕ → Bool} (f : ℝ → Bool)
    (hdig : ∀ t, b t = f (value β (tail b t)))
    (hfin : (Set.range fun t => value β (tail b t)).Finite) : EventuallyPeriodic b := by
  obtain ⟨s, t, hst, heq⟩ : ∃ s t, s < t ∧ value β (tail b s) = value β (tail b t) := by
    by_contra hne
    push Not at hne
    refine Set.infinite_range_of_injective (fun s t he => ?_) hfin
    rcases lt_trichotomy s t with h | h | h
    · exact absurd he (hne s t h)
    · exact h
    · exact absurd he.symm (hne t s h)
  have key : ∀ j, value β (tail b (s + j)) = value β (tail b (t + j)) := by
    intro j
    induction j with
    | zero => exact heq
    | succ j ih =>
      have hd : b (s + j) = b (t + j) := by rw [hdig, hdig, ih]
      rw [← add_assoc, ← add_assoc, tailValue_succ hβ, tailValue_succ hβ, ih, hd]
  refine ShiftOrbit.eventuallyPeriodic_of_shift_eq hst fun j => ?_
  rw [hdig, hdig, key]

end RealBase

/-- **For `β > 2` the value is one-to-one**: the digit `b t` is `1` iff `β · 0.b(t) b(t+1)… ≥ 1`,
since every tail value is at most `1/(β - 1) < 1`. -/
theorem value_injective {β : ℝ} (hβ : 2 < β) : Function.Injective (value β) := by
  have hβ1 : 1 < β := by linarith
  have hsmall : ∀ b : ℕ → Bool, value β b < 1 := fun b =>
    (value_le hβ1 b).trans_lt (by rw [div_lt_one (by linarith)]; linarith)
  -- the digit is read off the tail value
  have hdig : ∀ (b : ℕ → Bool) t, b t = true ↔ 1 ≤ β * value β (tail b t) := fun b t => by
    rw [mul_value hβ1, tail_tail_one, tail_zero_apply]
    have h0 := value_nonneg hβ1 (tail b (t + 1))
    have h1 := hsmall (tail b (t + 1))
    cases b t
    · simp only [Bool.false_eq_true, ite_false, zero_add, false_iff, not_le]
      exact h1
    · simp only [ite_true, true_iff]
      linarith
  intro b b' h
  have hval : ∀ t, value β (tail b t) = value β (tail b' t) := by
    intro t
    induction t with
    | zero =>
      have e : ∀ v : ℕ → Bool, tail v 0 = v := fun v => funext fun s => by simp [tail]
      rw [e, e]
      exact h
    | succ t ih =>
      rw [tailValue_succ hβ1, tailValue_succ hβ1, ih,
        show b t = b' t from Bool.eq_iff_iff.2 (by rw [hdig, hdig, ih])]
  funext t
  exact Bool.eq_iff_iff.2 (by rw [hdig, hdig, hval])

/-! ### Integer bases -/

/-- The real number `0.b(0) b(1) b(2) …` written in the integer base `B`. -/
noncomputable def baseValue (B : ℕ) (b : ℕ → Bool) : ℝ := value B b

/-- The base-`B` numeral of the first `t` digits, cast to `ℝ`, is the numeral in base `(B : ℝ)`. -/
theorem cast_lead (B : ℕ) (b : ℕ → Bool) (t : ℕ) : ((lead B b t : ℕ) : ℝ) = lead (B : ℝ) b t :=
  map_lead (Nat.castRingHom ℝ) B b t

section
variable {B : ℕ} (hB : 2 ≤ B)
include hB

/-- The base, as a real number, is at least `2`. -/
theorem two_le_cast : (2 : ℝ) ≤ B := by exact_mod_cast hB

theorem one_lt_cast : (1 : ℝ) < B := by linarith [two_le_cast hB]

/-- Each term is at most `1 / 2^(t+1)`, written `1 / 2 / 2^t` to match `tsum_geometric_two'`. -/
theorem term_le_two (b : ℕ → Bool) (t : ℕ) :
    (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1) ≤ 1 / 2 / 2 ^ t := by
  have hpow : (2 : ℝ) ^ (t + 1) ≤ (B : ℝ) ^ (t + 1) :=
    pow_le_pow_left₀ (by norm_num) (two_le_cast hB) _
  rw [div_div, ← pow_succ']
  split_ifs
  · exact one_div_le_one_div_of_le (by positivity) hpow
  · rw [zero_div]; positivity

/-- `0 ≤ 0.b(0) b(1) …`. -/
theorem baseValue_nonneg (b : ℕ → Bool) : 0 ≤ baseValue B b := value_nonneg (one_lt_cast hB) b

/-- `0.b(0) b(1) … ≤ 1`, by comparison with `∑ B^-(t+1) = 1/(B - 1)`. -/
theorem baseValue_le_one (b : ℕ → Bool) : baseValue B b ≤ 1 := by
  refine (value_le (one_lt_cast hB) b).trans ?_
  rw [div_le_one (by linarith [two_le_cast hB])]
  linarith [two_le_cast hB]

/-- A single digit `1` makes the value positive. -/
theorem baseValue_pos (b : ℕ → Bool) {s : ℕ} (hs : b s = true) : 0 < baseValue B b :=
  value_pos (one_lt_cast hB) b hs

/-- Peeling off the first digit: `B · 0.b₀b₁b₂… = b₀ + 0.b₁b₂…`. -/
theorem mul_baseValue (b : ℕ → Bool) :
    (B : ℝ) * baseValue B b = (if b 0 then 1 else 0) + baseValue B (tail b 1) :=
  mul_value (one_lt_cast hB) b

/-- Shifting by `t` digits: `B^t · 0.b₀b₁… = (b₀ … b_{t-1})_B + 0.b_t b_{t+1}…`. -/
theorem pow_mul_baseValue (b : ℕ → Bool) (t : ℕ) :
    (B : ℝ) ^ t * baseValue B b = lead B b t + baseValue B (tail b t) := by
  unfold baseValue
  rw [pow_mul_value (one_lt_cast hB) b t, cast_lead]

/-- One step of the digit dynamics: `x_{t+1} = B x_t - b(t)`. -/
theorem baseValue_tail_succ (b : ℕ → Bool) (t : ℕ) :
    baseValue B (tail b (t + 1)) = B * baseValue B (tail b t) - (if b t then 1 else 0) :=
  tailValue_succ (one_lt_cast hB) b t

/-- If infinitely many digits are `1`, the digit `b t` is read off the tail value. -/
theorem digit_iff (b : ℕ → Bool) (hinf : ∀ T, ∃ s, T ≤ s ∧ b s = true) (t : ℕ) :
    b t = true ↔ 1 < (B : ℝ) * baseValue B (tail b t) := by
  have h1 := mul_baseValue hB (tail b t)
  rw [tail_tail_one, tail_zero_apply] at h1
  rw [h1]
  obtain ⟨s, hs, hbs⟩ := hinf (t + 1)
  have hpos : 0 < baseValue B (tail b (t + 1)) := by
    refine baseValue_pos hB (tail b (t + 1)) (s := s - (t + 1)) ?_
    simp only [tail]
    rw [Nat.sub_add_cancel hs]
    exact hbs
  have hle := baseValue_le_one hB (tail b (t + 1))
  cases b t <;> simp <;> linarith

/-- (→): an eventually periodic digit sequence has a rational value (`mem_of_eventuallyPeriodic`
with the field `ℚ`). -/
theorem not_irrational_of_eventuallyPeriodic (b : ℕ → Bool) (h : EventuallyPeriodic b) :
    ¬ Irrational (baseValue B b) := by
  have hB' : (B : ℝ) ∈ (Rat.castHom ℝ).fieldRange := ⟨B, by simp⟩
  obtain ⟨q, hq⟩ := mem_of_eventuallyPeriodic (one_lt_cast hB) _ hB' h
  exact fun hirr => hirr ⟨q, hq⟩

/-- (←): a rational value forces an eventually periodic digit sequence: the tails take finitely
many values (`eventuallyPeriodic_of_finite_tails`). -/
theorem eventuallyPeriodic_of_not_irrational (b : ℕ → Bool) (h : ¬ Irrational (baseValue B b)) :
    EventuallyPeriodic b := by
  by_cases hfin : ∃ T, ∀ t, T ≤ t → b t = false
  · obtain ⟨T, hT⟩ := hfin
    exact ⟨T, 1, Nat.one_pos, fun t ht => by rw [hT t ht, hT (t + 1) (by omega)]⟩
  have hinf : ∀ T, ∃ s, T ≤ s ∧ b s = true := by
    intro T
    by_contra hT
    exact hfin ⟨T, fun t ht => by
      cases hbt : b t
      · rfl
      · exact absurd ⟨t, ht, hbt⟩ hT⟩
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational h
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hrq : (r.den : ℝ) * baseValue B b = r.num := by
    rw [hr]
    exact_mod_cast r.den_mul_eq_num
  -- `den · x_t` is an integer in `[0, den]`
  let m : ℕ → ℤ := fun t => (B : ℤ) ^ t * r.num - (r.den : ℤ) * lead B b t
  have hm : ∀ t, (m t : ℝ) = r.den * baseValue B (tail b t) := by
    intro t
    have e := pow_mul_baseValue hB b t
    simp only [m]
    push_cast
    linear_combination (r.den : ℝ) * e - (B : ℝ) ^ t * hrq
  have hmem : ∀ t, m t ∈ Set.Icc (0 : ℤ) r.den := by
    intro t
    have h0 := baseValue_nonneg hB (tail b t)
    have h1 := baseValue_le_one hB (tail b t)
    constructor
    · have : (0 : ℝ) ≤ m t := by rw [hm]; positivity
      exact_mod_cast this
    · have : (m t : ℝ) ≤ r.den := by rw [hm]; nlinarith
      exact_mod_cast this
  have hfin : (Set.range fun t => value B (tail b t)).Finite := by
    refine ((Set.finite_Icc (0 : ℤ) r.den).image fun z : ℤ => (z : ℝ) / r.den).subset ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨m t, hmem t, ?_⟩
    show (m t : ℝ) / r.den = baseValue B (tail b t)
    rw [hm, mul_div_cancel_left₀ _ hq.ne']
  exact eventuallyPeriodic_of_finite_tails (one_lt_cast hB) (fun x => decide (1 < (B : ℝ) * x))
    (fun t => Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff]; exact digit_iff hB b hinf t)) hfin

/-- `0.b(0) b(1) … < 1` in base `B ≥ 2` as soon as one digit is `0`. -/
theorem baseValue_lt_one {b : ℕ → Bool} {s : ℕ} (hs : b s = false) :
    baseValue B b < 1 := by
  have h := Summable.tsum_lt_tsum_of_nonneg (i := s) (term_nonneg (one_lt_cast hB) b)
    (term_le_two hB b)
    (by rw [hs]; simp only [Bool.false_eq_true, ite_false, zero_div]; positivity)
    (summable_geometric_two' 1)
  rwa [tsum_geometric_two' 1] at h

/-- If `b` has a `0` after every time, every tail value `0.b(t) b(t+1) …` is `< 1`. -/
theorem tail_lt_one {b : ℕ → Bool} (h : ¬ ∃ T, ∀ t, T ≤ t → b t = true) (t : ℕ) :
    baseValue B (tail b t) < 1 := by
  obtain ⟨s, hs, hbs⟩ : ∃ s, t ≤ s ∧ b s = false := by
    by_contra hT
    push Not at hT
    exact h ⟨t, fun u hu => by simpa using hT u hu⟩
  refine baseValue_lt_one hB (s := s - t) ?_
  simp only [tail]
  rw [Nat.sub_add_cancel hs]
  exact hbs

end

/-- **Rational digit sequences are exactly the eventually periodic ones.** For every base
`B ≥ 2`, a `0/1` digit sequence `b` is eventually periodic iff `0.b(0) b(1) b(2) …` in base `B` is
rational. -/
theorem eventuallyPeriodic_iff_not_irrational {B : ℕ} (hB : 2 ≤ B) (b : ℕ → Bool) :
    EventuallyPeriodic b ↔
      ¬ Irrational (∑' t, (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) :=
  ⟨not_irrational_of_eventuallyPeriodic hB b, eventuallyPeriodic_of_not_irrational hB b⟩

/-- The contrapositive: the base-`B` number `0.b(0) b(1) b(2) …` is irrational iff `b` is not
eventually periodic. -/
theorem irrational_iff_not_eventuallyPeriodic {B : ℕ} (hB : 2 ≤ B) (b : ℕ → Bool) :
    Irrational (∑' t, (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) ↔
      ¬ EventuallyPeriodic b := by
  rw [eventuallyPeriodic_iff_not_irrational hB, not_not]

/-- **Problem 1 in base `B`**: for every `B ≥ 2`, the center column is not eventually periodic iff
the base-`B` number `0.c(0) c(1) c(2) …` is irrational. -/
theorem problem1_iff_irrational_base {B : ℕ} (hB : 2 ≤ B) :
    Rule30Prize.Problem1 ↔ Irrational (∑' t, (if c t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_not_irrational hB, not_not]

/-- The center column of rule 30 read as the binary number `0.c(0) c(1) c(2) …₂`. -/
noncomputable def centerBinary : ℝ := ∑' t, (if c t then 1 else 0) / 2 ^ (t + 1)

/-- `centerBinary` is `0.c(0) c(1) c(2) …` in base `2`, as a `baseValue`. -/
theorem centerBinary_eq_baseValue : centerBinary = baseValue 2 c := by
  simp only [centerBinary, baseValue, value, Nat.cast_ofNat]

/-- **Problem 1 as irrationality**: the center column is not eventually periodic iff the binary
number `0.c(0) c(1) c(2) …₂` is irrational. -/
theorem problem1_iff_irrational_binary : Rule30Prize.Problem1 ↔ Irrational centerBinary := by
  have h := problem1_iff_irrational_base (B := 2) le_rfl
  rw [Nat.cast_ofNat] at h
  exact h

/-- The center column of rule 30 read as the decimal number `0.c(0) c(1) c(2) …₁₀`. -/
noncomputable def centerDecimal : ℝ := ∑' t, (if c t then 1 else 0) / 10 ^ (t + 1)

/-- **Problem 1 in decimal**: the center column is not eventually periodic iff the decimal number
`0.c(0) c(1) c(2) …₁₀` (all digits `0` or `1`) is irrational. -/
theorem problem1_iff_irrational_decimal : Rule30Prize.Problem1 ↔ Irrational centerDecimal := by
  have h := problem1_iff_irrational_base (B := 10) (by norm_num)
  rw [Nat.cast_ofNat] at h
  exact h

end Rule30Equivalents.BinaryIrrational
