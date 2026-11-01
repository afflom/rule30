module
public import Rule30UOR.EdgeParity
public import Rule30UOR.Automatic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Dyadic stability of the trinomial kernel

Below degree `2^j`, the trinomial row `2^(j+1) - 1 - m` is the row
`2^j - 1 - m` (for `m < 2^j`): the propagation kernels from row `m` to the
dyadic times collapse to one fixed array `stableKernel m d`, the coefficient
`d` of the power series `q^(-(m+1))`. The seed row `stableKernel 0` is the
3-periodic `1/q = 110110...`, and the rows are linked by the backward
Rule-150 recursion `q · K_(m+1) = K_m`. The dyadic column `j ↦ center (2^j)`
is then the reading, at position `2^j - 1`, of the carries of the rows
`m < 2^j` convolved with the fixed kernel: `center (2^j) = ¬ stableFormula j (2^j)`,
so the dyadic-column aperiodicity is the aperiodicity of the stable formula. -/

@[expose] public section

namespace Rule30UOR.StableKernel

open Rule30UOR.Core
open Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Automatic

/-! ## Dyadic stability -/

/-- **Dyadic stability**: below `2^j` the trinomial row `2^(j+1) - 1 - m` is the row `2^j - 1 - m`. -/
theorem trinomialParity_dyadic_stable (j m d : Nat) (hm : m < twopow j) (hd : d < twopow j) :
    trinomialParity (twopow (j + 1) - 1 - m) d = trinomialParity (twopow j - 1 - m) d := by
  induction j generalizing m d with
  | zero =>
    have h0 : twopow 0 = 1 := rfl
    have hm0 : m = 0 := by cfomega
    have hd0 : d = 0 := by cfomega
    subst hm0; subst hd0
    rfl
  | succ j ih =>
    have h1 : twopow (j + 1) = twopow j + twopow j := twopow_succ j
    have h2 : twopow (j + 1 + 1) = twopow (j + 1) + twopow (j + 1) := twopow_succ (j + 1)
    rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2
    · -- m even: both rows are odd
      obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a := ⟨m / 2, by cfomega⟩
      rw [show twopow (j + 1 + 1) - 1 - 2 * a = 2 * (twopow (j + 1) - 1 - a) + 1 by cfomega,
        show twopow (j + 1) - 1 - 2 * a = 2 * (twopow j - 1 - a) + 1 by cfomega]
      cases d with
      | zero =>
        rw [trinomialParity_odd_zero, trinomialParity_odd_zero]
        exact ih a 0 (by cfomega) (by cfomega)
      | succ d' =>
        rcases Nat.mod_two_eq_zero_or_one d' with hd2 | hd2
        · obtain ⟨e, rfl⟩ : ∃ e, d' = 2 * e := ⟨d' / 2, by cfomega⟩
          rw [trinomialParity_odd_odd, trinomialParity_odd_odd]
          exact ih a e (by cfomega) (by cfomega)
        · obtain ⟨e, rfl⟩ : ∃ e, d' = 2 * e + 1 := ⟨d' / 2, by cfomega⟩
          rw [show 2 * e + 1 + 1 = 2 * e + 2 by cfomega, trinomialParity_odd_even_succ,
            trinomialParity_odd_even_succ, ih a (e + 1) (by cfomega) (by cfomega),
            ih a e (by cfomega) (by cfomega)]
    · -- m odd: both rows are even
      obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a + 1 := ⟨m / 2, by cfomega⟩
      rw [show twopow (j + 1 + 1) - 1 - (2 * a + 1) = 2 * (twopow (j + 1) - 1 - a) by cfomega,
        show twopow (j + 1) - 1 - (2 * a + 1) = 2 * (twopow j - 1 - a) by cfomega]
      rcases Nat.mod_two_eq_zero_or_one d with hd2 | hd2
      · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by cfomega⟩
        rw [trinomialParity_even_even, trinomialParity_even_even]
        exact ih a e (by cfomega) (by cfomega)
      · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by cfomega⟩
        rw [trinomialParity_even_odd, trinomialParity_even_odd]

/-- Iterated dyadic stability: the row `2^(j+n) - 1 - m` is the row `2^j - 1 - m` below `2^j`. -/
theorem trinomialParity_dyadic_stable_iter (j m d : Nat) (hm : m < twopow j) (hd : d < twopow j) :
    ∀ n, trinomialParity (twopow (j + n) - 1 - m) d = trinomialParity (twopow j - 1 - m) d := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show j + (n + 1) = (j + n) + 1 by cfomega,
      trinomialParity_dyadic_stable (j + n) m d
        (Nat.lt_of_lt_of_le hm (Rule30UOR.Interfaces.twopow_mono _ _ (by cfomega)))
        (Nat.lt_of_lt_of_le hd (Rule30UOR.Interfaces.twopow_mono _ _ (by cfomega))),
      ih]

/-- **The stable kernel** `K_m(d)`: the coefficient `d` of the power series `q^(-(m+1))`,
read as the trinomial row `2^J - 1 - m` for any `J` with `m, d < 2^J`. -/
def stableKernel (m d : Nat) : Bool := trinomialParity (twopow (m + d + 1) - 1 - m) d

/-- Every dyadic scale with `m, d < 2^j` reads the same stable kernel. -/
theorem trinomialParity_eq_stableKernel (j m d : Nat) (hm : m < twopow j) (hd : d < twopow j) :
    trinomialParity (twopow j - 1 - m) d = stableKernel m d := by
  unfold stableKernel
  have hge := twopow_ge_succ (m + d + 1)
  rw [← trinomialParity_dyadic_stable_iter j m d hm hd (m + d + 1),
    ← trinomialParity_dyadic_stable_iter (m + d + 1) m d (by cfomega) (by cfomega) j,
    Nat.add_comm (m + d + 1) j]

/-! ## The backward Rule-150 recursion `q · K_(m+1) = K_m` -/

/-- One row of the trinomial triangle, degree `d + 2`. -/
theorem trinomialParity_row_succ (n d : Nat) :
    trinomialParity (n + 1) (d + 2) =
      bxor (bxor (trinomialParity n (d + 2)) (trinomialParity n (d + 1))) (trinomialParity n d) := by
  have h : ∀ e, (phiLinPow 1 n 1).testBit e = trinomialParity n e := testBit_phiLinPow_eq_trinomialParity n
  rw [← testBit_phiLinPow_eq_trinomialParity (n + 1) (d + 2)]
  show (phiLin 1 (phiLinPow 1 n 1)).testBit (d + 2) = _
  rw [testBit_phiLin, h, h, h, decide_eq_true (by cfomega : d + 2 ≥ 1),
    decide_eq_true (by cfomega : d + 2 ≥ 2 * 1), Bool.true_and, Bool.true_and,
    show d + 2 - 1 = d + 1 by cfomega, show d + 2 - 2 * 1 = d by cfomega]
  cases trinomialParity n (d + 2) <;> cases trinomialParity n (d + 1) <;> cases trinomialParity n d <;> rfl

/-- One row of the trinomial triangle, degree `0`. -/
theorem trinomialParity_row_succ_zero (n : Nat) : trinomialParity (n + 1) 0 = trinomialParity n 0 := by
  have h : ∀ e, (phiLinPow 1 n 1).testBit e = trinomialParity n e := testBit_phiLinPow_eq_trinomialParity n
  rw [← testBit_phiLinPow_eq_trinomialParity (n + 1) 0]
  show (phiLin 1 (phiLinPow 1 n 1)).testBit 0 = _
  rw [testBit_phiLin, h, decide_eq_false (by cfomega : ¬ (0 ≥ 1)),
    decide_eq_false (by cfomega : ¬ (0 ≥ 2 * 1)), Bool.false_and]
  cases trinomialParity n 0 <;> rfl

/-- One row of the trinomial triangle, degree `1`. -/
theorem trinomialParity_row_succ_one (n : Nat) :
    trinomialParity (n + 1) 1 = bxor (trinomialParity n 1) (trinomialParity n 0) := by
  have h : ∀ e, (phiLinPow 1 n 1).testBit e = trinomialParity n e := testBit_phiLinPow_eq_trinomialParity n
  rw [← testBit_phiLinPow_eq_trinomialParity (n + 1) 1]
  show (phiLin 1 (phiLinPow 1 n 1)).testBit 1 = _
  rw [testBit_phiLin, h, h, decide_eq_true (by cfomega : 1 ≥ 1),
    decide_eq_false (by cfomega : ¬ (1 ≥ 2 * 1)), Bool.true_and, Bool.false_and,
    show 1 - 1 = 0 by cfomega]
  cases trinomialParity n 1 <;> cases trinomialParity n 0 <;> rfl

/-- `q · K_(m+1) = K_m` at degree `d + 2`: the kernel is the trinomial triangle read backward. -/
theorem stableKernel_succ (m d : Nat) :
    stableKernel m (d + 2) =
      bxor (bxor (stableKernel (m + 1) (d + 2)) (stableKernel (m + 1) (d + 1))) (stableKernel (m + 1) d) := by
  have hge := twopow_ge_succ (m + d + 3)
  rw [← trinomialParity_eq_stableKernel (m + d + 3) m (d + 2) (by cfomega) (by cfomega),
    ← trinomialParity_eq_stableKernel (m + d + 3) (m + 1) (d + 2) (by cfomega) (by cfomega),
    ← trinomialParity_eq_stableKernel (m + d + 3) (m + 1) (d + 1) (by cfomega) (by cfomega),
    ← trinomialParity_eq_stableKernel (m + d + 3) (m + 1) d (by cfomega) (by cfomega),
    show twopow (m + d + 3) - 1 - m = (twopow (m + d + 3) - 1 - (m + 1)) + 1 by cfomega,
    trinomialParity_row_succ]

/-- `q · K_(m+1) = K_m` at degree `0`. -/
theorem stableKernel_succ_zero (m : Nat) : stableKernel m 0 = stableKernel (m + 1) 0 := by
  have hge := twopow_ge_succ (m + 3)
  rw [← trinomialParity_eq_stableKernel (m + 3) m 0 (by cfomega) (by cfomega),
    ← trinomialParity_eq_stableKernel (m + 3) (m + 1) 0 (by cfomega) (by cfomega),
    show twopow (m + 3) - 1 - m = (twopow (m + 3) - 1 - (m + 1)) + 1 by cfomega,
    trinomialParity_row_succ_zero]

/-- `q · K_(m+1) = K_m` at degree `1`. -/
theorem stableKernel_succ_one (m : Nat) :
    stableKernel m 1 = bxor (stableKernel (m + 1) 1) (stableKernel (m + 1) 0) := by
  have hge := twopow_ge_succ (m + 3)
  rw [← trinomialParity_eq_stableKernel (m + 3) m 1 (by cfomega) (by cfomega),
    ← trinomialParity_eq_stableKernel (m + 3) (m + 1) 1 (by cfomega) (by cfomega),
    ← trinomialParity_eq_stableKernel (m + 3) (m + 1) 0 (by cfomega) (by cfomega),
    show twopow (m + 3) - 1 - m = (twopow (m + 3) - 1 - (m + 1)) + 1 by cfomega,
    trinomialParity_row_succ_one]

/-! ## The seed kernel `1/q` is 3-periodic -/

theorem decide_mod3_odd (e : Nat) : decide ((2 * e + 1) % 3 ≠ 2) = decide (e % 3 ≠ 2) := by
  have h3 : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by cfomega
  rcases h3 with h | h | h
  · rw [decide_eq_true (by cfomega : (2 * e + 1) % 3 ≠ 2), decide_eq_true (by cfomega : e % 3 ≠ 2)]
  · rw [decide_eq_true (by cfomega : (2 * e + 1) % 3 ≠ 2), decide_eq_true (by cfomega : e % 3 ≠ 2)]
  · rw [decide_eq_false (by cfomega : ¬ ((2 * e + 1) % 3 ≠ 2)), decide_eq_false (by cfomega : ¬ (e % 3 ≠ 2))]

theorem decide_mod3_even_succ (e : Nat) :
    bxor (decide ((e + 1) % 3 ≠ 2)) (decide (e % 3 ≠ 2)) = decide ((2 * e + 2) % 3 ≠ 2) := by
  have h3 : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by cfomega
  rcases h3 with h | h | h
  · rw [decide_eq_true (by cfomega : (e + 1) % 3 ≠ 2), decide_eq_true (by cfomega : e % 3 ≠ 2),
      decide_eq_false (by cfomega : ¬ ((2 * e + 2) % 3 ≠ 2))]
    rfl
  · rw [decide_eq_false (by cfomega : ¬ ((e + 1) % 3 ≠ 2)), decide_eq_true (by cfomega : e % 3 ≠ 2),
      decide_eq_true (by cfomega : (2 * e + 2) % 3 ≠ 2)]
    rfl
  · rw [decide_eq_true (by cfomega : (e + 1) % 3 ≠ 2), decide_eq_false (by cfomega : ¬ (e % 3 ≠ 2)),
      decide_eq_true (by cfomega : (2 * e + 2) % 3 ≠ 2)]
    rfl

/-- **The row `2^j - 1` is `1/q = 110110...` below degree `2^j`.** -/
theorem trinomialParity_twopow_pred (j d : Nat) (hd : d < twopow j) :
    trinomialParity (twopow j - 1) d = decide (d % 3 ≠ 2) := by
  induction j generalizing d with
  | zero =>
    have h0 : twopow 0 = 1 := rfl
    have hd0 : d = 0 := by cfomega
    subst hd0
    rfl
  | succ j ih =>
    have h1 : twopow (j + 1) = twopow j + twopow j := twopow_succ j
    have hpos := Rule30UOR.Scale.twopow_pos j
    rw [show twopow (j + 1) - 1 = 2 * (twopow j - 1) + 1 by cfomega]
    cases d with
    | zero =>
      rw [trinomialParity_odd_zero, ih 0 hpos]
    | succ d' =>
      rcases Nat.mod_two_eq_zero_or_one d' with hd2 | hd2
      · obtain ⟨e, rfl⟩ : ∃ e, d' = 2 * e := ⟨d' / 2, by cfomega⟩
        rw [trinomialParity_odd_odd, ih e (by cfomega), decide_mod3_odd]
      · obtain ⟨e, rfl⟩ : ∃ e, d' = 2 * e + 1 := ⟨d' / 2, by cfomega⟩
        rw [show 2 * e + 1 + 1 = 2 * e + 2 by cfomega, trinomialParity_odd_even_succ,
          ih (e + 1) (by cfomega), ih e (by cfomega), decide_mod3_even_succ]

/-- **The seed kernel is 3-periodic**: `K_0 = 1/q = (1 + X)/(1 + X^3) = 110110...`. -/
theorem stableKernel_zero (d : Nat) : stableKernel 0 d = decide (d % 3 ≠ 2) := by
  have hge := twopow_ge_succ (d + 1)
  rw [← trinomialParity_eq_stableKernel (d + 1) 0 d (by cfomega) (by cfomega), Nat.sub_zero,
    trinomialParity_twopow_pred (d + 1) d (by cfomega)]

/-! ## The dyadic column through the stable kernel -/

/-- Convolution of the bits of `y` (fuel `f ≥ y`) with the stable kernel of row `m`, read at `t`. -/
def stableConvFuel (m : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | f + 1, y, t =>
    if y = 0 then false
    else bxor (if y % 2 = 1 then stableKernel m t else false)
      (if 1 ≤ t then stableConvFuel m f (y / 2) (t - 1) else false)

/-- Convolution of the bits of `y` with the stable kernel of row `m`, read at `t`. -/
def stableConv (m y t : Nat) : Bool := stableConvFuel m y y t

/-- Below `2^j`, the trinomial convolution with row `2^j - 1 - n` is the stable convolution of row `n`. -/
theorem convFuel_eq_stableConvFuel (j n : Nat) (hn : n < twopow j) :
    ∀ f y t, t < twopow j → convFuel (twopow j - 1 - n) f y t = stableConvFuel n f y t := by
  intro f
  induction f with
  | zero => intro y t _; rfl
  | succ f ih =>
    intro y t ht
    show (if y = 0 then false
        else bxor (if y % 2 = 1 then trinomialParity (twopow j - 1 - n) t else false)
          (if 1 ≤ t then convFuel (twopow j - 1 - n) f (y / 2) (t - 1) else false)) =
      (if y = 0 then false
        else bxor (if y % 2 = 1 then stableKernel n t else false)
          (if 1 ≤ t then stableConvFuel n f (y / 2) (t - 1) else false))
    rw [trinomialParity_eq_stableKernel j n t hn ht, ih (y / 2) (t - 1) (by cfomega)]

theorem conv_eq_stableConv (j n y t : Nat) (hn : n < twopow j) (ht : t < twopow j) :
    conv (twopow j - 1 - n) y t = stableConv n y t :=
  convFuel_eq_stableConvFuel j n hn y y t ht

/-- Shifting the source by one shifts the read position by one. -/
theorem conv_shiftLeft_one (k y t : Nat) (ht : 1 ≤ t) : conv k (y <<< 1) t = conv k y (t - 1) := by
  rw [← testBit_phiLinearPow_conv, ← testBit_phiLinearPow_conv, phiLinearPow_shiftLeft,
    Nat.testBit_shiftLeft, decide_eq_true (by cfomega : t ≥ 1), Bool.true_and]

/-- **The dyadic readout**: the XOR over the rows `n < N` of the interior carries of row `n`
convolved with the stable kernel `K_n`, read at `2^j - 1`. -/
def stableFormula (j : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => bxor (stableFormula j n) (stableConv n (interior n) (twopow j - 1))

theorem interiorFormula_twopow_eq_stableFormula (j : Nat) :
    ∀ n, n ≤ twopow j → interiorFormula (twopow j) n = stableFormula j n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    show bxor (interiorFormula (twopow j) n) (conv (twopow j - 1 - n) (interior n <<< 1) (twopow j)) =
      bxor (stableFormula j n) (stableConv n (interior n) (twopow j - 1))
    rw [ih (by cfomega), conv_shiftLeft_one _ _ _ (Rule30UOR.Scale.twopow_pos j),
      conv_eq_stableConv j n (interior n) (twopow j - 1) (by cfomega)
        (by have := Rule30UOR.Scale.twopow_pos j; cfomega)]

/-- The dyadic times `2^j`, `j ≥ 1`, are even. -/
theorem timeParity_twopow (j : Nat) (hj : 1 ≤ j) : timeParity (twopow j) = false := by
  cases j with
  | zero => exact absurd hj (by decide)
  | succ j =>
    unfold timeParity
    rw [twopow_succ]
    exact decide_eq_false (by cfomega)

/-- **The dyadic column reads the bulk carries through the stable kernel**:
`center (2^j) = ¬ stableFormula j (2^j)` for `j ≥ 1`. -/
theorem center_twopow_eq_stableFormula (j : Nat) (hj : 1 ≤ j) :
    center (twopow j) = !(stableFormula j (twopow j)) := by
  rw [center_eq_not_timeParity_xor_interior, timeParity_twopow j hj, interiorDiagonal_eq_formula,
    interiorFormula_twopow_eq_stableFormula j (twopow j) (Nat.le_refl _)]
  cases stableFormula j (twopow j) <;> rfl

/-! ## Problem 1 through the stable formula -/

/-- The stable formula at the dyadic times has period `d` from `K`. -/
def StableFormulaPeriodic (K d : Nat) : Prop :=
  ∀ j, K ≤ j → stableFormula (j + d) (twopow (j + d)) = stableFormula j (twopow j)

/-- The stable formula at the dyadic times is not eventually periodic. -/
def StableFormulaAperiodic : Prop := ∀ K d, 0 < d → ¬ StableFormulaPeriodic K d

/-- **The dyadic column is aperiodic iff the stable formula is.** -/
theorem dyadicColumnAperiodic_iff_stable : DyadicColumnAperiodic ↔ StableFormulaAperiodic := by
  constructor
  · intro h K d hd hs
    apply h (K + 1) d hd
    intro j hj
    rw [Nat.mul_one, Nat.mul_one, center_twopow_eq_stableFormula (j + d) (by cfomega),
      center_twopow_eq_stableFormula j (by cfomega), hs j (by cfomega)]
  · intro h K d hd hp
    apply h (K + 1) d hd
    intro j hj
    have hc := hp j (by cfomega)
    rw [Nat.mul_one, Nat.mul_one, center_twopow_eq_stableFormula (j + d) (by cfomega),
      center_twopow_eq_stableFormula j (by cfomega)] at hc
    exact Bool.not_inj hc

/-- **Problem 1 from the aperiodicity of the stable formula.** -/
theorem problem1_of_stableFormulaAperiodic (h : StableFormulaAperiodic) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_dyadic_column_aperiodic (dyadicColumnAperiodic_iff_stable.2 h)

end Rule30UOR.StableKernel
