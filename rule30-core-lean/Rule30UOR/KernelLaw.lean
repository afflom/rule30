module
public import Rule30UOR.DyadicRow
public import Rule30UOR.Band
public import Rule30UOR.Intersection
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The freezing law of the kernel subsequences

For `m < 2^k`, `r < 2^k` and `u ≥ 1` the row term of row `m` at time
`t = 2^k u + r` is bit `t` of `q^(2^k (u-1)) · Y` with
`Y = q^(2^k + r - 1 - m) · (interior m <<< 1)`. The power `q^(2^k s)` is the
Frobenius spread of `q^s` to stride `2^k`, so the bit is the convolution of
the coefficients `trinomialParity s i` with the blocks of `Y` of width `2^k`,
read at block `u`. `Y` lives below bit `2^(k+1) + 2r < 4 · 2^k`, so only the
blocks `0, 1, 2` of `Y` meet the kernel, at the coefficients `s + 1`, `s`,
`s − 1` of `q^s`: `trailingParity s`, `1`, `trailingParity s`. The law:

`rowTerm (2^k u + r) m = frozen k r m ⊕ (trailingParity (u − 1) ∧ second k r m)`,

with `frozen k r m = bit (2^k + r) of Y` (the term at `u = 1`, frozen for ever)
and `second k r m = bit (2^(k+1) + r) of Y ⊕ bit r of Y` (the second-order
correction, driven by the ruler `trailingParity`). Summed over the rows
`m < 2^k` this gives the kernel subsequence `kernelSeq k r u = center (2^k u + r)`
as the complement of the time parity of `r`, a frozen prefix, the ruler
times a second prefix, and the late tail of the rows `m ≥ 2^k`. -/

@[expose] public section

namespace Rule30UOR.KernelLaw

open Rule30UOR.Core
open Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Automatic
  Rule30UOR.StableKernel Rule30UOR.DyadicRow Rule30UOR.Band

/-! ## Boolean bookkeeping -/

theorem bxor_assoc (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `⊕_{m<n} (a ∧ f m) = a ∧ ⊕_{m<n} f m`. -/
theorem xorBelow_and (a : Bool) (f : Nat → Bool) (n : Nat) :
    xorBelow (fun m => a && f m) n = (a && xorBelow f n) := by
  cases a with
  | true =>
    rw [Bool.true_and]
    exact xorBelow_congr _ _ n (fun m _ => Bool.true_and (f m))
  | false =>
    rw [Bool.false_and]
    exact (xorBelow_congr _ _ n (fun m _ => Bool.false_and (f m))).trans (xorBelow_false n)

/-! ## The stride-`2^k` powers of `q` -/

theorem phiScale_eq_phiLin (k y : Nat) : phiScale k y = phiLin (twopow k) y := by
  show (y ^^^ (y <<< twopow k)) ^^^ (y <<< (twopow k + twopow k)) =
    (y ^^^ (y <<< twopow k)) ^^^ (y <<< (2 * twopow k))
  rw [show 2 * twopow k = twopow k + twopow k by cfomega]

/-- `q^(2^k s) = (1 + X^(2^k) + X^(2^(k+1)))^s`: the Frobenius spread of `q^s`. -/
theorem phiLinearPow_twopow_mul (k : Nat) : ∀ s y, phiLinearPow (twopow k * s) y = phiLinPow (twopow k) s y
  | 0, y => by rw [Nat.mul_zero]; rfl
  | s + 1, y => by
    rw [Nat.mul_add, Nat.mul_one, show twopow k * s + twopow k = twopow k + twopow k * s from Nat.add_comm _ _,
      Rule30UOR.Interfaces.phiLinearPow_add, Rule30UOR.Interfaces.phiLinear_freshman, phiScale_eq_phiLin,
      phiLinearPow_twopow_mul k s y]
    rfl

theorem phiLinPow_xor (s n a b : Nat) : phiLinPow s n (a ^^^ b) = phiLinPow s n a ^^^ phiLinPow s n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show phiLin s (phiLinPow s n (a ^^^ b)) = phiLin s (phiLinPow s n a) ^^^ phiLin s (phiLinPow s n b)
    rw [ih, phiLin_xor]

theorem phiLinPow_shiftLeft (s n c y : Nat) : phiLinPow s n (y <<< c) = phiLinPow s n y <<< c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show phiLin s (phiLinPow s n (y <<< c)) = phiLin s (phiLinPow s n y) <<< c
    rw [ih, phiLin_shiftLeft]

theorem phiLin_zero (s : Nat) : phiLin s 0 = 0 := by
  unfold phiLin
  rw [Nat.zero_shiftLeft, Nat.zero_shiftLeft, Nat.xor_zero, Nat.xor_zero]

theorem phiLinPow_zero_right (s n : Nat) : phiLinPow s n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show phiLin s (phiLinPow s n 0) = 0
    rw [ih, phiLin_zero]

/-! ## Three coefficients of `q^s` -/

/-- Coefficient `s + 1` of `q^s` is the ruler `trailingParity s`. -/
theorem trinomialParity_succ_self (s : Nat) : trinomialParity s (s + 1) = trailingParity s := by
  rw [← testBit_phiLinPow_eq_trinomialParity, linear_above_center]

/-- Coefficient `s − 1` of `q^s` is the ruler `trailingParity s`, for `s ≥ 1`. -/
theorem trinomialParity_pred_self (s : Nat) (hs : 1 ≤ s) : trinomialParity s (s - 1) = trailingParity s := by
  rw [← testBit_phiLinPow_eq_trinomialParity, linear_below_center s hs]

/-! ## The spread of one block -/

/-- A block `V < 2^(2^k)` under `q^(2^k s)` is spread by the coefficients of `q^s`:
bit `2^k i + r` of the image is `trinomialParity s i ∧ bit r of V`. -/
theorem phiLinPow_block_testBit (k : Nat) : ∀ s V i r, V < 2 ^ twopow k → r < twopow k →
    (phiLinPow (twopow k) s V).testBit (twopow k * i + r) = (trinomialParity s i && V.testBit r)
  | 0, V, i, r, hV, hr => by
    show V.testBit (twopow k * i + r) = (trinomialParity 0 i && V.testBit r)
    rw [trinomialParity_zero]
    cases i with
    | zero => rw [Nat.mul_zero, Nat.zero_add]; rfl
    | succ i =>
      rw [decide_eq_false (by cfomega), Bool.false_and]
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hV (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_add, Nat.mul_one]; cfomega))
  | s + 1, V, i, r, hV, hr => by
    show (phiLin (twopow k) (phiLinPow (twopow k) s V)).testBit (twopow k * i + r) = _
    rw [testBit_phiLin, phiLinPow_block_testBit k s V i r hV hr]
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, decide_eq_false (by cfomega : ¬ (r ≥ twopow k)),
        decide_eq_false (by cfomega : ¬ (r ≥ 2 * twopow k)), Rule30UOR.StableKernel.trinomialParity_row_succ_zero]
      cases trinomialParity s 0 <;> cases V.testBit r <;> rfl
    | succ i =>
      rw [Nat.mul_add, Nat.mul_one,
        show twopow k * i + twopow k + r - twopow k = twopow k * i + r by cfomega,
        decide_eq_true (by cfomega : twopow k * i + twopow k + r ≥ twopow k),
        phiLinPow_block_testBit k s V i r hV hr]
      cases i with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add]
        rw [decide_eq_false (by cfomega : ¬ (twopow k + r ≥ 2 * twopow k)), Rule30UOR.StableKernel.trinomialParity_row_succ_one]
        cases trinomialParity s 1 <;> cases trinomialParity s 0 <;> cases V.testBit r <;> rfl
      | succ i =>
        rw [Nat.mul_add, Nat.mul_one,
          show twopow k * i + twopow k + twopow k + r - 2 * twopow k = twopow k * i + r by cfomega,
          decide_eq_true (by cfomega : twopow k * i + twopow k + twopow k + r ≥ 2 * twopow k),
          phiLinPow_block_testBit k s V i r hV hr, show i + 1 + 1 = i + 2 by cfomega, Rule30UOR.StableKernel.trinomialParity_row_succ]
        cases trinomialParity s (i + 2) <;> cases trinomialParity s (i + 1) <;> cases trinomialParity s i <;>
          cases V.testBit r <;> rfl

/-! ## Peeling the low block -/

theorem split_low_high (n Y : Nat) : Y = (Y % 2 ^ n) ^^^ ((Y >>> n) <<< n) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge b n with h | h
  · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ (b ≥ n)), Bool.true_and, Bool.false_and, Bool.xor_false]
  · rw [decide_eq_false (by cfomega : ¬ (b < n)), decide_eq_true h, Bool.false_and, Bool.true_and, Bool.false_xor,
      show n + (b - n) = b by cfomega]

theorem phiLinPow_split (k s Y : Nat) :
    phiLinPow (twopow k) s Y =
      phiLinPow (twopow k) s (Y % 2 ^ twopow k) ^^^ (phiLinPow (twopow k) s (Y >>> twopow k) <<< twopow k) := by
  rw [← phiLinPow_shiftLeft, ← phiLinPow_xor, ← split_low_high]

/-- Bit `r < 2^k` of `q^(2^k s) · Y` is bit `r` of `Y`. -/
theorem block_testBit_zero (k s Y r : Nat) (hr : r < twopow k) :
    (phiLinPow (twopow k) s Y).testBit r = Y.testBit r := by
  rw [phiLinPow_split, Nat.testBit_xor, Nat.testBit_shiftLeft, decide_eq_false (by cfomega : ¬ (r ≥ twopow k)),
    Bool.false_and, Bool.xor_false]
  have h := phiLinPow_block_testBit k s (Y % 2 ^ twopow k) 0 r (Nat.mod_lt _ (Nat.two_pow_pos _)) hr
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [h, Rule30UOR.Intersection.trinomialParity_zero_right, Bool.true_and, Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]

/-- Bit `2^k (i+1) + r` of `q^(2^k s) · Y`: the low block of `Y` at coefficient `i + 1`,
plus the same reading of `Y >>> 2^k` one block lower. -/
theorem block_testBit_succ (k s Y i r : Nat) (hr : r < twopow k) :
    (phiLinPow (twopow k) s Y).testBit (twopow k * (i + 1) + r) =
      bxor (trinomialParity s (i + 1) && Y.testBit r)
        ((phiLinPow (twopow k) s (Y >>> twopow k)).testBit (twopow k * i + r)) := by
  rw [phiLinPow_split, Nat.testBit_xor, Nat.testBit_shiftLeft,
    phiLinPow_block_testBit k s _ (i + 1) r (Nat.mod_lt _ (Nat.two_pow_pos _)) hr, Nat.testBit_mod_two_pow,
    decide_eq_true hr, Bool.true_and, Nat.mul_add, Nat.mul_one,
    decide_eq_true (by cfomega : twopow k * i + twopow k + r ≥ twopow k), Bool.true_and,
    show twopow k * i + twopow k + r - twopow k = twopow k * i + r by cfomega, Rule30UOR.Scale.bxor_eq]

/-- Unrolling `j` blocks: bit `2^k (i + j) + r` of `q^(2^k s) · Y` is the XOR over the blocks
`l < j` of `Y` at the coefficients `i + j − l`, plus the reading of `Y >>> 2^k j` at block `i`. -/
theorem block_testBit_unroll (k s r : Nat) (hr : r < twopow k) : ∀ j Y i,
    (phiLinPow (twopow k) s Y).testBit (twopow k * (i + j) + r) =
      bxor (xorBelow (fun l => trinomialParity s (i + j - l) && Y.testBit (twopow k * l + r)) j)
        ((phiLinPow (twopow k) s (Y >>> (twopow k * j))).testBit (twopow k * i + r))
  | 0, Y, i => by
    rw [Nat.add_zero, Nat.mul_zero, Nat.shiftRight_zero]
    show _ = bxor false _
    cases (phiLinPow (twopow k) s Y).testBit (twopow k * i + r) <;> rfl
  | j + 1, Y, i => by
    rw [show i + (j + 1) = i + j + 1 by cfomega, block_testBit_succ k s Y (i + j) r hr,
      block_testBit_unroll k s r hr j (Y >>> twopow k) i, xorBelow_front]
    show bxor (trinomialParity s (i + j + 1) && Y.testBit r)
        (bxor (xorBelow (fun l => trinomialParity s (i + j - l) && (Y >>> twopow k).testBit (twopow k * l + r)) j)
          ((phiLinPow (twopow k) s (Y >>> twopow k >>> (twopow k * j))).testBit (twopow k * i + r))) =
      bxor (bxor (trinomialParity s (i + j + 1 - 0) && Y.testBit (twopow k * 0 + r))
        (xorBelow (fun l => trinomialParity s (i + j + 1 - (l + 1)) && Y.testBit (twopow k * (l + 1) + r)) j))
        ((phiLinPow (twopow k) s (Y >>> (twopow k * (j + 1)))).testBit (twopow k * i + r))
    have e2 : xorBelow (fun l => trinomialParity s (i + j + 1 - (l + 1)) && Y.testBit (twopow k * (l + 1) + r)) j =
        xorBelow (fun l => trinomialParity s (i + j - l) && (Y >>> twopow k).testBit (twopow k * l + r)) j := by
      apply xorBelow_congr
      intro l _
      rw [Nat.testBit_shiftRight, show i + j + 1 - (l + 1) = i + j - l by cfomega, Nat.mul_add, Nat.mul_one,
        show twopow k * l + twopow k + r = twopow k + (twopow k * l + r) by cfomega]
    have e3 : Y >>> twopow k >>> (twopow k * j) = Y >>> (twopow k * (j + 1)) := by
      rw [← Nat.shiftRight_add, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [Nat.sub_zero, Nat.mul_zero, Nat.zero_add, e2, e3]
    exact (bxor_assoc _ _ _).symm

/-! ## The shifted row and its three frozen bits -/

/-- `Y = q^(2^k + r − 1 − m) · (interior m <<< 1)`: row `m` propagated to time `2^k + r`. -/
def shiftedRow (k r m : Nat) : Nat := phiLinearPow (twopow k + r - 1 - m) (interior m <<< 1)

/-- The frozen term of row `m` on the class `r` at scale `k`: bit `2^k + r` of `Y`. -/
def frozen (k r m : Nat) : Bool := Rule30UOR.WittDefect.rowBit (shiftedRow k r m) (twopow k + r)

/-- The second-order term: bit `2^(k+1) + r` of `Y` against bit `r` of `Y`. -/
def second (k r m : Nat) : Bool :=
  bxor (Rule30UOR.WittDefect.rowBit (shiftedRow k r m) (twopow (k + 1) + r))
    (Rule30UOR.WittDefect.rowBit (shiftedRow k r m) r)

/-- `Y` lives below bit `2^(k+1) + 2r`. -/
theorem shiftedRow_lt (k r m : Nat) (hm : m < twopow k) : shiftedRow k r m < 2 ^ (twopow (k + 1) + 2 * r) := by
  unfold shiftedRow
  have hw : interior m <<< 1 < 2 ^ (2 * m + 1 + 1) := shiftLeft_lt_two_pow _ _ 1 (interior_lt m)
  have h := phiLinearPow_lt_of_lt (twopow k + r - 1 - m) _ _ hw
  rw [show 2 * (twopow k + r - 1 - m) + (2 * m + 1 + 1) = twopow (k + 1) + 2 * r by rw [twopow_succ]; cfomega] at h
  exact h

theorem rowTerm_eq_block (k s r m : Nat) (hm : m < twopow k) :
    rowTerm (twopow k * (s + 1) + r) m =
      (phiLinPow (twopow k) s (shiftedRow k r m)).testBit (twopow k * (s + 1) + r) := by
  unfold rowTerm Rule30UOR.WittDefect.rowBit shiftedRow
  rw [show twopow k * (s + 1) + r - 1 - m = twopow k * s + (twopow k + r - 1 - m) by
      rw [Nat.mul_add, Nat.mul_one]; cfomega,
    Rule30UOR.Interfaces.phiLinearPow_add, phiLinearPow_twopow_mul]

/-- **The freezing law.** For `m < 2^k`, `r < 2^k`, `u ≥ 1`:
`rowTerm (2^k u + r) m = frozen k r m ⊕ (trailingParity (u − 1) ∧ second k r m)`. -/
theorem rowTerm_kernel_law (k r u m : Nat) (hm : m < twopow k) (hr : r < twopow k) (hu : 1 ≤ u) :
    rowTerm (twopow k * u + r) m = bxor (frozen k r m) (trailingParity (u - 1) && second k r m) := by
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by cfomega⟩
  rw [Nat.add_sub_cancel, rowTerm_eq_block k s r m hm]
  have hY := shiftedRow_lt k r m hm
  have hun := block_testBit_unroll k s r hr (s + 1) (shiftedRow k r m) 0
  rw [Nat.zero_add, Nat.mul_zero, Nat.zero_add, block_testBit_zero k s _ r hr, Nat.testBit_shiftRight] at hun
  rw [hun]
  unfold frozen second Rule30UOR.WittDefect.rowBit
  have h3 : ∀ l, 3 ≤ l → (shiftedRow k r m).testBit (twopow k * l + r) = false := by
    intro l hl
    apply Nat.testBit_lt_two_pow
    refine Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by decide) ?_)
    have : twopow k * 3 ≤ twopow k * l := Nat.mul_le_mul_left _ hl
    rw [twopow_succ]
    cfomega
  cases s with
  | zero =>
    show bxor (bxor false (trinomialParity 0 (0 + 1 - 0) && (shiftedRow k r m).testBit (twopow k * 0 + r)))
        ((shiftedRow k r m).testBit (twopow k * (0 + 1) + r)) = _
    rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.mul_one, Nat.sub_zero, trinomialParity_zero]
    cases (shiftedRow k r m).testBit (twopow k + r) <;> rfl
  | succ s =>
    cases s with
    | zero =>
      show bxor (bxor (bxor false (trinomialParity 1 (0 + 1 + 1 - 0) && (shiftedRow k r m).testBit (twopow k * 0 + r)))
            (trinomialParity 1 (0 + 1 + 1 - 1) && (shiftedRow k r m).testBit (twopow k * 1 + r)))
          ((shiftedRow k r m).testBit (twopow k * (0 + 1 + 1) + r)) = _
      rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.mul_one, Nat.sub_zero, Nat.add_sub_cancel,
        trinomialParity_succ_self 1, trinomialParity_central, twopow_succ,
        show twopow k * (1 + 1) + r = twopow k + twopow k + r by cfomega]
      cases (shiftedRow k r m).testBit r <;> cases (shiftedRow k r m).testBit (twopow k + r) <;>
        cases (shiftedRow k r m).testBit (twopow k + twopow k + r) <;> rfl
    | succ s =>
      rw [show s + 1 + 1 + 1 = 3 + s by cfomega, Rule30UOR.Antidiagonal.xorBelow_split]
      show bxor (bxor (bxor (bxor (bxor false
              (trinomialParity (s + 1 + 1) (3 + s - 0) && (shiftedRow k r m).testBit (twopow k * 0 + r)))
              (trinomialParity (s + 1 + 1) (3 + s - 1) && (shiftedRow k r m).testBit (twopow k * 1 + r)))
              (trinomialParity (s + 1 + 1) (3 + s - 2) && (shiftedRow k r m).testBit (twopow k * 2 + r)))
            (xorBelow (fun i => trinomialParity (s + 1 + 1) (3 + s - (3 + i)) &&
              (shiftedRow k r m).testBit (twopow k * (3 + i) + r)) s))
          ((shiftedRow k r m).testBit (twopow k * (3 + s) + r)) = _
      have htail : xorBelow (fun i => trinomialParity (s + 1 + 1) (3 + s - (3 + i)) &&
          (shiftedRow k r m).testBit (twopow k * (3 + i) + r)) s = false := by
        refine (xorBelow_congr _ (fun _ => false) s (fun i _ => ?_)).trans (xorBelow_false s)
        rw [h3 (3 + i) (by cfomega), Bool.and_false]
      rw [htail, h3 (3 + s) (by cfomega), Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.sub_zero,
        show 3 + s - 1 = s + 1 + 1 by cfomega, show 3 + s - 2 = s + 1 + 1 - 1 by cfomega,
        show 3 + s = s + 1 + 1 + 1 by cfomega, trinomialParity_succ_self, trinomialParity_central,
        trinomialParity_pred_self (s + 1 + 1) (by cfomega), twopow_succ,
        show twopow k * 2 + r = twopow k + twopow k + r by cfomega]
      cases trailingParity (s + 1 + 1) <;> cases (shiftedRow k r m).testBit r <;>
        cases (shiftedRow k r m).testBit (twopow k + r) <;>
        cases (shiftedRow k r m).testBit (twopow k + twopow k + r) <;> rfl

/-! ## The kernel subsequences -/

/-- The frozen prefix: `⊕_{m < 2^k} frozen k r m`. -/
def frozenPrefix (k r : Nat) : Bool := xorBelow (fun m => frozen k r m) (twopow k)

/-- The second-order prefix: `⊕_{m < 2^k} second k r m`. -/
def secondPrefix (k r : Nat) : Bool := xorBelow (fun m => second k r m) (twopow k)

/-- The late tail: the row terms of the rows `2^k ≤ m < 2^k u + r` at time `2^k u + r`. -/
def lateTail (k r u : Nat) : Bool :=
  xorBelow (fun i => rowTerm (twopow k * u + r) (twopow k + i)) (twopow k * u + r - twopow k)

/-- **The interior formula on the class `r` at scale `k`.** -/
theorem interiorFormula_kernel (k r u : Nat) (hr : r < twopow k) (hu : 1 ≤ u) :
    interiorFormula (twopow k * u + r) (twopow k * u + r) =
      bxor (bxor (frozenPrefix k r) (trailingParity (u - 1) && secondPrefix k r)) (lateTail k r u) := by
  have hle : twopow k ≤ twopow k * u := Nat.le_mul_of_pos_right _ hu
  have hsplit := Rule30UOR.Antidiagonal.xorBelow_split (rowTerm (twopow k * u + r)) (twopow k) (twopow k * u + r - twopow k)
  rw [show twopow k + (twopow k * u + r - twopow k) = twopow k * u + r by cfomega] at hsplit
  rw [interiorFormula_eq_xorBelow_rowTerm, hsplit,
    xorBelow_congr (rowTerm (twopow k * u + r))
      (fun m => bxor (frozen k r m) (trailingParity (u - 1) && second k r m)) (twopow k)
      (fun m hm => rowTerm_kernel_law k r u m hm hr hu),
    xorBelow_bxor, xorBelow_and]
  rfl

/-- The time parity on the class `r` at scale `k ≥ 1` is the parity of `r`. -/
theorem timeParity_twopow_mul_add (k u r : Nat) (hk : 1 ≤ k) : timeParity (twopow k * u + r) = timeParity r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by cfomega⟩
  rw [twopow_succ, Nat.add_mul, show twopow j * u + twopow j * u + r = r + 2 * (twopow j * u) by cfomega,
    timeParity_add_two_mul]

/-- **The kernel subsequence, explicitly**: for `k ≥ 1`, `r < 2^k`, `u ≥ 1`,
`center (2^k u + r) = ¬(timeParity r ⊕ frozenPrefix k r ⊕ (trailingParity (u−1) ∧ secondPrefix k r) ⊕ lateTail k r u)`. -/
theorem kernelSeq_explicit (k r u : Nat) (hr : r < twopow k) (hu : 1 ≤ u) (hk : 1 ≤ k) :
    Rule30UOR.Automatic.kernelSeq k r u =
      !(bxor (timeParity r)
        (bxor (bxor (frozenPrefix k r) (trailingParity (u - 1) && secondPrefix k r)) (lateTail k r u))) := by
  unfold Rule30UOR.Automatic.kernelSeq
  rw [center_eq_not_timeParity_xor_interior, interiorDiagonal_eq_formula, interiorFormula_kernel k r u hr hu,
    timeParity_twopow_mul_add k u r hk]

/-! ## The class `r = 0`: the dyadic law at every multiple of `2^k` -/

theorem shiftedRow_testBit_zero (k r m : Nat) : (shiftedRow k r m).testBit 0 = false := by
  unfold shiftedRow
  rw [Rule30UOR.WittDefect.q_power_bit_zero, Nat.testBit_shiftLeft]
  rfl

theorem second_zero (k m : Nat) (hm : m < twopow k) : second k 0 m = false := by
  unfold second Rule30UOR.WittDefect.rowBit
  have h2 : (shiftedRow k 0 m).testBit (twopow (k + 1) + 0) = false := by
    rw [Nat.add_zero]
    apply Nat.testBit_lt_two_pow
    have := shiftedRow_lt k 0 m hm
    rw [Nat.mul_zero, Nat.add_zero] at this
    exact this
  rw [shiftedRow_testBit_zero, h2]
  rfl

theorem frozen_zero (k m : Nat) (hm : m < twopow k) : frozen k 0 m = dyadicRow m := by
  rw [← rowTerm_twopow_eq_dyadicRow k m hm]
  unfold frozen shiftedRow rowTerm
  rw [Nat.add_zero]

/-- **The dyadic law at every multiple of `2^k`**: `rowTerm (2^k u) m = dyadicRow m` for `m < 2^k`, `u ≥ 1`. -/
theorem rowTerm_twopow_mul (k u m : Nat) (hm : m < twopow k) (hu : 1 ≤ u) :
    rowTerm (twopow k * u) m = dyadicRow m := by
  have h := rowTerm_kernel_law k 0 u m hm (Rule30UOR.Scale.twopow_pos k) hu
  rw [Nat.add_zero, second_zero k m hm, frozen_zero k m hm, Bool.and_false] at h
  rw [h]
  cases dyadicRow m <;> rfl

theorem frozenPrefix_zero (k : Nat) : frozenPrefix k 0 = xorBelow dyadicRow (twopow k) :=
  xorBelow_congr _ _ _ (fun m hm => frozen_zero k m hm)

theorem secondPrefix_zero (k : Nat) : secondPrefix k 0 = false :=
  (xorBelow_congr _ (fun _ => false) _ (fun m hm => second_zero k m hm)).trans (xorBelow_false _)

/-- **The center at the multiples of `2^k`**: `center (2^k u) = center (2^k) ⊕ lateTail k 0 u` for `k ≥ 1`, `u ≥ 1`. -/
theorem center_twopow_mul (k u : Nat) (hk : 1 ≤ k) (hu : 1 ≤ u) :
    center (twopow k * u) = bxor (center (twopow k)) (lateTail k 0 u) := by
  have h := kernelSeq_explicit k 0 u (Rule30UOR.Scale.twopow_pos k) hu hk
  unfold Rule30UOR.Automatic.kernelSeq at h
  rw [Nat.add_zero, frozenPrefix_zero, secondPrefix_zero] at h
  rw [h, center_twopow_eq_prefix k hk]
  cases xorBelow dyadicRow (twopow k) <;> cases lateTail k 0 u <;> cases trailingParity (u - 1) <;> rfl

/-! ## The class `r = 1`: no second-order term -/

theorem lt_two_pow_of_testBit (x n : Nat) (hx : x < 2 ^ (n + 1)) (hb : x.testBit n = false) : x < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rcases Nat.lt_or_ge n i with h | h
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h))
  · rw [show i = n by cfomega]
    exact hb

/-- For `m ≥ 1` the interior carries live below bit `2m`. -/
theorem interior_lt_of_pos (m : Nat) (hm : 1 ≤ m) : interior m < 2 ^ (2 * m) :=
  lt_two_pow_of_testBit _ _ (interior_lt m) (interior_testBit_left_edge m hm)

theorem phiLinearPow_testBit_one (n y : Nat) (h0 : y.testBit 0 = false) :
    (phiLinearPow n y).testBit 1 = y.testBit 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [phiLinearPow_step]
    show ((phiLinearPow n y ^^^ (phiLinearPow n y <<< 1)) ^^^ (phiLinearPow n y <<< 2)).testBit 1 = y.testBit 1
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, ih,
      Rule30UOR.WittDefect.q_power_bit_zero, h0]
    cases y.testBit 1 <;> rfl

theorem interior_zero : interior 0 = 1 := by decide

theorem second_one_zero (k : Nat) (hk : 1 ≤ k) : second k 1 0 = false := by
  unfold second Rule30UOR.WittDefect.rowBit shiftedRow
  rw [Nat.add_sub_cancel, Nat.sub_zero, interior_zero, Rule30UOR.Interfaces.phiLinear_freshman]
  have hA : phiScale k (1 <<< 1) = (2 ^^^ (2 <<< twopow k)) ^^^ (2 <<< (twopow k + twopow k)) := rfl
  have h2 : 2 ≤ twopow k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by cfomega⟩
    have := Rule30UOR.Scale.twopow_pos j
    rw [twopow_succ]; cfomega
  have hb1 : ((2 ^^^ (2 <<< twopow k)) ^^^ (2 <<< (twopow k + twopow k))).testBit 1 = true := by
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      decide_eq_false (by cfomega : ¬ (1 ≥ twopow k)), decide_eq_false (by cfomega : ¬ (1 ≥ twopow k + twopow k)),
      Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false]
    rfl
  have hb2 : ((2 ^^^ (2 <<< twopow k)) ^^^ (2 <<< (twopow k + twopow k))).testBit (twopow (k + 1) + 1) = true := by
    rw [twopow_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      decide_eq_true (by cfomega : twopow k + twopow k + 1 ≥ twopow k),
      decide_eq_true (by cfomega : twopow k + twopow k + 1 ≥ twopow k + twopow k), Bool.true_and, Bool.true_and,
      show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow, Nat.testBit_two_pow, Nat.testBit_two_pow,
      decide_eq_false (by cfomega : ¬ (1 = twopow k + twopow k + 1)),
      decide_eq_false (by cfomega : ¬ (1 = twopow k + twopow k + 1 - twopow k)),
      decide_eq_true (by cfomega : 1 = twopow k + twopow k + 1 - (twopow k + twopow k))]
    rfl
  rw [hA, hb1, hb2]
  rfl

theorem second_one_pos (k m : Nat) (hm : m < twopow k) (hm1 : 1 ≤ m) : second k 1 m = false := by
  unfold second Rule30UOR.WittDefect.rowBit
  have h1 : (shiftedRow k 1 m).testBit 1 = false := by
    unfold shiftedRow
    rw [phiLinearPow_testBit_one _ _ (by rw [Nat.testBit_shiftLeft]; rfl), Nat.testBit_shiftLeft,
      interior_testBit_zero, decide_eq_false (by cfomega : ¬ (m = 0))]
    rfl
  have h2 : (shiftedRow k 1 m).testBit (twopow (k + 1) + 1) = false := by
    apply Nat.testBit_lt_two_pow
    unfold shiftedRow
    have hw : interior m <<< 1 < 2 ^ (2 * m + 1) := shiftLeft_lt_two_pow _ _ 1 (interior_lt_of_pos m hm1)
    have h := phiLinearPow_lt_of_lt (twopow k + 1 - 1 - m) _ _ hw
    rw [show 2 * (twopow k + 1 - 1 - m) + (2 * m + 1) = twopow (k + 1) + 1 by rw [twopow_succ]; cfomega] at h
    exact h
  rw [h1, h2]
  rfl

theorem second_one (k m : Nat) (hk : 1 ≤ k) (hm : m < twopow k) : second k 1 m = false := by
  rcases Nat.lt_or_ge m 1 with h | h
  · rw [show m = 0 by cfomega]
    exact second_one_zero k hk
  · exact second_one_pos k m hm h

theorem secondPrefix_one (k : Nat) (hk : 1 ≤ k) : secondPrefix k 1 = false :=
  (xorBelow_congr _ (fun _ => false) _ (fun m hm => second_one k m hk hm)).trans (xorBelow_false _)

/-- **The class `t ≡ 1 (mod 2^k)` has no second-order term**: for `k ≥ 1`, `u ≥ 1`,
`center (2^k u + 1) = center (2^k + 1) ⊕ lateTail k 1 1 ⊕ lateTail k 1 u`. -/
theorem center_twopow_mul_add_one (k u : Nat) (hk : 1 ≤ k) (hu : 1 ≤ u) :
    center (twopow k * u + 1) = bxor (center (twopow k + 1)) (bxor (lateTail k 1 1) (lateTail k 1 u)) := by
  have h2 : 1 < twopow k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by cfomega⟩
    have := Rule30UOR.Scale.twopow_pos j
    rw [twopow_succ]; cfomega
  have hu' := kernelSeq_explicit k 1 u h2 hu hk
  have h1 := kernelSeq_explicit k 1 1 h2 (Nat.le_refl 1) hk
  unfold Rule30UOR.Automatic.kernelSeq at hu' h1
  rw [secondPrefix_one k hk, Bool.and_false] at hu' h1
  rw [Nat.mul_one] at h1
  rw [hu', h1]
  cases timeParity 1 <;> cases frozenPrefix k 1 <;> cases lateTail k 1 1 <;> cases lateTail k 1 u <;> rfl

end Rule30UOR.KernelLaw
