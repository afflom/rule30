module
public import Rule30UOR.StableKernel
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Scale-free row terms of the dyadic column

The interior ledger at time `t` is the XOR over the rows `m < t` of the term
`rowTerm t m`: bit `t` of `q^(t-1-m) · (interior m <<< 1)`. For `m < 2^j` the
term of row `m` at time `2^(j+1)` is its term at time `2^j` (Frobenius:
`q^(2^(j+1)-1-m) = phiScale j (q^(2^j-1-m))`, and the row's cone keeps the
two shifted copies out of bit `2^(j+1)`). So every row `m` contributes one
fixed bit `dyadicRow m` to every dyadic time `2^j > m`, the dyadic column is
`center (2^j) = ¬ ⊕_{m < 2^j} dyadicRow m`, and its steps are the block parities
`blockParity j = ⊕_{2^j ≤ m < 2^(j+1)} dyadicRow m`, which are the late Witt
responses `wittRespBool (2^j) j`. -/

@[expose] public section

namespace Rule30UOR.DyadicRow

open Rule30UOR.Core
open Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Automatic
  Rule30UOR.StableKernel

/-! ## The row terms -/

/-- The interior-ledger term of row `m` read at the center at time `t`:
bit `t` of `q^(t-1-m) · (interior m <<< 1)`. -/
def rowTerm (t m : Nat) : Bool :=
  Rule30UOR.WittDefect.rowBit (phiLinearPow (t - 1 - m) (interior m <<< 1)) t

theorem rowTerm_eq_conv (t m : Nat) : rowTerm t m = conv (t - 1 - m) (interior m <<< 1) t :=
  testBit_phiLinearPow_conv _ _ _

/-- The interior formula is the XOR of the row terms. -/
theorem interiorFormula_eq_xorBelow_rowTerm (t n : Nat) :
    interiorFormula t n = xorBelow (rowTerm t) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show bxor (interiorFormula t n) (conv (t - 1 - n) (interior n <<< 1) t) =
      bxor (xorBelow (rowTerm t) n) (rowTerm t n)
    rw [ih, rowTerm_eq_conv]

/-! ## Width bounds -/

theorem shiftLeft_lt_two_pow (y n k : Nat) (hy : y < 2 ^ n) : y <<< k < 2 ^ (n + k) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos k)

/-- Row `t` lives below bit `2t + 1`. -/
theorem row_lt (t : Nat) : row t < 2 ^ (2 * t + 1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    show row t ^^^ ((row t <<< 1) ||| (row t <<< 2)) < 2 ^ (2 * (t + 1) + 1)
    have h0 : row t < 2 ^ (2 * (t + 1) + 1) :=
      Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by cfomega))
    have h1 : row t <<< 1 < 2 ^ (2 * (t + 1) + 1) :=
      Nat.lt_of_lt_of_le (shiftLeft_lt_two_pow _ _ 1 ih) (Nat.pow_le_pow_right (by decide) (by cfomega))
    have h2 : row t <<< 2 < 2 ^ (2 * (t + 1) + 1) :=
      Nat.lt_of_lt_of_le (shiftLeft_lt_two_pow _ _ 2 ih) (Nat.pow_le_pow_right (by decide) (by cfomega))
    exact Nat.xor_lt_two_pow h0 (Nat.or_lt_two_pow h1 h2)

/-- The interior carries of row `m` live below bit `2m + 1`. -/
theorem interior_lt (m : Nat) : interior m < 2 ^ (2 * m + 1) := by
  unfold interior edgeSource
  have hc : carry (row m) < 2 ^ (2 * m + 1) :=
    Nat.lt_of_le_of_lt (show carry (row m) ≤ row m from Nat.and_le_left) (row_lt m)
  have h1 : 1 <<< (2 * m) < 2 ^ (2 * m + 1) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
    have hp : 0 < 2 ^ (2 * m) := Nat.two_pow_pos _
    cfomega
  have h2 : (if rdiag 1 m then 2 else 0) < 2 ^ (2 * m + 1) := by
    cases m with
    | zero =>
      rw [rdiag_one_eq_parity]
      decide
    | succ m =>
      have h8 : 2 < 2 ^ (2 * (m + 1) + 1) :=
        Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 3) (Nat.pow_le_pow_right (by decide) (by cfomega))
      rcases Bool.eq_false_or_eq_true (rdiag 1 (m + 1)) with h | h
      · rw [h]; exact h8
      · rw [h]; exact Nat.two_pow_pos _
  exact Nat.xor_lt_two_pow hc (Nat.xor_lt_two_pow h1 h2)

/-- `q^n · y` lives below bit `2n + k` when `y` lives below bit `k`. -/
theorem phiLinearPow_lt_of_lt (n y k : Nat) (hy : y < 2 ^ k) :
    phiLinearPow n y < 2 ^ (2 * n + k) := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.zero_add]; exact hy
  | succ n ih =>
    rw [phiLinearPow_step]
    show (phiLinearPow n y ^^^ (phiLinearPow n y <<< 1)) ^^^ (phiLinearPow n y <<< 2) <
      2 ^ (2 * (n + 1) + k)
    have h0 : phiLinearPow n y < 2 ^ (2 * (n + 1) + k) :=
      Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by cfomega))
    have h1 : phiLinearPow n y <<< 1 < 2 ^ (2 * (n + 1) + k) :=
      Nat.lt_of_lt_of_le (shiftLeft_lt_two_pow _ _ 1 ih) (Nat.pow_le_pow_right (by decide) (by cfomega))
    have h2 : phiLinearPow n y <<< 2 < 2 ^ (2 * (n + 1) + k) :=
      Nat.lt_of_lt_of_le (shiftLeft_lt_two_pow _ _ 2 ih) (Nat.pow_le_pow_right (by decide) (by cfomega))
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 h1) h2

/-- Bit `0` of `q^n · y` is bit `0` of `y`. -/
theorem phiLinearPow_testBit_zero (n y : Nat) : (phiLinearPow n y).testBit 0 = y.testBit 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [phiLinearPow_step]
    show ((phiLinearPow n y ^^^ (phiLinearPow n y <<< 1)) ^^^ (phiLinearPow n y <<< 2)).testBit 0 =
      y.testBit 0
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, ih]
    cases y.testBit 0 <;> rfl

/-! ## Scale-freeness -/

/-- Bit `2^(k+1)` of `phiScale k Z` is bit `2^k` of `Z` when `Z` has no bit `0` and
lives below bit `2^(k+1)`: only the middle copy survives. -/
theorem phiScale_testBit_double (k Z : Nat) (h0 : Z.testBit 0 = false)
    (hlt : Z < 2 ^ twopow (k + 1)) :
    (phiScale k Z).testBit (twopow (k + 1)) = Z.testBit (twopow k) := by
  have h1 : twopow (k + 1) = twopow k + twopow k := twopow_succ k
  rw [h1] at hlt ⊢
  change ((Z ^^^ (Z <<< twopow k)) ^^^ (Z <<< (twopow k + twopow k))).testBit (twopow k + twopow k) =
    Z.testBit (twopow k)
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    decide_eq_true (by cfomega : twopow k + twopow k ≥ twopow k),
    decide_eq_true (Nat.le_refl (twopow k + twopow k)), Bool.true_and, Bool.true_and,
    Nat.add_sub_cancel, Nat.sub_self, h0, Nat.testBit_lt_two_pow hlt]
  cases Z.testBit (twopow k) <;> rfl

/-- **Scale-freeness of the row terms**: for `m < 2^j` the term of row `m` at time
`2^(j+1)` is its term at time `2^j`. -/
theorem rowTerm_twopow_succ (j m : Nat) (hm : m < twopow j) :
    rowTerm (twopow (j + 1)) m = rowTerm (twopow j) m := by
  unfold rowTerm Rule30UOR.WittDefect.rowBit
  have h1 : twopow (j + 1) = twopow j + twopow j := twopow_succ j
  have hsub : twopow (j + 1) - 1 - m = twopow j + (twopow j - 1 - m) := by cfomega
  rw [hsub, Rule30UOR.Interfaces.phiLinearPow_add, Rule30UOR.Interfaces.phiLinear_freshman]
  apply phiScale_testBit_double
  · rw [phiLinearPow_testBit_zero, Nat.testBit_shiftLeft]
    rfl
  · have hw : interior m <<< 1 < 2 ^ (2 * m + 1 + 1) := shiftLeft_lt_two_pow _ _ 1 (interior_lt m)
    have h := phiLinearPow_lt_of_lt (twopow j - 1 - m) _ _ hw
    rw [show 2 * (twopow j - 1 - m) + (2 * m + 1 + 1) = twopow (j + 1) by cfomega] at h
    exact h

theorem rowTerm_twopow_iter (j m n : Nat) (hm : m < twopow j) :
    rowTerm (twopow (j + n)) m = rowTerm (twopow j) m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show rowTerm (twopow (j + n + 1)) m = rowTerm (twopow j) m
    rw [rowTerm_twopow_succ (j + n) m
      (Nat.lt_of_lt_of_le hm (Rule30UOR.Automatic.twopow_mono (by cfomega))), ih]

/-- The scale-free row sequence: row `m`'s term at any dyadic time beyond `m`. -/
def dyadicRow (m : Nat) : Bool := rowTerm (twopow (m + 1)) m

theorem lt_twopow_succ (m : Nat) : m < twopow (m + 1) :=
  Nat.lt_of_lt_of_le (Rule30UOR.Interfaces.twopow_gt_self m)
    (Rule30UOR.Automatic.twopow_mono (Nat.le_succ m))

theorem rowTerm_twopow_eq_dyadicRow (j m : Nat) (hm : m < twopow j) :
    rowTerm (twopow j) m = dyadicRow m := by
  unfold dyadicRow
  rw [← rowTerm_twopow_iter j m (m + 1) hm, Nat.add_comm j (m + 1),
    rowTerm_twopow_iter (m + 1) m j (lt_twopow_succ m)]

/-! ## The dyadic column as a prefix parity -/

theorem interiorFormula_twopow_eq_xorBelow (j n : Nat) (hn : n ≤ twopow j) :
    interiorFormula (twopow j) n = xorBelow dyadicRow n := by
  rw [interiorFormula_eq_xorBelow_rowTerm]
  exact xorBelow_congr _ _ n (fun m hm => rowTerm_twopow_eq_dyadicRow j m (by cfomega))

theorem stableFormula_eq_xorBelow (j : Nat) : stableFormula j (twopow j) = xorBelow dyadicRow (twopow j) := by
  rw [← interiorFormula_twopow_eq_stableFormula j (twopow j) (Nat.le_refl _),
    interiorFormula_twopow_eq_xorBelow j (twopow j) (Nat.le_refl _)]

/-- **The dyadic column is the prefix parity of `dyadicRow` at the dyadic lengths**:
`center (2^j) = ¬ ⊕_{m < 2^j} dyadicRow m` for `j ≥ 1`. -/
theorem center_twopow_eq_prefix (j : Nat) (hj : 1 ≤ j) :
    center (twopow j) = !(xorBelow dyadicRow (twopow j)) := by
  rw [center_eq_not_timeParity_xor_interior, timeParity_twopow j hj, interiorDiagonal_eq_formula,
    interiorFormula_twopow_eq_xorBelow j (twopow j) (Nat.le_refl _)]
  cases xorBelow dyadicRow (twopow j) <;> rfl

/-! ## Block parities -/

theorem xorBelow_add (g : Nat → Bool) (a b : Nat) :
    xorBelow g (a + b) = bxor (xorBelow g a) (xorBelow (fun i => g (a + i)) b) := by
  induction b with
  | zero =>
    show xorBelow g a = bxor (xorBelow g a) false
    cases xorBelow g a <;> rfl
  | succ b ih =>
    show bxor (xorBelow g (a + b)) (g (a + b)) =
      bxor (xorBelow g a) (bxor (xorBelow (fun i => g (a + i)) b) (g (a + b)))
    rw [ih]
    cases xorBelow g a <;> cases xorBelow (fun i => g (a + i)) b <;> cases g (a + b) <;> rfl

/-- The parity of `dyadicRow` over the block `[2^j, 2^(j+1))`. -/
def blockParity (j : Nat) : Bool := xorBelow (fun i => dyadicRow (twopow j + i)) (twopow j)

theorem bxor_left_cancel (c a b : Bool) (h : bxor c a = bxor c b) : a = b := by
  cases a <;> cases b <;> cases c <;> first | rfl | exact absurd h (by decide)

/-- **The dyadic column steps by the block parities**:
`center (2^(j+1)) = center (2^j) ⊕ blockParity j` for `j ≥ 1`. -/
theorem center_twopow_succ_eq (j : Nat) (hj : 1 ≤ j) :
    center (twopow (j + 1)) = bxor (center (twopow j)) (blockParity j) := by
  have h1 : twopow (j + 1) = twopow j + twopow j := twopow_succ j
  rw [center_twopow_eq_prefix (j + 1) (by cfomega), center_twopow_eq_prefix j hj, h1,
    xorBelow_add]
  unfold blockParity
  cases xorBelow dyadicRow (twopow j) <;> cases xorBelow (fun i => dyadicRow (twopow j + i)) (twopow j) <;> rfl

/-- **The late Witt response at the dyadic time is the block parity of `dyadicRow`.** -/
theorem wittRespBool_twopow_eq_blockParity (j : Nat) (hj : 1 ≤ j) :
    Rule30UOR.Interfaces.wittRespBool (twopow j) j = blockParity j := by
  have h := center_twopow_succ j
  rw [center_twopow_succ_eq j hj] at h
  exact (bxor_left_cancel _ _ _ h).symm

/-- The window response at the dyadic time is the complemented block parity. -/
theorem response_twopow_eq_not_blockParity (j : Nat) (hj : 1 ≤ j) :
    Rule30UOR.Scale.response (twopow j) j = !(blockParity j) := by
  have h := Rule30UOR.Interfaces.wittRespBool_xor_response_ge (twopow j) j (Nat.le_refl _)
  rw [Nat.sub_self, Rule30UOR.Right.rdiag_eq_R, Ruliology.CellularAutomata.Rule30Diagonals.R_zero,
    wittRespBool_twopow_eq_blockParity j hj] at h
  rcases Bool.eq_false_or_eq_true (blockParity j) with hb | hb <;>
    rcases Bool.eq_false_or_eq_true (Rule30UOR.Scale.response (twopow j) j) with hr | hr <;>
    rw [hb, hr] at h <;> rw [hb, hr] <;> first | rfl | exact absurd h (by decide)

/-! ## Problem 1 through the block parities -/

/-- The block parities have period `d` from `K`. -/
def BlockParityPeriodic (K d : Nat) : Prop :=
  ∀ j, K ≤ j → blockParity (j + d) = blockParity j

/-- The block parities are not eventually periodic. -/
def BlockParityAperiodic : Prop := ∀ K d, 0 < d → ¬ BlockParityPeriodic K d

/-- A period of the dyadic column is a period of its steps, the block parities. -/
theorem blockParityPeriodic_of_dilationPeriodic (K d : Nat) (h : DilationPeriodic 1 K d) :
    BlockParityPeriodic (K + 1) d := by
  intro j hj
  have h0 := h j (by cfomega)
  have h1 := h (j + 1) (by cfomega)
  rw [Nat.mul_one, Nat.mul_one] at h0 h1
  rw [show j + 1 + d = j + d + 1 by cfomega, center_twopow_succ_eq (j + d) (by cfomega),
    center_twopow_succ_eq j (by cfomega), h0] at h1
  exact bxor_left_cancel _ _ _ h1

theorem dyadicColumnAperiodic_of_blockParityAperiodic (h : BlockParityAperiodic) :
    DyadicColumnAperiodic := by
  intro K d hd hp
  exact h (K + 1) d hd (blockParityPeriodic_of_dilationPeriodic K d hp)

/-- **Problem 1 from the aperiodicity of the block parities.** -/
theorem problem1_of_blockParityAperiodic (h : BlockParityAperiodic) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_of_dyadic_column_aperiodic (dyadicColumnAperiodic_of_blockParityAperiodic h)

end Rule30UOR.DyadicRow
