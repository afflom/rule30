module
public import Rule30UOR.EdgeParity
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

@[expose] public section

/-! # The carry as an intersection

Over the single-element field the row is a set, and the carry `carry y = y ∧ (y ≪ 1)`
is the intersection of the row with its own translate: the characteristic-1 content of
Rule 30, as opposed to the characteristic-2 content `phiLinear`. `center t = ¬(timeParity t ⊕
interiorDiagonal t)` reads the gasket-weighted self-intersections of every row. On the linear
rows `q^n` the self-intersection is exact: an even row `q^{2m} = q^m(X²)` has no adjacent ones, so
its self-intersection is empty; an odd row `q^{2m+1} = q · q^m(X²)` intersects its translate exactly
at the run boundaries of `q^m`. -/

namespace Rule30UOR.Intersection

open Rule30UOR.Core Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.WittDefect

/-- Bit `i` of the carry: the row at `i` and at `i − 1`. -/
theorem rowBit_carry (y i : Nat) :
    rowBit (carry y) i = (rowBit y i && (decide (1 ≤ i) && rowBit y (i - 1))) := by
  show (y &&& (y <<< 1)).testBit i = (y.testBit i && (decide (1 ≤ i) && y.testBit (i - 1)))
  rw [Nat.testBit_and, Nat.testBit_shiftLeft]

/-- Bits of the linear rows are the trinomial parities. -/
theorem rowBit_linear (n d : Nat) : rowBit (phiLinPow 1 n 1) d = trinomialParity n d :=
  testBit_phiLinPow_eq_trinomialParity n d

/-- **An even linear row has empty self-intersection**: `q^{2m}` has no two adjacent ones. -/
theorem linear_self_intersection_even (m : Nat) : carry (phiLinPow 1 (2 * m) 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (carry (phiLinPow 1 (2 * m) 1)).testBit i = (0 : Nat).testBit i
  rw [Nat.zero_testBit]
  have h := rowBit_carry (phiLinPow 1 (2 * m) 1) i
  show rowBit (carry (phiLinPow 1 (2 * m) 1)) i = false
  rw [h]
  rcases Nat.lt_or_ge i 1 with hi | hi
  · rw [decide_eq_false (by cfomega)]; cases rowBit (phiLinPow 1 (2 * m) 1) i <;> rfl
  · rw [decide_eq_true hi, rowBit_linear, rowBit_linear]
    rcases Nat.mod_two_eq_zero_or_one i with he | ho
    · have : i - 1 = 2 * ((i - 1) / 2) + 1 := by cfomega
      rw [this, trinomialParity_even_odd]
      cases trinomialParity (2 * m) i <;> rfl
    · have : i = 2 * (i / 2) + 1 := by cfomega
      rw [this, trinomialParity_even_odd]
      rfl

/-- **An odd linear row intersects its translate at the run boundaries of the half row**, odd
positions: bit `2(i+1)+1` of `carry q^{2m+1}` is `[q^m has i+1 and not i]`. -/
theorem linear_self_intersection_odd_rise (m i : Nat) :
    rowBit (carry (phiLinPow 1 (2 * m + 1) 1)) (2 * (i + 1) + 1) =
      (trinomialParity m (i + 1) && !(trinomialParity m i)) := by
  rw [rowBit_carry, decide_eq_true (by cfomega), rowBit_linear, rowBit_linear,
    show 2 * (i + 1) + 1 - 1 = 2 * i + 2 by cfomega, trinomialParity_odd_odd,
    trinomialParity_odd_even_succ]
  cases trinomialParity m (i + 1) <;> cases trinomialParity m i <;> rfl

/-- Even positions: bit `2i+2` of `carry q^{2m+1}` is `[q^m has i and not i+1]`. -/
theorem linear_self_intersection_odd_fall (m i : Nat) :
    rowBit (carry (phiLinPow 1 (2 * m + 1) 1)) (2 * i + 2) =
      (trinomialParity m i && !(trinomialParity m (i + 1))) := by
  rw [rowBit_carry, decide_eq_true (by cfomega), rowBit_linear, rowBit_linear,
    show 2 * i + 2 - 1 = 2 * i + 1 by cfomega, trinomialParity_odd_odd,
    trinomialParity_odd_even_succ]
  cases trinomialParity m (i + 1) <;> cases trinomialParity m i <;> rfl

/-- Every linear row begins with `1`: `trinomialParity n 0 = true`. -/
theorem trinomialParity_zero_right_fuel : ∀ f n, n ≤ f → trinomialParity n 0 = true
  | 0, n, hn => by
    rw [show n = 0 by cfomega]; rfl
  | f + 1, n, hn => by
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · rw [show n = 0 by cfomega]; rfl
    · rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · rw [show n = 2 * (n / 2) by cfomega, show (0 : Nat) = 2 * 0 by rfl, trinomialParity_even_even]
        exact trinomialParity_zero_right_fuel f (n / 2) (by cfomega)
      · rw [show n = 2 * (n / 2) + 1 by cfomega, trinomialParity_odd_zero]
        exact trinomialParity_zero_right_fuel f (n / 2) (by cfomega)

theorem trinomialParity_zero_right (n : Nat) : trinomialParity n 0 = true :=
  trinomialParity_zero_right_fuel n n (Nat.le_refl n)

/-- The first odd position of an odd row always carries: `q^m` begins with `1`. -/
theorem linear_self_intersection_odd_one (m : Nat) :
    rowBit (carry (phiLinPow 1 (2 * m + 1) 1)) 1 = true := by
  rw [rowBit_carry, decide_eq_true (Nat.le_refl 1), rowBit_linear, rowBit_linear,
    show (1 : Nat) - 1 = 0 by rfl, trinomialParity_odd_zero, trinomialParity_zero_right,
    show (1 : Nat) = 2 * 0 + 1 by rfl, trinomialParity_odd_odd, trinomialParity_zero_right]
  rfl

/-! ## The self-intersection of a sum: linear, cross and ledger terms

`row m = q^m ⊕ W_m` (`row_eq_linear_xor_ledger`), and the intersection of a sum with its translate
splits into the two self-intersections and the cross term. -/

/-- The cross term of the self-intersection: `a ∧ σb ⊕ b ∧ σa`. -/
def cross (a b : Nat) : Nat := (a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))

/-- **`carry (a ⊕ b) = carry a ⊕ carry b ⊕ cross a b`.** -/
theorem carry_xor (a b : Nat) : carry (a ^^^ b) = (carry a ^^^ carry b) ^^^ cross a b := by
  apply Nat.eq_of_testBit_eq
  intro i
  show ((a ^^^ b) &&& ((a ^^^ b) <<< 1)).testBit i =
    (((a &&& (a <<< 1)) ^^^ (b &&& (b <<< 1))) ^^^ ((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1)))).testBit i
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases a.testBit i <;> cases b.testBit i <;> cases decide (1 ≤ i) <;> cases a.testBit (i - 1) <;>
    cases b.testBit (i - 1) <;> rfl

/-- **The carries of a row are the linear self-intersection, the cross term and the ledger
self-intersection.** -/
theorem carry_row_split (m : Nat) :
    carry (row m) = (carry (phiLinearPow m 1) ^^^ carry (winWitt 0 m)) ^^^ cross (phiLinearPow m 1) (winWitt 0 m) := by
  rw [row_eq_linear_xor_ledger, carry_xor]

end Rule30UOR.Intersection
