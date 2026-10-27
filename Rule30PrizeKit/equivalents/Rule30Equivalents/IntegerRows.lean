module

public import Rule30Equivalents.Basic
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule 30 as an integer sequence

Read row `t` of rule 30 (from a single black cell) as a binary number whose bit `0` is the
rightmost black cell, at position `t`: bit `j` is the cell at position `t - j`. Doubling then
moves every cell one place to the left, and rule 30 (`left xor (center or right)`) becomes

    a 0 = 1,    a (t + 1) = a t ^^^ ((2 * a t) ||| (4 * a t)),

the sequence 1, 7, 25, 111, 401, 1783, … (OEIS A110240). The centre cell at time `t` is bit `t`
of `a t`, so Problem 1 is a statement about this explicit integer recurrence.

* `testBit_a`: bit `j` of `a t` is `cell t (t - j)`, the right diagonal `R j t`.
* `center_eq_testBit`: the centre cell at time `t` is bit `t` of `a t`.
* `problem1_iff_integer_rows`: Problem 1 holds iff `t ↦ (a t).testBit t` is not eventually
  periodic.
* `diagArray`, `diagArray_row_periodic`, `problem1_iff_diagArray`: in the array
  `(j, t) ↦ bit j of a t`, every row `j` is periodic in `t` with period dividing `2 ^ j`
  (the right diagonals, `Rule30Diagonals.R_periodic`), and Problem 1 says that its main diagonal
  is not eventually periodic. The diagonal always reads bit `t` early in that bit's cycle.

The map `a ↦ a ^^^ ((2 * a) ||| (4 * a))` is a T-function: bit `j` of the image depends only on
bits `j`, `j - 1` and `j - 2` of the argument, with bit `j` entering through `xor`.

Sources: S. Wolfram, *A New Kind of Science* (2002), the integer form of rule 30; OEIS A110240 and
A051023.
-/

@[expose] public section

namespace Rule30Equivalents.IntegerRows

open Ruliology.CellularAutomata

/-- Row `t` of rule 30 as a binary number: bit `j` is the cell at position `t - j`. -/
def a : Nat → Nat
  | 0 => 1
  | t + 1 => a t ^^^ ((2 * a t) ||| (4 * a t))

/-- The first rows, as in OEIS A110240. -/
theorem a_values : (List.range 6).map a = [1, 7, 25, 111, 401, 1783] := by decide

theorem testBit_two_mul (x j : Nat) :
    (2 * x).testBit j = (decide (1 ≤ j) && x.testBit (j - 1)) := by
  rw [show 2 * x = x <<< 1 by rw [Nat.shiftLeft_eq]; omega, Nat.testBit_shiftLeft]

theorem testBit_four_mul (x j : Nat) :
    (4 * x).testBit j = (decide (2 ≤ j) && x.testBit (j - 2)) := by
  rw [show 4 * x = x <<< 2 by rw [Nat.shiftLeft_eq]; omega, Nat.testBit_shiftLeft]

/-- Bit `j` of row `t` is the cell at position `t - j`. -/
theorem testBit_a : ∀ t j, (a t).testBit j = Rule30Jen.cell t ((t : Int) - j)
  | 0, 0 => rfl
  | 0, j + 1 => by
    show Nat.testBit 1 (j + 1) = decide (((0 : Nat) : Int) - ((j + 1 : Nat) : Int) = 0)
    rw [Nat.testBit_succ]
    simp only [Nat.reduceDiv, Nat.zero_testBit]
    symm; simp only [decide_eq_false_iff_not]; omega
  | t + 1, j => by
    rw [a, Nat.testBit_xor, Nat.testBit_or, testBit_two_mul, testBit_four_mul, testBit_a t j,
      Rule30Jen.cell]
    unfold Rule30Jen.rule
    have e1 : ((t + 1 : Nat) : Int) - (j : Int) - 1 = (t : Int) - (j : Int) := by omega
    rw [e1]
    rcases j with _ | _ | k
    · -- j = 0: the right edge; the cells at `t + 1` and `t + 2` are white
      have d1 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
      have d2 : decide (2 ≤ 0) = false := decide_eq_false (by omega)
      have h3 : Rule30Jen.cell t (((t + 1 : Nat) : Int) - ((0 : Nat) : Int) + 1) = false :=
        Rule30Diagonals.cell_eq_false_of_gt t _ (by omega)
      have h2 : Rule30Jen.cell t (((t + 1 : Nat) : Int) - ((0 : Nat) : Int)) = false :=
        Rule30Diagonals.cell_eq_false_of_gt t _ (by omega)
      rw [d1, d2, h3, h2]
      simp
    · -- j = 1: the cell at `t + 1` is white
      have d1 : decide (1 ≤ 0 + 1) = true := decide_eq_true (by omega)
      have d2 : decide (2 ≤ 0 + 1) = false := decide_eq_false (by omega)
      have h3 : Rule30Jen.cell t (((t + 1 : Nat) : Int) - ((0 + 1 : Nat) : Int) + 1) = false :=
        Rule30Diagonals.cell_eq_false_of_gt t _ (by omega)
      have e2 : ((t + 1 : Nat) : Int) - ((0 + 1 : Nat) : Int) = (t : Int) - ((0 : Nat) : Int) := by
        omega
      rw [d1, d2, Bool.true_and, Bool.false_and, Bool.or_false, show 0 + 1 - 1 = 0 from rfl,
        testBit_a t 0, h3, e2, Bool.or_false]
    · -- j = k + 2
      have d1 : decide (1 ≤ k + 1 + 1) = true := decide_eq_true (by omega)
      have d2 : decide (2 ≤ k + 1 + 1) = true := decide_eq_true (by omega)
      have e2 : ((t + 1 : Nat) : Int) - ((k + 1 + 1 : Nat) : Int) =
          (t : Int) - ((k + 1 : Nat) : Int) := by omega
      have e3 : ((t + 1 : Nat) : Int) - ((k + 1 + 1 : Nat) : Int) + 1 =
          (t : Int) - ((k : Nat) : Int) := by omega
      rw [d1, d2, Bool.true_and, Bool.true_and, show k + 1 + 1 - 1 = k + 1 from rfl,
        show k + 1 + 1 - 2 = k from rfl, testBit_a t (k + 1), testBit_a t k, e3, e2]

/-- The centre cell at time `t` is bit `t` of row `t`. -/
theorem center_eq_testBit (t : Nat) : Rule30Prize.center t = (a t).testBit t := by
  rw [testBit_a]; show Rule30Jen.cell t 0 = _; congr 1; omega

/-- **Problem 1 as a statement about an integer recurrence.** With
`a 0 = 1` and `a (t + 1) = a t ^^^ ((2 * a t) ||| (4 * a t))`, Problem 1 holds iff the sequence
`t ↦ bit t of a t` is not eventually periodic. -/
theorem problem1_iff_integer_rows :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => (a t).testBit t) := by
  have h : (fun t => (a t).testBit t) = c := funext fun t => (center_eq_testBit t).symm
  rw [h]; exact problem1_iff_not_eventuallyPeriodic

/-- The array of the rows' bits: `diagArray j t` is bit `j` of `a t`. -/
def diagArray (j t : Nat) : Bool := (a t).testBit j

/-- Row `j` of the array is the `j`-th right diagonal of rule 30. -/
theorem diagArray_eq_R (j t : Nat) : diagArray j t = Rule30Diagonals.R j t := testBit_a t j

/-- Every row of the array is periodic, with period dividing `2 ^ j`. -/
theorem diagArray_row_periodic (j t : Nat) : diagArray j (t + 2 ^ j) = diagArray j t := by
  rw [diagArray_eq_R, diagArray_eq_R]; exact Rule30Diagonals.R_periodic j t

/-- **Problem 1 as a statement about the main diagonal of the array.** Every row is periodic, and
Problem 1 says the main diagonal `t ↦ diagArray t t` is not eventually periodic. -/
theorem problem1_iff_diagArray :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => diagArray t t) :=
  problem1_iff_integer_rows

end Rule30Equivalents.IntegerRows
