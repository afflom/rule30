module
public import Rule30UOR.RightPeriods
public import Rule30UOR.Gasket
public import Rule30UOR.Fixed
public import Rule30UOR.KernelRoot
public import Rule30UOR.DyadicRow
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The light cone at every column, and at every dyadic scale

Rule 30 is rule 60 plus the run-end source: `cell (s+1) p = cell s (p−1) ⊕ cell s p ⊕ runEnd s (p+1)`
(`cell_succ_pascal`), where `runEnd s p = cell s p ∧ ¬cell s (p−1)` is the left end of a black run
(`carry60_eq_runEnd`: the core's rule-60 carry is the run-end one place to the right). Integrating
this law in Pascal coordinates gives one transport formula for every column and every start:

* `cell_add_eq_stepCone`: `cell (t+n) p = ⊕_a C(n,a)·cell t (p−a) ⊕ ⊕_{i<n} ⊕_q C(n−1−i,q)·runEnd (t+i) (p+1−q)`;
  its source part is the window response of `Scale` in Pascal form (`window60_eq_sourcePart`).
* `cell_eq_seedAt_bxor_coneAt` (start `0`): every column is the transported seed `C(t,p)` plus its
  own cone `coneAt p`. `coneAt 0` is the left light cone (`coneAt_zero`) and `coneAt (−1)` is the cone
  from column `0` (`coneAt_neg_one`), so **the cone from column `0` is column `−1`**
  (`Rule30UOR.KernelRoot.coneZero_eq_cell`), and the increment law is the rule at column `0`. With the right
  tower: `maskedTower_increment_eq_Lh` reads column `−1` of the half driven by the center as the
  masked tower word plus the increment.
* At spacing `2^k` the same integration applies to Frobenius' scale identity (`Scale.scale`): rule
  30 at scale `2^k` is rule 60 at spacing `2^k` sourced by the block responses `window60 · (2^k)`
  (`cell_block_duhamel`), and inside the cone the center is its residue plus the block cone
  (`center_block_cone`). The block responses compose (`window60_twopow_succ`) and the binomial
  weights are Frobenius' and Kummer's (`pascalParity_twopow_inner`, `Rule30UOR.ColumnCone.pascalParity_complement_aux`).
  Cancelling at a scale is the period: at every single scale `k`, Problem 1 is exactly the absence
  of a common eventual period of the block cones in the block index (`problem1_iff_noBlockConePeriod`).
* One nonlinear fact of the run-end field: run-ends are never adjacent (`runEnd_not_adjacent`).
* Every right word starts white for `2s < j` (`Rule30UOR.KernelRoot.towerWord_white`) and repeats that prefix at
  Jen's period (`towerWord_white_periodic`).

The transport statements are linear in the run-end field and hold, with the seed term replaced by
the transported initial row, for the orbit of any initial row; none of them refutes a center period
by itself.
-/

@[expose] public section

namespace Rule30UOR.ColumnCone

open Rule30UOR.Core Rule30UOR.Ledger Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Band
  Rule30UOR.Antidiagonal

/-! ## Rule 30 is rule 60 plus the run-end source -/

/-- The core's rule-60 carry is the run-end one place to the right. -/
theorem carry60_eq_runEnd (s : Nat) (p : Int) : carry60 s p = runEnd s (p + 1) := by
  unfold carry60 runEnd
  rw [Rule30UOR.Scale.sub_neg_one, show p + 1 - 1 = p by cfomega, Bool.and_comm]

/-- **Rule 30 is rule 60 plus the run-end source**. -/
theorem cell_succ_pascal (s : Nat) (p : Int) :
    cell (s + 1) p = bxor (bxor (cell s (p - 1)) (cell s p)) (runEnd s (p + 1)) := by
  rw [Rule30UOR.Scale.split_cell, ← carry60_eq_runEnd, Rule30UOR.Scale.bxor_eq, Rule30UOR.Scale.bxor_eq]
  rfl

/-- **Run-ends are never adjacent**: the run-ends of a row form an independent set. -/
theorem runEnd_not_adjacent (j : Nat) (p : Int) : (runEnd j p && runEnd j (p + 1)) = false := by
  unfold runEnd
  rw [show p + 1 - 1 = p by cfomega]
  cases cell j p <;> cases cell j (p - 1) <;> cases cell j (p + 1) <;> rfl

/-! ## Pascal's rule integrated -/

private theorem pascalSum_succ (n : Nat) (g : Nat → Bool) :
    xorBelow (fun a => pascalParity (n + 1) a && g a) (n + 2) =
      bxor (xorBelow (fun a => pascalParity n a && g (a + 1)) (n + 1))
        (xorBelow (fun a => pascalParity n a && g a) (n + 1)) := by
  have h1 : xorBelow (fun a => pascalParity (n + 1) a && g a) (n + 2) =
      bxor (pascalParity (n + 1) 0 && g 0)
        (xorBelow (fun m => pascalParity (n + 1) (m + 1) && g (m + 1)) (n + 1)) :=
    xorBelow_front _ (n + 1)
  have h2 : xorBelow (fun a => pascalParity n a && g a) (n + 1) =
      bxor (pascalParity n 0 && g 0) (xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n) :=
    xorBelow_front _ n
  have h3 : xorBelow (fun m => pascalParity (n + 1) (m + 1) && g (m + 1)) (n + 1) =
      bxor (xorBelow (fun m => pascalParity n m && g (m + 1)) (n + 1))
        (xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) (n + 1)) := by
    rw [← xorBelow_bxor]
    exact xorBelow_congr _ _ (n + 1) (fun m _ => by
      show (pascalParity (n + 1) (m + 1) && g (m + 1)) =
        bxor (pascalParity n m && g (m + 1)) (pascalParity n (m + 1) && g (m + 1))
      rw [pascalParity_succ, cone_and_bxor])
  have h4 : xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) (n + 1) =
      xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n := by
    show bxor (xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n)
      (pascalParity n (n + 1) && g (n + 1)) = _
    rw [pascalParity_gt n (n + 1) (by cfomega), Bool.false_and, cone_bxor_false_right]
  rw [h1, h2, h3, h4, pascalParity_zero_right, pascalParity_zero_right]
  cases g 0 <;> cases xorBelow (fun m => pascalParity n m && g (m + 1)) (n + 1) <;>
    cases xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n <;> rfl

private theorem sub_mul_succ (p : Int) (d a : Nat) :
    p - ((d * (a + 1) : Nat) : Int) = p - (d : Int) - ((d * a : Nat) : Int) := by
  rw [Nat.mul_succ]
  generalize d * a = M
  cfomega

private theorem lin_step (Y : Int → Bool) (d n : Nat) (p : Int) :
    xorBelow (fun a => pascalParity (n + 1) a && Y (p - ((d * a : Nat) : Int))) (n + 1 + 1) =
      bxor (xorBelow (fun a => pascalParity n a && Y (p - (d : Int) - ((d * a : Nat) : Int))) (n + 1))
        (xorBelow (fun a => pascalParity n a && Y (p - ((d * a : Nat) : Int))) (n + 1)) := by
  have h := pascalSum_succ n (fun a => Y (p - ((d * a : Nat) : Int)))
  have e : xorBelow (fun a => pascalParity n a && Y (p - ((d * (a + 1) : Nat) : Int))) (n + 1) =
      xorBelow (fun a => pascalParity n a && Y (p - (d : Int) - ((d * a : Nat) : Int))) (n + 1) :=
    xorBelow_congr _ _ (n + 1) (fun a _ => by
      show (pascalParity n a && Y (p - ((d * (a + 1) : Nat) : Int))) =
        (pascalParity n a && Y (p - (d : Int) - ((d * a : Nat) : Int)))
      rw [sub_mul_succ])
  rw [← e]
  exact h

private theorem src_row_succ (S : Nat → Int → Bool) (d t n i : Nat) (p : Int) (hi : i < n) :
    xorBelow (fun q => pascalParity (n + 1 - 1 - i) q && S (t + i) (p - ((d * q : Nat) : Int))) (n + 1 - i) =
      bxor (xorBelow (fun q => pascalParity (n - 1 - i) q &&
          S (t + i) (p - (d : Int) - ((d * q : Nat) : Int))) (n - i))
        (xorBelow (fun q => pascalParity (n - 1 - i) q && S (t + i) (p - ((d * q : Nat) : Int))) (n - i)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = i + m + 1 := ⟨n - i - 1, by cfomega⟩
  rw [show i + m + 1 + 1 - 1 - i = m + 1 by cfomega, show i + m + 1 + 1 - i = m + 1 + 1 by cfomega,
    show i + m + 1 - 1 - i = m by cfomega, show i + m + 1 - i = m + 1 by cfomega]
  exact lin_step (S (t + i)) d m p

private theorem src_step (S : Nat → Int → Bool) (d t n : Nat) (p : Int) :
    xorBelow (fun i => xorBelow (fun q => pascalParity (n + 1 - 1 - i) q &&
        S (t + i) (p - ((d * q : Nat) : Int))) (n + 1 - i)) (n + 1) =
      bxor (bxor (xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
            S (t + i) (p - (d : Int) - ((d * q : Nat) : Int))) (n - i)) n)
          (xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
            S (t + i) (p - ((d * q : Nat) : Int))) (n - i)) n))
        (S (t + n) p) := by
  have hr : xorBelow (fun i => xorBelow (fun q => pascalParity (n + 1 - 1 - i) q &&
        S (t + i) (p - ((d * q : Nat) : Int))) (n + 1 - i)) n =
      xorBelow (fun i => bxor (xorBelow (fun q => pascalParity (n - 1 - i) q &&
            S (t + i) (p - (d : Int) - ((d * q : Nat) : Int))) (n - i))
          (xorBelow (fun q => pascalParity (n - 1 - i) q &&
            S (t + i) (p - ((d * q : Nat) : Int))) (n - i))) n :=
    xorBelow_congr _ _ n (fun i hi => src_row_succ S d t n i p hi)
  have hl : xorBelow (fun q => pascalParity (n + 1 - 1 - n) q &&
      S (t + n) (p - ((d * q : Nat) : Int))) (n + 1 - n) = S (t + n) p := by
    rw [show n + 1 - 1 - n = 0 by cfomega, show n + 1 - n = 1 by cfomega]
    show bxor false (pascalParity 0 0 && S (t + n) (p - ((d * 0 : Nat) : Int))) = S (t + n) p
    rw [pascalParity_zero_right, Nat.mul_zero, show p - ((0 : Nat) : Int) = p by cfomega]
    cases S (t + n) p <;> rfl
  show bxor (xorBelow (fun i => xorBelow (fun q => pascalParity (n + 1 - 1 - i) q &&
        S (t + i) (p - ((d * q : Nat) : Int))) (n + 1 - i)) n)
      (xorBelow (fun q => pascalParity (n + 1 - 1 - n) q &&
        S (t + n) (p - ((d * q : Nat) : Int))) (n + 1 - n)) = _
  rw [hr, hl, xorBelow_bxor]

/-- Pascal's rule integrated: a field obeying rule 60 at spacing `d` with source `S` is the binomial
transport of its start plus the binomial transport of the sources. -/
private theorem pascal_duhamel (X S : Nat → Int → Bool) (d t : Nat)
    (hX : ∀ s p, X (s + 1) p = bxor (bxor (X s (p - (d : Int))) (X s p)) (S s p)) :
    ∀ n p, X (t + n) p =
      bxor (xorBelow (fun a => pascalParity n a && X t (p - ((d * a : Nat) : Int))) (n + 1))
        (xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
          S (t + i) (p - ((d * q : Nat) : Int))) (n - i)) n) := by
  intro n
  induction n with
  | zero =>
    intro p
    show X t p = bxor (bxor false (pascalParity 0 0 && X t (p - ((d * 0 : Nat) : Int)))) false
    rw [pascalParity_zero_right, Nat.mul_zero, show p - ((0 : Nat) : Int) = p by cfomega]
    cases X t p <;> rfl
  | succ n ih =>
    intro p
    rw [show t + (n + 1) = (t + n) + 1 by cfomega, hX (t + n) p, ih (p - (d : Int)), ih p,
      lin_step (X t) d n p, src_step S d t n p]
    cases xorBelow (fun a => pascalParity n a && X t (p - (d : Int) - ((d * a : Nat) : Int))) (n + 1) <;>
      cases xorBelow (fun a => pascalParity n a && X t (p - ((d * a : Nat) : Int))) (n + 1) <;>
      cases xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
        S (t + i) (p - (d : Int) - ((d * q : Nat) : Int))) (n - i)) n <;>
      cases xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
        S (t + i) (p - ((d * q : Nat) : Int))) (n - i)) n <;>
      cases S (t + n) p <;> rfl

/-! ## The transport at every column -/

/-- The start of the window transported `n` steps by rule 60: `⊕_{a ≤ n} C(n,a)·cell t (p−a)`. -/
def linearPart (n t : Nat) (p : Int) : Bool :=
  xorBelow (fun a => pascalParity n a && cell t (p - (a : Int))) (n + 1)

/-- The run-ends of time `t + i` transported to time `t + n`, read at column `p`. -/
def sourceRow (n t i : Nat) (p : Int) : Bool :=
  xorBelow (fun q => pascalParity (n - 1 - i) q && runEnd (t + i) (p + 1 - (q : Int))) (n - i)

/-- The run-ends of the window `[t, t + n)` transported to time `t + n`, read at column `p`. -/
def sourcePart (n t : Nat) (p : Int) : Bool := xorBelow (fun i => sourceRow n t i p) n

/-- The `n`-step transport formula. -/
def stepCone (n t : Nat) (p : Int) : Bool := bxor (linearPart n t p) (sourcePart n t p)

/-- **The `n`-step formula at every column**: the cell is the binomial transport of the start plus
the binomial transport of the run-ends of the window. -/
theorem cell_add_eq_stepCone (n t : Nat) (p : Int) : cell (t + n) p = stepCone n t p := by
  rw [pascal_duhamel cell (fun s p => runEnd s (p + 1)) 1 t
    (fun s p => by rw [cell_succ_pascal]; rfl) n p]
  unfold stepCone linearPart sourcePart sourceRow
  have e1 : xorBelow (fun a => pascalParity n a && cell t (p - ((1 * a : Nat) : Int))) (n + 1) =
      xorBelow (fun a => pascalParity n a && cell t (p - (a : Int))) (n + 1) :=
    xorBelow_congr _ _ (n + 1) (fun a _ => by rw [Nat.one_mul])
  have e2 : xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
        runEnd (t + i) (p - ((1 * q : Nat) : Int) + 1)) (n - i)) n =
      xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
        runEnd (t + i) (p + 1 - (q : Int))) (n - i)) n :=
    xorBelow_congr _ _ n (fun i _ => xorBelow_congr _ _ (n - i) (fun q _ => by
      show (pascalParity (n - 1 - i) q && runEnd (t + i) (p - ((1 * q : Nat) : Int) + 1)) =
        (pascalParity (n - 1 - i) q && runEnd (t + i) (p + 1 - (q : Int)))
      rw [Nat.one_mul, show p - (q : Int) + 1 = p + 1 - (q : Int) by cfomega]))
  rw [← e1, ← e2]

/-- **The window response of `Scale` in Pascal form**: `window60 t n p` is the source part. -/
theorem window60_eq_sourcePart (n t : Nat) (p : Int) : window60 t n p = sourcePart n t p := by
  have h := pascal_duhamel (fun m p => window60 t m p) (fun s p => runEnd (t + s) (p + 1)) 1 0
    (fun s p => by
      show window60 t (s + 1) p =
        bxor (bxor (window60 t s (p - ((1 : Nat) : Int))) (window60 t s p)) (runEnd (t + s) (p + 1))
      rw [window60_step, ← carry60_eq_runEnd]
      rfl) n p
  have e1 : xorBelow (fun a => pascalParity n a && window60 t 0 (p - ((1 * a : Nat) : Int))) (n + 1) = false :=
    (xorBelow_congr _ (fun _ => false) (n + 1) (fun a _ => Bool.and_false _)).trans (xorBelow_false _)
  have e2 : xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
        runEnd (t + (0 + i)) (p - ((1 * q : Nat) : Int) + 1)) (n - i)) n = sourcePart n t p :=
    xorBelow_congr _ _ n (fun i _ => xorBelow_congr _ _ (n - i) (fun q _ => by
      show (pascalParity (n - 1 - i) q && runEnd (t + (0 + i)) (p - ((1 * q : Nat) : Int) + 1)) =
        (pascalParity (n - 1 - i) q && runEnd (t + i) (p + 1 - (q : Int)))
      rw [Nat.zero_add, Nat.one_mul, show p - (q : Int) + 1 = p + 1 - (q : Int) by cfomega]))
  have hw : window60 t (0 + n) p = bxor
      (xorBelow (fun a => pascalParity n a && window60 t 0 (p - ((1 * a : Nat) : Int))) (n + 1))
      (xorBelow (fun i => xorBelow (fun q => pascalParity (n - 1 - i) q &&
        runEnd (t + (0 + i)) (p - ((1 * q : Nat) : Int) + 1)) (n - i)) n) := h
  rw [Nat.zero_add, e1, e2, cone_bxor_false] at hw
  exact hw

/-! ## The cone of every column from the seed -/

/-- The seed transported to time `t`: `C(t, p) mod 2` on the columns `p ≥ 0`, white on `p < 0`. -/
def seedAt (t : Nat) : Int → Bool
  | Int.ofNat m => pascalParity t m
  | Int.negSucc _ => false

/-- The cone of column `p`: the run-ends of all earlier times transported to `(t, p)`. -/
def coneAt (p : Int) (t : Nat) : Bool :=
  xorBelow (fun j => xorBelow (fun q => pascalParity (t - 1 - j) q &&
    runEnd j (p + 1 - (q : Int))) (t - j)) t

private theorem cell_zero_ne (x : Int) (h : x ≠ 0) : cell 0 x = false := by
  rw [Rule30UOR.Scale.cell_zero_eq]
  exact decide_eq_false h

private theorem xorBelow_point (f : Nat → Bool) (m : Nat) :
    ∀ N, xorBelow (fun a => f a && cell 0 ((m : Int) - (a : Int))) N = (f m && decide (m < N))
  | 0 => by
    show false = (f m && decide (m < 0))
    rw [decide_eq_false (Nat.not_lt_zero m), Bool.and_false]
  | N + 1 => by
    show bxor (xorBelow (fun a => f a && cell 0 ((m : Int) - (a : Int))) N)
      (f N && cell 0 ((m : Int) - (N : Int))) = (f m && decide (m < N + 1))
    rw [xorBelow_point f m N]
    rcases Nat.lt_or_ge N m with h | h
    · rw [cell_zero_ne _ (by cfomega), decide_eq_false (by cfomega : ¬ m < N),
        decide_eq_false (by cfomega : ¬ m < N + 1)]
      cases f m <;> cases f N <;> rfl
    · rcases Nat.lt_or_ge m N with h2 | h2
      · rw [cell_zero_ne _ (by cfomega), decide_eq_true (by cfomega : m < N),
          decide_eq_true (by cfomega : m < N + 1)]
        cases f m <;> cases f N <;> rfl
      · obtain rfl : N = m := by cfomega
        rw [show (N : Int) - (N : Int) = 0 by cfomega, decide_eq_false (by cfomega : ¬ N < N),
          decide_eq_true (by cfomega : N < N + 1)]
        show bxor (f N && false) (f N && true) = (f N && true)
        cases f N <;> rfl

/-- At start `0` the linear part is the transported seed. -/
theorem linearPart_seed (t : Nat) (p : Int) : linearPart t 0 p = seedAt t p := by
  unfold linearPart
  cases p with
  | ofNat m =>
    show xorBelow (fun a => pascalParity t a && cell 0 ((m : Int) - (a : Int))) (t + 1) = pascalParity t m
    rw [xorBelow_point (fun a => pascalParity t a) m (t + 1)]
    rcases Nat.lt_or_ge m (t + 1) with h | h
    · rw [decide_eq_true h, Bool.and_true]
    · rw [decide_eq_false (by cfomega : ¬ m < t + 1), Bool.and_false, pascalParity_gt t m (by cfomega)]
  | negSucc m =>
    show xorBelow (fun a => pascalParity t a && cell 0 (Int.negSucc m - (a : Int))) (t + 1) = false
    have h0 := Int.negSucc_lt_zero m
    exact (xorBelow_congr _ (fun _ => false) (t + 1) (fun a _ => by
      show (pascalParity t a && cell 0 (Int.negSucc m - (a : Int))) = false
      rw [cell_zero_ne _ (by cfomega), Bool.and_false])).trans (xorBelow_false _)

/-- At start `0` the source part is the cone of the column. -/
theorem sourcePart_seed (t : Nat) (p : Int) : sourcePart t 0 p = coneAt p t := by
  unfold sourcePart sourceRow coneAt
  exact xorBelow_congr _ _ t (fun j _ => by rw [Nat.zero_add])

/-- **Every column is the transported seed plus its own cone.** -/
theorem cell_eq_seedAt_bxor_coneAt (t : Nat) (p : Int) : cell t p = bxor (seedAt t p) (coneAt p t) := by
  have h := cell_add_eq_stepCone t 0 p
  rw [Nat.zero_add] at h
  rw [h]
  unfold stepCone
  rw [linearPart_seed, sourcePart_seed]

/-- The cone of column `0` is the left light cone. -/
theorem coneAt_zero (t : Nat) : coneAt 0 t = leftCone t := by
  unfold coneAt leftCone
  exact xorBelow_congr _ _ t (fun j _ => xorBelow_congr _ _ (t - j) (fun q _ => by
    show (pascalParity (t - 1 - j) q && runEnd j (0 + 1 - (q : Int))) =
      (pascalParity (t - 1 - j) q && runEnd j (1 - (q : Int)))
    rw [show (0 : Int) + 1 - (q : Int) = 1 - (q : Int) by cfomega]))

/-- The cone of column `−1` is the cone from column `0` of the increment law. -/
theorem coneAt_neg_one (t : Nat) : coneAt (-1) t = coneZero t := by
  unfold coneAt coneZero
  exact xorBelow_congr _ _ t (fun j _ => xorBelow_congr _ _ (t - j) (fun q _ => by
    show (pascalParity (t - 1 - j) q && runEnd j (-1 + 1 - (q : Int))) =
      (pascalParity (t - 1 - j) q && runEnd j (-(q : Int)))
    rw [show (-1 : Int) + 1 - (q : Int) = -(q : Int) by cfomega]))

/-- The center is the complement of the left light cone at every time. -/
theorem center_eq_not_coneAt_zero (t : Nat) : center t = !(coneAt 0 t) := by
  show cell t 0 = !(coneAt 0 t)
  rw [cell_eq_seedAt_bxor_coneAt t 0]
  show bxor (pascalParity t 0) (coneAt 0 t) = !(coneAt 0 t)
  rw [pascalParity_zero_right]
  cases coneAt 0 t <;> rfl

/-- **The masked tower word plus the increment is column `−1` of the half driven by the center**:
the recombination `Fixed.Phi` at column `0`, read in the coordinates of the right tower. -/
theorem maskedTower_increment_eq_Lh (t : Nat) :
    bxor (towerWord (t - 1) t && !(center t)) (bxor (center (t + 1)) (center t)) =
      Rule30UOR.Fixed.Lh Ruliology.CellularAutomata.Rule30Prize.center t (-1) := by
  have hm : (towerWord (t - 1) t && !(center t)) = maskedColumn t := by
    rcases t with _ | t
    · rfl
    · unfold maskedColumn
      rw [show t + 1 - 1 = t by cfomega, ← rdiag_eq_towerWord, ← cell_eq_rdiag (t + 1) t 1 (by cfomega)]
  rw [hm, center_increment_all, Rule30UOR.Fixed.Lh_center t (-1) (by cfomega),
    ← Rule30UOR.Scale.cell_eq_kit, ← Rule30UOR.KernelRoot.coneZero_eq_cell]
  cases maskedColumn t <;> cases coneZero t <;> rfl

/-! ## The dyadic scales: Frobenius and Kummer -/

/-- **Frobenius**: `C(2^k, a)` is even strictly between `0` and `2^k`. -/
theorem pascalParity_twopow_inner (k a : Nat) (ha0 : 0 < a) (ha : a < twopow k) :
    pascalParity (twopow k) a = false := by
  have h := pascalParity_add_twopow_mul k 0 a 1 ha
  rw [Nat.zero_add, Nat.mul_one] at h
  rw [h, pascalParity_zero_left a (by cfomega)]

/-- **Kummer at the complement**: for `i, q < 2^k`, `C(2^k − 1 − i, q) ≡ C(q + i, q)`; both are odd
exactly when the binary digits of `q` and `i` are disjoint (the Sierpinski mask). The digit
induction. -/
theorem pascalParity_complement_aux : ∀ (k i q : Nat), i < twopow k → q < twopow k →
    pascalParity (twopow k - 1 - i) q = pascalParity (q + i) q
  | 0, i, q, hi, hq => by
    have h1 : twopow 0 = 1 := rfl
    rw [show i = 0 by cfomega, show q = 0 by cfomega]
    rfl
  | k + 1, i, q, hi, hq => by
    have h2 : twopow (k + 1) = 2 * twopow k := by rw [twopow_succ]; cfomega
    rw [h2] at hi hq ⊢
    obtain ⟨a, e, he, rfl⟩ : ∃ a e, e < 2 ∧ i = 2 * a + e :=
      ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by cfomega⟩
    obtain ⟨b, f, hf, rfl⟩ : ∃ b f, f < 2 ∧ q = 2 * b + f :=
      ⟨q / 2, q % 2, Nat.mod_lt _ (by decide), by cfomega⟩
    have ha : a < twopow k := by cfomega
    have hb : b < twopow k := by cfomega
    have ih := pascalParity_complement_aux k a b ha hb
    rcases Nat.lt_or_ge e 1 with he0 | he1 <;> rcases Nat.lt_or_ge f 1 with hf0 | hf1
    · obtain rfl : e = 0 := by cfomega
      obtain rfl : f = 0 := by cfomega
      rw [show 2 * twopow k - 1 - (2 * a + 0) = 2 * (twopow k - 1 - a) + 1 by cfomega,
        show 2 * b + 0 + (2 * a + 0) = 2 * (b + a) by cfomega, show 2 * b + 0 = 2 * b by cfomega,
        pascalParity_odd_even, pascalParity_even_even, ih]
    · obtain rfl : e = 0 := by cfomega
      obtain rfl : f = 1 := by cfomega
      rw [show 2 * twopow k - 1 - (2 * a + 0) = 2 * (twopow k - 1 - a) + 1 by cfomega,
        show 2 * b + 1 + (2 * a + 0) = 2 * (b + a) + 1 by cfomega,
        pascalParity_odd_odd, pascalParity_odd_odd, ih]
    · obtain rfl : e = 1 := by cfomega
      obtain rfl : f = 0 := by cfomega
      rw [show 2 * twopow k - 1 - (2 * a + 1) = 2 * (twopow k - 1 - a) by cfomega,
        show 2 * b + 0 + (2 * a + 1) = 2 * (b + a) + 1 by cfomega, show 2 * b + 0 = 2 * b by cfomega,
        pascalParity_even_even, pascalParity_odd_even, ih]
    · obtain rfl : e = 1 := by cfomega
      obtain rfl : f = 1 := by cfomega
      rw [show 2 * twopow k - 1 - (2 * a + 1) = 2 * (twopow k - 1 - a) by cfomega,
        show 2 * b + 1 + (2 * a + 1) = 2 * (b + a + 1) by cfomega,
        pascalParity_even_odd, pascalParity_even_odd]

/-- **The block responses compose**: the response of a block of length `2^(k+1)` is the first half's
response at `p` and at `p − 2^k` plus the second half's response. -/
theorem window60_twopow_succ (t k : Nat) (p : Int) :
    window60 t (twopow (k + 1)) p =
      bxor (bxor (window60 t (twopow k) p) (window60 t (twopow k) (p + Rule30UOR.Scale.negpow k)))
        (window60 (t + twopow k) (twopow k) p) := by
  rw [show twopow (k + 1) = twopow k + twopow k from rfl, Rule30UOR.Gasket.window60_add,
    Rule30UOR.Scale.freshman, Rule30UOR.Scale.bxor_eq, Rule30UOR.Scale.bxor_eq]
  unfold Rule30UOR.Scale.negpow
  rw [show p + -((twopow k : Nat) : Int) = p - ((twopow k : Nat) : Int) by cfomega]

/-- The start of a block run transported `u` blocks by rule 60 at spacing `2^k`. -/
def blockSeed (k r u : Nat) (p : Int) : Bool :=
  xorBelow (fun h => pascalParity u h && cell r (p - ((twopow k * h : Nat) : Int))) (u + 1)

/-- The response of block `v` transported to block `u`, read at column `p`. -/
def blockRow (k r u v : Nat) (p : Int) : Bool :=
  xorBelow (fun h => pascalParity (u - 1 - v) h &&
    window60 (r + twopow k * v) (twopow k) (p - ((twopow k * h : Nat) : Int))) (u - v)

/-- The responses of the blocks `0, …, u − 1` transported to block `u`. -/
def blockCone (k r u : Nat) (p : Int) : Bool := xorBelow (fun v => blockRow k r u v p) u

/-- **Rule 30 at scale `2^k` is rule 60 at spacing `2^k` sourced by the block responses.** -/
theorem cell_block_duhamel (k r u : Nat) (p : Int) :
    cell (r + twopow k * u) p = bxor (blockSeed k r u p) (blockCone k r u p) := by
  have h := pascal_duhamel (fun v p => cell (r + twopow k * v) p)
    (fun v p => window60 (r + twopow k * v) (twopow k) p) (twopow k) 0
    (fun s p => by
      show cell (r + twopow k * (s + 1)) p =
        bxor (bxor (cell (r + twopow k * s) (p - ((twopow k : Nat) : Int))) (cell (r + twopow k * s) p))
          (window60 (r + twopow k * s) (twopow k) p)
      rw [show r + twopow k * (s + 1) = (r + twopow k * s) + twopow k by rw [Nat.mul_succ]; cfomega,
        Rule30UOR.Scale.scale, Rule30UOR.Scale.bxor_eq, Rule30UOR.Scale.bxor_eq]
      cases cell (r + twopow k * s) p <;> cases cell (r + twopow k * s) (p - ((twopow k : Nat) : Int)) <;>
        cases window60 (r + twopow k * s) (twopow k) p <;> rfl) u p
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- Inside the cone the seed part of a block run is the residue's center. -/
theorem blockSeed_center (k r u : Nat) (hr : r < twopow k) : blockSeed k r u 0 = center r := by
  unfold blockSeed
  rw [xorBelow_front]
  have e : xorBelow (fun m => pascalParity u (m + 1) &&
      cell r (0 - ((twopow k * (m + 1) : Nat) : Int))) u = false :=
    (xorBelow_congr _ (fun _ => false) u (fun m _ => by
      have hm : twopow k ≤ twopow k * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
      show (pascalParity u (m + 1) && cell r (0 - ((twopow k * (m + 1) : Nat) : Int))) = false
      rw [Rule30UOR.Scale.cell_left_white r _ (by generalize twopow k * (m + 1) = M at hm ⊢; cfomega),
        Bool.and_false])).trans (xorBelow_false _)
  rw [e, pascalParity_zero_right, Nat.mul_zero, show (0 : Int) - ((0 : Nat) : Int) = 0 by cfomega]
  show bxor (true && cell r 0) false = cell r 0
  cases cell r 0 <;> rfl

/-- **The center inside the cone of scale `2^k`**: for `r < 2^k`, `center (r + 2^k u)` is the
residue's center plus the block cone. -/
theorem center_block_cone (k r u : Nat) (hr : r < twopow k) :
    center (r + twopow k * u) = bxor (center r) (blockCone k r u 0) := by
  rw [← blockSeed_center k r u hr]
  exact cell_block_duhamel k r u 0

/-- The block cones of scale `2^k` at the center repeat with period `P` in the block index from
block `U`, on every residue. -/
def BlockConePeriodic (k U P : Nat) : Prop :=
  ∀ r u, r < twopow k → U ≤ u → blockCone k r (u + P) 0 = blockCone k r u 0

/-- A center period makes every block cone periodic with the same period in the block index. -/
theorem blockConePeriodic_of_centerPeriodic (T P k : Nat) (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    BlockConePeriodic k T P := by
  intro r u hr hu
  have hk := Rule30UOR.Scale.twopow_pos k
  have hle : u ≤ twopow k * u := Nat.le_mul_of_pos_left u hk
  have hper : center (r + twopow k * (u + P)) = center (r + twopow k * u) := by
    rw [show r + twopow k * (u + P) = (r + twopow k * u) + twopow k * P by rw [Nat.mul_add]; cfomega]
    exact Rule30UOR.Scale.center_mul hc (twopow k) (r + twopow k * u)
      (by generalize twopow k * u = M at hle ⊢; cfomega)
  rw [center_block_cone k r (u + P) hr, center_block_cone k r u hr] at hper
  exact Rule30UOR.DyadicRow.bxor_left_cancel _ _ _ hper

/-- Periodic block cones at one scale give a center period. -/
theorem centerPeriodic_of_blockConePeriodic (k U P : Nat) (h : BlockConePeriodic k U P) :
    Rule30UOR.Scale.CenterPeriodic (twopow k * U) (twopow k * P) := by
  intro t ht
  have hk := Rule30UOR.Scale.twopow_pos k
  have hd : t % twopow k + twopow k * (t / twopow k) = t := Nat.mod_add_div t (twopow k)
  have hU : U ≤ t / twopow k :=
    (Nat.le_div_iff_mul_le hk).mpr (by rw [Nat.mul_comm]; exact ht)
  have hr : t % twopow k < twopow k := Nat.mod_lt _ hk
  rw [← hd, show t % twopow k + twopow k * (t / twopow k) + twopow k * P =
      t % twopow k + twopow k * (t / twopow k + P) by rw [Nat.mul_add]; cfomega,
    center_block_cone k _ _ hr, center_block_cone k _ _ hr, h _ _ hr hU]

/-- The block cones of scale `2^k` have no eventual period in the block index. -/
def NoBlockConePeriod (k : Nat) : Prop := ∀ U P, 0 < P → ¬ BlockConePeriodic k U P

/-- **Cancelling at a scale is the period**: at every single scale `k`, Problem 1 is exactly the
statement that the block cones at the center have no common eventual period in the block index. -/
theorem problem1_iff_noBlockConePeriod (k : Nat) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ NoBlockConePeriod k := by
  rw [Rule30UOR.Scale.problem1_iff]
  unfold NoBlockConePeriod
  constructor
  · intro h U P hP hb
    exact h (twopow k * U) (twopow k * P) (Nat.mul_pos (Rule30UOR.Scale.twopow_pos k) hP)
      (centerPeriodic_of_blockConePeriodic k U P hb)
  · intro h T P hP hc
    exact h T P hP (blockConePeriodic_of_centerPeriodic T P k hc)

/-! ## The white prefix of the right words -/

/-- The white prefix repeats at Jen's period `2^(jenExp j)`. -/
theorem towerWord_white_periodic (j m s : Nat) (h : s + s < j) :
    towerWord j (s + twopow (Rule30UOR.RightPeriods.jenExp j) * m) = false := by
  induction m with
  | zero => rw [Nat.mul_zero, Nat.add_zero]; exact Rule30UOR.KernelRoot.towerWord_white j s h
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, Rule30UOR.RightPeriods.towerWord_jen_periodic j]
    exact ih

end Rule30UOR.ColumnCone
