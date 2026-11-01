module
public import Rule30UOR.LeftTower
public import Rule30UOR.Fixed
public import Rule30UOR.KitConstructive
public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Rule30UOR.KernelRoot
public import Rule30UOR.Automatic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The Pascal cone is the local rule integrated

The left light cone (`Antidiagonal.center_eq_leftCone`) is Duhamel's formula for rule 30 read as
rule 60 with sources: `x (t+1) p = x t (p−1) ⊕ x t p ⊕ runEnd t (p+1)`, the last term being the
carry `(b ∨ c) ⊕ b = c ∧ ¬b`. Integrating it gives the binomial transport of the run-ends.

* `Rule30UOR.KernelRoot.coneZero_eq_cell`: the cone from column `0` is column `−1`, so the increment law is the rule at
  column `0`, and `KernelRoot.not_eventuallyPeriodic_coneZero` (every period, no masked Jen) is Jen's adjacency
  theorem for the columns `−1, 0`.
* `transport_unique`: the Pascal transport is the unique solution of rule 60 with sources. For any
  boundary column `c`, the left half `Fixed.Lh c` driven from white is the transport of its own
  run-ends (`drivenShift_eq_transport`, `driven_duhamel` at every column).
* `driven_cone_defect`, `driven_cone_iff_btc`: for every boundary with `c 0 = true`, the cone
  identity `c t = ¬ drivenCone c t` fails exactly by the parity of the black-time defects, so it holds
  at every time exactly when `c` is black-time consistent (`c t → c (t+1) = ¬ Lh c t (−1)`). At the
  center the driven cone is the light cone (`drivenCone_center`), which re-proves
  `center t = ¬ leftCone t` for every `t` from black-time consistency alone (`center_eq_not_leftCone`).
* `isFixed_iff`, `problem1_iff_noPeriodicConsistent`: the fixed point of `Fixed.Phi` is black-time
  plus white-time consistency (`c ¬t → c (t+1) = Lh c t (−1) ⊕ Rh c t 1`); the light cone sees only
  the black times, and at white times its depth-`0` source is the right half's column `+1`
  (`drivenEnd_zero_of_wtc`).
* `problem1_of_noPeriodicBlackConsistent`: the left-only obligation the lens leaves, implied by the
  kit-level left mask at the start black at `−1` (`noPeriodicBlackConsistent_of_drivenLeftMask`).
  `driven_column_not_eventuallyPeriodic`: a periodically driven left half has an aperiodic column
  `−1`, hence an aperiodic cone from column `0` (the refuted route `driven-left-cone`, as a theorem).
* `leftCone_eq_xor_diagonalCone`: the light cone splits over the left diagonals, each read by the
  Fibonacci–Pascal transport `fibPascal` (2-kernel: `fibPascal_odd`, `fibPascal_even`), and
  `diagonalCone_periodic`: diagonal `d` contributes a `3·2^d`-periodic word from time `2^d`. So
  `problem1_iff_leftTail`: at every depth `D`, Problem 1 is the aperiodicity of the diagonals beyond
  `D`; no finite set of diagonals decides it.
-/

@[expose] public section

namespace Rule30UOR.DiagonalCone

open Rule30UOR.Core Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Band Rule30UOR.Antidiagonal
  Rule30UOR.LeftTower

/-! ## The cone from column `0` is column `−1` -/

/-! ## The Pascal transport: rule 60 with sources -/

/-- One row of the transport: the sources of time `j` at the depths `a + q`, `q ≤ n`, weighted by
`C(n, q) mod 2`. -/
def transportRow (S : Nat → Nat → Bool) (n j a : Nat) : Bool :=
  xorBelow (fun q => pascalParity n q && S j (a + q)) (n + 1)

/-- The Pascal transport of the source field `S` (time, depth) to depth `a` at time `t`. -/
def transport (S : Nat → Nat → Bool) (t a : Nat) : Bool :=
  xorBelow (fun j => transportRow S (t - 1 - j) j a) t

theorem bxor_rot (u x y : Bool) : bxor u (bxor x y) = bxor (bxor u y) x := by
  cases u <;> cases x <;> cases y <;> rfl

theorem and_bxor_left (p x y : Bool) : (p && bxor x y) = bxor (p && x) (p && y) := by
  cases p <;> cases x <;> cases y <;> rfl

/-- Pascal's rule on one row of the transport. -/
theorem transportRow_pascal (S : Nat → Nat → Bool) (n j a : Nat) :
    transportRow S (n + 1) j a = bxor (transportRow S n j a) (transportRow S n j (a + 1)) := by
  unfold transportRow
  have h1 : xorBelow (fun q => pascalParity (n + 1) q && S j (a + q)) (n + 1 + 1) =
      bxor (pascalParity (n + 1) 0 && S j (a + 0))
        (xorBelow (fun m => pascalParity (n + 1) (m + 1) && S j (a + (m + 1))) (n + 1)) :=
    xorBelow_front _ (n + 1)
  have h2 : xorBelow (fun q => pascalParity n q && S j (a + q)) (n + 1) =
      bxor (pascalParity n 0 && S j (a + 0))
        (xorBelow (fun m => pascalParity n (m + 1) && S j (a + (m + 1))) n) :=
    xorBelow_front _ n
  have h3 : xorBelow (fun m => pascalParity (n + 1) (m + 1) && S j (a + (m + 1))) (n + 1) =
      bxor (xorBelow (fun m => pascalParity n m && S j (a + 1 + m)) (n + 1))
        (xorBelow (fun m => pascalParity n (m + 1) && S j (a + (m + 1))) (n + 1)) := by
    rw [← xorBelow_bxor]
    apply xorBelow_congr
    intro m _
    show (pascalParity (n + 1) (m + 1) && S j (a + (m + 1))) =
      bxor (pascalParity n m && S j (a + 1 + m)) (pascalParity n (m + 1) && S j (a + (m + 1)))
    rw [pascalParity_succ, cone_and_bxor, show a + 1 + m = a + (m + 1) by cfomega]
  have h4 : xorBelow (fun m => pascalParity n (m + 1) && S j (a + (m + 1))) (n + 1) =
      xorBelow (fun m => pascalParity n (m + 1) && S j (a + (m + 1))) n := by
    show bxor (xorBelow (fun m => pascalParity n (m + 1) && S j (a + (m + 1))) n)
      (pascalParity n (n + 1) && S j (a + (n + 1))) = _
    rw [pascalParity_gt n (n + 1) (by cfomega), Bool.false_and, cone_bxor_false_right]
  rw [h1, h2, h3, h4, pascalParity_zero_right, pascalParity_zero_right]
  exact bxor_rot _ _ _

/-- **The transport solves rule 60 with sources**: depth `a` at time `t + 1` is depth `a` and
depth `a + 1` at time `t` plus the source at `(t, a)`. -/
theorem transport_succ (S : Nat → Nat → Bool) (t a : Nat) :
    transport S (t + 1) a = bxor (bxor (transport S t a) (transport S t (a + 1))) (S t a) := by
  unfold transport
  show bxor (xorBelow (fun j => transportRow S (t + 1 - 1 - j) j a) t)
    (transportRow S (t + 1 - 1 - t) t a) = _
  have hlast : transportRow S (t + 1 - 1 - t) t a = S t a := by
    rw [show t + 1 - 1 - t = 0 by cfomega]
    show bxor false (pascalParity 0 0 && S t (a + 0)) = S t a
    rw [pascalParity_zero_right, Bool.true_and, cone_bxor_false]
    rfl
  rw [hlast, xorBelow_congr (fun j => transportRow S (t + 1 - 1 - j) j a)
      (fun j => bxor (transportRow S (t - 1 - j) j a) (transportRow S (t - 1 - j) j (a + 1))) t
      (fun j _ => by
        show transportRow S (t + 1 - 1 - j) j a = _
        rw [show t + 1 - 1 - j = (t - 1 - j) + 1 by cfomega, transportRow_pascal]),
    xorBelow_bxor]

/-- **Uniqueness**: a field that starts white and obeys rule 60 with the sources `S` is their
transport. -/
theorem transport_unique (S X : Nat → Nat → Bool)
    (hstep : ∀ t a, X (t + 1) a = bxor (bxor (X t a) (X t (a + 1))) (S t a))
    (h0 : ∀ a, X 0 a = false) : ∀ t a, X t a = transport S t a := by
  intro t
  induction t with
  | zero => intro a; rw [h0]; rfl
  | succ t ih => intro a; rw [hstep, ih a, ih (a + 1), transport_succ]

/-- The transport is linear in the sources. -/
theorem transport_bxor (S U : Nat → Nat → Bool) (t a : Nat) :
    transport (fun j b => bxor (S j b) (U j b)) t a = bxor (transport S t a) (transport U t a) := by
  unfold transport
  rw [← xorBelow_bxor]
  apply xorBelow_congr
  intro j _
  unfold transportRow
  rw [← xorBelow_bxor]
  apply xorBelow_congr
  intro q _
  exact and_bxor_left _ _ _

/-- A source on depth `0` alone reaches depth `0` with weight `1`: its running parity. -/
theorem transport_point (g : Nat → Bool) (t : Nat) :
    transport (fun j b => decide (b = 0) && g j) t 0 = xorBelow g t := by
  unfold transport
  apply xorBelow_congr
  intro j _
  unfold transportRow
  rw [xorBelow_front,
    xorBelow_congr _ (fun _ => false) _ (fun m _ => by
      show (pascalParity (t - 1 - j) (m + 1) && (decide (0 + (m + 1) = 0) && g j)) = false
      rw [decide_eq_false (by cfomega : ¬ (0 + (m + 1) = 0))]
      cases pascalParity (t - 1 - j) (m + 1) <;> rfl),
    xorBelow_false, pascalParity_zero_right]
  show bxor (true && (decide (0 + 0 = 0) && g j)) false = g j
  cases g j <;> rfl

/-! ## The driven left half is the transport of its own run-ends -/

section Driven

open Rule30UOR.Fixed

theorem Lh_zero_neg (c : Nat → Bool) (p : Int) (hp : p < 0) : Lh c 0 p = false := by
  simp only [Lh, if_pos hp]

theorem Lh_col0 (c : Nat → Bool) (t : Nat) : Lh c t 0 = c t := by
  cases t with
  | zero => simp only [Lh, if_neg (by decide : ¬ ((0 : Int) < 0))]
  | succ t => simp only [Lh, if_neg (by decide : ¬ ((0 : Int) < 0))]

theorem Lh_succ_neg (c : Nat → Bool) (t : Nat) (p : Int) (hp : p < 0) :
    Lh c (t + 1) p = Ruliology.CellularAutomata.Rule30Jen.rule (Lh c t (p - 1)) (Lh c t p) (Lh c t (p + 1)) := by
  simp only [Lh, if_pos hp]

theorem rule_split (l m r : Bool) :
    Ruliology.CellularAutomata.Rule30Jen.rule l m r = bxor (bxor m l) (r && !m) := by
  cases l <;> cases m <;> cases r <;> rfl

/-- The source of the left half driven by `c` at depth `a` (position `1 − a`): for `a ≥ 1` the
run-end of the half; at `a = 0` the effective run-end at column `+1`, read off the rule at
column `0` on the white times of `c`. -/
def drivenEnd (c : Nat → Bool) (j a : Nat) : Bool :=
  if a = 0 then (bxor (c (j + 1)) (Lh c j (-1)) && !(c j))
  else (Lh c j (1 - (a : Int)) && !(Lh c j (-(a : Int))))

/-- The exact source: at depth `0`, whatever makes column `0` equal to `c`. -/
def exactEnd (c : Nat → Bool) (j a : Nat) : Bool :=
  if a = 0 then bxor (bxor (c (j + 1)) (Lh c j (-1))) (c j)
  else (Lh c j (1 - (a : Int)) && !(Lh c j (-(a : Int))))

/-- The black-time defect: `c` is black at `j` and `c (j+1)` is not the complement of column `−1`. -/
def blackDefect (c : Nat → Bool) (j : Nat) : Bool := c j && !(bxor (c (j + 1)) (Lh c j (-1)))

/-- A boundary column is black-time consistent: at every black time the next value is the
complement of column `−1` of the half it drives. -/
def BlackTimeConsistent (c : Nat → Bool) : Prop := ∀ t, c t = true → c (t + 1) = !(Lh c t (-1))

/-- The cone of the half driven by `c`: the transport of its sources to column `0`. -/
def drivenCone (c : Nat → Bool) (t : Nat) : Bool := transport (drivenEnd c) t 0

/-- The driven half at depth `a` with the seed's own propagation removed. -/
def drivenShift (c : Nat → Bool) (t a : Nat) : Bool :=
  bxor (Lh c t (-(a : Int))) (c 0 && decide (a = 0))

theorem drivenShift_zero (c : Nat → Bool) (a : Nat) : drivenShift c 0 a = false := by
  unfold drivenShift
  rcases a with _ | b
  · rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0]
    cases c 0 <;> rfl
  · rw [Lh_zero_neg c _ (by cfomega), decide_eq_false (by cfomega : ¬ (b + 1 = 0)), Bool.and_false]
    rfl

/-- **The driven half obeys rule 60 with its exact sources.** -/
theorem drivenShift_step (c : Nat → Bool) (t a : Nat) :
    drivenShift c (t + 1) a = bxor (bxor (drivenShift c t a) (drivenShift c t (a + 1))) (exactEnd c t a) := by
  unfold drivenShift exactEnd
  rcases a with _ | b
  · rw [if_pos rfl, show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0, Lh_col0,
      show (-((0 + 1 : Nat) : Int)) = -1 by cfomega, decide_eq_false (by cfomega : ¬ (0 + 1 = 0)),
      Bool.and_false]
    cases c 0 <;> cases c t <;> cases c (t + 1) <;> cases Lh c t (-1) <;> rfl
  · have hstep := Lh_succ_neg c t (-((b + 1 : Nat) : Int)) (by cfomega)
    rw [show (-((b + 1 : Nat) : Int)) - 1 = -((b + 1 + 1 : Nat) : Int) by cfomega,
      show (-((b + 1 : Nat) : Int)) + 1 = 1 - ((b + 1 : Nat) : Int) by cfomega] at hstep
    rw [if_neg (by cfomega : ¬ (b + 1 = 0)), hstep, rule_split,
      decide_eq_false (by cfomega : ¬ (b + 1 = 0)), decide_eq_false (by cfomega : ¬ (b + 1 + 1 = 0)),
      Bool.and_false]
    cases Lh c t (-((b + 1 + 1 : Nat) : Int)) <;> cases Lh c t (-((b + 1 : Nat) : Int)) <;>
      cases Lh c t (1 - ((b + 1 : Nat) : Int)) <;> rfl

/-- **Duhamel for the driven half**: the driven half (seed propagation removed) is the transport
of its exact sources. -/
theorem drivenShift_eq_transport (c : Nat → Bool) : ∀ t a, drivenShift c t a = transport (exactEnd c) t a :=
  transport_unique (exactEnd c) (drivenShift c) (drivenShift_step c) (drivenShift_zero c)

/-- The exact source is the driven source plus the black-time defect on depth `0`. -/
theorem exactEnd_split (c : Nat → Bool) (j a : Nat) :
    exactEnd c j a = bxor (drivenEnd c j a) (decide (a = 0) && blackDefect c j) := by
  unfold exactEnd drivenEnd blackDefect
  rcases a with _ | b
  · rw [if_pos rfl, if_pos rfl]
    cases c j <;> cases c (j + 1) <;> cases Lh c j (-1) <;> rfl
  · rw [if_neg (by cfomega : ¬ (b + 1 = 0)), if_neg (by cfomega : ¬ (b + 1 = 0)),
      decide_eq_false (by cfomega : ¬ (b + 1 = 0)), Bool.false_and]
    cases (Lh c j (1 - ((b + 1 : Nat) : Int)) && !Lh c j (-((b + 1 : Nat) : Int))) <;> rfl

theorem transport_exactEnd (c : Nat → Bool) (t : Nat) :
    transport (exactEnd c) t 0 = bxor (drivenCone c t) (xorBelow (blackDefect c) t) := by
  have e : exactEnd c = fun j b => bxor (drivenEnd c j b) (decide (b = 0) && blackDefect c j) :=
    funext fun j => funext fun b => exactEnd_split c j b
  rw [e, transport_bxor, transport_point]
  rfl

/-- **The cone identity fails exactly by the black-time defects**: for every boundary with
`c 0 = true`, `¬ drivenCone c t = c t ⊕ (parity of the defects before t)`. -/
theorem driven_cone_defect (c : Nat → Bool) (h0 : c 0 = true) (t : Nat) :
    (!(drivenCone c t)) = bxor (c t) (xorBelow (blackDefect c) t) := by
  have h := drivenShift_eq_transport c t 0
  unfold drivenShift at h
  rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0, h0, transport_exactEnd] at h
  revert h
  cases c t <;> cases drivenCone c t <;> cases xorBelow (blackDefect c) t <;> decide

theorem blackDefect_false_of_btc (c : Nat → Bool) (h : BlackTimeConsistent c) (j : Nat) :
    blackDefect c j = false := by
  unfold blackDefect
  cases hj : c j
  · rfl
  · rw [h j hj]
    cases Lh c j (-1) <;> rfl

theorem btc_of_blackDefect_false (c : Nat → Bool) (h : ∀ j, blackDefect c j = false) :
    BlackTimeConsistent c := by
  intro t ht
  have e := h t
  unfold blackDefect at e
  rw [ht] at e
  revert e
  cases c (t + 1) <;> cases Lh c t (-1) <;> decide

/-- **The cone identity is exactly black-time consistency.** -/
theorem driven_cone_iff_btc (c : Nat → Bool) (h0 : c 0 = true) :
    (∀ t, c t = !(drivenCone c t)) ↔ BlackTimeConsistent c := by
  constructor
  · intro h
    have hx : ∀ t, xorBelow (blackDefect c) t = false := by
      intro t
      have e := driven_cone_defect c h0 t
      rw [← h t] at e
      revert e
      cases c t <;> cases xorBelow (blackDefect c) t <;> decide
    apply btc_of_blackDefect_false
    intro j
    have e := hx (j + 1)
    show blackDefect c j = false
    have e' : bxor (xorBelow (blackDefect c) j) (blackDefect c j) = false := e
    rw [hx j] at e'
    revert e'
    cases blackDefect c j <;> decide
  · intro h t
    have hx : xorBelow (blackDefect c) t = false := by
      rw [xorBelow_congr (blackDefect c) (fun _ => false) t (fun j _ => blackDefect_false_of_btc c h j),
        xorBelow_false]
    have e := driven_cone_defect c h0 t
    rw [hx] at e
    revert e
    cases c t <;> cases drivenCone c t <;> decide

/-- **The center is black-time consistent**: at a black center time, column `−1` is the
complement of the next center value. -/
theorem center_blackTimeConsistent : BlackTimeConsistent Ruliology.CellularAutomata.Rule30Prize.center := by
  intro t ht
  rw [Lh_center t (-1) (by cfomega)]
  have e := Ruliology.CellularAutomata.Rule30MaskedJen.left_of_black t 0 ht
  rw [show (0 : Int) - 1 = -1 by cfomega] at e
  rw [e]
  show Ruliology.CellularAutomata.Rule30Jen.cell (t + 1) 0 = !!(Ruliology.CellularAutomata.Rule30Jen.cell (t + 1) 0)
  cases Ruliology.CellularAutomata.Rule30Jen.cell (t + 1) 0 <;> rfl

/-- Duhamel at every column of the driven half: column `−(a+1)` is the transport of the driven
sources to depth `a + 1`. -/
theorem driven_duhamel (c : Nat → Bool) (t a : Nat) :
    transport (drivenEnd c) t (a + 1) = Lh c t (-((a + 1 : Nat) : Int)) := by
  have h := drivenShift_eq_transport c t (a + 1)
  unfold drivenShift at h
  rw [decide_eq_false (by cfomega : ¬ (a + 1 = 0)), Bool.and_false] at h
  have e : transport (exactEnd c) t (a + 1) = transport (drivenEnd c) t (a + 1) := by
    unfold transport
    apply xorBelow_congr
    intro j _
    unfold transportRow
    apply xorBelow_congr
    intro q _
    show (pascalParity (t - 1 - j) q && exactEnd c j (a + 1 + q)) =
      (pascalParity (t - 1 - j) q && drivenEnd c j (a + 1 + q))
    unfold exactEnd drivenEnd
    rw [if_neg (by cfomega : ¬ (a + 1 + q = 0)), if_neg (by cfomega : ¬ (a + 1 + q = 0))]
  rw [← e, ← h]
  cases Lh c t (-((a + 1 : Nat) : Int)) <;> rfl

/-- The driven cone from column `0` is column `−1` of the driven half. -/
theorem driven_coneZero_eq_Lh (c : Nat → Bool) (t : Nat) : transport (drivenEnd c) t 1 = Lh c t (-1) :=
  driven_duhamel c t 0

end Driven


/-! ## The center: the left light cone is black-time consistency integrated -/

section CenterCone

open Rule30UOR.Fixed

/-- At the center the driven sources are the left run-ends of the pattern. -/
theorem drivenEnd_center (j q : Nat) :
    drivenEnd Ruliology.CellularAutomata.Rule30Prize.center j q = leftEnd j q := by
  unfold drivenEnd leftEnd runEnd
  rcases q with _ | b
  · rw [if_pos rfl, Lh_center j (-1) (by cfomega), show (1 : Int) - ((0 : Nat) : Int) = 1 by cfomega,
      show (1 : Int) - 1 = 0 by cfomega, Rule30UOR.Scale.cell_eq_kit, Rule30UOR.Scale.cell_eq_kit]
    show (bxor (Ruliology.CellularAutomata.Rule30Jen.rule (Ruliology.CellularAutomata.Rule30Jen.cell j (0 - 1))
        (Ruliology.CellularAutomata.Rule30Jen.cell j 0) (Ruliology.CellularAutomata.Rule30Jen.cell j (0 + 1)))
        (Ruliology.CellularAutomata.Rule30Jen.cell j (-1)) && !(Ruliology.CellularAutomata.Rule30Jen.cell j 0)) = _
    rw [show (0 : Int) - 1 = -1 by cfomega, show (0 : Int) + 1 = 1 by cfomega]
    cases Ruliology.CellularAutomata.Rule30Jen.cell j (-1) <;> cases Ruliology.CellularAutomata.Rule30Jen.cell j 0 <;>
      cases Ruliology.CellularAutomata.Rule30Jen.cell j 1 <;> rfl
  · rw [if_neg (by cfomega : ¬ (b + 1 = 0)), Lh_center j _ (by cfomega), Lh_center j _ (by cfomega),
      Rule30UOR.Scale.cell_eq_kit, Rule30UOR.Scale.cell_eq_kit,
      show (1 : Int) - ((b + 1 : Nat) : Int) - 1 = -((b + 1 : Nat) : Int) by cfomega]

/-- The cone of the half driven by the center is the left light cone. -/
theorem drivenCone_center (t : Nat) :
    drivenCone Ruliology.CellularAutomata.Rule30Prize.center t = leftCone t := by
  unfold drivenCone transport leftCone
  apply xorBelow_congr
  intro j hj
  unfold transportRow coneRow
  rw [show t - j = t - 1 - j + 1 by cfomega]
  apply xorBelow_congr
  intro q _
  show (pascalParity (t - 1 - j) q && drivenEnd Ruliology.CellularAutomata.Rule30Prize.center j (0 + q)) =
    (pascalParity (t - 1 - j) q && leftEnd j q)
  rw [Nat.zero_add, drivenEnd_center]

/-- **The left light cone at every time, from black-time consistency alone**: `center t = ¬ leftCone t`
for all `t`, by Duhamel for the half driven by the center (no tower, no Lucas). -/
theorem center_eq_not_leftCone (t : Nat) : center t = !(leftCone t) := by
  have e := driven_cone_defect Ruliology.CellularAutomata.Rule30Prize.center rfl t
  rw [drivenCone_center,
    xorBelow_congr _ (fun _ => false) t
      (fun j _ => blackDefect_false_of_btc _ center_blackTimeConsistent j),
    xorBelow_false, Rule30UOR.Scale.bxor_eq, Bool.xor_false] at e
  rw [Rule30UOR.Scale.center_eq_kit, ← e]

end CenterCone

/-! ## The left-only obligation the lens leaves -/

section LeftOnly

open Rule30UOR.Fixed

/-- A column is eventually white. -/
def EventuallyWhite (c : Nat → Bool) : Prop := ∃ T, ∀ t, T ≤ t → c t = false

/-- **No eventually periodic black-time consistent boundary keeps black times**: every boundary
with `c 0 = true` whose next value is the complement of its driven column `−1` at each black time,
and which is eventually periodic, is eventually white. -/
def NoPeriodicBlackConsistent : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c →
    Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic c → EventuallyWhite c

/-- **The left-only obligation decides Problem 1.** -/
theorem problem1_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 := by
  intro hep
  obtain ⟨T, hT⟩ := h Ruliology.CellularAutomata.Rule30Prize.center rfl center_blackTimeConsistent hep
  exact Rule30UOR.KitConstructive.center_not_eventually_constant ⟨T, false, hT⟩

/-- The kit-level left mask (`Rule30LeftMask.LeftMask` of the bridge, verbatim). -/
def DrivenLeftMask : Prop :=
  ∀ (c : Nat → Bool) (s : Int → Bool) (m : Nat), 0 < m →
    (∀ p : Int, p < -(m : Int) → s p = false) → s (-(m : Int)) = true →
    Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic c → (∀ T, ∃ t, T ≤ t ∧ c t = true) →
    ¬ ∃ T, ∀ t, T ≤ t → c t = true →
      Ruliology.CellularAutomata.Rule30DrivenLeft.L c s t (-1) = !c (t + 1)

/-- From time `1` the half driven by `c` from white is the kit's driven half with start black at `−1`
and boundary `c (· + 1)`. -/
theorem L_shift (c : Nat → Bool) : ∀ (k : Nat) (p : Int), p ≤ 0 →
    Ruliology.CellularAutomata.Rule30DrivenLeft.L (fun k => c (k + 1)) (fun p => Lh c 1 p) k p = Lh c (k + 1) p
  | 0, p, hp => by
    rcases Int.lt_or_eq_of_le hp with h | h
    · simp only [Ruliology.CellularAutomata.Rule30DrivenLeft.L, if_pos h]
    · subst h
      simp only [Ruliology.CellularAutomata.Rule30DrivenLeft.L, if_neg (by decide : ¬ ((0 : Int) < 0))]
      exact (Lh_col0 c 1).symm
  | k + 1, p, hp => by
    rcases Int.lt_or_eq_of_le hp with h | h
    · rw [Ruliology.CellularAutomata.Rule30DrivenLeft.L_succ h, Lh_succ_neg c (k + 1) p h,
        L_shift c k (p - 1) (by cfomega), L_shift c k p (by cfomega), L_shift c k (p + 1) (by cfomega)]
    · subst h
      rw [Ruliology.CellularAutomata.Rule30DrivenLeft.L_col0, Lh_col0]

theorem start_white (c : Nat → Bool) (p : Int) (hp : p < -((1 : Nat) : Int)) : Lh c 1 p = false := by
  rw [Lh_succ_neg c 0 p (by cfomega), Lh_zero_neg c (p - 1) (by cfomega), Lh_zero_neg c p (by cfomega),
    Lh_zero_neg c (p + 1) (by cfomega)]
  rfl

theorem start_black (c : Nat → Bool) (h0 : c 0 = true) : Lh c 1 (-((1 : Nat) : Int)) = true := by
  rw [show (-((1 : Nat) : Int)) = -1 by cfomega, Lh_succ_neg c 0 (-1) (by decide),
    Lh_zero_neg c (-1 - 1) (by decide), Lh_zero_neg c (-1) (by decide), show (-1 : Int) + 1 = 0 by decide,
    Lh_col0, h0]
  rfl

theorem shift_eventuallyPeriodic (c : Nat → Bool) (hc : Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic c) :
    Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic (fun k => c (k + 1)) := by
  obtain ⟨T, P, hP, h⟩ := hc
  refine ⟨T, P, hP, fun k hk => ?_⟩
  show c (k + P + 1) = c (k + 1)
  rw [show k + P + 1 = k + 1 + P by cfomega]
  exact h (k + 1) (by cfomega)

/-- **The kit-level left mask implies the left-only obligation** (start black at `−1` at time `1`). -/
theorem noPeriodicBlackConsistent_of_drivenLeftMask (hL : DrivenLeftMask) : NoPeriodicBlackConsistent := by
  intro c h0 hbtc hep
  have hep' := shift_eventuallyPeriodic c hep
  obtain ⟨T, P, hP, hper⟩ := hep
  refine Decidable.byCases (p := ∃ r, r < P ∧ c (T + r) = true) (fun hb => ?_) (fun hno => ?_)
  · exfalso
    obtain ⟨r, _, hr⟩ := hb
    have hrec : ∀ N, ∃ t, N ≤ t ∧ c (t + 1) = true := by
      intro N
      have hNP : (N + 1) * 1 ≤ (N + 1) * P := Nat.mul_le_mul_left (N + 1) hP
      refine ⟨T + r + (N + 1) * P - 1, by cfomega, ?_⟩
      rw [show T + r + (N + 1) * P - 1 + 1 = T + r + (N + 1) * P by cfomega,
        Ruliology.CellularAutomata.Rule30Jen.periodic_mul hper (N + 1) (T + r) (by cfomega)]
      exact hr
    refine hL (fun k => c (k + 1)) (fun p => Lh c 1 p) 1 (by decide) (start_white c) (start_black c h0)
      hep' hrec ⟨0, fun k _ hk => ?_⟩
    show Ruliology.CellularAutomata.Rule30DrivenLeft.L (fun k => c (k + 1)) (fun p => Lh c 1 p) k (-1) =
      !c (k + 1 + 1)
    rw [L_shift c k (-1) (by decide), hbtc (k + 1) hk]
    cases Lh c (k + 1) (-1) <;> rfl
  · refine ⟨T, fun u hu => ?_⟩
    have hr : (u - T) % P < P := Nat.mod_lt _ hP
    have he : T + (u - T) % P + ((u - T) / P) * P = u := by
      have hh := Nat.mod_add_div (u - T) P
      rw [Nat.mul_comm P ((u - T) / P)] at hh
      cfomega
    have hp := Ruliology.CellularAutomata.Rule30Jen.periodic_mul hper ((u - T) / P) (T + (u - T) % P) (by cfomega)
    rw [he] at hp
    rw [hp]
    cases h : c (T + (u - T) % P)
    · rfl
    · exact absurd ⟨(u - T) % P, hr, h⟩ hno

/-- **The driven column `−1` has no eventual period**: for every eventually periodic boundary with
`c 0 = true`, column `−1` of the half it drives from white (equivalently, by `driven_coneZero_eq_Lh`,
its cone from column `0`) is not eventually periodic. Jen's adjacency theorem inside the half. -/
theorem driven_column_not_eventuallyPeriodic (c : Nat → Bool) (h0 : c 0 = true)
    (hc : Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic c) :
    ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic (fun t => Lh c t (-1)) := by
  intro hx
  apply Ruliology.CellularAutomata.Rule30DrivenLeft.col_neg_one_not_periodic
    (c := fun k => c (k + 1)) (s := fun p => Lh c 1 p) (m := 1) (start_white c) (start_black c h0)
    (by decide) (shift_eventuallyPeriodic c hc)
  obtain ⟨T, P, hP, h⟩ := hx
  refine ⟨T, P, hP, fun k hk => ?_⟩
  show Ruliology.CellularAutomata.Rule30DrivenLeft.L (fun k => c (k + 1)) (fun p => Lh c 1 p) (k + P) (-1) =
    Ruliology.CellularAutomata.Rule30DrivenLeft.L (fun k => c (k + 1)) (fun p => Lh c 1 p) k (-1)
  rw [L_shift c (k + P) (-1) (by decide), L_shift c k (-1) (by decide), show k + P + 1 = k + 1 + P by cfomega]
  exact h (k + 1) (by cfomega)

end LeftOnly


/-! ## The Fibonacci–Pascal transport along one left diagonal

On the left diagonal `d` (cells `cell s (d − s)`), the run-end at time `d + m − 1` sits at position
`1 − m` and reaches the center at time `t` with weight `C(t − d − m, m) mod 2`: the anti-diagonal
binomial sums, whose total over a constant word is the Fibonacci parity (period 3). -/

/-- `⊕_{m ≤ n} C(n − m, m) ρ(m)`. -/
def fibPascal (ρ : Nat → Bool) (n : Nat) : Bool :=
  xorBelow (fun m => pascalParity (n - m) m && ρ m) (n + 1)

theorem fibPascal_congr (ρ σ : Nat → Bool) (h : ∀ m, ρ m = σ m) (n : Nat) :
    fibPascal ρ n = fibPascal σ n := by
  unfold fibPascal
  apply xorBelow_congr
  intro m _
  show (pascalParity (n - m) m && ρ m) = (pascalParity (n - m) m && σ m)
  rw [h m]

theorem fibPascal_zero (ρ : Nat → Bool) : fibPascal ρ 0 = ρ 0 := by
  show bxor false (pascalParity (0 - 0) 0 && ρ 0) = ρ 0
  rw [pascalParity_zero_right]
  cases ρ 0 <;> rfl

theorem fibPascal_bxor (ρ σ : Nat → Bool) (n : Nat) :
    fibPascal (fun m => bxor (ρ m) (σ m)) n = bxor (fibPascal ρ n) (fibPascal σ n) := by
  unfold fibPascal
  rw [← xorBelow_bxor]
  apply xorBelow_congr
  intro m _
  exact and_bxor_left _ _ _

/-- The odd part of the 2-kernel: `f_ρ(2n+1) = f_{ρ(2·)}(n)`. -/
theorem fibPascal_odd (ρ : Nat → Bool) (n : Nat) :
    fibPascal ρ (2 * n + 1) = fibPascal (fun k => ρ (2 * k)) n := by
  unfold fibPascal
  have h := xorBelow_even_odd (fun m => pascalParity (2 * n + 1 - m) m && ρ m) (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by cfomega] at h
  rw [h, xorBelow_congr (fun k => pascalParity (2 * n + 1 - (2 * k + 1)) (2 * k + 1) && ρ (2 * k + 1))
      (fun _ => false) (n + 1)
      (fun k hk => by
        show (pascalParity (2 * n + 1 - (2 * k + 1)) (2 * k + 1) && ρ (2 * k + 1)) = false
        rw [show 2 * n + 1 - (2 * k + 1) = 2 * (n - k) by cfomega, pascalParity_even_odd, Bool.false_and]),
    xorBelow_false, cone_bxor_false_right]
  apply xorBelow_congr
  intro k hk
  show (pascalParity (2 * n + 1 - 2 * k) (2 * k) && ρ (2 * k)) = (pascalParity (n - k) k && ρ (2 * k))
  rw [show 2 * n + 1 - 2 * k = 2 * (n - k) + 1 by cfomega, pascalParity_odd_even]

/-- The even part of the 2-kernel: `f_ρ(2n+2) = f_{ρ(2·)}(n+1) ⊕ f_{ρ(2·+1)}(n)`. -/
theorem fibPascal_even (ρ : Nat → Bool) (n : Nat) :
    fibPascal ρ (2 * n + 2) =
      bxor (fibPascal (fun k => ρ (2 * k)) (n + 1)) (fibPascal (fun k => ρ (2 * k + 1)) n) := by
  unfold fibPascal
  have h := xorBelow_even_odd (fun m => pascalParity (2 * n + 2 - m) m && ρ m) (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 2 by cfomega] at h
  show bxor (xorBelow (fun m => pascalParity (2 * n + 2 - m) m && ρ m) (2 * n + 2))
      (pascalParity (2 * n + 2 - (2 * n + 2)) (2 * n + 2) && ρ (2 * n + 2)) =
    bxor (bxor (xorBelow (fun k => pascalParity (n + 1 - k) k && ρ (2 * k)) (n + 1))
        (pascalParity (n + 1 - (n + 1)) (n + 1) && ρ (2 * (n + 1))))
      (xorBelow (fun k => pascalParity (n - k) k && ρ (2 * k + 1)) (n + 1))
  rw [h, show 2 * n + 2 - (2 * n + 2) = 0 by cfomega, show n + 1 - (n + 1) = 0 by cfomega,
    pascalParity_zero_left (2 * n + 2) (by cfomega), pascalParity_zero_left (n + 1) (by cfomega),
    Bool.false_and, Bool.false_and, cone_bxor_false_right, cone_bxor_false_right]
  rw [xorBelow_congr (fun k => pascalParity (2 * n + 2 - 2 * k) (2 * k) && ρ (2 * k))
      (fun k => pascalParity (n + 1 - k) k && ρ (2 * k)) (n + 1)
      (fun k hk => by
        show (pascalParity (2 * n + 2 - 2 * k) (2 * k) && ρ (2 * k)) = (pascalParity (n + 1 - k) k && ρ (2 * k))
        rw [show 2 * n + 2 - 2 * k = 2 * (n + 1 - k) by cfomega, pascalParity_even_even]),
    xorBelow_congr (fun k => pascalParity (2 * n + 2 - (2 * k + 1)) (2 * k + 1) && ρ (2 * k + 1))
      (fun k => pascalParity (n - k) k && ρ (2 * k + 1)) (n + 1)
      (fun k hk => by
        show (pascalParity (2 * n + 2 - (2 * k + 1)) (2 * k + 1) && ρ (2 * k + 1)) =
          (pascalParity (n - k) k && ρ (2 * k + 1))
        rw [show 2 * n + 2 - (2 * k + 1) = 2 * (n - k) + 1 by cfomega, pascalParity_odd_odd])]

/-- On a constant word the transport is the Fibonacci parity: `b` off the residue `2 mod 3`. -/
theorem fibPascal_const (b : Bool) : ∀ n, fibPascal (fun _ => b) n = (b && !(decide (n % 3 = 2))) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by cfomega⟩
      rcases k with _ | k
      · rw [fibPascal_zero]
        cases b <;> rfl
      · rw [show 2 * (k + 1) = 2 * k + 2 by cfomega, fibPascal_even, ih (k + 1) (by cfomega), ih k (by cfomega)]
        rcases (by cfomega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
        · rw [decide_eq_false (by cfomega : ¬ ((k + 1) % 3 = 2)), decide_eq_false (by cfomega : ¬ (k % 3 = 2)),
            decide_eq_true (by cfomega : (2 * k + 2) % 3 = 2)]
          cases b <;> rfl
        · rw [decide_eq_true (by cfomega : (k + 1) % 3 = 2), decide_eq_false (by cfomega : ¬ (k % 3 = 2)),
            decide_eq_false (by cfomega : ¬ ((2 * k + 2) % 3 = 2))]
          cases b <;> rfl
        · rw [decide_eq_false (by cfomega : ¬ ((k + 1) % 3 = 2)), decide_eq_true (by cfomega : k % 3 = 2),
            decide_eq_false (by cfomega : ¬ ((2 * k + 2) % 3 = 2))]
          cases b <;> rfl
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by cfomega⟩
      rw [fibPascal_odd, ih k (by cfomega)]
      rcases (by cfomega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
      · rw [decide_eq_false (by cfomega : ¬ (k % 3 = 2)), decide_eq_false (by cfomega : ¬ ((2 * k + 1) % 3 = 2))]
      · rw [decide_eq_false (by cfomega : ¬ (k % 3 = 2)), decide_eq_false (by cfomega : ¬ ((2 * k + 1) % 3 = 2))]
      · rw [decide_eq_true (by cfomega : k % 3 = 2), decide_eq_true (by cfomega : (2 * k + 1) % 3 = 2)]

/-- **Period `3·2^a`**: on a `2^a`-periodic word the transport is `3·2^a`-periodic from `0`, and it
vanishes at `3·2^a − 1`. -/
theorem fibPascal_periodic (a : Nat) : ∀ ρ : Nat → Bool, (∀ m, ρ (m + twopow a) = ρ m) →
    (∀ n, fibPascal ρ (n + 3 * twopow a) = fibPascal ρ n) ∧ fibPascal ρ (3 * twopow a - 1) = false := by
  induction a with
  | zero =>
    intro ρ hρ
    have hc : ∀ m, ρ m = ρ 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [← ih]; exact hρ m
    have hf : ∀ n, fibPascal ρ n = (ρ 0 && !(decide (n % 3 = 2))) := fun n => by
      rw [fibPascal_congr ρ (fun _ => ρ 0) hc n, fibPascal_const]
    refine ⟨fun n => ?_, ?_⟩
    · rw [hf, hf, show (n + 3 * twopow 0) % 3 = n % 3 by (show (n + 3 * 1) % 3 = n % 3; cfomega)]
    · rw [hf]
      show (ρ 0 && !(decide ((3 * 1 - 1) % 3 = 2))) = false
      cases ρ 0 <;> rfl
  | succ a ih =>
    intro ρ hρ
    have hQ : 0 < twopow a := Rule30UOR.Scale.twopow_pos a
    have h2 : twopow (a + 1) = twopow a + twopow a := rfl
    have hρe : ∀ m, ρ (2 * (m + twopow a)) = ρ (2 * m) := fun m => by
      rw [show 2 * (m + twopow a) = 2 * m + twopow (a + 1) by rw [h2]; cfomega]
      exact hρ (2 * m)
    have hρo : ∀ m, ρ (2 * (m + twopow a) + 1) = ρ (2 * m + 1) := fun m => by
      rw [show 2 * (m + twopow a) + 1 = 2 * m + 1 + twopow (a + 1) by rw [h2]; cfomega]
      exact hρ (2 * m + 1)
    obtain ⟨Pe, Ve⟩ := ih (fun k => ρ (2 * k)) hρe
    obtain ⟨Po, Vo⟩ := ih (fun k => ρ (2 * k + 1)) hρo
    refine ⟨fun n => ?_, ?_⟩
    · rw [show 3 * twopow (a + 1) = 2 * (3 * twopow a) by rw [h2]; cfomega]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by cfomega⟩
        rcases k with _ | k
        · rw [show 2 * 0 + 2 * (3 * twopow a) = 2 * (3 * twopow a - 1) + 2 by cfomega, fibPascal_even,
            show 3 * twopow a - 1 + 1 = 0 + 3 * twopow a by cfomega, Pe 0, Vo, cone_bxor_false_right,
            fibPascal_zero, show 2 * 0 = 0 from rfl, fibPascal_zero]
        · rw [show 2 * (k + 1) + 2 * (3 * twopow a) = 2 * (k + 3 * twopow a) + 2 by cfomega, fibPascal_even,
            show 2 * (k + 1) = 2 * k + 2 by cfomega, fibPascal_even,
            show k + 3 * twopow a + 1 = (k + 1) + 3 * twopow a by cfomega, Pe (k + 1), Po k]
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by cfomega⟩
        rw [show 2 * k + 1 + 2 * (3 * twopow a) = 2 * (k + 3 * twopow a) + 1 by cfomega, fibPascal_odd,
          fibPascal_odd, Pe k]
    · rw [show 3 * twopow (a + 1) - 1 = 2 * (3 * twopow a - 1) + 1 by rw [h2]; cfomega, fibPascal_odd]
      exact Ve

/-- **Eventual period `3·2^a`**: a word that is `2^a`-periodic from `M ≤ 2^a` has a transport that is
`3·2^a`-periodic from `M − 1` (Lucas's higher-bit law for the transient). -/
theorem fibPascal_eventually_periodic (a M : Nat) (ρ : Nat → Bool) (hM : M ≤ twopow a)
    (hρ : ∀ m, M ≤ m → ρ (m + twopow a) = ρ m) :
    ∀ n, M ≤ n + 1 → fibPascal ρ (n + 3 * twopow a) = fibPascal ρ n := by
  intro n hn
  have hper : ∀ m, ρ (m + twopow a + twopow a) = ρ (m + twopow a) :=
    fun m => hρ (m + twopow a) (by cfomega)
  have hsplit : ∀ m, ρ m = bxor (ρ (m + twopow a)) (bxor (ρ m) (ρ (m + twopow a))) := by
    intro m
    cases ρ m <;> cases ρ (m + twopow a) <;> rfl
  have hdelta : ∀ N, M ≤ N + 1 →
      fibPascal (fun m => bxor (ρ m) (ρ (m + twopow a))) N =
        xorBelow (fun m => pascalParity (N - m) m && bxor (ρ m) (ρ (m + twopow a))) M := by
    intro N hN
    unfold fibPascal
    exact xorBelow_of_vanish _ M (N + 1) (fun m hm _ => by
      show (pascalParity (N - m) m && bxor (ρ m) (ρ (m + twopow a))) = false
      rw [hρ m hm]
      cases pascalParity (N - m) m <;> cases ρ m <;> rfl) (N + 1) hN (Nat.le_refl _)
  have e1 := fibPascal_congr ρ _ hsplit (n + 3 * twopow a)
  have e2 := fibPascal_congr ρ _ hsplit n
  rw [fibPascal_bxor] at e1 e2
  rw [e1, e2, (fibPascal_periodic a (fun m => ρ (m + twopow a)) hper).1 n,
    hdelta (n + 3 * twopow a) (by cfomega), hdelta n hn,
    xorBelow_congr (fun m => pascalParity (n + 3 * twopow a - m) m && bxor (ρ m) (ρ (m + twopow a)))
      (fun m => pascalParity (n - m) m && bxor (ρ m) (ρ (m + twopow a))) M
      (fun m hm => by
        show (pascalParity (n + 3 * twopow a - m) m && bxor (ρ m) (ρ (m + twopow a))) =
          (pascalParity (n - m) m && bxor (ρ m) (ρ (m + twopow a)))
        rw [show n + 3 * twopow a - m = (n - m) + twopow a * 3 by
            rw [Nat.mul_comm (twopow a) 3]; cfomega,
          pascalParity_add_twopow_mul a (n - m) m 3 (by cfomega)])]

/-! ## The left-diagonal split -/

/-- The run-end of the left diagonal `d` at time `d + m − 1` (position `1 − m`). -/
def diagEnd (d m : Nat) : Bool := decide (1 ≤ d + m) && runEnd (d + m - 1) (1 - (m : Int))

/-- The contribution of the left diagonal `d` to the light cone at time `t`. -/
def diagonalCone (d t : Nat) : Bool := decide (d ≤ t) && fibPascal (diagEnd d) (t - d)

theorem leftCone_rect (t : Nat) :
    leftCone t = xorBelow (fun q => xorBelow (fun j => pascalParity (t - 1 - j) q && leftEnd j q) t) (t + 1) := by
  unfold leftCone
  rw [xorBelow_congr (coneRow t) (fun j => xorBelow (fun q => pascalParity (t - 1 - j) q && leftEnd j q) (t + 1)) t
    (fun j hj => by
      unfold coneRow coneTerm
      exact (xorBelow_of_vanish (fun q => pascalParity (t - 1 - j) q && leftEnd j q) (t - j) (t + 1)
        (fun q hq _ => by
          show (pascalParity (t - 1 - j) q && leftEnd j q) = false
          rw [pascalParity_gt _ _ (by cfomega), Bool.false_and]) (t + 1) (by cfomega) (Nat.le_refl _)).symm)]
  exact xorBelow_swap (fun j q => pascalParity (t - 1 - j) q && leftEnd j q) (t + 1) t

theorem diagonals_rect (t : Nat) :
    xorBelow (fun d => diagonalCone d t) (t + 1) =
      xorBelow (fun q => xorBelow (fun d => pascalParity (t - d - q) q && diagEnd d q) (t + 1)) (t + 1) := by
  rw [xorBelow_congr (fun d => diagonalCone d t)
    (fun d => xorBelow (fun q => pascalParity (t - d - q) q && diagEnd d q) (t + 1)) (t + 1)
    (fun d hd => by
      show (decide (d ≤ t) && fibPascal (diagEnd d) (t - d)) = _
      rw [decide_eq_true (by cfomega : d ≤ t), Bool.true_and]
      unfold fibPascal
      exact (xorBelow_of_vanish (fun q => pascalParity (t - d - q) q && diagEnd d q) (t - d + 1) (t + 1)
        (fun q hq _ => by
          show (pascalParity (t - d - q) q && diagEnd d q) = false
          rw [pascalParity_gt _ _ (by cfomega), Bool.false_and]) (t + 1) (by cfomega) (by cfomega)).symm)]
  exact xorBelow_swap (fun d q => pascalParity (t - d - q) q && diagEnd d q) (t + 1) (t + 1)

/-- One distance `q` from column `+1`: the run-ends at that distance, read by time or by diagonal. -/
theorem distance_column_eq (t q : Nat) (hq : q < t + 1) :
    xorBelow (fun j => pascalParity (t - 1 - j) q && leftEnd j q) t =
      xorBelow (fun d => pascalParity (t - d - q) q && diagEnd d q) (t + 1) := by
  rcases q with _ | r
  · rw [xorBelow_front (fun d => pascalParity (t - d - 0) 0 && diagEnd d 0) t]
    show _ = bxor (pascalParity (t - 0 - 0) 0 && (decide (1 ≤ 0 + 0) && runEnd (0 + 0 - 1) (1 - ((0 : Nat) : Int))))
      (xorBelow (fun m => pascalParity (t - (m + 1) - 0) 0 && diagEnd (m + 1) 0) t)
    rw [decide_eq_false (by cfomega : ¬ (1 ≤ 0 + 0)), Bool.false_and, Bool.and_false, cone_bxor_false]
    apply xorBelow_congr
    intro j _
    show (pascalParity (t - 1 - j) 0 && runEnd j (1 - ((0 : Nat) : Int))) =
      (pascalParity (t - (j + 1) - 0) 0 && (decide (1 ≤ j + 1 + 0) && runEnd (j + 1 + 0 - 1) (1 - ((0 : Nat) : Int))))
    rw [pascalParity_zero_right, pascalParity_zero_right, decide_eq_true (by cfomega : 1 ≤ j + 1 + 0),
      Bool.true_and, show j + 1 + 0 - 1 = j by cfomega]
    rfl
  · have hL := xorBelow_split (fun j => pascalParity (t - 1 - j) (r + 1) && leftEnd j (r + 1)) r (t - r)
    rw [show r + (t - r) = t by cfomega] at hL
    have hR := xorBelow_split (fun d => pascalParity (t - d - (r + 1)) (r + 1) && diagEnd d (r + 1)) (t - r) (r + 1)
    rw [show t - r + (r + 1) = t + 1 by cfomega] at hR
    rw [hL, hR,
      xorBelow_congr (fun j => pascalParity (t - 1 - j) (r + 1) && leftEnd j (r + 1)) (fun _ => false) r
        (fun j hj => by
          show (pascalParity (t - 1 - j) (r + 1) && (cell j (1 - ((r + 1 : Nat) : Int)) &&
            !(cell j (1 - ((r + 1 : Nat) : Int) - 1)))) = false
          rw [Rule30UOR.Scale.cell_left_white j _ (by cfomega)]
          cases pascalParity (t - 1 - j) (r + 1) <;> rfl),
      xorBelow_congr (fun i => pascalParity (t - (t - r + i) - (r + 1)) (r + 1) && diagEnd (t - r + i) (r + 1))
        (fun _ => false) (r + 1)
        (fun i hi => by
          show (pascalParity (t - (t - r + i) - (r + 1)) (r + 1) && diagEnd (t - r + i) (r + 1)) = false
          rw [pascalParity_gt _ _ (by cfomega), Bool.false_and]),
      xorBelow_false, xorBelow_false, cone_bxor_false, cone_bxor_false_right]
    apply xorBelow_congr
    intro i _
    show (pascalParity (t - 1 - (r + i)) (r + 1) && runEnd (r + i) (1 - ((r + 1 : Nat) : Int))) =
      (pascalParity (t - i - (r + 1)) (r + 1) &&
        (decide (1 ≤ i + (r + 1)) && runEnd (i + (r + 1) - 1) (1 - ((r + 1 : Nat) : Int))))
    rw [decide_eq_true (by cfomega : 1 ≤ i + (r + 1)), Bool.true_and, show i + (r + 1) - 1 = r + i by cfomega,
      show t - i - (r + 1) = t - 1 - (r + i) by cfomega]

/-- **The left-diagonal split**: the light cone is the XOR over the left diagonals `d ≤ t` of their
Fibonacci–Pascal transports. -/
theorem leftCone_eq_xor_diagonalCone (t : Nat) : leftCone t = xorBelow (fun d => diagonalCone d t) (t + 1) := by
  rw [leftCone_rect, diagonals_rect]
  exact xorBelow_congr _ _ (t + 1) (fun q hq => distance_column_eq t q hq)

/-- The center in left-diagonal form. -/
theorem center_eq_not_xor_diagonalCone (t : Nat) :
    center t = !(xorBelow (fun d => diagonalCone d t) (t + 1)) := by
  rw [center_eq_not_leftCone, leftCone_eq_xor_diagonalCone]


/-! ## Every diagonal cone is eventually periodic: period `3·2^d` from `2^d` -/

/-- The run-ends of the left diagonal `d ≥ 1` in the left table: diagonal `d` black, diagonal
`d − 1` white, at time `d + m − 1`. -/
theorem diagEnd_eq_ldiag (d m : Nat) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    diagEnd d m = (ldiag d (d + m - 1) && !(ldiag (d - 1) (d + m - 1))) := by
  unfold diagEnd runEnd
  have e1 := Rule30UOR.Interfaces.ldiag_eq_cell_neg d (m - 1)
  have e2 := Rule30UOR.Interfaces.ldiag_eq_cell_neg (d - 1) m
  rw [show d + (m - 1) = d + m - 1 by cfomega, show (-((m - 1 : Nat) : Int)) = 1 - (m : Int) by cfomega] at e1
  rw [show d - 1 + m = d + m - 1 by cfomega, show (-(m : Int)) = 1 - (m : Int) - 1 by cfomega] at e2
  rw [decide_eq_true (by cfomega : 1 ≤ d + m), Bool.true_and, e1, e2]

/-- On the left edge every time is a run-end. -/
theorem diagEnd_zero (m : Nat) (hm : 1 ≤ m) : diagEnd 0 m = true := by
  unfold diagEnd runEnd
  have e1 := Rule30UOR.Interfaces.ldiag_eq_cell_neg 0 (m - 1)
  rw [Rule30UOR.Interfaces.ldiag_zero_eq_true, show 0 + (m - 1) = 0 + m - 1 by cfomega,
    show (-((m - 1 : Nat) : Int)) = 1 - (m : Int) by cfomega] at e1
  rw [decide_eq_true (by cfomega : 1 ≤ 0 + m), ← e1, Rule30UOR.Scale.cell_left_white _ _ (by cfomega)]
  rfl

/-- The run-ends of the left diagonal `d` are `2^d`-periodic from `2^d − d`. -/
theorem diagEnd_periodic (d m : Nat) (hm : twopow d - d ≤ m) : diagEnd d (m + twopow d) = diagEnd d m := by
  have hdt := Rule30UOR.Automatic.twopow_ge_succ d
  rcases d with _ | e
  · rw [diagEnd_zero (m + twopow 0) (by cfomega), diagEnd_zero m (by cfomega)]
  · obtain ⟨h0, h1⟩ := leftPeriodic_pair e
    have hp0 := leftPeriodic_mul e (leftPeriod e) (leftPeriod e) 2 h0
    have hp1 := leftPeriodic_mul (e + 1) (leftPeriod e) (leftPeriod e) 2 h1
    have hlp : 2 * leftPeriod e = twopow (e + 1) := leftPeriod_eq_twopow (e + 1)
    have hpos : 1 ≤ leftPeriod e := by rw [leftPeriod_eq_twopow]; exact Rule30UOR.Scale.twopow_pos e
    rw [hlp] at hp0 hp1
    rw [diagEnd_eq_ldiag (e + 1) (m + twopow (e + 1)) (by cfomega) (by cfomega),
      diagEnd_eq_ldiag (e + 1) m (by cfomega) (by cfomega),
      show e + 1 + (m + twopow (e + 1)) - 1 = (e + 1 + m - 1) + twopow (e + 1) by cfomega,
      show e + 1 - 1 = e by cfomega,
      hp1 (e + 1 + m - 1) (by cfomega), hp0 (e + 1 + m - 1) (by cfomega)]

theorem diagEnd_periodic_mul (d m : Nat) (hm : twopow d - d ≤ m) :
    ∀ k, diagEnd d (m + twopow d * k) = diagEnd d m := by
  intro k
  induction k with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, diagEnd_periodic d (m + twopow d * k) (by cfomega), ih]

/-- **Every diagonal cone below depth `D` is eventually periodic with the common period `3·2^D`
from `2^D`.** -/
theorem diagonalCone_periodic_le (d D t : Nat) (hd : d ≤ D) (ht : twopow D ≤ t) :
    diagonalCone d (t + 3 * twopow D) = diagonalCone d t := by
  have hdt := Rule30UOR.Automatic.twopow_ge_succ d
  have hdD := Rule30UOR.Interfaces.twopow_mono d D hd
  unfold diagonalCone
  rw [decide_eq_true (by cfomega : d ≤ t + 3 * twopow D), decide_eq_true (by cfomega : d ≤ t),
    Bool.true_and, Bool.true_and, show t + 3 * twopow D - d = (t - d) + 3 * twopow D by cfomega]
  refine fibPascal_eventually_periodic D (twopow d - d) (diagEnd d) (by cfomega) ?_ (t - d) (by cfomega)
  intro m hm
  have e := Rule30UOR.Automatic.twopow_add d (D - d)
  rw [show d + (D - d) = D by cfomega] at e
  rw [e]
  exact diagEnd_periodic_mul d m hm (twopow (D - d))

/-- **Every diagonal cone is eventually periodic**: the contribution of the left diagonal `d` to the
light cone is `3·2^d`-periodic from time `2^d`. -/
theorem diagonalCone_periodic (d t : Nat) (ht : twopow d ≤ t) :
    diagonalCone d (t + 3 * twopow d) = diagonalCone d t :=
  diagonalCone_periodic_le d d t (Nat.le_refl d) ht

/-! ## Any finite depth: the tail beyond it carries Problem 1 -/

/-- The diagonals `d ≤ D` read at time `t`. -/
def leftHead (D t : Nat) : Bool := xorBelow (fun d => diagonalCone d t) (D + 1)

/-- The diagonals `d > D` read at time `t`. -/
def leftTail (D t : Nat) : Bool := xorBelow (fun d => decide (D < d) && diagonalCone d t) (t + 1)

/-- The light cone is the head at its own depth: `leftCone t = leftHead t t` (first-order form of
the left-diagonal split). -/
theorem leftCone_eq_leftHead (t : Nat) : leftCone t = leftHead t t :=
  leftCone_eq_xor_diagonalCone t

theorem leftHead_periodic (D t : Nat) (ht : twopow D ≤ t) : leftHead D (t + 3 * twopow D) = leftHead D t := by
  unfold leftHead
  exact xorBelow_congr _ _ (D + 1) (fun d hd => diagonalCone_periodic_le d D t (by cfomega) ht)

theorem leftCone_eq_head_tail (D t : Nat) (hD : D ≤ t) : leftCone t = bxor (leftHead D t) (leftTail D t) := by
  rw [leftCone_eq_xor_diagonalCone,
    xorBelow_congr (fun d => diagonalCone d t)
      (fun d => bxor (decide (d ≤ D) && diagonalCone d t) (decide (D < d) && diagonalCone d t)) (t + 1)
      (fun d _ => by
        show diagonalCone d t = bxor (decide (d ≤ D) && diagonalCone d t) (decide (D < d) && diagonalCone d t)
        rcases Nat.lt_or_ge D d with h | h
        · rw [decide_eq_false (by cfomega : ¬ (d ≤ D)), decide_eq_true h]
          cases diagonalCone d t <;> rfl
        · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ (D < d))]
          cases diagonalCone d t <;> rfl),
    xorBelow_bxor]
  unfold leftHead leftTail
  rw [xorBelow_of_vanish (fun d => decide (d ≤ D) && diagonalCone d t) (D + 1) (t + 1)
      (fun d hd _ => by
        show (decide (d ≤ D) && diagonalCone d t) = false
        rw [decide_eq_false (by cfomega : ¬ (d ≤ D)), Bool.false_and]) (t + 1) (by cfomega) (Nat.le_refl _),
    xorBelow_congr (fun d => decide (d ≤ D) && diagonalCone d t) (fun d => diagonalCone d t) (D + 1)
      (fun d hd => by
        show (decide (d ≤ D) && diagonalCone d t) = diagonalCone d t
        rw [decide_eq_true (by cfomega : d ≤ D), Bool.true_and])]

theorem leftHead_mul (D t : Nat) (ht : twopow D ≤ t) :
    ∀ k, leftHead D (t + k * (3 * twopow D)) = leftHead D t :=
  fun k => Ruliology.CellularAutomata.Rule30Jen.periodic_mul (f := fun t => leftHead D t)
    (fun s hs => leftHead_periodic D s hs) k t ht

/-- **At every depth `D`, Problem 1 is the aperiodicity of the tail beyond `D`**: the diagonals
`d ≤ D` are jointly `3·2^D`-periodic from `2^D`, so they never decide Problem 1. -/
theorem problem1_iff_leftTail (D : Nat) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔
      ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic (leftTail D) := by
  have hdt := Rule30UOR.Automatic.twopow_ge_succ D
  have hQ := Rule30UOR.Scale.twopow_pos D
  constructor
  · intro h1 htail
    obtain ⟨S, Q, hQpos, hS⟩ := htail
    apply h1
    refine ⟨S + twopow D, Q * (3 * twopow D), Nat.mul_pos hQpos (by cfomega), fun t ht => ?_⟩
    rw [← Rule30UOR.Scale.center_eq_kit, ← Rule30UOR.Scale.center_eq_kit, center_eq_not_leftCone,
      center_eq_not_leftCone, leftCone_eq_head_tail D (t + Q * (3 * twopow D)) (by cfomega),
      leftCone_eq_head_tail D t (by cfomega), leftHead_mul D t (by cfomega) Q,
      Nat.mul_comm Q (3 * twopow D),
      Ruliology.CellularAutomata.Rule30Jen.periodic_mul (f := leftTail D) hS (3 * twopow D) t (by cfomega)]
  · intro h hep
    obtain ⟨T, P, hP, hc⟩ := hep
    apply h
    refine ⟨T + twopow D + 2, P * (3 * twopow D), Nat.mul_pos hP (by cfomega), fun t ht => ?_⟩
    have hcone : ∀ s, T ≤ s → leftCone (s + P) = leftCone s := by
      intro s hs
      have e := hc s hs
      rw [← Rule30UOR.Scale.center_eq_kit, ← Rule30UOR.Scale.center_eq_kit, center_eq_not_leftCone,
        center_eq_not_leftCone] at e
      exact not_inj_aux _ _ e
    rw [show P * (3 * twopow D) = 3 * twopow D * P from Nat.mul_comm _ _]
    have hc1 := leftCone_eq_head_tail D (t + 3 * twopow D * P) (by cfomega)
    have hc2 := leftCone_eq_head_tail D t (by cfomega)
    have hh : leftHead D (t + 3 * twopow D * P) = leftHead D t := by
      rw [Nat.mul_comm (3 * twopow D) P]
      exact leftHead_mul D t (by cfomega) P
    rw [Ruliology.CellularAutomata.Rule30Jen.periodic_mul (f := leftCone) hcone (3 * twopow D) t (by cfomega),
      hh, hc2] at hc1
    revert hc1
    cases leftHead D t <;> cases leftTail D t <;> cases leftTail D (t + 3 * twopow D * P) <;> decide

/-! ## The fixed point splits: black times (left only) and white times (the coupling) -/

section FixedSplit

open Rule30UOR.Fixed

/-- A boundary column is white-time consistent: at every white time the next value is column `−1`
of the left half it drives XOR column `+1` of the right half it drives. -/
def WhiteTimeConsistent (c : Nat → Bool) : Prop :=
  ∀ t, c t = false → c (t + 1) = bxor (Lh c t (-1)) (Rh c t 1)

/-- **The fixed-point equation is black-time consistency plus white-time consistency.** -/
theorem isFixed_iff (c : Nat → Bool) :
    IsFixed c ↔ c 0 = true ∧ BlackTimeConsistent c ∧ WhiteTimeConsistent c := by
  constructor
  · rintro ⟨h0, hf⟩
    refine ⟨h0, fun t ht => ?_, fun t ht => ?_⟩
    · rw [hf t]
      unfold Phi
      rw [ht, rule_split]
      cases Lh c t (-1) <;> cases Rh c t 1 <;> rfl
    · rw [hf t]
      unfold Phi
      rw [ht, rule_split]
      cases Lh c t (-1) <;> cases Rh c t 1 <;> rfl
  · rintro ⟨h0, hb, hw⟩
    refine ⟨h0, fun t => ?_⟩
    unfold Phi
    cases ht : c t
    · rw [hw t ht, rule_split]
      cases Lh c t (-1) <;> cases Rh c t 1 <;> rfl
    · rw [hb t ht, rule_split]
      cases Lh c t (-1) <;> cases Rh c t 1 <;> rfl

/-- No eventually periodic column with `c 0 = true` is consistent at both its black and its white
times. -/
def NoPeriodicConsistent : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c → WhiteTimeConsistent c →
    ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic c

/-- **Problem 1 is: no eventually periodic column is consistent at both its black and its white
times.** Dropping the white times gives `NoPeriodicBlackConsistent`, the lens's left-only form. -/
theorem problem1_iff_noPeriodicConsistent :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ NoPeriodicConsistent := by
  refine Iff.trans problem1_iff_no_periodic_fixed ⟨fun h c h0 hb hw => ?_, fun h c hc => ?_⟩
  · exact h c ((isFixed_iff c).2 ⟨h0, hb, hw⟩)
  · obtain ⟨h0, hb, hw⟩ := (isFixed_iff c).1 hc
    exact h c h0 hb hw

theorem noPeriodicConsistent_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) :
    NoPeriodicConsistent := by
  intro c h0 hb _ hep
  obtain ⟨T, hT⟩ := h c h0 hb hep
  have hfix : IsFixed c := by
    refine (isFixed_iff c).2 ⟨h0, hb, ?_⟩
    assumption
  have e := fixed_unique hfix.1 hfix.2
  exact Rule30UOR.KitConstructive.center_not_eventually_constant ⟨T, false, fun t ht => by rw [← e t]; exact hT t ht⟩

/-- **At a white-time consistent column the depth-`0` source is the right half's column `+1`**:
the effective column of the left cone is `Rh c t 1` on the white times of `c`. -/
theorem drivenEnd_zero_of_wtc (c : Nat → Bool) (hw : WhiteTimeConsistent c) (j : Nat) :
    drivenEnd c j 0 = (Rh c j 1 && !(c j)) := by
  unfold drivenEnd
  rw [if_pos rfl]
  cases hj : c j
  · rw [hw j hj]
    cases Lh c j (-1) <;> cases Rh c j 1 <;> rfl
  · cases bxor (c (j + 1)) (Lh c j (-1)) <;> cases Rh c j 1 <;> rfl

end FixedSplit

/-! ## First-order forms -/

section FirstOrder

open Rule30UOR.Fixed

/-- The cone identity of a boundary column at every time. -/
def ConeIdentity (c : Nat → Bool) : Prop := ∀ t, c t = !(drivenCone c t)

/-- For every boundary with `c 0 = true`, the cone identity is black-time consistency. -/
def ConeIdentityIsBlackConsistency : Prop :=
  ∀ c : Nat → Bool, c 0 = true → (ConeIdentity c ↔ BlackTimeConsistent c)

/-- **The light-cone identity is exactly black-time consistency.** -/
theorem coneIdentityIsBlackConsistency : ConeIdentityIsBlackConsistency :=
  fun c h0 => driven_cone_iff_btc c h0

/-- Column `−1` of the half driven by `c` from white. -/
def drivenColumn (c : Nat → Bool) (t : Nat) : Bool := Lh c t (-1)

/-- For every eventually periodic boundary with `c 0 = true`, the driven column `−1` (equivalently
the driven cone from column `0`) is not eventually periodic. -/
def DrivenColumnAperiodic : Prop :=
  ∀ c : Nat → Bool, c 0 = true → Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic c →
    ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic (drivenColumn c)

/-- **A periodically driven left half has an aperiodic cone from column `0`.** -/
theorem drivenColumnAperiodic : DrivenColumnAperiodic :=
  fun c h0 hc => driven_column_not_eventuallyPeriodic c h0 hc

/-- The center is black-time consistent, in first-order form. -/
def CenterBlackConsistent : Prop := BlackTimeConsistent Ruliology.CellularAutomata.Rule30Prize.center

theorem centerBlackConsistent : CenterBlackConsistent := center_blackTimeConsistent

end FirstOrder

end Rule30UOR.DiagonalCone
