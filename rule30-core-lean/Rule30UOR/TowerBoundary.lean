module
public import Rule30UOR.DiagonalCone
public import Rule30UOR.ZeroDiagonals
public import Rule30UOR.Interfaces.Part02
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Edge towers and black-time consistency

A family of left diagonals `W j u` (depth `j`, time `u`) obeying the left recursion at every time,
with a black edge diagonal, is an *edge tower* (`EdgeTower`). Read as `x u p = W (p + u) u`, it is the
Rule 30 orbit of the row `x 0` (black at `0`, white to its left, arbitrary to its right), and the
anti-diagonal at phase `s` is column `-s` of that orbit (a reading, not mechanized here). The seeded
table (`Rule30Diagonals.D`, `Core.ldiag`), the zero-state (`Intent.E`) and the eventual cycles
`cyc c` of the half driven by any boundary `c` are edge towers.

* `drivenDiag_antiDiag`, `antiDiag_blackTimeConsistent`: the anti-diagonal `t ↦ W t (t + s)` of an
  edge tower, at every phase `s`, drives a left half equal to the tower itself (no transient) and
  is black-time consistent; it is never eventually white (`antiDiag_not_eventuallyWhite`).
* `antiDiag_not_eventuallyPeriodic`, `zeroState_center_not_eventuallyPeriodic`,
  `noZCenterPeriod_of_noPeriodicBlackConsistent`: a necessity link. The left-only obligation
  `NoPeriodicBlackConsistent` forbids a periodic anti-diagonal in every edge tower, so it contains
  the zero-state's own Problem 1 at every phase (`Interfaces.NoZCenterPeriod`).
* `drivenDiag_periodic`, `edgeTower_cyc`, `companion_blackTimeConsistent`, `cyc_companion`,
  `cycle_barrier`: an obstruction of narrow scope. Every boundary has a black-time-consistent
  companion with the same eventual diagonal cycles, so black-time consistency alone (without the
  periodicity hypothesis) forbids no property of the eventual cycles.
* `noPeriodicBlackConsistent_iff`: bookkeeping in the style of `Intent.gate`, not a sharpening.
  The same template split holds with the center (or any black-time-consistent reference with a black
  start that is never eventually white) in place of the companion; all boundary-specific content
  stays in the second conjunct.
-/

@[expose] public section

namespace Rule30UOR.TowerBoundary

open Rule30UOR.Core
open Rule30UOR.Fixed Rule30UOR.DiagonalCone
open Ruliology.CellularAutomata

/-! ### Driven diagonals -/

/-- Diagonal `j` of the left half driven by `c`, read at time `t` (position `j - t`). -/
def drivenDiag (c : Nat → Bool) (j t : Nat) : Bool := Lh c t ((j : Int) - (t : Int))

/-- The half driven by any boundary is white left of its light cone. -/
theorem Lh_white (c : Nat → Bool) : ∀ (t : Nat) (p : Int), p < -(t : Int) → Lh c t p = false := by
  intro t
  induction t with
  | zero => intro p hp; exact Lh_zero_neg c p (by cfomega)
  | succ t ih =>
    intro p hp
    rw [Lh_succ_neg c t p (by cfomega), ih (p - 1) (by cfomega), ih p (by cfomega), ih (p + 1) (by cfomega)]
    rfl

theorem drivenDiag_zero (c : Nat → Bool) (h0 : c 0 = true) : ∀ t, drivenDiag c 0 t = true := by
  intro t
  induction t with
  | zero =>
    show Lh c 0 (((0 : Nat) : Int) - ((0 : Nat) : Int)) = true
    rw [show ((0 : Nat) : Int) - ((0 : Nat) : Int) = 0 by cfomega, Lh_col0, h0]
  | succ t ih =>
    unfold drivenDiag at ih ⊢
    rw [Lh_succ_neg c t _ (by cfomega), Lh_white c t _ (by cfomega), Lh_white c t _ (by cfomega),
      show ((0 : Nat) : Int) - ((t + 1 : Nat) : Int) + 1 = ((0 : Nat) : Int) - (t : Int) by cfomega, ih]
    rfl

theorem drivenDiag_one (c : Nat → Bool) (h0 : c 0 = true) (t : Nat) (ht : 2 ≤ t) : drivenDiag c 1 t = true := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by cfomega⟩
  have e := drivenDiag_zero c h0 u
  unfold drivenDiag at e ⊢
  rw [Lh_succ_neg c u _ (by cfomega), Lh_white c u _ (by cfomega),
    show ((1 : Nat) : Int) - ((u + 1 : Nat) : Int) = ((0 : Nat) : Int) - (u : Int) by cfomega, e]
  rfl

theorem drivenDiag_step (c : Nat → Bool) (j t : Nat) (ht : j + 2 ≤ t) :
    drivenDiag c (j + 2) (t + 1) =
      Rule30Jen.rule (drivenDiag c j t) (drivenDiag c (j + 1) t) (drivenDiag c (j + 2) t) := by
  unfold drivenDiag
  rw [Lh_succ_neg c t _ (by cfomega),
    show ((j + 2 : Nat) : Int) - ((t + 1 : Nat) : Int) - 1 = (j : Int) - (t : Int) by cfomega,
    show ((j + 2 : Nat) : Int) - ((t + 1 : Nat) : Int) + 1 = ((j + 2 : Nat) : Int) - (t : Int) by cfomega,
    show ((j + 2 : Nat) : Int) - ((t + 1 : Nat) : Int) = ((j + 1 : Nat) : Int) - (t : Int) by cfomega]

/-! ### Edge towers and their anti-diagonals -/

/-- An edge tower: a family of left diagonals `W j u` (depth `j`, time `u`) obeying the left
recursion at every time, with the edge diagonal black and diagonal `1` black after time `0`. -/
def EdgeTower (W : Nat → Nat → Bool) : Prop :=
  (∀ u, W 0 u = true) ∧ (∀ u, W 1 (u + 1) = true) ∧
    ∀ j u, W (j + 2) (u + 1) = bxor (W j u) (W (j + 1) u || W (j + 2) u)

/-- The anti-diagonal of a tower at phase `s`: diagonal `t` read at time `t + s`. -/
def antiDiag (W : Nat → Nat → Bool) (s t : Nat) : Bool := W t (t + s)

theorem antiDiag_zero {W : Nat → Nat → Bool} (hW : EdgeTower W) (s : Nat) : antiDiag W s 0 = true :=
  hW.1 _

/-- **The half driven by a tower's anti-diagonal is the tower itself** (no transient): diagonal
`j` of the driven half at time `t ≥ j` is `W j (t + s)`. -/
theorem drivenDiag_antiDiag {W : Nat → Nat → Bool} (hW : EdgeTower W) (s j t : Nat) (hj : j ≤ t) :
    drivenDiag (antiDiag W s) j t = W j (t + s) := by
  obtain ⟨h0, h1, hst⟩ := hW
  have main : ∀ t j, j ≤ t → drivenDiag (antiDiag W s) j t = W j (t + s) := by
    intro t
    induction t with
    | zero =>
      intro j hj
      obtain rfl : j = 0 := by cfomega
      show Lh (antiDiag W s) 0 (((0 : Nat) : Int) - ((0 : Nat) : Int)) = _
      rw [show ((0 : Nat) : Int) - ((0 : Nat) : Int) = 0 by cfomega, Lh_col0]
      rfl
    | succ t ih =>
      intro j hj
      rcases Nat.lt_or_ge j (t + 1) with hlt | hge
      · unfold drivenDiag at ih ⊢
        rw [Lh_succ_neg _ t _ (by cfomega), show t + 1 + s = (t + s) + 1 by cfomega]
        rcases j with _ | _ | i
        · -- the edge diagonal
          rw [Lh_white _ t _ (by cfomega), Lh_white _ t _ (by cfomega),
            show ((0 : Nat) : Int) - ((t + 1 : Nat) : Int) + 1 = ((0 : Nat) : Int) - (t : Int) by cfomega,
            ih 0 (by cfomega), h0, h0]
          rfl
        · -- diagonal `1` (here `t ≥ 1`)
          rw [Lh_white _ t _ (by cfomega),
            show ((0 + 1 : Nat) : Int) - ((t + 1 : Nat) : Int) = ((0 : Nat) : Int) - (t : Int) by cfomega,
            ih 0 (by cfomega), h0, h1]
          rfl
        · rw [show ((i + 1 + 1 : Nat) : Int) - ((t + 1 : Nat) : Int) - 1 = (i : Int) - (t : Int) by cfomega,
            show ((i + 1 + 1 : Nat) : Int) - ((t + 1 : Nat) : Int) + 1 = ((i + 1 + 1 : Nat) : Int) - (t : Int) by cfomega,
            show ((i + 1 + 1 : Nat) : Int) - ((t + 1 : Nat) : Int) = ((i + 1 : Nat) : Int) - (t : Int) by cfomega,
            ih i (by cfomega), ih (i + 1) (by cfomega), ih (i + 1 + 1) (by cfomega)]
          exact ((hst i (t + s)).trans (Rule30UOR.Scale.bxor_eq _ _)).symm
      · obtain rfl : j = t + 1 := by cfomega
        show Lh (antiDiag W s) (t + 1) (((t + 1 : Nat) : Int) - ((t + 1 : Nat) : Int)) = _
        rw [show ((t + 1 : Nat) : Int) - ((t + 1 : Nat) : Int) = 0 by cfomega, Lh_col0]
        rfl
  exact main t j hj

/-- Column `-1` of the half driven by the anti-diagonal is diagonal `t` of the tower. -/
theorem Lh_antiDiag_neg_one {W : Nat → Nat → Bool} (hW : EdgeTower W) (s t : Nat) :
    Lh (antiDiag W s) (t + 1) (-1) = W t (t + 1 + s) := by
  have e := drivenDiag_antiDiag hW s t (t + 1) (by cfomega)
  unfold drivenDiag at e
  rw [show (t : Int) - ((t + 1 : Nat) : Int) = -1 by cfomega] at e
  exact e

/-- **Every anti-diagonal of an edge tower is black-time consistent.** -/
theorem antiDiag_blackTimeConsistent {W : Nat → Nat → Bool} (hW : EdgeTower W) (s : Nat) :
    BlackTimeConsistent (antiDiag W s) := by
  intro t ht
  rcases t with _ | t
  · rw [Lh_zero_neg _ (-1) (by cfomega)]
    show W 1 (1 + s) = !false
    rw [show 1 + s = s + 1 by cfomega, hW.2.1]
    rfl
  · rw [Lh_antiDiag_neg_one hW s t]
    have e := hW.2.2 t (t + 1 + s)
    have ht' : W (t + 1) (t + 1 + s) = true := ht
    show W (t + 1 + 1) (t + 1 + 1 + s) = _
    rw [show t + 1 + 1 + s = (t + 1 + s) + 1 by cfomega, e, ht']
    cases W t (t + 1 + s) <;> rfl

/-- **No anti-diagonal of an edge tower is eventually white**: if it were, column `+1`
(`W (t+1) (t+s)`) would be monotone and equal to column `-1`, which would then be eventually
constant, against the driven Jen theorem. -/
theorem antiDiag_not_eventuallyWhite {W : Nat → Nat → Bool} (hW : EdgeTower W) (s : Nat) :
    ¬ EventuallyWhite (antiDiag W s) := by
  intro hw
  obtain ⟨T, hT⟩ := hw
  have hz : ∀ t, T ≤ t → W t (t + s) = false := hT
  have hep : Rule30Jen.EventuallyPeriodic (antiDiag W s) :=
    ⟨T, 1, by decide, fun t ht => by rw [hT t ht, hT (t + 1) (by cfomega)]⟩
  have hnot := driven_column_not_eventuallyPeriodic (antiDiag W s) (antiDiag_zero hW s) hep
  -- column `+1` at time `t` is `W (t + 1) (t + s)`; it is monotone after `T`
  have hmono : ∀ t, T ≤ t → W (t + 1) (t + s) = true → W (t + 1 + 1) (t + 1 + s) = true := by
    intro t ht h
    have e := hW.2.2 t (t + s)
    rw [show t + 1 + s = (t + s) + 1 by cfomega, e, h, hz t ht]
    rfl
  -- column `-1` equals column `+1` after `T`
  have heq : ∀ t, T ≤ t → Lh (antiDiag W s) (t + 1) (-1) = W (t + 1 + 1) (t + 1 + s) := by
    intro t ht
    rw [Lh_antiDiag_neg_one hW s t]
    have e := hW.2.2 t (t + 1 + s)
    have c1 : W (t + 1) (t + 1 + s) = false := hz (t + 1) (by cfomega)
    have c2 : W (t + 1 + 1) (t + 1 + 1 + s) = false := hz (t + 1 + 1) (by cfomega)
    rw [show t + 1 + 1 + s = (t + 1 + s) + 1 by cfomega, e, c1] at c2
    revert c2
    cases W t (t + 1 + s) <;> cases W (t + 1 + 1) (t + 1 + s) <;> decide
  have hnever : ¬ ∃ t0, T ≤ t0 ∧ W (t0 + 1) (t0 + s) = true := by
    intro ⟨t0, ht0, hb⟩
    have hall : ∀ n, W (t0 + n + 1) (t0 + n + s) = true := by
      intro n
      induction n with
      | zero => exact hb
      | succ n ih =>
        have h := hmono (t0 + n) (by cfomega) ih
        rw [show t0 + (n + 1) + 1 = t0 + n + 1 + 1 by cfomega, show t0 + (n + 1) + s = t0 + n + 1 + s by cfomega]
        exact h
    apply hnot
    refine ⟨t0 + 1, 1, by decide, fun t ht => ?_⟩
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by cfomega⟩
    show Lh (antiDiag W s) (u + 1 + 1) (-1) = Lh (antiDiag W s) (u + 1) (-1)
    rw [heq (u + 1) (by cfomega), heq u (by cfomega)]
    have a1 := hall (u + 1 + 1 - t0)
    have a0 := hall (u + 1 - t0)
    rw [show t0 + (u + 1 + 1 - t0) + 1 = u + 1 + 1 + 1 by cfomega,
      show t0 + (u + 1 + 1 - t0) + s = u + 1 + 1 + s by cfomega] at a1
    rw [show t0 + (u + 1 - t0) + 1 = u + 1 + 1 by cfomega,
      show t0 + (u + 1 - t0) + s = u + 1 + s by cfomega] at a0
    rw [a1, a0]
  apply hnot
  refine ⟨T + 1, 1, by decide, fun t ht => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by cfomega⟩
  have hf : ∀ v, T ≤ v → W (v + 1) (v + s) = false := by
    intro v hv
    cases h : W (v + 1) (v + s)
    · rfl
    · exact absurd ⟨v, hv, h⟩ hnever
  show Lh (antiDiag W s) (u + 1 + 1) (-1) = Lh (antiDiag W s) (u + 1) (-1)
  rw [heq (u + 1) (by cfomega), heq u (by cfomega), hf (u + 1 + 1) (by cfomega), hf (u + 1) (by cfomega)]

/-- **Black-time consistency forbids a periodic anti-diagonal in every edge tower.** -/
theorem antiDiag_not_eventuallyPeriodic (h : NoPeriodicBlackConsistent) {W : Nat → Nat → Bool}
    (hW : EdgeTower W) (s : Nat) : ¬ Rule30Jen.EventuallyPeriodic (antiDiag W s) := fun hep =>
  antiDiag_not_eventuallyWhite hW s
    (h (antiDiag W s) (antiDiag_zero hW s) (antiDiag_blackTimeConsistent hW s) hep)

/-! ### Instances: the seeded tower and the zero-state -/

/-- The seeded left diagonals form an edge tower; its anti-diagonal at phase `0` is the center. -/
theorem edgeTower_seed : EdgeTower Rule30Diagonals.D :=
  ⟨Rule30Diagonals.D_zero, Rule30Diagonals.D_one,
    fun j u => (Rule30Diagonals.D_step j u).trans (Rule30UOR.Scale.bxor_eq _ _).symm⟩

theorem antiDiag_seed (t : Nat) : antiDiag Rule30Diagonals.D 0 t = Rule30Prize.center t :=
  (Rule30Diagonals.center_eq_D t).symm

/-- The core's left table is an edge tower. -/
theorem edgeTower_ldiag : EdgeTower ldiag :=
  ⟨fun u => by cases u <;> rfl, fun u => ldiag_one u, fun j u => ldiag_step j u⟩

/-- The zero-state (the eventual pattern of every left diagonal) is an edge tower. -/
theorem edgeTower_zeroState : EdgeTower Rule30UOR.Intent.E :=
  ⟨Rule30UOR.ZeroDiagonals.E_zero', fun u => Rule30UOR.ZeroDiagonals.E_one' (u + 1),
    fun j u => (Rule30UOR.Intent.E_step j u).trans (Rule30UOR.Scale.bxor_eq _ _).symm⟩

/-- **The left-only obligation contains the zero-state's own Problem 1, at every phase.** -/
theorem zeroState_center_not_eventuallyPeriodic (h : NoPeriodicBlackConsistent) (s : Nat) :
    ¬ Rule30Jen.EventuallyPeriodic (antiDiag Rule30UOR.Intent.E s) :=
  antiDiag_not_eventuallyPeriodic h edgeTower_zeroState s

/-- **The register target implies the canonical zero-state target** `NoZCenterPeriod`. -/
theorem noZCenterPeriod_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) :
    Rule30UOR.Interfaces.NoZCenterPeriod := by
  intro T Q hQ hper
  apply zeroState_center_not_eventuallyPeriodic h 0
  refine ⟨T, Q, hQ, fun t ht => ?_⟩
  show Rule30UOR.Intent.E (t + Q) (t + Q + 0) = Rule30UOR.Intent.E t (t + 0)
  exact hper t ht

/-! ### The settled companion: black-time consistency alone sees no cycle data -/

/-- Settle bounds of the driven diagonals; they do not depend on the boundary. -/
def settleBound : Nat → Nat
  | 0 => 0
  | 1 => 2
  | j + 2 => max (max (settleBound j) (settleBound (j + 1))) (j + 2) + twopow (j + 1)

theorem settleBound_succ_ge : ∀ j, settleBound j ≤ settleBound (j + 1)
  | 0 => by decide
  | 1 => by decide
  | j + 2 => by
    show settleBound (j + 2) ≤ max (max (settleBound (j + 1)) (settleBound (j + 2))) (j + 2 + 1) + twopow (j + 1 + 1)
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _))

theorem settleBound_mono (i j : Nat) (hij : i ≤ j) : settleBound i ≤ settleBound j := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by cfomega
    exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact Nat.le_trans (ih (by cfomega)) (settleBound_succ_ge j)
    · obtain rfl : i = j + 1 := by cfomega
      exact Nat.le_refl _

theorem settleBound_ge : ∀ j, j ≤ settleBound j
  | 0 => Nat.le_refl _
  | 1 => by decide
  | j + 2 => by
    show j + 2 ≤ max (max (settleBound j) (settleBound (j + 1))) (j + 2) + twopow (j + 1)
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)

/-- **Every driven diagonal settles**: diagonal `j` is `2^j`-periodic from `settleBound j`,
whatever the boundary. -/
theorem drivenDiag_periodic (c : Nat → Bool) (h0 : c 0 = true) (j t : Nat) (ht : settleBound j ≤ t) :
    drivenDiag c j (t + twopow j) = drivenDiag c j t := by
  have pair : ∀ j, (∀ t, settleBound j ≤ t → drivenDiag c j (t + twopow j) = drivenDiag c j t) ∧
      (∀ t, settleBound (j + 1) ≤ t → drivenDiag c (j + 1) (t + twopow (j + 1)) = drivenDiag c (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun t _ => by rw [drivenDiag_zero c h0, drivenDiag_zero c h0], fun t ht => ?_⟩
      have ht' : 2 ≤ t := ht
      rw [drivenDiag_one c h0 _ (by cfomega), drivenDiag_one c h0 _ ht']
    | succ j ih =>
      obtain ⟨ha, hb⟩ := ih
      refine ⟨hb, ?_⟩
      have hp : twopow (j + 1 + 1) = 2 * twopow (j + 1) := by
        rw [show twopow (j + 1 + 1) = twopow (j + 1) + twopow (j + 1) from twopow_succ (j + 1)]; cfomega
      have hq : twopow (j + 1) = 2 * twopow j := by
        rw [show twopow (j + 1) = twopow j + twopow j from twopow_succ j]; cfomega
      have ha2 : ∀ t, settleBound j ≤ t → drivenDiag c j (t + twopow (j + 1)) = drivenDiag c j t := by
        intro t ht
        rw [hq, show t + 2 * twopow j = (t + twopow j) + twopow j by cfomega, ha _ (by cfomega), ha t ht]
      have hT := Rule30Diagonals.transducer_periodic (x := drivenDiag c (j + 2))
        (F := fun t b => Rule30Jen.rule (drivenDiag c j t) (drivenDiag c (j + 1) t) b)
        (T := max (max (settleBound j) (settleBound (j + 1))) (j + 2)) (L := twopow (j + 1))
        (fun t ht => drivenDiag_step c j t (by cfomega))
        (fun t ht => by
          funext b
          show Rule30Jen.rule (drivenDiag c j (t + twopow (j + 1))) (drivenDiag c (j + 1) (t + twopow (j + 1))) b =
            Rule30Jen.rule (drivenDiag c j t) (drivenDiag c (j + 1) t) b
          rw [ha2 t (by cfomega), hb t (by cfomega)])
      intro t ht
      have ht' : max (max (settleBound j) (settleBound (j + 1))) (j + 2) + twopow (j + 1) ≤ t := ht
      rw [hp]
      exact hT t ht'
  exact (pair j).1 t ht

/-- The eventual cycle of driven diagonal `j`, read at time `u`. -/
def cyc (c : Nat → Bool) (j u : Nat) : Bool := drivenDiag c j (u + settleBound j * twopow j)

theorem drivenDiag_late (c : Nat → Bool) (h0 : c 0 = true) (j a b k : Nat) (hb : settleBound j ≤ b)
    (h : a = b + k * twopow j) : drivenDiag c j a = drivenDiag c j b := by
  rw [h]
  exact Rule30Jen.periodic_mul (drivenDiag_periodic c h0 j) k b hb

theorem cyc_eq (c : Nat → Bool) (h0 : c 0 = true) (j t : Nat) (ht : settleBound j ≤ t) :
    cyc c j t = drivenDiag c j t :=
  drivenDiag_late c h0 j _ t (settleBound j) ht rfl

/-- Any late reading at a multiple of the period is the cycle. -/
theorem cyc_eq_late (c : Nat → Bool) (h0 : c 0 = true) (j u M : Nat) (hM : settleBound j ≤ M) :
    drivenDiag c j (u + M * twopow j) = cyc c j u := by
  unfold cyc
  have h1 : settleBound j * twopow j ≤ M * twopow j := Nat.mul_le_mul_right _ hM
  apply drivenDiag_late c h0 j _ _ (M - settleBound j)
    (Nat.le_trans (Nat.le_mul_of_pos_right _ (Rule30UOR.Scale.twopow_pos j)) (Nat.le_add_left _ _))
  rw [Nat.sub_mul]
  generalize settleBound j * twopow j = A at *
  generalize M * twopow j = B at *
  cfomega

/-- **The eventual cycles of any driven half form an edge tower.** -/
theorem edgeTower_cyc (c : Nat → Bool) (h0 : c 0 = true) : EdgeTower (cyc c) := by
  refine ⟨fun u => drivenDiag_zero c h0 _, fun u => drivenDiag_one c h0 _ ?_, fun j u => ?_⟩
  · have : 2 ≤ settleBound 1 * twopow 1 := by decide
    cfomega
  · have hj2 : j + 2 ≤ settleBound (j + 2) := settleBound_ge (j + 2)
    have hm2 : settleBound (j + 2) ≤ settleBound (j + 2) * twopow (j + 2) :=
      Nat.le_mul_of_pos_right _ (Rule30UOR.Scale.twopow_pos _)
    have hp2 : twopow (j + 2) = 4 * twopow j := by
      rw [show twopow (j + 2) = twopow (j + 1) + twopow (j + 1) from twopow_succ (j + 1),
        show twopow (j + 1) = twopow j + twopow j from twopow_succ j]; cfomega
    have hp1 : twopow (j + 2) = 2 * twopow (j + 1) := by
      rw [show twopow (j + 2) = twopow (j + 1) + twopow (j + 1) from twopow_succ (j + 1)]; cfomega
    have m0 : settleBound j ≤ settleBound (j + 2) := settleBound_mono j (j + 2) (by cfomega)
    have m1 : settleBound (j + 1) ≤ settleBound (j + 2) := settleBound_mono (j + 1) (j + 2) (by cfomega)
    have e0 : drivenDiag c j (u + settleBound (j + 2) * twopow (j + 2)) = cyc c j u := by
      rw [hp2, ← Nat.mul_assoc, Nat.mul_comm (settleBound (j + 2)) 4]
      exact cyc_eq_late c h0 j u _ (by cfomega)
    have e1 : drivenDiag c (j + 1) (u + settleBound (j + 2) * twopow (j + 2)) = cyc c (j + 1) u := by
      rw [hp1, ← Nat.mul_assoc, Nat.mul_comm (settleBound (j + 2)) 2]
      exact cyc_eq_late c h0 (j + 1) u _ (by cfomega)
    have hN : j + 2 ≤ u + settleBound (j + 2) * twopow (j + 2) := by
      generalize settleBound (j + 2) * twopow (j + 2) = N at *
      cfomega
    show drivenDiag c (j + 2) (u + 1 + settleBound (j + 2) * twopow (j + 2)) = _
    rw [Nat.add_right_comm u 1, drivenDiag_step c j _ hN, e0, e1, Rule30UOR.Scale.bxor_eq]
    rfl

/-- **The settled companion of a boundary**: the anti-diagonal of its own eventual cycles. -/
def companion (c : Nat → Bool) : Nat → Bool := antiDiag (cyc c) 0

theorem companion_zero (c : Nat → Bool) (h0 : c 0 = true) : companion c 0 = true :=
  antiDiag_zero (edgeTower_cyc c h0) 0

/-- **Every boundary has a black-time-consistent companion** (whether or not it is itself
black-time consistent). -/
theorem companion_blackTimeConsistent (c : Nat → Bool) (h0 : c 0 = true) :
    BlackTimeConsistent (companion c) :=
  antiDiag_blackTimeConsistent (edgeTower_cyc c h0) 0

/-- **The companion's driven half is settled from the start and has the same eventual diagonals.** -/
theorem companion_drivenDiag (c : Nat → Bool) (h0 : c 0 = true) (j t : Nat) (ht : settleBound j ≤ t) :
    drivenDiag (companion c) j t = drivenDiag c j t := by
  rw [companion, drivenDiag_antiDiag (edgeTower_cyc c h0) 0 j t (Nat.le_trans (settleBound_ge j) ht),
    Nat.add_zero, cyc_eq c h0 j t ht]

theorem cyc_companion (c : Nat → Bool) (h0 : c 0 = true) : cyc (companion c) = cyc c := by
  funext j u
  have hm : settleBound j ≤ u + settleBound j * twopow j :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ (Rule30UOR.Scale.twopow_pos _)) (Nat.le_add_left _ _)
  exact companion_drivenDiag c h0 j _ hm

/-- **Cycle barrier** (narrow scope): whatever black-time consistency alone forbids of the eventual
diagonal cycles, it forbids for every boundary. A lemma that uses the periodicity hypothesis as well
is not covered: the companion of a periodic boundary need not be periodic. -/
theorem cycle_barrier (Φ : (Nat → Nat → Bool) → Prop)
    (hΦ : ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c → ¬ Φ (cyc c)) :
    ∀ c : Nat → Bool, c 0 = true → ¬ Φ (cyc c) := fun c h0 h =>
  hΦ (companion c) (companion_zero c h0) (companion_blackTimeConsistent c h0)
    (by rw [cyc_companion c h0]; exact h)

/-- Under the left-only obligation every companion is aperiodic. -/
theorem companion_not_eventuallyPeriodic (h : NoPeriodicBlackConsistent) (c : Nat → Bool) (h0 : c 0 = true) :
    ¬ Rule30Jen.EventuallyPeriodic (companion c) :=
  antiDiag_not_eventuallyPeriodic h (edgeTower_cyc c h0) 0

/-! ### Bookkeeping: the template split of the left-only obligation

Not a sharpening and not two new obligations: the first conjunct is a consequence of the target
(`companion_not_eventuallyPeriodic`), the second is vacuous under it, and the same split holds with
the center in place of the companion. -/

/-- No boundary's companion is eventually periodic. -/
def NoPeriodicCompanion : Prop :=
  ∀ c : Nat → Bool, c 0 = true → ¬ Rule30Jen.EventuallyPeriodic (companion c)

/-- An eventually periodic black-time-consistent boundary that keeps black times eventually
equals its companion. -/
def PeriodicBlackConsistentSettles : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c → Rule30Jen.EventuallyPeriodic c →
    ¬ EventuallyWhite c → ∃ T, ∀ t, T ≤ t → c t = companion c t

theorem noPeriodicBlackConsistent_iff :
    NoPeriodicBlackConsistent ↔ NoPeriodicCompanion ∧ PeriodicBlackConsistentSettles := by
  constructor
  · intro h
    exact ⟨fun c h0 => companion_not_eventuallyPeriodic h c h0,
      fun c h0 hbtc hep hnw => absurd (h c h0 hbtc hep) hnw⟩
  · intro ⟨ha, hb⟩ c h0 hbtc hep
    obtain ⟨T, P, hP, hper⟩ := hep
    refine Decidable.byCases (p := ∃ r, r < P ∧ c (T + r) = true) (fun hblk => ?_) (fun hno => ?_)
    · exfalso
      obtain ⟨r, _, hr⟩ := hblk
      have hnw : ¬ EventuallyWhite c := by
        intro ⟨T', hT'⟩
        have hNP : (T' + 1) * 1 ≤ (T' + 1) * P := Nat.mul_le_mul_left (T' + 1) hP
        have e := Rule30Jen.periodic_mul hper (T' + 1) (T + r) (by cfomega)
        rw [hr, hT' _ (by cfomega)] at e
        exact absurd e (by decide)
      obtain ⟨T2, hT2⟩ := hb c h0 hbtc ⟨T, P, hP, hper⟩ hnw
      apply ha c h0
      refine ⟨T + T2, P, hP, fun t ht => ?_⟩
      rw [← hT2 (t + P) (by cfomega), ← hT2 t (by cfomega), hper t (by cfomega)]
    · refine ⟨T, fun u hu => ?_⟩
      have hr : (u - T) % P < P := Nat.mod_lt _ hP
      have he : T + (u - T) % P + ((u - T) / P) * P = u := by
        have hh := Nat.mod_add_div (u - T) P
        rw [Nat.mul_comm P ((u - T) / P)] at hh
        cfomega
      have hp := Rule30Jen.periodic_mul hper ((u - T) / P) (T + (u - T) % P) (by cfomega)
      rw [he] at hp
      rw [hp]
      cases h : c (T + (u - T) % P)
      · rfl
      · exact absurd ⟨(u - T) % P, hr, h⟩ hno

end Rule30UOR.TowerBoundary
