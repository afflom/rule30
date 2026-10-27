module

public import Rule30Equivalents.Basic
public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Problem 1 as a causal fixed point of the two driven halves

The single black cell splits into a black center and two white halves. Each half evolves as the
half driven by the center column (`Rule30DrivenLeft.L` on the left, `Rule30Ether.drv` on the right),
and the center is updated from its two neighbours. So the center column solves the causal system

    u 0 = true,   u (t + 1) = rule (L u ∅ t (-1)) (u t) (drv u ∅ t 1).

* `center_solves`: the center column solves it.
* `eq_center_of_solves`: it is the only solution. The driven halves are causal (`L_causal`,
  `drv_causal`): at time `t` they read the driver only up to time `t`.
* `problem1_iff_coupled_halves`: Problem 1 holds iff no solution of the system is
  eventually periodic.
-/

@[expose] public section

namespace Rule30Equivalents.CoupledHalves

open Ruliology.CellularAutomata Rule30Jen
open Rule30DrivenLeft (L L_col0)
open Rule30Ether (drv drv_col0 drv_init cell_eq_drv)

/-- The causal system of the center column and its two driven halves. -/
def Solves (u : Nat → Bool) : Prop :=
  u 0 = true ∧ ∀ t, u (t + 1) = rule (L u (fun _ => false) t (-1)) (u t) (drv u (fun _ => false) t 1)

/-- The driven left half reads its start only on the left. -/
theorem L_congr_start {c : Nat → Bool} {s s' : Int → Bool} (h : ∀ p, p < 0 → s p = s' p) :
    ∀ t p, L c s t p = L c s' t p
  | 0, p => by
    show (if p < 0 then s p else c 0) = (if p < 0 then s' p else c 0)
    by_cases hp : p < 0
    · rw [ite_eq_left hp, ite_eq_left hp, h p hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
  | t + 1, p => by
    show (if p < 0 then rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) else c (t + 1)) =
      (if p < 0 then rule (L c s' t (p - 1)) (L c s' t p) (L c s' t (p + 1)) else c (t + 1))
    rw [L_congr_start h t (p - 1), L_congr_start h t p, L_congr_start h t (p + 1)]

/-- The driven left half is causal. -/
theorem L_causal {c c' : Nat → Bool} {s : Int → Bool} :
    ∀ t, (∀ k, k ≤ t → c k = c' k) → ∀ p, L c s t p = L c' s t p
  | 0, h, p => by
    show (if p < 0 then s p else c 0) = (if p < 0 then s p else c' 0)
    rw [h 0 (Nat.le_refl 0)]
  | t + 1, h, p => by
    show (if p < 0 then rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) else c (t + 1)) =
      (if p < 0 then rule (L c' s t (p - 1)) (L c' s t p) (L c' s t (p + 1)) else c' (t + 1))
    have h' : ∀ k, k ≤ t → c k = c' k := fun k hk => h k (by omega)
    rw [L_causal t h' (p - 1), L_causal t h' p, L_causal t h' (p + 1), h (t + 1) (Nat.le_refl _)]

/-- The driven right half is causal. -/
theorem drv_causal {c c' : Nat → Bool} {x : Nat → Bool} :
    ∀ t, (∀ k, k ≤ t → c k = c' k) → ∀ p, drv c x t p = drv c' x t p
  | 0, h, p => by
    rcases p with _ | p
    · rw [drv_col0, drv_col0, h 0 (Nat.le_refl 0)]
    · rw [drv_init _ _ _ (by omega), drv_init _ _ _ (by omega)]
  | t + 1, h, p => by
    rcases p with _ | p
    · rw [drv_col0, drv_col0, h (t + 1) (Nat.le_refl _)]
    · show rule (drv c x t p) (drv c x t (p + 1)) (drv c x t (p + 2)) =
        rule (drv c' x t p) (drv c' x t (p + 1)) (drv c' x t (p + 2))
      have h' : ∀ k, k ≤ t → c k = c' k := fun k hk => h k (by omega)
      rw [drv_causal t h' p, drv_causal t h' (p + 1), drv_causal t h' (p + 2)]

/-- **The center column solves the system.** -/
theorem center_solves : Solves c := by
  refine ⟨rfl, fun t => ?_⟩
  have hl : L c (fun _ => false) t (-1) = cell t (-1) := by
    have := Rule30DrivenLeft.cell_eq_L 0 t (-1) (by omega)
    simp only [Nat.zero_add] at this
    rw [← this]
    exact L_congr_start (fun p hp => by
      show false = cell 0 p
      simp [cell]; omega) t (-1)
  have hr : drv c (fun _ => false) t 1 = cell t 1 := by
    have h0 := cell_eq_drv 0 t 1
    simp only [Nat.zero_add] at h0
    have h1 : cell t 1 = drv (fun t => cell t 0) (fun p => cell 0 (p : Int)) t 1 := h0
    rw [h1]
    exact Rule30PeriodTwoSideways.drv_congr (fun p hp => by
      show false = cell 0 (p : Int)
      simp [cell]; omega) t 1
  show cell (t + 1) 0 = rule (L c (fun _ => false) t (-1)) (cell t 0) (drv c (fun _ => false) t 1)
  rw [hl, hr]
  rfl

/-- **The center column is the only solution.** -/
theorem eq_center_of_solves {u : Nat → Bool} (h : Solves u) : u = c := by
  have key : ∀ t, ∀ k, k ≤ t → u k = c k := by
    intro t
    induction t with
    | zero =>
      intro k hk
      rw [show k = 0 by omega, h.1]
      rfl
    | succ t ih =>
      intro k hk
      rcases Nat.lt_or_ge k (t + 1) with hk' | hk'
      · exact ih k (by omega)
      · rw [show k = t + 1 by omega, h.2 t, center_solves.2 t, L_causal t ih (-1),
          drv_causal t ih 1, ih t (Nat.le_refl t)]
  funext t
  exact key t t (Nat.le_refl t)

/-- **Problem 1 ⟺ no solution of the coupled-halves system is eventually periodic**. -/
theorem problem1_iff_coupled_halves : Rule30Prize.Problem1 ↔
    ∀ u : Nat → Bool, u 0 = true →
      (∀ t, u (t + 1) = Rule30Jen.rule (Rule30DrivenLeft.L u (fun _ => false) t (-1)) (u t)
        (Rule30Ether.drv u (fun _ => false) t 1)) →
      ¬ Rule30Jen.EventuallyPeriodic u := by
  constructor
  · intro h u h0 hrec
    rw [eq_center_of_solves ⟨h0, hrec⟩]
    exact h
  · intro h
    exact h c center_solves.1 center_solves.2

end Rule30Equivalents.CoupledHalves
