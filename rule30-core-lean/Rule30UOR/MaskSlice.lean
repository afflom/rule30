module
public import Rule30UOR.UnitSeedMask
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The period slices of the left mask

An annotation on the open claim `black-time-consistency`, not a route: every statement here is an
exact relation between named statements, and none proves `DiagonalCone.DrivenLeftMask`,
`Rule30PeriodTwo.Q01` or `Problem1`.

* `L_congr_or`: the kit's driven half sees its driver only through the OR-gate of column `-1`,
  `L c s k (-1) || c k`. Two drivers with the same OR-gate at every time give the same half at
  every `p < 0`, from every seed. `UnitSeedMask.L_eq_zero_driven` (one driver white) and
  `Walled.Lh_eq_Lh_runMask` (the run mask under black-time consistency) are instances.
* `DrivenLeftMaskAt Q`: the kit-level left mask restricted to boundaries of eventual period `Q`.
  The mask implies every slice (`drivenLeftMaskAt_of_drivenLeftMask`), and the slice at `Q * n`
  implies the slice at `Q` (`drivenLeftMaskAt_of_mul`).
* `drivenLeftMaskAt_one`: the slice at period `1` holds. An eventually black boundary that is
  black-time consistent would make column `-1` eventually white, which Jen's adjacency theorem
  inside the half excludes (`black_tail_contra`).
* `q01_iff_drivenLeftMaskAt_two`: the slice at period `2` is exactly the kit's open `Q01`, for
  every finite seed. Restarted at a late black time (`UnitSeedMask.L_from` and the edge), an
  alternating boundary that is black-time consistent saturates the OR-gate at every black time,
  so its half is the zero-driven half from a finite seed. The all-black phase is the slice at
  period `1`. So period `2` is the first open slice of the mask, `q01_of_drivenLeftMaskAt_even`
  puts `Q01` inside every slice of even period, and `UnitSeedMask.q01_of_drivenLeftMask` factors
  through the slice.
-/

@[expose] public section

namespace Rule30UOR.MaskSlice

open Rule30UOR.Core Rule30UOR.Fixed Rule30UOR.DiagonalCone
open Ruliology.CellularAutomata

/-! ## The OR-gate congruence -/

/-- **The driven half sees its driver only through `col(-1) || driver`.** Two drivers with the
same OR-gate at every time give the same half at every `p < 0`, from every seed. -/
theorem L_congr_or (c d : Nat → Bool) (s : Int → Bool)
    (h : ∀ k, (Rule30DrivenLeft.L c s k (-1) || c k) = (Rule30DrivenLeft.L c s k (-1) || d k)) :
    ∀ (k : Nat) (p : Int), p < 0 → Rule30DrivenLeft.L c s k p = Rule30DrivenLeft.L d s k p := by
  intro k
  induction k with
  | zero => intro p hp; rw [Rule30DrivenLeft.L_zero hp, Rule30DrivenLeft.L_zero hp]
  | succ k ih =>
    intro p hp
    rw [Rule30DrivenLeft.L_succ hp, Rule30DrivenLeft.L_succ hp, ih (p - 1) (by cfomega)]
    rcases Int.lt_or_eq_of_le (show p + 1 ≤ 0 by cfomega) with hp1 | hp1
    · rw [ih p hp, ih (p + 1) hp1]
    · rw [hp1, Rule30DrivenLeft.L_col0, Rule30DrivenLeft.L_col0, show p = -1 by cfomega]
      show xor _ (_ || c k) = xor _ (_ || d k)
      rw [h k, ih (-1) (by decide)]

/-! ## The slices of the mask by eventual period -/

/-- The kit-level left mask (`DiagonalCone.DrivenLeftMask`) on the boundaries of eventual period
`Q`: no finite seed of the half driven by such a boundary with late black times is black-time
consistent after any transient. -/
def DrivenLeftMaskAt (Q : Nat) : Prop :=
  ∀ (c : Nat → Bool) (s : Int → Bool) (m : Nat), 0 < m →
    (∀ p : Int, p < -(m : Int) → s p = false) → s (-(m : Int)) = true →
    (∃ T, ResidueJen.BoundaryPeriodic c T Q) → (∀ T, ∃ t, T ≤ t ∧ c t = true) →
    ¬ ∃ T, ∀ t, T ≤ t → c t = true → Rule30DrivenLeft.L c s t (-1) = !c (t + 1)

/-- **The mask implies every slice.** -/
theorem drivenLeftMaskAt_of_drivenLeftMask (Q : Nat) (hQ : 0 < Q) (h : DrivenLeftMask) :
    DrivenLeftMaskAt Q := by
  intro c s m hm hs0 hs1 hc hrec hT
  obtain ⟨T, hper⟩ := hc
  exact h c s m hm hs0 hs1 ⟨T, Q, hQ, hper⟩ hrec hT

/-- **The slice at a multiple of `Q` implies the slice at `Q`.** -/
theorem drivenLeftMaskAt_of_mul (Q n : Nat) (h : DrivenLeftMaskAt (Q * n)) : DrivenLeftMaskAt Q := by
  intro c s m hm hs0 hs1 hc hrec hT
  obtain ⟨T, hper⟩ := hc
  have hper' : ∀ t, T ≤ t → c (t + Q) = c t := hper
  refine h c s m hm hs0 hs1 ⟨T, fun t ht => ?_⟩ hrec hT
  rw [Nat.mul_comm Q n]
  exact Rule30Jen.periodic_mul hper' n t ht

/-- A boundary black from `t0` and black-time consistent from `t0` would make column `-1` of its
half white from `t0`; Jen's adjacency theorem inside the half excludes it. -/
theorem black_tail_contra (c : Nat → Bool) (s : Int → Bool) (m : Nat) (hm : 0 < m)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false) (hs1 : s (-(m : Int)) = true) (t0 : Nat)
    (hb : ∀ t, t0 ≤ t → c t = true)
    (hcons : ∀ t, t0 ≤ t → c t = true → Rule30DrivenLeft.L c s t (-1) = !c (t + 1)) : False := by
  have hw : ∀ t, t0 ≤ t → Rule30DrivenLeft.L c s t (-1) = false := by
    intro t ht
    rw [hcons t ht (hb t ht), hb (t + 1) (by cfomega)]
    rfl
  refine Rule30DrivenLeft.col_neg_one_not_periodic (c := c) hs0 hs1 hm
    ⟨t0, 1, by decide, fun t ht => by rw [hb (t + 1) (by cfomega), hb t ht]⟩
    ⟨t0, 1, by decide, fun t ht => ?_⟩
  show Rule30DrivenLeft.L c s (t + 1) (-1) = Rule30DrivenLeft.L c s t (-1)
  rw [hw (t + 1) (by cfomega), hw t ht]

/-- **The slice at period `1` holds** (Jen inside the half). -/
theorem drivenLeftMaskAt_one : DrivenLeftMaskAt 1 := by
  intro c s m hm hs0 hs1 hc hrec hT
  obtain ⟨T0, hper⟩ := hc
  obtain ⟨T1, hcons⟩ := hT
  obtain ⟨t0, ht0, hct0⟩ := hrec (T0 + T1)
  have hper' : ∀ t, T0 ≤ t → c (t + 1) = c t := hper
  have hb : ∀ t, t0 ≤ t → c t = true := by
    intro t ht
    have e := Rule30Jen.periodic_mul hper' (t - t0) t0 (by cfomega)
    rw [show t0 + (t - t0) * 1 = t by cfomega] at e
    rw [e, hct0]
  exact black_tail_contra c s m hm hs0 hs1 t0 hb (fun t ht => hcons t (by cfomega))

/-- **The slice at period `2` contains `Q01`**: at the boundary `(10)^∞` the hypothesis of `Q01`
saturates the OR-gate at every black time. -/
theorem q01_of_drivenLeftMaskAt_two (hL : DrivenLeftMaskAt 2) : Rule30PeriodTwo.Q01 := by
  intro m s hm hs0 hs1 hall
  have key := UnitSeedMask.L_eq_zero_driven (fun t => decide (t % 2 = 0)) s (fun t ht => Or.inr (by
    have ht2 : t % 2 = 0 := of_decide_eq_true ht
    rw [show t = 2 * (t / 2) by cfomega]
    exact hall (t / 2)))
  refine hL (fun t => decide (t % 2 = 0)) s m hm hs0 hs1
    ⟨0, fun t _ => by
      show decide ((t + 2) % 2 = 0) = decide (t % 2 = 0)
      rw [Nat.add_mod_right]⟩
    (fun N => ⟨2 * N, by cfomega, decide_eq_true (by cfomega)⟩)
    ⟨0, fun t _ ht => ?_⟩
  have ht2 : t % 2 = 0 := of_decide_eq_true ht
  have hk : t = 2 * (t / 2) := by cfomega
  rw [key t (-1) (by decide), hk, hall (t / 2),
    decide_eq_false (by cfomega : ¬ ((2 * (t / 2) + 1) % 2 = 0))]
  rfl

/-- **`Q01` decides the slice at period `2`**, for every finite seed. Restarted at a late black
time `t0` the half is driven from the finite row at `t0` (leftmost black at `-(m + t0)`). If the
boundary alternates from `t0`, black-time consistency keeps column `-1` black at every black time,
so the half is the zero-driven half and its even times are the hypothesis of `Q01`. If it is
black from `t0`, the slice at period `1` applies. -/
theorem drivenLeftMaskAt_two_of_q01 (hQ : Rule30PeriodTwo.Q01) : DrivenLeftMaskAt 2 := by
  intro c s m hm hs0 hs1 hc hrec hT
  obtain ⟨T0, hper⟩ := hc
  obtain ⟨T1, hcons⟩ := hT
  obtain ⟨t0, ht0, hct0⟩ := hrec (T0 + T1)
  have hper2 : ∀ t, T0 ≤ t → c (t + 2) = c t := hper
  have hev : ∀ k, c (t0 + 2 * k) = c t0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [show t0 + 2 * (k + 1) = t0 + 2 * k + 2 by cfomega, hper2 _ (by cfomega), ih]
  have hodd : ∀ k, c (t0 + 2 * k + 1) = c (t0 + 1) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show t0 + 2 * (k + 1) + 1 = t0 + 2 * k + 1 + 2 by cfomega, hper2 _ (by cfomega), ih]
  cases h1 : c (t0 + 1)
  · -- alternating from `t0`: the half from `t0` is the zero-driven half from a finite seed
    have hnext : ∀ j, c (t0 + j) = true → c (t0 + j + 1) = false := by
      intro j hj
      rcases Nat.mod_two_eq_zero_or_one j with e | e
      · rw [show t0 + j + 1 = t0 + 2 * (j / 2) + 1 by cfomega, hodd, h1]
      · rw [show t0 + j = t0 + 2 * (j / 2) + 1 by cfomega, hodd, h1] at hj
        exact Bool.noConfusion hj
    have hcol : ∀ j, c (t0 + j) = true → Rule30DrivenLeft.L c s (t0 + j) (-1) = true := by
      intro j hj
      rw [hcons (t0 + j) (by cfomega) hj, hnext j hj]
      rfl
    obtain ⟨he0, he1⟩ := Rule30DrivenLeft.edge (c := c) hs0 hs1 hm t0
    have key := UnitSeedMask.L_eq_zero_driven (fun j => c (t0 + j))
      (fun p => Rule30DrivenLeft.L c s t0 p)
      (fun j hj => Or.inl (by rw [UnitSeedMask.L_from c s t0 j (-1) (by decide)]; exact hcol j hj))
    refine hQ (m + t0) (fun p => Rule30DrivenLeft.L c s t0 p) (by cfomega) (fun p hp => he0 p hp) he1
      (fun k => ?_)
    rw [← key (2 * k) (-1) (by decide), UnitSeedMask.L_from c s t0 (2 * k) (-1) (by decide)]
    exact hcol (2 * k) (by rw [hev k, hct0])
  · -- black from `t0`: the slice at period `1`
    have hb : ∀ t, t0 ≤ t → c t = true := by
      intro t ht
      rcases Nat.mod_two_eq_zero_or_one (t - t0) with e | e
      · rw [show t = t0 + 2 * ((t - t0) / 2) by cfomega, hev, hct0]
      · rw [show t = t0 + 2 * ((t - t0) / 2) + 1 by cfomega, hodd, h1]
    exact black_tail_contra c s m hm hs0 hs1 t0 hb (fun t ht => hcons t (by cfomega))

/-- **The slice of the mask at period `2` is exactly `Q01`.** -/
theorem q01_iff_drivenLeftMaskAt_two : Rule30PeriodTwo.Q01 ↔ DrivenLeftMaskAt 2 :=
  ⟨drivenLeftMaskAt_two_of_q01, q01_of_drivenLeftMaskAt_two⟩

/-- **Every slice of even period contains `Q01`.** -/
theorem q01_of_drivenLeftMaskAt_even (n : Nat) (h : DrivenLeftMaskAt (2 * n)) : Rule30PeriodTwo.Q01 :=
  q01_of_drivenLeftMaskAt_two (drivenLeftMaskAt_of_mul 2 n h)

/-! ## First-order forms -/

/-- The OR-gate congruence of the driven half, for every pair of drivers and every seed. -/
def OrGateCongruence : Prop :=
  ∀ (c d : Nat → Bool) (s : Int → Bool),
    (∀ k, (Rule30DrivenLeft.L c s k (-1) || c k) = (Rule30DrivenLeft.L c s k (-1) || d k)) →
    ∀ (k : Nat) (p : Int), p < 0 → Rule30DrivenLeft.L c s k p = Rule30DrivenLeft.L d s k p

theorem orGateCongruence : OrGateCongruence := L_congr_or

end Rule30UOR.MaskSlice

