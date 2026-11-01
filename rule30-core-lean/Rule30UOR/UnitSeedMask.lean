module
public import Rule30UOR.ResidueJen
public import Ruliology.CellularAutomata.Rule30PeriodTwo
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The left mask at the unit seed

The kit-level left mask `DiagonalCone.DrivenLeftMask` (every finite start of the left half driven
by an eventually periodic boundary with late black times fails black-time consistency, after any
transient) implies the left-only obligation `NoPeriodicBlackConsistent`
(`DiagonalCone.noPeriodicBlackConsistent_of_drivenLeftMask`). This module makes the relation exact.

* `drivenLeftMask_iff_zero`: the transient of the mask is another seed. By the edge, the row at
  the onset `T` is a finite start with leftmost black cell at `-(m + T)`, and the driven half
  restarted there is the half driven by the shifted boundary (`L_from`), so the mask after a
  transient is the mask from time `0` (`DrivenLeftMaskZero`).
* `noPeriodicBlackConsistent_iff_singleSeedMask`: the obligation is exactly the mask at one seed,
  the unit seed (black only at `-1`), from time `0`, for boundaries starting black
  (`SingleSeedMask`). Every other finite seed is content of the mask beyond the obligation.
* `q01_of_drivenLeftMask`: at the boundary `(10)^∞` the mask is the kit's open period-two question
  `Rule30PeriodTwo.Q01`. The general step is `L_eq_zero_driven`: a left half whose column `-1` is
  black at every black time of its boundary is the zero-driven half (the OR-gate is saturated
  there).
* `noPeriodTwoBlackConsistent_of_q01`: conversely `Q01` already decides the obligation on every
  boundary of eventual period `2` (`NoPeriodTwoBlackConsistent`): the alternating case is `Q01` at
  the row `Lh c (S + 2)`, the all-black case is Jen inside the half
  (`DiagonalCone.driven_column_not_eventuallyPeriodic`). So `Q01` sits between the mask and the
  period-two part of the obligation; the kit's `not_eventually_period_two_of_Q01` is its instance
  at the center.
* `periodTwo_skeleton`: for the boundary `(10)^∞` the kit's stripe and the comb (`comb_evolves`)
  are two infinite starts, both black at column `-1` at every even time, that differ at every
  other cell of the half-plane. Among infinite starts the black-time data of `(10)^∞` determine
  column `-1` at the even times and no other cell, so a single forced cell propagated leftward
  (Jen's mechanism) cannot pass column `-1` for this word.
* `mask_window_satisfiable`: no finite window refutes the mask (the kit's barrier).

None of these is a route: each is an exact relation between named statements, and none proves
`NoPeriodicBlackConsistent`, `SingleSeedMask` or `Q01`. Chain:
`DrivenLeftMask ↔ DrivenLeftMaskZero → SingleSeedMask ↔ NoPeriodicBlackConsistent → Problem1`, and
`DrivenLeftMask → Q01 → NoPeriodTwoBlackConsistent`.
-/

@[expose] public section

namespace Rule30UOR.UnitSeedMask

open Rule30UOR.Core Rule30UOR.Fixed Rule30UOR.DiagonalCone
open Ruliology.CellularAutomata

/-! ## The driven half restarted -/

/-- The driven half sees its seed only at `p < 0`. -/
theorem L_seed_congr (c : Nat → Bool) {s s2 : Int → Bool} (h : ∀ p : Int, p < 0 → s p = s2 p) :
    ∀ (t : Nat) (p : Int), p < 0 → Rule30DrivenLeft.L c s t p = Rule30DrivenLeft.L c s2 t p := by
  intro t
  induction t with
  | zero => intro p hp; rw [Rule30DrivenLeft.L_zero hp, Rule30DrivenLeft.L_zero hp]; exact h p hp
  | succ t ih =>
    intro p hp
    rw [Rule30DrivenLeft.L_succ hp, Rule30DrivenLeft.L_succ hp, ih (p - 1) (by cfomega), ih p hp]
    rcases Int.lt_or_le (p + 1) 0 with hq | hq
    · rw [ih (p + 1) hq]
    · rw [show p + 1 = 0 by cfomega, Rule30DrivenLeft.L_col0, Rule30DrivenLeft.L_col0]

/-- The semigroup law of the driven half: from time `T` it is the half driven by the shifted
boundary from its own row at `T`. -/
theorem L_from (c : Nat → Bool) (s : Int → Bool) (T : Nat) :
    ∀ (k : Nat) (p : Int), p ≤ 0 →
      Rule30DrivenLeft.L (fun k => c (T + k)) (fun p => Rule30DrivenLeft.L c s T p) k p =
        Rule30DrivenLeft.L c s (T + k) p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rcases Int.lt_or_le p 0 with h | h
    · rw [Rule30DrivenLeft.L_zero h]; rfl
    · rw [show p = 0 by cfomega, Rule30DrivenLeft.L_col0, Rule30DrivenLeft.L_col0]
  | succ k ih =>
    intro p hp
    rcases Int.lt_or_le p 0 with h | h
    · rw [Rule30DrivenLeft.L_succ h, show T + (k + 1) = (T + k) + 1 by cfomega, Rule30DrivenLeft.L_succ h,
        ih (p - 1) (by cfomega), ih p (by cfomega), ih (p + 1) (by cfomega)]
    · rw [show p = 0 by cfomega, Rule30DrivenLeft.L_col0, Rule30DrivenLeft.L_col0]

/-- The half driven from white, restarted at time `T`: the kit's driven half with the shifted
boundary and the row at `T` as its start. -/
theorem Lh_from (c : Nat → Bool) (T : Nat) :
    ∀ (k : Nat) (p : Int), p ≤ 0 →
      Rule30DrivenLeft.L (fun k => c (T + k)) (fun p => Lh c T p) k p = Lh c (T + k) p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rcases Int.lt_or_le p 0 with h | h
    · rw [Rule30DrivenLeft.L_zero h]; rfl
    · rw [show p = 0 by cfomega, Rule30DrivenLeft.L_col0, Lh_col0]
  | succ k ih =>
    intro p hp
    rcases Int.lt_or_le p 0 with h | h
    · rw [Rule30DrivenLeft.L_succ h, show T + (k + 1) = (T + k) + 1 by cfomega, Lh_succ_neg c (T + k) p h,
        ih (p - 1) (by cfomega), ih p (by cfomega), ih (p + 1) (by cfomega)]
    · rw [show p = 0 by cfomega, Rule30DrivenLeft.L_col0, Lh_col0]

/-- **Saturated boundary.** If at every black time of the boundary `b` column `-1` is black (in
the half driven by `b` or in the zero-driven half), the two halves agree at every `p < 0`: the
OR-gate of column `-1` is saturated whenever `b` is black. -/
theorem L_eq_zero_driven (b : Nat → Bool) (s : Int → Bool)
    (hm : ∀ t, b t = true →
      Rule30DrivenLeft.L b s t (-1) = true ∨ Rule30DrivenLeft.L (fun _ => false) s t (-1) = true) :
    ∀ (t : Nat) (p : Int), p < 0 →
      Rule30DrivenLeft.L b s t p = Rule30DrivenLeft.L (fun _ => false) s t p := by
  intro t
  induction t with
  | zero => intro p hp; rw [Rule30DrivenLeft.L_zero hp, Rule30DrivenLeft.L_zero hp]
  | succ t ih =>
    intro p hp
    rw [Rule30DrivenLeft.L_succ hp, Rule30DrivenLeft.L_succ hp, ih (p - 1) (by cfomega), ih p hp]
    rcases Int.lt_or_le (p + 1) 0 with hq | hq
    · rw [ih (p + 1) hq]
    · have e : p = -1 := by cfomega
      subst e
      rw [show (-1 : Int) + 1 = 0 by rfl, Rule30DrivenLeft.L_col0, Rule30DrivenLeft.L_col0]
      cases hbt : b t
      · rfl
      · have hz : Rule30DrivenLeft.L (fun _ => false) s t (-1) = true := by
          rcases hm t hbt with h | h
          · rw [← ih (-1) (by decide)]; exact h
          · exact h
        rw [hz]
        cases Rule30DrivenLeft.L (fun _ => false) s t (-1 - 1) <;> rfl

/-! ## The transient of the mask is a seed -/

/-- The left mask with no transient: black-time consistency from time `0`. -/
def DrivenLeftMaskZero : Prop :=
  ∀ (c : Nat → Bool) (s : Int → Bool) (m : Nat), 0 < m →
    (∀ p : Int, p < -(m : Int) → s p = false) → s (-(m : Int)) = true →
    Rule30Jen.EventuallyPeriodic c → (∀ T, ∃ t, T ≤ t ∧ c t = true) →
    ¬ ∀ t, c t = true → Rule30DrivenLeft.L c s t (-1) = !c (t + 1)

/-- **The transient of the mask is a seed.** The row at the onset `T` is again a finite seed
(leftmost black at `-(m + T)`, by the edge), so the eventual mask is the mask from time `0`. -/
theorem drivenLeftMask_iff_zero : DrivenLeftMask ↔ DrivenLeftMaskZero := by
  constructor
  · intro h c s m hm hs0 hs1 hc hrec hall
    exact h c s m hm hs0 hs1 hc hrec ⟨0, fun t _ ht => hall t ht⟩
  · intro h c s m hm hs0 hs1 hc hrec hT
    obtain ⟨T, hT⟩ := hT
    obtain ⟨he0, he1⟩ := Rule30DrivenLeft.edge (c := c) hs0 hs1 hm T
    refine h (fun k => c (T + k)) (fun p => Rule30DrivenLeft.L c s T p) (m + T) (by cfomega)
      (fun p hp => he0 p hp) he1 ?_ ?_ ?_
    · obtain ⟨T0, P, hP, hper⟩ := hc
      exact ⟨T0, P, hP, fun k hk => by
        show c (T + (k + P)) = c (T + k)
        rw [show T + (k + P) = T + k + P by cfomega]
        exact hper (T + k) (by cfomega)⟩
    · intro N
      obtain ⟨t, ht, hct⟩ := hrec (T + N)
      exact ⟨t - T, by cfomega, by
        show c (T + (t - T)) = true
        rw [show T + (t - T) = t by cfomega]
        exact hct⟩
    · intro k hk
      rw [L_from c s T k (-1) (by decide)]
      exact hT (T + k) (by cfomega) hk

/-! ## The obligation is the mask at the unit seed -/

/-- The unit seed: one black cell at `-1`. -/
def unitSeed (p : Int) : Bool := decide (p = -1)

theorem unitSeed_eq_Lh_one (c : Nat → Bool) (h0 : c 0 = true) (p : Int) (hp : p < 0) :
    unitSeed p = Lh c 1 p := by
  rcases Int.lt_or_le p (-1) with h | h
  · rw [start_white c p (by cfomega)]
    exact decide_eq_false (by cfomega)
  · rw [show p = -((1 : Nat) : Int) by cfomega, start_black c h0]
    exact decide_eq_true (by cfomega)

/-- The mask at the unit seed, from time `0`, for boundaries starting black. -/
def SingleSeedMask : Prop :=
  ∀ c : Nat → Bool, c 0 = true → Rule30Jen.EventuallyPeriodic c → (∀ T, ∃ t, T ≤ t ∧ c t = true) →
    ¬ ∀ t, c t = true → Rule30DrivenLeft.L c unitSeed t (-1) = !c (t + 1)

/-- The boundary with one black cell prepended. -/
def cons1 (c : Nat → Bool) : Nat → Bool
  | 0 => true
  | t + 1 => c t

/-- **The obligation is the mask at one seed.** `NoPeriodicBlackConsistent` is exactly the left
mask restricted to the unit seed at `-1`, consistency from time `0`, and boundaries starting
black. -/
theorem noPeriodicBlackConsistent_iff_singleSeedMask :
    NoPeriodicBlackConsistent ↔ SingleSeedMask := by
  constructor
  · intro h c h0 hc hrec hall
    have hbtc : BlackTimeConsistent (cons1 c) := by
      intro t ht
      cases t with
      | zero =>
        show c 0 = !(Lh (cons1 c) 0 (-1))
        rw [Lh_zero_neg _ _ (by decide), h0]; rfl
      | succ k =>
        show c (k + 1) = !(Lh (cons1 c) (k + 1) (-1))
        rw [← L_shift (cons1 c) k (-1) (by decide),
          L_seed_congr _ (fun p hp => (unitSeed_eq_Lh_one (cons1 c) rfl p hp).symm) k (-1) (by decide)]
        have e : Rule30DrivenLeft.L (fun k => cons1 c (k + 1)) unitSeed k (-1) = !c (k + 1) :=
          hall k ht
        rw [e]; cases c (k + 1) <;> rfl
    have hep : Rule30Jen.EventuallyPeriodic (cons1 c) := by
      obtain ⟨T, P, hP, hper⟩ := hc
      refine ⟨T + 1, P, hP, fun t ht => ?_⟩
      cases t with
      | zero => exact absurd ht (by cfomega)
      | succ j =>
        rw [show j + 1 + P = (j + P) + 1 by cfomega]
        exact hper j (by cfomega)
    obtain ⟨T, hT⟩ := h (cons1 c) rfl hbtc hep
    obtain ⟨t, ht, hct⟩ := hrec T
    have h2 : c t = false := hT (t + 1) (by cfomega)
    rw [hct] at h2
    exact Bool.noConfusion h2
  · intro h c h0 hbtc hep
    have hep2 := shift_eventuallyPeriodic c hep
    have h1 : c 1 = true := by
      have e := hbtc 0 h0
      rw [Lh_zero_neg _ _ (by decide)] at e
      exact e
    obtain ⟨T, P, hP, hper⟩ := hep
    refine Decidable.byCases (p := ∃ r, r < P ∧ c (T + r) = true) (fun hb => ?_) (fun hno => ?_)
    · exfalso
      obtain ⟨r, _, hr⟩ := hb
      have hrec : ∀ N, ∃ t, N ≤ t ∧ c (t + 1) = true := by
        intro N
        have hNP : (N + 1) * 1 ≤ (N + 1) * P := Nat.mul_le_mul_left (N + 1) hP
        refine ⟨T + r + (N + 1) * P - 1, by cfomega, ?_⟩
        rw [show T + r + (N + 1) * P - 1 + 1 = T + r + (N + 1) * P by cfomega,
          Rule30Jen.periodic_mul hper (N + 1) (T + r) (by cfomega)]
        exact hr
      refine h (fun k => c (k + 1)) h1 hep2 hrec (fun k hk => ?_)
      rw [L_seed_congr _ (fun p hp => unitSeed_eq_Lh_one c h0 p hp) k (-1) (by decide),
        L_shift c k (-1) (by decide), hbtc (k + 1) hk]
      cases Lh c (k + 1) (-1) <;> rfl
    · refine ⟨T, fun u hu => ?_⟩
      have hr : (u - T) % P < P := Nat.mod_lt _ hP
      have he : T + (u - T) % P + ((u - T) / P) * P = u := by
        have hh := Nat.mod_add_div (u - T) P
        rw [Nat.mul_comm P ((u - T) / P)] at hh
        cfomega
      have hp := Rule30Jen.periodic_mul hper ((u - T) / P) (T + (u - T) % P) (by cfomega)
      rw [he] at hp
      rw [hp]
      cases hc : c (T + (u - T) % P)
      · rfl
      · exact absurd ⟨(u - T) % P, hr, hc⟩ hno

/-- The mask from time `0` contains the unit-seed mask. -/
theorem singleSeedMask_of_zero (h : DrivenLeftMaskZero) : SingleSeedMask :=
  fun c _ hc hrec => h c unitSeed 1 (by decide) (fun p hp => decide_eq_false (by cfomega))
    (decide_eq_true (by cfomega)) hc hrec

/-! ## Period two: the mask contains `Q₀₁`, and `Q₀₁` decides the obligation at period two -/

/-- **The mask contains `Q₀₁`.** At the boundary `(10)^∞` the hypothesis of `Q₀₁` saturates the
OR-gate at every black time, so the driven half is the zero-driven half and the mask instance is
the kit's open period-two question. -/
theorem q01_of_drivenLeftMask (hL : DrivenLeftMask) : Rule30PeriodTwo.Q01 := by
  intro m s hm hs0 hs1 hall
  have key := L_eq_zero_driven (fun t => decide (t % 2 = 0)) s (fun t ht => Or.inr (by
    have ht2 : t % 2 = 0 := of_decide_eq_true ht
    rw [show t = 2 * (t / 2) by cfomega]
    exact hall (t / 2)))
  refine hL (fun t => decide (t % 2 = 0)) s m hm hs0 hs1
    ⟨0, 2, by decide, fun t _ => by
      show decide ((t + 2) % 2 = 0) = decide (t % 2 = 0)
      rw [Nat.add_mod_right]⟩
    (fun N => ⟨2 * N, by cfomega, decide_eq_true (by cfomega)⟩)
    ⟨0, fun t _ ht => ?_⟩
  have ht2 : t % 2 = 0 := of_decide_eq_true ht
  have hk : t = 2 * (t / 2) := by cfomega
  rw [key t (-1) (by decide), hk, hall (t / 2),
    decide_eq_false (by cfomega : ¬ ((2 * (t / 2) + 1) % 2 = 0))]
  rfl

/-- A black-time consistent boundary alternating from `S` (black at `S + 2k`, white at
`S + 2k + 1`) is the hypothesis of `Q₀₁` at the row `Lh c (S + 2)`. -/
theorem alternating_contra (hQ : Rule30PeriodTwo.Q01) (c : Nat → Bool) (h0 : c 0 = true)
    (hb : BlackTimeConsistent c) (S : Nat)
    (halt : ∀ k, c (S + 2 * k) = true ∧ c (S + 2 * k + 1) = false) : False := by
  have hcol : ∀ t, c (S + 2 + t) = true → Lh c (S + 2 + t) (-1) = true := by
    intro t ht
    have hw : c (S + 2 + t + 1) = false := by
      rcases Nat.mod_two_eq_zero_or_one t with e | e
      · rw [show S + 2 + t + 1 = S + 2 * (t / 2 + 1) + 1 by cfomega]
        exact (halt (t / 2 + 1)).2
      · rw [show S + 2 + t = S + 2 * (t / 2 + 1) + 1 by cfomega, (halt (t / 2 + 1)).2] at ht
        exact Bool.noConfusion ht
    have e := hb (S + 2 + t) ht
    rw [hw] at e
    cases h : Lh c (S + 2 + t) (-1)
    · rw [h] at e; exact Bool.noConfusion e
    · rfl
  have key := L_eq_zero_driven (fun j => c (S + 2 + j)) (fun p => Lh c (S + 2) p) (fun t ht => Or.inl (by
    rw [Lh_from c (S + 2) t (-1) (by decide)]
    exact hcol t ht))
  obtain ⟨he0, he1⟩ := ResidueJen.Lh_edge c h0 (S + 2)
  refine hQ (S + 2) (fun p => Lh c (S + 2) p) (by cfomega) (fun p hp => he0 p hp) he1 (fun k => ?_)
  rw [← key (2 * k) (-1) (by decide), Lh_from c (S + 2) (2 * k) (-1) (by decide)]
  refine hcol (2 * k) ?_
  rw [show S + 2 + 2 * k = S + 2 * (k + 1) by cfomega]
  exact (halt (k + 1)).1

/-- No black-time consistent boundary starting black has eventual period `2` and late black
times. -/
def NoPeriodTwoBlackConsistent : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c →
    (∃ T, ResidueJen.BoundaryPeriodic c T 2) → EventuallyWhite c

/-- **`Q₀₁` decides the obligation at period two.** The alternating boundaries are `Q₀₁` at a row
of the half (`alternating_contra`); the eventually black boundary would make column `-1`
eventually white, which Jen's adjacency theorem inside the half excludes. -/
theorem noPeriodTwoBlackConsistent_of_q01 (hQ : Rule30PeriodTwo.Q01) : NoPeriodTwoBlackConsistent := by
  intro c h0 hb hT
  obtain ⟨T, hper⟩ := hT
  have hev : ∀ k, c (T + 2 * k) = c T := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show T + 2 * (k + 1) = T + 2 * k + 2 by cfomega, hper (T + 2 * k) (by cfomega), ih]
  have hodd : ∀ k, c (T + 1 + 2 * k) = c (T + 1) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show T + 1 + 2 * (k + 1) = T + 1 + 2 * k + 2 by cfomega, hper (T + 1 + 2 * k) (by cfomega), ih]
  have hall : ∀ u, T ≤ u → c u = c T ∨ c u = c (T + 1) := by
    intro u hu
    rcases Nat.mod_two_eq_zero_or_one (u - T) with e | e
    · left
      rw [show u = T + 2 * ((u - T) / 2) by cfomega]
      exact hev _
    · right
      rw [show u = T + 1 + 2 * ((u - T) / 2) by cfomega]
      exact hodd _
  cases h1 : c T <;> cases h2 : c (T + 1)
  · refine ⟨T, fun u hu => ?_⟩
    rcases hall u hu with e | e
    · rw [e, h1]
    · rw [e, h2]
  · exfalso
    refine alternating_contra hQ c h0 hb (T + 1) (fun k => ⟨?_, ?_⟩)
    · rw [hodd k, h2]
    · rw [show T + 1 + 2 * k + 1 = T + 2 * (k + 1) by cfomega, hev, h1]
  · exfalso
    refine alternating_contra hQ c h0 hb T (fun k => ⟨?_, ?_⟩)
    · rw [hev k, h1]
    · rw [show T + 2 * k + 1 = T + 1 + 2 * k by cfomega, hodd k, h2]
  · exfalso
    have hblack : ∀ u, T ≤ u → c u = true := by
      intro u hu
      rcases hall u hu with e | e
      · rw [e, h1]
      · rw [e, h2]
    have hwhite : ∀ u, T ≤ u → Lh c u (-1) = false := by
      intro u hu
      have e := hb u (hblack u hu)
      rw [hblack (u + 1) (by cfomega)] at e
      cases h : Lh c u (-1)
      · rfl
      · rw [h] at e; exact Bool.noConfusion e
    exact driven_column_not_eventuallyPeriodic c h0 ⟨T, 2, by decide, hper⟩
      ⟨T, 1, by decide, fun u hu => by
        show Lh c (u + 1) (-1) = Lh c u (-1)
        rw [hwhite (u + 1) (by cfomega), hwhite u hu]⟩

/-! ## The period-two skeleton -/

/-- The comb: black at the even positions `≤ -2`, column `-1` black exactly at the even times. -/
def comb (t : Nat) (p : Int) : Bool := if p = -1 then decide (t % 2 = 0) else decide (p % 2 = 0)

/-- The comb is a solution of the zero-driven left half. -/
theorem comb_evolves : ∀ (t : Nat) (p : Int), p < 0 →
    Rule30DrivenLeft.L (fun _ => false) (comb 0) t p = comb t p := by
  intro t
  induction t with
  | zero => intro p hp; exact Rule30DrivenLeft.L_zero hp
  | succ t ih =>
    intro p hp
    rw [Rule30DrivenLeft.L_succ hp, ih (p - 1) (by cfomega), ih p hp]
    rcases Int.lt_or_le (p + 1) 0 with hq | hq
    · rw [ih (p + 1) hq]
      rcases Int.lt_or_le (p + 1) (-1) with hr | hr
      · -- `p ≤ -3`: no neighbour is column `-1`
        unfold comb
        rw [if_neg (by cfomega), if_neg (by cfomega), if_neg (by cfomega), if_neg (by cfomega)]
        rcases (show p % 2 = 0 ∨ p % 2 = 1 by cfomega) with h | h
        · rw [decide_eq_false (by cfomega : ¬ ((p - 1) % 2 = 0)), decide_eq_true h,
            decide_eq_false (by cfomega : ¬ ((p + 1) % 2 = 0))]; rfl
        · rw [decide_eq_true (by cfomega : (p - 1) % 2 = 0), decide_eq_false (by cfomega : ¬ (p % 2 = 0)),
            decide_eq_true (by cfomega : (p + 1) % 2 = 0)]; rfl
      · -- `p = -2`
        have e : p = -2 := by cfomega
        subst e
        unfold comb
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg (by decide)]
        cases decide (t % 2 = 0) <;> rfl
    · -- `p = -1`
      have e : p = -1 := by cfomega
      subst e
      rw [show (-1 : Int) + 1 = 0 by rfl, Rule30DrivenLeft.L_col0]
      unfold comb
      rw [if_neg (by decide), if_pos rfl, if_pos rfl]
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · rw [decide_eq_true h, decide_eq_false (by cfomega : ¬ ((t + 1) % 2 = 0))]; rfl
      · rw [decide_eq_false (by cfomega : ¬ (t % 2 = 0)), decide_eq_true (by cfomega : (t + 1) % 2 = 0)]; rfl

/-- **The period-two black-time data fix one cell per black time and nothing else.** The stripe and
the comb both keep column `-1` black at every even time of the zero-driven left half (the
black-time consistency of `(10)^∞`), and they differ at every other cell of the half-plane: at
every position `≤ -2` at every time, and at column `-1` at every odd time. -/
theorem periodTwo_skeleton :
    (∀ k, Rule30DrivenLeft.L (fun _ => false) (comb 0) (2 * k) (-1) = true) ∧
    (∀ k, Rule30DrivenLeft.L (fun _ => false) Rule30PeriodTwo.stripe (2 * k) (-1) = true) ∧
    ∀ (t : Nat) (p : Int), p < 0 → (p = -1 → t % 2 = 1) →
      Rule30DrivenLeft.L (fun _ => false) (comb 0) t p ≠
        Rule30DrivenLeft.L (fun _ => false) Rule30PeriodTwo.stripe t p := by
  refine ⟨fun k => ?_, fun k => Rule30PeriodTwo.stripe_col (2 * k), fun t p hp hodd => ?_⟩
  · rw [comb_evolves (2 * k) (-1) (by decide)]
    unfold comb
    rw [if_pos rfl]
    exact decide_eq_true (by cfomega)
  · rw [comb_evolves t p hp, Rule30PeriodTwo.stripe_fixed t p hp]
    unfold comb Rule30PeriodTwo.stripe
    rcases Int.lt_or_le p (-1) with h | h
    · rw [if_neg (by cfomega)]
      rcases (show p % 2 = 0 ∨ p % 2 = 1 by cfomega) with e | e
      · rw [decide_eq_true e, decide_eq_false (by cfomega : ¬ (p % 2 = 1))]; decide
      · rw [decide_eq_false (by cfomega : ¬ (p % 2 = 0)), decide_eq_true e]; decide
    · have e : p = -1 := by cfomega
      subst e
      have ht : t % 2 = 1 := hodd rfl
      rw [if_pos rfl, decide_eq_false (by cfomega : ¬ (t % 2 = 0)), decide_eq_true (by decide)]
      decide

/-- **No finite window refutes the mask.** For every driver and every horizon `N`, some finite
seed (leftmost black at `-(N + 2)`) is black-time consistent on `[0, N]` (the kit's barrier). -/
theorem mask_window_satisfiable (c : Nat → Bool) (N : Nat) :
    ∃ s : Int → Bool, (∀ p : Int, p < -((N + 2 : Nat) : Int) → s p = false) ∧
      s (-((N + 2 : Nat) : Int)) = true ∧
      ∀ t, t ≤ N → c t = true → Rule30DrivenLeft.L c s t (-1) = !c (t + 1) := by
  obtain ⟨s, h0, h1, h2⟩ := Rule30DrivenLeft.barrier_exists (c := c) (fun t => !c (t + 1))
    (n := N + 2) (by cfomega)
  exact ⟨s, h0, h1, fun t ht _ => h2 t (by cfomega)⟩

/-! ## First-order forms -/

/-- The comb is a solution of the zero-driven left half at every cell `p < 0`. -/
def CombSolution : Prop :=
  ∀ (t : Nat) (p : Int), p < 0 → Rule30DrivenLeft.L (fun _ => false) (comb 0) t p = comb t p

theorem combSolution : CombSolution := comb_evolves

/-- The stripe and the comb both keep column `-1` black at the even times of the zero-driven half
and differ at every other cell. -/
def PeriodTwoSkeleton : Prop :=
  (∀ k, Rule30DrivenLeft.L (fun _ => false) (comb 0) (2 * k) (-1) = true) ∧
    (∀ k, Rule30DrivenLeft.L (fun _ => false) Rule30PeriodTwo.stripe (2 * k) (-1) = true) ∧
    ∀ (t : Nat) (p : Int), p < 0 → (p = -1 → t % 2 = 1) →
      Rule30DrivenLeft.L (fun _ => false) (comb 0) t p ≠
        Rule30DrivenLeft.L (fun _ => false) Rule30PeriodTwo.stripe t p

theorem periodTwoSkeleton : PeriodTwoSkeleton := periodTwo_skeleton

/-- For every driver and horizon `N`, a finite seed of width `N + 2` is black-time consistent on
`[0, N]`. -/
def MaskWindowSatisfiable : Prop :=
  ∀ (c : Nat → Bool) (N : Nat), ∃ s : Int → Bool,
    (∀ p : Int, p < -((N + 2 : Nat) : Int) → s p = false) ∧ s (-((N + 2 : Nat) : Int)) = true ∧
      ∀ t, t ≤ N → c t = true → Rule30DrivenLeft.L c s t (-1) = !c (t + 1)

theorem maskWindowSatisfiable : MaskWindowSatisfiable := mask_window_satisfiable

end Rule30UOR.UnitSeedMask

