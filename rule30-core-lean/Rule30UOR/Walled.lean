module
public import Rule30UOR.DiagonalCone
public import Ruliology.CellularAutomata.Rule30ZeroBoundary
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The walled column: black-time consistency on isolated black times

An annotation on the open claim `black-time-consistency` (`DiagonalCone.NoPeriodicBlackConsistent`),
not a route: every statement here is an exact relation between named statements, and none of them
proves the obligation or `Problem1`.

* `Lh_eq_Lh_runMask`, `btc_col_linear`: under black-time consistency the driven left half sees the
  boundary only through its run interiors `runMask c t = c t ∧ c (t+1)`, and column `-1` is rule 60
  with the run mask as an additive source (the OR-gate becomes an XOR).
* `walled`: column `-1` of rule 30 on the left half-line from one black cell against a white wall
  (`seedDriver`: column `0` black at time `0` only). It is the zero-boundary column from the single
  black cell at depth `1` (`walled_eq_zrow`).
* `noPeriodicIsolatedBlackConsistent_iff`: the part of the obligation on boundaries with no two
  adjacent black times after time `1` (`IsolatedBlack`) is *exactly* the statement that the walled
  column has no infinite progression of black cells of step `≥ 2` (`¬ WalledAP`). Hence
  `not_walledAP_of_noPeriodicBlackConsistent`. A walled progression would refute the obligation.
* `walledAP_iff`: the restrictions in `WalledAP` are normal forms: step `1` is excluded by Jen's
  adjacency theorem inside the half, start `0` by the white start, and a progression from any start
  `≥ 1` has a tail from `3`.
* `not_walledAPTwo_of_Q01`: step `2` is the kit's open `Q01` at the one-cell start, in every phase.
  `ZeroWallQ P` is the step-`P` member of that family (`q01_iff_zeroWallQ_two`), and the family
  decides `WalledAP` (`not_walledAP_of_zeroWallFamily`).
* `noPeriodicEventuallyIsolated_of_zeroWallFamily`: the family decides more, every eventually
  periodic black-time consistent boundary whose periodic part has no adjacent black times: after
  the last run interior the left half restarts against a wall from a finite row
  (`Lh_restart_zrow`, `row_finSupp`). The chain is
  `ZeroWallFamily → NoPeriodicEventuallyIsolatedBlackConsistent → NoPeriodicIsolatedBlackConsistent
  ↔ ¬ WalledAP`, with `NoPeriodicBlackConsistent` implying each slice.
* `not_isolatedBlack_center`: the center has a black run at times `3, 4`, so the isolated slice
  does not contain it.
-/

@[expose] public section

namespace Rule30UOR.Walled

open Rule30UOR.Core Rule30UOR.Fixed Rule30UOR.DiagonalCone
open Ruliology.CellularAutomata

/-! ## The effective driver of a black-time consistent boundary -/

/-- The run-interior mask of a boundary: black now and black next. -/
def runMask (c : Nat → Bool) (t : Nat) : Bool := c t && c (t + 1)

/-- **Effective driver.** Under black-time consistency the left half sees only the run interiors:
at a black time that ends a run the OR-gate of column `-1` is saturated by column `-1` itself. -/
theorem Lh_eq_Lh_runMask (c : Nat → Bool) (h : BlackTimeConsistent c) :
    ∀ (t : Nat) (p : Int), p < 0 → Lh c t p = Lh (runMask c) t p := by
  intro t
  induction t with
  | zero => intro p hp; rw [Lh_zero_neg c p hp, Lh_zero_neg _ p hp]
  | succ t ih =>
    intro p hp
    rw [Lh_succ_neg c t p hp, Lh_succ_neg _ t p hp, ih (p - 1) (by cfomega), ih p hp]
    rcases Int.lt_or_le (p + 1) 0 with hq | hq
    · rw [ih (p + 1) hq]
    · have hp1 : p = -1 := by cfomega
      subst hp1
      rw [show (-1 : Int) + 1 = 0 by decide, Lh_col0, Lh_col0, ← ih (-1) (by decide)]
      unfold runMask Rule30Jen.rule
      cases hct : c t
      · rfl
      · rw [h t hct]
        cases Lh c t (-1) <;> rfl

/-- **Column `-1` is rule 60 with the run mask as source** under black-time consistency. -/
theorem btc_col_linear (c : Nat → Bool) (h : BlackTimeConsistent c) (t : Nat) :
    Lh c (t + 1) (-1) = bxor (bxor (Lh c t (-2)) (Lh c t (-1))) (runMask c t) := by
  rw [Lh_succ_neg c t (-1) (by decide), show (-1 : Int) - 1 = -2 by decide,
    show (-1 : Int) + 1 = 0 by decide, Lh_col0]
  unfold runMask Rule30Jen.rule
  cases hct : c t
  · cases Lh c t (-2) <;> cases Lh c t (-1) <;> rfl
  · rw [h t hct]
    cases Lh c t (-2) <;> cases Lh c t (-1) <;> rfl

/-- No two adjacent black times after time `1`. -/
def IsolatedBlack (c : Nat → Bool) : Prop := ∀ t, 1 ≤ t → runMask c t = false

/-! ## The walled column -/

/-- The seed driver: column `0` black at time `0`, white afterwards (a white wall). -/
def seedDriver : Nat → Bool
  | 0 => true
  | _ + 1 => false

theorem seedDriver_pos (t : Nat) (ht : 1 ≤ t) : seedDriver t = false := by
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by cfomega⟩
  rfl

/-- **The walled column**: column `-1` of rule 30 on the left half-line from one black cell, with
column `0` held white from time `1`. -/
def walled (t : Nat) : Bool := Lh seedDriver t (-1)

theorem walled_zero : walled 0 = false := Lh_zero_neg seedDriver (-1) (by decide)

theorem walled_one : walled 1 = true := by
  have hb := start_black seedDriver rfl
  rw [show (-((1 : Nat) : Int)) = -1 by decide] at hb
  exact hb

/-- The walled column is black along the progression `s + k P`. -/
def WalledProgression (s P : Nat) : Prop := ∀ k, walled (s + k * P) = true

/-- An infinite arithmetic progression (step at least `2`, from time at least `3`) of black cells
in the walled column. -/
def WalledAP : Prop := ∃ s P : Nat, 3 ≤ s ∧ 2 ≤ P ∧ WalledProgression s P

/-! ## A walled progression is an isolated black-time consistent boundary -/

/-- The boundary built from a progression: black at `0`, `1` and on the progression. -/
def apBoundary (s P : Nat) (t : Nat) : Bool :=
  decide (t ≤ 1) || (decide (s ≤ t) && decide ((t - s) % P = 0))

theorem apBoundary_true {s P t : Nat} (h2 : 2 ≤ t) (ht : apBoundary s P t = true) :
    ∃ k, t = s + k * P := by
  unfold apBoundary at ht
  have h1 : decide (t ≤ 1) = false := decide_eq_false (by cfomega)
  rw [h1, Bool.false_or, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at ht
  obtain ⟨hst, hmod⟩ := ht
  refine ⟨(t - s) / P, ?_⟩
  have hh := Nat.mod_add_div (t - s) P
  rw [hmod, Nat.zero_add, Nat.mul_comm] at hh
  cfomega

theorem apBoundary_next {s P t : Nat} (hs : 3 ≤ s) (hP : 2 ≤ P) (k : Nat) (ht : t = s + k * P) :
    apBoundary s P (t + 1) = false := by
  unfold apBoundary
  have h1 : decide (t + 1 ≤ 1) = false := decide_eq_false (by cfomega)
  rw [h1, Bool.false_or]
  have hm : (t + 1 - s) % P = 1 := by
    rw [show t + 1 - s = 1 + k * P by cfomega, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by cfomega)
  rw [hm, decide_eq_false (by cfomega : ¬ (1 = 0)), Bool.and_false]

theorem apBoundary_two {s P : Nat} (hs : 3 ≤ s) : apBoundary s P 2 = false := by
  unfold apBoundary
  rw [decide_eq_false (by cfomega : ¬ (2 ≤ 1)), decide_eq_false (by cfomega : ¬ (s ≤ 2)), Bool.false_and]
  rfl

theorem apBoundary_isolated {s P : Nat} (hs : 3 ≤ s) (hP : 2 ≤ P) : IsolatedBlack (apBoundary s P) := by
  intro t ht
  unfold runMask
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · obtain rfl : t = 1 := by cfomega
    show (apBoundary s P 1 && apBoundary s P 2) = false
    rw [apBoundary_two hs, Bool.and_false]
  · cases hc : apBoundary s P t
    · rfl
    · obtain ⟨k, hk⟩ := apBoundary_true h2 hc
      rw [apBoundary_next hs hP k hk]
      rfl

/-- The progression boundary drives the same left half as the seed driver. -/
theorem Lh_apBoundary {s P : Nat} (hw : WalledProgression s P) :
    ∀ (t : Nat) (p : Int), p < 0 → Lh (apBoundary s P) t p = Lh seedDriver t p := by
  intro t
  induction t with
  | zero => intro p hp; rw [Lh_zero_neg _ p hp, Lh_zero_neg _ p hp]
  | succ t ih =>
    intro p hp
    rw [Lh_succ_neg _ t p hp, Lh_succ_neg _ t p hp, ih (p - 1) (by cfomega), ih p hp]
    rcases Int.lt_or_le (p + 1) 0 with hq | hq
    · rw [ih (p + 1) hq]
    · have hp1 : p = -1 := by cfomega
      subst hp1
      rw [show (-1 : Int) + 1 = 0 by decide, Lh_col0, Lh_col0]
      unfold Rule30Jen.rule
      congr 1
      rcases Nat.lt_or_ge t 2 with h2 | h2
      · rcases Nat.lt_or_ge t 1 with h1 | h1
        · rw [show t = 0 by cfomega]; rfl
        · rw [show t = 1 by cfomega]
          have hb := start_black seedDriver rfl
          rw [show (-((1 : Nat) : Int)) = -1 by decide] at hb
          rw [hb]; rfl
      · cases hc : apBoundary s P t
        · rw [seedDriver_pos t (by cfomega)]
        · obtain ⟨k, hk⟩ := apBoundary_true h2 hc
          have hwt : Lh seedDriver t (-1) = true := by rw [hk]; exact hw k
          rw [hwt]; rfl

/-- The obligation restricted to boundaries with isolated black times after time `1`. -/
def NoPeriodicIsolatedBlackConsistent : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c → Rule30Jen.EventuallyPeriodic c →
    IsolatedBlack c → EventuallyWhite c

/-- **A walled progression is an eventually periodic isolated black-time consistent boundary.** -/
theorem not_walledAP_of_isolatedSlice (h : NoPeriodicIsolatedBlackConsistent) : ¬ WalledAP := by
  rintro ⟨s, P, hs, hP, hw⟩
  have hL := Lh_apBoundary hw
  have h0 : apBoundary s P 0 = true := rfl
  have hbtc : BlackTimeConsistent (apBoundary s P) := by
    intro t ht
    rw [hL t (-1) (by decide)]
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · rcases Nat.lt_or_ge t 1 with h1 | h1
      · rw [show t = 0 by cfomega]; rfl
      · rw [show t = 1 by cfomega]
        have hb := start_black seedDriver rfl
        rw [show (-((1 : Nat) : Int)) = -1 by decide] at hb
        rw [hb]
        exact apBoundary_two hs
    · obtain ⟨k, hk⟩ := apBoundary_true h2 ht
      rw [apBoundary_next hs hP k hk]
      have hwt : Lh seedDriver t (-1) = true := by rw [hk]; exact hw k
      rw [hwt]; rfl
  have hep : Rule30Jen.EventuallyPeriodic (apBoundary s P) := by
    refine ⟨s, P, by cfomega, fun t ht => ?_⟩
    unfold apBoundary
    rw [decide_eq_false (by cfomega : ¬ (t + P ≤ 1)), decide_eq_false (by cfomega : ¬ (t ≤ 1)),
      decide_eq_true (by cfomega : s ≤ t + P), decide_eq_true (by cfomega : s ≤ t),
      show t + P - s = (t - s) + 1 * P by cfomega, Nat.add_mul_mod_self_right]
  obtain ⟨T, hT⟩ := h (apBoundary s P) h0 hbtc hep (apBoundary_isolated hs hP)
  have hb : apBoundary s P (s + T * P) = true := by
    unfold apBoundary
    rw [decide_eq_true (by cfomega : s ≤ s + T * P), show s + T * P - s = 0 + T * P by cfomega,
      Nat.add_mul_mod_self_right, Nat.zero_mod]
    cases decide (s + T * P ≤ 1) <;> rfl
  have hle : T ≤ s + T * P := by
    have : T * 1 ≤ T * P := Nat.mul_le_mul_left T (by cfomega)
    cfomega
  rw [hT _ hle] at hb
  exact Bool.false_ne_true hb

/-- The obligation contains its isolated slice. -/
theorem noPeriodicIsolated_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) :
    NoPeriodicIsolatedBlackConsistent :=
  fun c h0 hb hep _ => h c h0 hb hep

/-- **The obligation forbids walled progressions.** -/
theorem not_walledAP_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) : ¬ WalledAP :=
  not_walledAP_of_isolatedSlice (noPeriodicIsolated_of_noPeriodicBlackConsistent h)

/-! ## On the isolated slice column `-1` is the walled column -/

/-- Under black-time consistency with no adjacent blacks after time `1`, column `-1` is the walled
column. -/
theorem Lh_isolated (c : Nat → Bool) (h0 : c 0 = true) (h : BlackTimeConsistent c)
    (hiso : IsolatedBlack c) (t : Nat) : Lh c t (-1) = walled t := by
  have h1 : c 1 = true := by
    have e := h 0 h0
    rw [Lh_zero_neg c (-1) (by decide)] at e
    exact e
  have hm : runMask c = seedDriver := by
    funext u
    rcases Nat.lt_or_ge u 1 with hu | hu
    · rw [show u = 0 by cfomega]
      show (c 0 && c 1) = seedDriver 0
      rw [h0, h1]; rfl
    · rw [hiso u hu, seedDriver_pos u hu]
  rw [Lh_eq_Lh_runMask c h t (-1) (by decide), hm]
  rfl

/-- **The isolated slice is the walled progression problem**: if the walled column has no infinite
progression of black cells, no eventually periodic black-time consistent boundary with isolated
black times keeps black times. -/
theorem isolated_slice_of_not_walledAP (hW : ¬ WalledAP) : NoPeriodicIsolatedBlackConsistent := by
  intro c h0 h hep hiso
  have hcol := Lh_isolated c h0 h hiso
  obtain ⟨T, P, hP, hper⟩ := hep
  refine Decidable.byCases (p := ∃ r, r < P ∧ c (T + 3 + r) = true) (fun hb => ?_) (fun hno => ?_)
  · exfalso
    obtain ⟨r, _, hr⟩ := hb
    have hall : ∀ k, c (T + 3 + r + k * P) = true := by
      intro k
      rw [Rule30Jen.periodic_mul hper k (T + 3 + r) (by cfomega)]
      exact hr
    have hP2 : 2 ≤ P := by
      rcases Nat.lt_or_ge P 2 with hlt | hge
      · have hP1 : P = 1 := by cfomega
        have e := hiso (T + 3 + r) (by cfomega)
        have e1 := hall 1
        rw [hP1, Nat.one_mul] at e1
        unfold runMask at e
        rw [hr, e1] at e
        exact absurd e (by decide)
      · exact hge
    refine hW ⟨T + 3 + r, P, by cfomega, hP2, fun k => ?_⟩
    have hb := hall k
    have e := h _ hb
    have hn : c (T + 3 + r + k * P + 1) = false := by
      have e2 := hiso (T + 3 + r + k * P) (by cfomega)
      unfold runMask at e2
      rw [hb, Bool.true_and] at e2
      exact e2
    rw [hn, hcol] at e
    revert e
    cases walled (T + 3 + r + k * P) <;> decide
  · refine ⟨T + 3, fun u hu => ?_⟩
    have hr : (u - (T + 3)) % P < P := Nat.mod_lt _ hP
    have he : T + 3 + (u - (T + 3)) % P + ((u - (T + 3)) / P) * P = u := by
      have hh := Nat.mod_add_div (u - (T + 3)) P
      rw [Nat.mul_comm P ((u - (T + 3)) / P)] at hh
      cfomega
    have hp := Rule30Jen.periodic_mul hper ((u - (T + 3)) / P) (T + 3 + (u - (T + 3)) % P) (by cfomega)
    rw [he] at hp
    rw [hp]
    cases hc : c (T + 3 + (u - (T + 3)) % P)
    · rfl
    · exact absurd ⟨(u - (T + 3)) % P, hr, hc⟩ hno

/-- **The isolated slice of the obligation is exactly `¬ WalledAP`.** -/
theorem noPeriodicIsolatedBlackConsistent_iff : NoPeriodicIsolatedBlackConsistent ↔ ¬ WalledAP :=
  ⟨not_walledAP_of_isolatedSlice, isolated_slice_of_not_walledAP⟩

/-! ## Normal forms of the progression problem -/

theorem walledProgression_shift (s P n : Nat) (h : WalledProgression s P) :
    WalledProgression (s + n * P) P := by
  intro k
  have e : (n + k) * P = n * P + k * P := Nat.add_mul n k P
  rw [show s + n * P + k * P = s + (n + k) * P by rw [e]; cfomega]
  exact h (n + k)

/-- No progression starts at time `0`: the walled column is white there. -/
theorem not_walledProgression_zero (P : Nat) : ¬ WalledProgression 0 P := by
  intro h
  have e := h 0
  rw [Nat.zero_mul, Nat.add_zero, walled_zero] at e
  exact Bool.false_ne_true e

/-- **Step `1` is Jen inside the half**: the walled column is not eventually black. -/
theorem not_walledProgression_step_one (s : Nat) : ¬ WalledProgression s 1 := by
  intro h
  apply driven_column_not_eventuallyPeriodic seedDriver rfl
    ⟨1, 1, by decide, fun t ht => by rw [seedDriver_pos (t + 1) (by cfomega), seedDriver_pos t ht]⟩
  refine ⟨s, 1, by decide, fun t ht => ?_⟩
  show walled (t + 1) = walled t
  have e1 := h (t + 1 - s)
  have e2 := h (t - s)
  rw [Nat.mul_one, show s + (t + 1 - s) = t + 1 by cfomega] at e1
  rw [Nat.mul_one, show s + (t - s) = t by cfomega] at e2
  rw [e1, e2]

/-- Some infinite arithmetic progression of black cells in the walled column. -/
def WalledBlackProgression : Prop := ∃ s P : Nat, 0 < P ∧ WalledProgression s P

/-- **The bounds in `WalledAP` are normal forms**: `WalledAP` is the existence of any infinite
arithmetic progression of black cells in the walled column. -/
theorem walledAP_iff : WalledAP ↔ WalledBlackProgression := by
  constructor
  · rintro ⟨s, P, _, hP, h⟩
    exact ⟨s, P, by cfomega, h⟩
  · rintro ⟨s, P, hP, h⟩
    rcases Nat.lt_or_ge P 2 with h2 | h2
    · obtain rfl : P = 1 := by cfomega
      exact absurd h (not_walledProgression_step_one s)
    · rcases Nat.lt_or_ge s 1 with h1 | h1
      · obtain rfl : s = 0 := by cfomega
        exact absurd h (not_walledProgression_zero P)
      · exact ⟨s + 2 * P, P, by cfomega, h2, walledProgression_shift s P 2 h⟩

/-! ## The walled column is the zero-boundary column from one cell -/

/-- The zero-boundary start with one black cell at depth `1`. -/
def seedRow : Nat → Bool
  | 0 => false
  | 1 => true
  | _ + 2 => false

theorem seedRow_fin (k : Nat) (hk : 1 < k) : seedRow k = false := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by cfomega⟩
  rfl

theorem seedRow_eq (k : Nat) : Lh seedDriver 1 (-(k : Int)) = seedRow k := by
  match k with
  | 0 =>
    rw [show (-((0 : Nat) : Int)) = 0 by decide, Lh_col0]
    rfl
  | 1 => exact start_black seedDriver rfl
  | j + 2 =>
    rw [start_white seedDriver _ (by cfomega)]
    rfl

theorem seedRow_fun : (fun k : Nat => Lh seedDriver 1 (-(k : Int))) = seedRow := funext seedRow_eq

/-- Every depth of the walled half from time `1` is the zero-boundary half from `seedRow`. -/
theorem Lh_seed_eq_zrow (t k : Nat) (hk : 1 ≤ k) :
    Lh seedDriver (t + 1) (-(k : Int)) = Rule30ZeroBoundary.zrow seedRow t k := by
  have e1 := L_shift seedDriver t (-(k : Int)) (by cfomega)
  have hd : (fun k => seedDriver (k + 1)) = fun _ => false := funext fun _ => rfl
  rw [hd] at e1
  have e2 := Rule30ZeroBoundary.L_eq_zrow (fun p => Lh seedDriver 1 p) t k hk
  rw [seedRow_fun] at e2
  rw [← e1, e2]

/-- **The walled column is the zero-boundary column from the single black cell at depth `1`.** -/
theorem walled_eq_zrow (t : Nat) : walled (t + 1) = Rule30ZeroBoundary.zrow seedRow t 1 := by
  have e := Lh_seed_eq_zrow t 1 (Nat.le_refl 1)
  rw [show (-((1 : Nat) : Int)) = -1 by decide] at e
  exact e

/-! ## The kit's period questions at the one-cell start -/

/-- The step-`P` zero-wall question: no finitely supported start of the zero-boundary left half
keeps column `-1` black at every `P`-th step from time `0`. `Q01` is `P = 2`. -/
def ZeroWallQ (P : Nat) : Prop :=
  ∀ L : Nat → Bool, Rule30ZeroBoundary.FinSupp L → ¬ ∀ k, Rule30ZeroBoundary.zrow L (k * P) 1 = true

/-- **`Q01` is the step-`2` zero-wall question.** -/
theorem q01_iff_zeroWallQ_two : Rule30ZeroBoundary.Q01 ↔ ZeroWallQ 2 := by
  refine Rule30ZeroBoundary.Q01_iff_any_phase.trans ⟨fun h L hfin hall => ?_, fun h L T hfin hall => ?_⟩
  · exact h L 0 hfin fun s => by rw [show 0 + 2 * s = s * 2 by cfomega]; exact hall s
  · obtain ⟨W, hW⟩ := hfin
    refine h (Rule30ZeroBoundary.zrow L T) ⟨W + T, fun k hk => Rule30ZeroBoundary.zrow_fin hW T k hk⟩
      fun k => ?_
    rw [← Rule30ZeroBoundary.zrow_shift, show T + k * 2 = T + 2 * k by cfomega]
    exact hall k

/-- The step-`P` zero-wall question decides every step-`P` walled progression. -/
theorem not_walledProgression_of_zeroWallQ (P s : Nat) (h : ZeroWallQ P) (hs : 1 ≤ s) :
    ¬ WalledProgression s P := by
  intro hw
  refine h (Rule30ZeroBoundary.zrow seedRow (s - 1))
    ⟨1 + (s - 1), fun k hk => Rule30ZeroBoundary.zrow_fin (W := 1) seedRow_fin (s - 1) k hk⟩ fun k => ?_
  rw [← Rule30ZeroBoundary.zrow_shift, ← walled_eq_zrow, show s - 1 + k * P + 1 = s + k * P by cfomega]
  exact hw k

/-- The zero-wall questions at every step `≥ 2`. -/
def ZeroWallFamily : Prop := ∀ P, 2 ≤ P → ZeroWallQ P

theorem not_walledAP_of_zeroWallFamily (h : ZeroWallFamily) : ¬ WalledAP := by
  rintro ⟨s, P, hs, hP, hw⟩
  exact not_walledProgression_of_zeroWallQ P s (h P hP) (by cfomega) hw

/-- A step-`2` walled progression. -/
def WalledAPTwo : Prop := ∃ s, 3 ≤ s ∧ WalledProgression s 2

/-- **The kit's open `Q01` decides the step-`2` walled progressions.** -/
theorem not_walledAPTwo_of_Q01 (hQ : Rule30ZeroBoundary.Q01) : ¬ WalledAPTwo := by
  rintro ⟨s, hs, hw⟩
  exact not_walledProgression_of_zeroWallQ 2 s (q01_iff_zeroWallQ_two.1 hQ) (by cfomega) hw

/-- **The obligation implies `Q01` at the one-cell start, in every phase.** -/
theorem not_walledAPTwo_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) :
    ¬ WalledAPTwo := by
  rintro ⟨s, hs, hw⟩
  exact not_walledAP_of_noPeriodicBlackConsistent h ⟨s, 2, hs, Nat.le_refl 2, hw⟩

/-! ## Eventually isolated boundaries: the zero-wall family decides them -/

/-- Every row of a driven half, read leftward from column `-1`, is finitely supported (the light
cone). -/
theorem row_finSupp (c : Nat → Bool) (T : Nat) :
    Rule30ZeroBoundary.FinSupp (fun i => Lh c T (-(i : Int))) := by
  have hcone : ∀ (t : Nat) (p : Int), p < -(t : Int) → Lh c t p = false := by
    intro t
    induction t with
    | zero => intro p hp; exact Lh_zero_neg c p (by cfomega)
    | succ t ih =>
      intro p hp
      rw [Lh_succ_neg c t p (by cfomega), ih (p - 1) (by cfomega), ih p (by cfomega), ih (p + 1) (by cfomega)]
      rfl
  exact ⟨T, fun i hi => hcone T (-(i : Int)) (by cfomega)⟩

/-- **Restart against a wall.** From a time `T` after which the boundary stays white, the driven
half is the zero-boundary half from its row at `T`. -/
theorem Lh_restart_zrow (m : Nat → Bool) (T : Nat) (hm : ∀ t, T ≤ t → m t = false) :
    ∀ (j k : Nat), 1 ≤ k →
      Lh m (T + j) (-(k : Int)) = Rule30ZeroBoundary.zrow (fun i => Lh m T (-(i : Int))) j k := by
  intro j
  induction j with
  | zero =>
    intro k hk
    rw [Nat.add_zero, Rule30ZeroBoundary.zrow_zero_of_pos _ hk]
  | succ j ih =>
    intro k hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by cfomega⟩
    rw [show T + (j + 1) = (T + j) + 1 by cfomega,
      Lh_succ_neg m (T + j) (-((i + 1 : Nat) : Int)) (by cfomega), Rule30ZeroBoundary.zrow_succ,
      show (-((i + 1 : Nat) : Int)) - 1 = -((i + 2 : Nat) : Int) by cfomega,
      ih (i + 2) (by cfomega), ih (i + 1) (by cfomega)]
    rcases Nat.lt_or_ge i 1 with hi | hi
    · obtain rfl : i = 0 := by cfomega
      rw [show (-((0 + 1 : Nat) : Int)) + 1 = 0 by decide, Lh_col0, hm (T + j) (by cfomega),
        Rule30ZeroBoundary.zrow_wall]
      rfl
    · rw [show (-((i + 1 : Nat) : Int)) + 1 = -(i : Int) by cfomega, ih i hi]
      rfl

/-- From some time on, no two adjacent black times. -/
def EventuallyIsolated (c : Nat → Bool) : Prop := ∃ T, ∀ t, T ≤ t → runMask c t = false

/-- The obligation on boundaries whose periodic part has no two adjacent black times. -/
def NoPeriodicEventuallyIsolatedBlackConsistent : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c → Rule30Jen.EventuallyPeriodic c →
    EventuallyIsolated c → EventuallyWhite c

/-- The obligation contains its eventually isolated slice. -/
theorem noPeriodicEventuallyIsolated_of_noPeriodicBlackConsistent (h : NoPeriodicBlackConsistent) :
    NoPeriodicEventuallyIsolatedBlackConsistent :=
  fun c h0 hb hep _ => h c h0 hb hep

/-- The eventually isolated slice contains the isolated slice. -/
theorem noPeriodicIsolated_of_eventuallyIsolated (h : NoPeriodicEventuallyIsolatedBlackConsistent) :
    NoPeriodicIsolatedBlackConsistent :=
  fun c h0 hb hep hiso => h c h0 hb hep ⟨1, hiso⟩

/-- **The zero-wall family decides every eventually isolated boundary.** After the last run
interior the left half is the zero-boundary half from a finite row (`Lh_eq_Lh_runMask`,
`Lh_restart_zrow`), and a black residue of the period is a step-`P` progression of black cells in
its column `-1`. -/
theorem noPeriodicEventuallyIsolated_of_zeroWallFamily (h : ZeroWallFamily) :
    NoPeriodicEventuallyIsolatedBlackConsistent := by
  intro c _ hb hep hiso
  obtain ⟨T1, hT1⟩ := hiso
  obtain ⟨T, P, hP, hper⟩ := hep
  refine Decidable.byCases (p := ∃ r, r < P ∧ c (T + T1 + r) = true) (fun hbl => ?_) (fun hno => ?_)
  · exfalso
    obtain ⟨r, _, hr⟩ := hbl
    have hall : ∀ k, c (T + T1 + r + k * P) = true := fun k => by
      rw [Rule30Jen.periodic_mul hper k (T + T1 + r) (by cfomega)]
      exact hr
    have hnext : ∀ k, c (T + T1 + r + k * P + 1) = false := fun k => by
      have e := hT1 (T + T1 + r + k * P) (by cfomega)
      unfold runMask at e
      rw [hall k, Bool.true_and] at e
      exact e
    have hP2 : 2 ≤ P := by
      rcases Nat.lt_or_ge P 2 with hlt | hge
      · have e := hnext 0
        have e1 := hall 1
        have hP1 : P = 1 := by cfomega
        rw [hP1, Nat.one_mul] at e1
        rw [Nat.zero_mul, Nat.add_zero, e1] at e
        exact absurd e (by decide)
      · exact hge
    have hcol : ∀ k, Lh (runMask c) (T + T1 + r + k * P) (-1) = true := fun k => by
      have e := hb _ (hall k)
      rw [hnext k, Lh_eq_Lh_runMask c hb _ (-1) (by decide)] at e
      revert e
      cases Lh (runMask c) (T + T1 + r + k * P) (-1) <;> decide
    have hm : ∀ t, T + T1 + r ≤ t → runMask c t = false := fun t ht => hT1 t (by cfomega)
    refine h P hP2 (fun i => Lh (runMask c) (T + T1 + r) (-(i : Int))) (row_finSupp _ _) fun k => ?_
    have e := Lh_restart_zrow (runMask c) (T + T1 + r) hm (k * P) 1 (Nat.le_refl 1)
    rw [show (-((1 : Nat) : Int)) = -1 by decide] at e
    rw [← e]
    exact hcol k
  · refine ⟨T + T1, fun v hv => ?_⟩
    have hr : (v - (T + T1)) % P < P := Nat.mod_lt _ hP
    have he : T + T1 + (v - (T + T1)) % P + ((v - (T + T1)) / P) * P = v := by
      have hh := Nat.mod_add_div (v - (T + T1)) P
      rw [Nat.mul_comm P ((v - (T + T1)) / P)] at hh
      cfomega
    have hp := Rule30Jen.periodic_mul hper ((v - (T + T1)) / P) (T + T1 + (v - (T + T1)) % P) (by cfomega)
    rw [he] at hp
    rw [hp]
    cases hc : c (T + T1 + (v - (T + T1)) % P)
    · rfl
    · exact absurd ⟨(v - (T + T1)) % P, hr, hc⟩ hno

/-- The walled column is not eventually periodic (Jen inside the half). -/
theorem walled_not_eventuallyPeriodic : ¬ Rule30Jen.EventuallyPeriodic walled :=
  driven_column_not_eventuallyPeriodic seedDriver rfl
    ⟨1, 1, by decide, fun t ht => by rw [seedDriver_pos (t + 1) (by cfomega), seedDriver_pos t ht]⟩

/-! ## The center is outside the isolated slice -/

theorem center_runMask_three : runMask Rule30Prize.center 3 = true := by decide

/-- The center is black-time consistent (`center_blackTimeConsistent`) but has adjacent black
times, so the isolated slice says nothing about it. -/
theorem not_isolatedBlack_center : ¬ IsolatedBlack Rule30Prize.center := by
  intro h
  have e := h 3 (by decide)
  rw [center_runMask_three] at e
  exact Bool.noConfusion e

/-! ## First-order forms -/

/-- Under black-time consistency the left half is driven by the run mask. -/
def EffectiveDriver : Prop :=
  ∀ c : Nat → Bool, BlackTimeConsistent c →
    ∀ (t : Nat) (p : Int), p < 0 → Lh c t p = Lh (runMask c) t p

theorem effectiveDriver : EffectiveDriver := Lh_eq_Lh_runMask

/-- Under black-time consistency column `-1` is rule 60 with the run mask as source. -/
def ColumnLinear : Prop :=
  ∀ c : Nat → Bool, BlackTimeConsistent c →
    ∀ t, Lh c (t + 1) (-1) = bxor (bxor (Lh c t (-2)) (Lh c t (-1))) (runMask c t)

theorem columnLinear : ColumnLinear := btc_col_linear

/-- On the isolated slice column `-1` is the walled column. -/
def IsolatedWalled : Prop :=
  ∀ c : Nat → Bool, c 0 = true → BlackTimeConsistent c → IsolatedBlack c →
    ∀ t, Lh c t (-1) = walled t

theorem isolatedWalled : IsolatedWalled := Lh_isolated

end Rule30UOR.Walled
