module

public import Rule30UOR.DefectFront
public import Rule30UOR.Scale
public import Rule30UOR.MaskedObservation

/-!
# Central localization of collision sources

Statements are authored in `rule30-paper/src/Observations.lex.tex`.
An adjacent defect and a common future black center force incompatible paired colors
within a bounded distance. Finite XOR rigidity then forces a nearby carry collision.
Under a hypothetical period `P`, common black centers occur within `P` steps, so collision
sources recur in the fixed left band `[-P, -2]`. This strengthens the earlier
central-band localization. It remains a necessary condition, not Problem 1.
-/

@[expose] public section

namespace Rule30UOR.CentralCollision

open Ruliology.CellularAutomata Rule30Jen Rule30Prize
open Rule30UOR.TemporalDefect Rule30UOR.Collision Rule30UOR.DefectFront
open Rule30XorRigidity.HalfLine (Good good_symm)

def leftAdjacentDefect (Q t : Nat) : Bool := defect Q t (-1)

def CentralCollision (Q t B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ (B : Int) ∧ collision Q t x = true

def NearCollision (Q t H B : Nat) : Prop :=
  ∃ s : Nat, s ≤ H ∧ CentralCollision Q (t + s) B

/-- One fixed central column, distinct from the collision-free column `-1`, carries
nonzero collisions arbitrarily late. -/
def RecurrentCentralCollision (Q B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ (B : Int) ∧ x ≠ -1 ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collision Q t x = true

/-- A collision source in a fixed left strip, excluding the source-free column `-1`. -/
def LeftCollision (Q t B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ -2 ∧ collision Q t x = true

/-- A single fixed column of the left strip carries collisions arbitrarily late. -/
def RecurrentLeftCollision (Q B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ -2 ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collision Q t x = true

/-- Frontier obstruction at fixed period: under a hypothetical periodic center of period `P`,
the period-scale recurrent central collision witness must fail. -/
def NoRecurrentCentralCollision : Prop :=
  ∀ T P : Nat, 0 < P → Rule30UOR.Scale.CenterPeriodic T P →
    ¬ RecurrentCentralCollision P (2 * P)

private theorem white_cone (t : Nat) : ∀ (r : Nat) (p : Int),
    (∀ q : Int, p - (r : Int) ≤ q → q ≤ p + (r : Int) → cell t q = false) →
    cell (t + r) p = false := by
  intro r
  induction r with
  | zero => intro p h; simpa using h p (by omega) (by omega)
  | succ r ih =>
    intro p h
    rw [show t + (r + 1) = (t + r) + 1 by omega]
    change rule (cell (t + r) (p - 1)) (cell (t + r) p) (cell (t + r) (p + 1)) = false
    rw [ih (p - 1) (fun q hq1 hq2 => h q (by omega) (by omega)),
      ih p (fun q hq1 hq2 => h q (by omega) (by omega)),
      ih (p + 1) (fun q hq1 hq2 => h q (by omega) (by omega))]
    rfl

private theorem black_ancestor (t r : Nat) (h : center (t + r) = true) :
    ∃ q : Int, -(r : Int) ≤ q ∧ q ≤ (r : Int) ∧ cell t q = true := by
  apply Classical.byContradiction
  intro hn
  have hw := white_cone t r 0 (by
    intro q hq1 hq2
    cases hq : cell t q
    · rfl
    · exact (hn ⟨q, by omega, by omega, hq⟩).elim)
  change cell (t + r) 0 = true at h
  rw [hw] at h
  contradiction

/-- Generic finite-horizon localization, before imposing any periodicity hypothesis. -/
theorem unit_defect_forces_near_collision_kit (Q t r : Nat)
    (hd : leftAdjacentDefect Q t = true)
    (ha : center (t + r) = true) (hb : center ((t + r) + Q) = true) :
    NearCollision Q t (r + 1) (2 * (r + 1)) := by
  have incompatible : ∃ q : Int, -(r : Int) ≤ q ∧ q ≤ (r : Int) ∧
      ¬ Good (cell t (-1)) (cell (t + Q) (-1)) (cell t q) (cell (t + Q) q) := by
    cases h1 : cell t (-1) <;> cases h2 : cell (t + Q) (-1)
    · simp [leftAdjacentDefect, defect, difference, h1, h2] at hd
    · obtain ⟨q, hq1, hq2, hq⟩ := black_ancestor t r ha
      exact ⟨q, hq1, hq2, by simp [Good, hq]⟩
    · have hb' : center ((t + Q) + r) = true := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
      obtain ⟨q, hq1, hq2, hq⟩ := black_ancestor (t + Q) r hb'
      exact ⟨q, hq1, hq2, by simp [Good, hq]⟩
    · simp [leftAdjacentDefect, defect, difference, h1, h2] at hd
  obtain ⟨q, hq1, hq2, hbad⟩ := incompatible
  by_cases hq : -1 ≤ q
  · let d := (q + 1).toNat
    have hcast : (d : Int) = q + 1 := Int.toNat_of_nonneg (by omega)
    have hh := temporal_collision_of_incompatible Q t (-1) d (by
      simpa only [show (-1 : Int) + (d : Int) = q by omega] using hbad)
    obtain ⟨s, hs, x, hx1, hx2, hcol⟩ := hh
    exact ⟨s, by omega, x, by omega, by omega, hcol⟩
  · let d := (-1 - q).toNat
    have hcast : (d : Int) = -1 - q := Int.toNat_of_nonneg (by omega)
    have hh := temporal_collision_of_incompatible Q t q d (by
      rw [show q + (d : Int) = -1 by omega]
      intro he
      exact hbad (good_symm _ _ _ _ he))
    obtain ⟨s, hs, x, hx1, hx2, hcol⟩ := hh
    exact ⟨s, by omega, x, by omega, by omega, hcol⟩

theorem unit_defect_forces_near_collision (Q t r : Nat)
    (hd : leftAdjacentDefect Q t = true)
    (ha : Rule30UOR.Core.center (t + r) = true)
    (hb : Rule30UOR.Core.center ((t + r) + Q) = true) :
    NearCollision Q t (r + 1) (2 * (r + 1)) :=
  unit_defect_forces_near_collision_kit Q t r hd
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using ha)
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using hb)

private theorem black_within_period {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (t : Nat) (ht : T ≤ t) :
    ∃ r : Nat, r < P ∧ center (t + r) = true := by
  have hex : ∃ u : Nat, t ≤ u ∧ center u = true := by
    apply Classical.byContradiction
    intro hn
    apply center_not_eventually_constant
    refine ⟨t, false, fun u hu => ?_⟩
    cases hb : center u
    · rfl
    · exact (hn ⟨u, hu, hb⟩).elim
  obtain ⟨u, hu, hb⟩ := hex
  let r := (u - t) % P
  have hr : r < P := Nat.mod_lt _ hP
  have he : (t + r) + ((u - t) / P) * P = u := by
    have hh := Nat.mod_add_div (u - t) P
    rw [Nat.mul_comm P ((u - t) / P)] at hh
    dsimp [r]
    omega
  have hp := periodic_mul hc ((u - t) / P) (t + r) (by omega)
  rw [he] at hp
  exact ⟨r, hr, hp.symm.trans hb⟩

private theorem kit_period {T P : Nat} (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∀ t, T ≤ t → center (t + P) = center t := by
  intro t ht
  simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht

/-- A white-phase unit defect must already have been present in a bounded left
prefix at a preceding black phase. Matching prefixes would determine its whole trace. -/
private theorem black_left_defect_before {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (m v : Nat)
    (hv : T + P ≤ v) (hd : leftAdjacentDefect (m * P) v = true) :
    ∃ b k : Nat, v + 1 - P ≤ b ∧ b ≤ v ∧ 1 ≤ k ∧ k ≤ P ∧
      center b = true ∧ defect (m * P) b (-(k : Int)) = true := by
  let a := v + 1 - P
  have ha : T ≤ a := by dsimp [a]; omega
  obtain ⟨r, hr, hblack⟩ := black_within_period hP hc a ha
  let b := a + r
  have hb1 : v + 1 - P ≤ b := by dsimp [b, a]; omega
  have hb2 : b ≤ v := by dsimp [b, a]; omega
  have hbT : T ≤ b := by dsimp [b]; omega
  have hgap : v - b < P := by omega
  have hwhite : center v = false := by
    have hp := defect_right_and_white_of_clean_pair (m * P) v 0
      (center_defect_zero hc m v (by omega))
      (center_defect_zero hc m (v + 1) (by omega)) hd
    exact hp.2
  by_cases hex : ∃ k : Nat, 1 ≤ k ∧ k ≤ P ∧ defect (m * P) b (-(k : Int)) = true
  · obtain ⟨k, hk1, hkP, hk⟩ := hex
    exact ⟨b, k, hb1, hb2, hk1, hkP, hblack, hk⟩
  · have pref : Rule30UOR.MaskedObservation.LeftPrefixAgree b (b + m * P) P := by
      intro k hk1 hkP
      have hz : defect (m * P) b (-(k : Int)) = false := by
        cases hh : defect (m * P) b (-(k : Int))
        · rfl
        · exact (hex ⟨k, hk1, hkP, hh⟩).elim
      exact ((difference_eq_false_iff (fun t => cell t (-(k : Int))) (m * P) b).1 hz).symm
    have win : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + m * P) P := by
      intro j hj
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (periodic_mul hc m (b + j) (by omega)).symm
    have he := (Rule30UOR.MaskedObservation.prefix_agreement_iff_white_trace
      b (b + m * P) P win).1 pref (v - b) hgap (by
        simpa only [show b + (v - b) = v by omega] using hwhite)
    have he' : cell v (-1) = cell (v + m * P) (-1) := by
      simpa only [Rule30UOR.MaskedObservation.leftDigit,
        show -((1 : Nat) : Int) = (-1 : Int) by omega,
        show b + (v - b) = v by omega,
        show b + m * P + (v - b) = v + m * P by omega] using he
    have hz : leftAdjacentDefect (m * P) v = false := by
      simp [leftAdjacentDefect, defect, difference, he']
    rw [hz] at hd
    contradiction

/-- Black-phase prefix observation and mixed-colour collision transport put the
source entirely on the left. The bound comes from the actual moving left edge. -/
theorem periodic_left_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 3 * P ∧
      LeftCollision (m * P) t P := by
  have hp := kit_period hc
  obtain ⟨r, hr0, hr, hd, _, _⟩ := exists_unit_defect_and_white_center_of_periodic
    hP hp m (N + P) hm (by omega)
  obtain ⟨b, k, hb1, hb2, hk1, hkP, hblack, hdef⟩ :=
    black_left_defect_before hP hp m (N + P + (r - 1)) (by omega) hd
  have hbT : T ≤ b := by omega
  obtain ⟨s, hs, x, hx1, hx2, hcol⟩ := left_collision_of_defect_and_black (m * P) b k hdef
    hblack ((periodic_mul hp m b hbT).trans hblack)
  have hne : x ≠ -1 := by
    intro he
    rw [he] at hcol
    have hz := Rule30UOR.DefectSource.collision_neg_one_of_agree (m * P) (b + s)
      (center_defect_zero hp m (b + s) (by omega))
      (center_defect_zero hp m (b + s + 1) (by omega))
    rw [hz] at hcol
    contradiction
  exact ⟨b + s, by omega, by omega, x, by omega, by omega, hcol⟩

theorem periodic_left_collisions (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∃ t : Nat, N ≤ t ∧ LeftCollision (m * P) t P := by
  obtain ⟨t, ht, _, hcol⟩ := periodic_left_collision_window T P m (max T N) hP hm hc (by omega)
  exact ⟨t, by omega, hcol⟩

/-- The localization radius depends only on the proposed period, not the transient,
time, or period multiplier. -/
theorem periodic_unit_defect_forces_near_collision (T P m t : Nat) (hP : 0 < P)
    (_hm : 0 < m) (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t)
    (hd : leftAdjacentDefect (m * P) t = true) : NearCollision (m * P) t P (2 * P) := by
  have hp := kit_period hc
  obtain ⟨r, hr, hb⟩ := black_within_period hP hp t ht
  have hb' : center ((t + r) + m * P) = true := (periodic_mul hp m (t + r) (by omega)).trans hb
  obtain ⟨s, hs, x, hx1, hx2, hcol⟩ :=
    unit_defect_forces_near_collision_kit (m * P) t r hd hb hb'
  exact ⟨s, by omega, x, by omega, by omega, hcol⟩

/-- The moving left edge gives a quantitative recurrence window. A left defect at
distance `N + m*P` reaches a unit pair within that many steps; localization then
takes at most `P` more steps. No recurrence rate is inferred from measured data. -/
theorem periodic_central_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + P ∧
      CentralCollision (m * P) t (2 * P) := by
  obtain ⟨r, hr0, hr, hd, _, _⟩ :=
    exists_unit_defect_and_white_center_of_periodic hP (kit_period hc) m N hm hN
  obtain ⟨s, hs, hcol⟩ := periodic_unit_defect_forces_near_collision
    T P m (N + (r - 1)) hP hm hc (by omega) hd
  exact ⟨N + (r - 1) + s, by omega, by omega, hcol⟩

/-- A hypothetical periodic center forces collision sources arbitrarily late in a
fixed central strip. They cannot all escape with the moving cone edges. -/
theorem periodic_central_collisions (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∃ t : Nat, N ≤ t ∧ CentralCollision (m * P) t (2 * P) := by
  obtain ⟨t, ht, _, hcol⟩ := periodic_central_collision_window
    T P m (max T N) hP hm hc (by omega)
  exact ⟨t, by omega, hcol⟩

private theorem finite_recurrent_choice (f : Nat → Nat → Prop) (n : Nat) :
    (∀ N : Nat, ∃ t : Nat, N ≤ t ∧ ∃ i : Nat, i < n ∧ f i t) →
    ∃ i : Nat, i < n ∧ ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ f i t := by
  induction n with
  | zero =>
    intro h
    obtain ⟨t, ht, i, hi, hf⟩ := h 0
    omega
  | succ n ih =>
    intro h
    by_cases hn : ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ f n t
    · exact ⟨n, by omega, hn⟩
    · obtain ⟨N0, hN0⟩ := Classical.not_forall.mp hn
      obtain ⟨i, hi, hf⟩ := ih (by
        intro N
        obtain ⟨t, ht, j, hj, hf⟩ := h (max N N0)
        have hne : j ≠ n := by
          intro he
          subst j
          exact hN0 ⟨t, by omega, hf⟩
        exact ⟨t, by omega, j, by omega, hf⟩)
      exact ⟨i, by omega, hf⟩

/-- A periodic center forces recurrence at a fixed strictly left column. Neither
right-side sources nor sources escaping with the cone edges suffice. -/
theorem periodic_recurrent_left_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentLeftCollision (m * P) P := by
  obtain ⟨i, hi, hf⟩ := finite_recurrent_choice
    (fun i t => collision (m * P) t (-(P : Int) + (i : Int)) = true) (P - 1) (by
      intro N
      obtain ⟨t, ht, x, hx1, hx2, hcol⟩ := periodic_left_collisions T P m N hP hm hc
      refine ⟨t, ht, (x + (P : Int)).toNat, by omega, ?_⟩
      simpa only [Int.toNat_of_nonneg (show 0 ≤ x + (P : Int) by omega),
        show -(P : Int) + (x + (P : Int)) = x by omega] using hcol)
  exact ⟨-(P : Int) + (i : Int), by omega, by omega, hf⟩

/-- Finite choice localizes recurrence to one fixed source column. The central strip
is not a closed dynamical system: this theorem does not make its source signal periodic. -/
theorem periodic_recurrent_central_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentCentralCollision (m * P) (2 * P) := by
  obtain ⟨x, hx1, hx2, hf⟩ := periodic_recurrent_left_column T P m hP hm hc
  exact ⟨x, by omega, by omega, by omega, hf⟩

/-- Frontier reduction: any eventual periodic center hypothesis yields a fixed-band
recurrent central collision witness. This packages the `T, P` witness extraction and
the periodic recurrence theorem into one contradiction-ready consequence. -/
theorem recurrent_central_collision_of_eventual_periodic
  (m : Nat) (hm : 0 < m) (hc : EventuallyPeriodic Rule30Prize.center) :
    ∃ T P : Nat, 0 < P ∧ Rule30UOR.Scale.CenterPeriodic T P ∧
      RecurrentCentralCollision (m * P) (2 * P) := by
  obtain ⟨T, P, hP, hper⟩ := hc
  refine ⟨T, P, hP, ?_, periodic_recurrent_central_column T P m hP hm ?_⟩
  · intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hper t ht
  · intro t ht
    simpa only [Rule30UOR.Scale.center_eq_kit] using hper t ht

/-- Canonical interface form of the same frontier reduction: excluding periodic-center
recurrent central collisions is exactly a `NoPeriod` witness. -/
theorem noPeriod_of_no_recurrent_central_collision
    (hno : ∀ T P : Nat, 0 < P →
      Rule30UOR.Scale.CenterPeriodic T P →
      ¬ RecurrentCentralCollision P (2 * P)) :
    Rule30UOR.Scale.NoPeriod := by
  intro T P hP hcP
  have hrec : RecurrentCentralCollision P (2 * P) := by
    simpa [Nat.one_mul] using
      periodic_recurrent_central_column T P 1 hP (by decide) hcP
  exact hno T P hP hcP hrec

/-- Canonical `NoPeriod` implies the recurrent-central-collision criterion vacuously,
since its periodic-center premise is impossible. -/
theorem no_recurrent_central_collision_of_noPeriod
    (h : Rule30UOR.Scale.NoPeriod) : NoRecurrentCentralCollision := by
  intro T P hP hcP
  exact (h T P hP hcP).elim

/-- Exact canonical form at this layer: excluding periodic-center recurrent central
collisions is equivalent to `NoPeriod`. -/
theorem no_recurrent_central_collision_iff_noPeriod :
    NoRecurrentCentralCollision ↔ Rule30UOR.Scale.NoPeriod := by
  constructor
  · exact noPeriod_of_no_recurrent_central_collision
  · exact no_recurrent_central_collision_of_noPeriod

/-- Problem 1 follows once one rules out fixed-band recurrent central collisions under
every hypothetical periodic-center witness. -/
theorem problem1_of_no_recurrent_central_collision
    (hno : ∀ T P : Nat, 0 < P →
      Rule30UOR.Scale.CenterPeriodic T P →
      ¬ RecurrentCentralCollision P (2 * P)) :
    Rule30Prize.Problem1 := by
  exact Rule30UOR.Scale.problem1_of_noPeriod
    (noPeriod_of_no_recurrent_central_collision hno)

/-- Problem 1 implies the recurrent-central-collision obstruction criterion. -/
theorem no_recurrent_central_collision_of_problem1
    (h : Rule30Prize.Problem1) : NoRecurrentCentralCollision := by
  exact no_recurrent_central_collision_of_noPeriod
    (Rule30UOR.Scale.noPeriod_of_problem1 h)

/-- Exact frontier at this layer: Problem 1 is equivalent to excluding recurrent central
collision witnesses under every periodic-center hypothesis. -/
theorem problem1_iff_no_recurrent_central_collision :
    Rule30Prize.Problem1 ↔ NoRecurrentCentralCollision := by
  rw [Rule30UOR.Scale.problem1_iff]
  exact (no_recurrent_central_collision_iff_noPeriod).symm

end Rule30UOR.CentralCollision
