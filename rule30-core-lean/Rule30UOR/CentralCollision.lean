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
open Rule30UOR.TemporalDefect Rule30UOR.Collision Rule30UOR.DefectFront Rule30UOR.DefectSource
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

/-- A cone witness retaining the collision's unit/black endpoint orientation. -/
def AdvancingLeftCone (Q t k : Nat) : Prop :=
  ∃ s : Nat, 2 * s ≤ k ∧ ∃ x : Int, -(k : Int) + (s : Int) ≤ x ∧
    x ≤ -(s : Int) ∧ x < 0 ∧ AdvancingCollision Q (t + s) x

def AdvancingLeftCollision (Q t B : Nat) : Prop :=
  ∃ x : Int, -(B : Int) ≤ x ∧ x ≤ -2 ∧ AdvancingCollision Q t x

/-- Both the column and one of the advancing orientations recur infinitely often. -/
def RecurrentAdvancingLeftCollision (Q B : Nat) : Prop :=
  ∃ k c : Nat, 2 ≤ k ∧ k ≤ B ∧ (c = 3 ∨ c = 5) ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collisionCode Q t k = c

/-- The sharper mixed-colour witness is a cone with an advancing right endpoint. -/
theorem left_defect_black_cone (Q t k : Nat)
    (hd : leftDefect Q t k = true)
    (ha : Rule30UOR.Core.center t = true) (hb : Rule30UOR.Core.center (t + Q) = true) :
    AdvancingLeftCone Q t k := by
  exact left_advancing_collision_of_defect_and_black Q t k
    (by simpa only [leftDefect] using hd)
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using ha)
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using hb)

/-- The characteristic starting one step after an advancing source is true up to
its first erasure. The target depth decreases by one at each step. -/
def FirstPathErasure (Q t k j : Nat) : Prop :=
  j + 1 < k ∧
    (∀ i : Nat, i ≤ j → leftDefect Q (t + 1 + i) (k - (i + 1)) = true) ∧
    ErasureEvent Q (t + 1 + j) (k - (j + 2))

/-- A fixed source orientation, first-erasure offset, gate pattern and reset colour
recur together. This is a finite observation pattern, not a closed strip dynamics. -/
def RecurrentSourceErasure (Q B : Nat) : Prop :=
  ∃ k c j g z : Nat, 2 ≤ k ∧ k ≤ B ∧ (c = 3 ∨ c = 5) ∧ j + 1 < k ∧
    1 ≤ g ∧ g ≤ 6 ∧ (z = 0 ∨ z = 3) ∧
    ∀ N : Nat, ∃ t : Nat, N ≤ t ∧ collisionCode Q t k = c ∧
      FirstPathErasure Q t k j ∧ gateCode Q (t + 1 + j) (k - (j + 2)) = g ∧
      leftColour Q (t + 2 + j) (k - (j + 2)) = z

private theorem first_drop : ∀ n : Nat, ∀ f : Nat → Bool, f 0 = true → f n = false →
    ∃ j : Nat, j < n ∧ (∀ i : Nat, i ≤ j → f i = true) ∧ f (j + 1) = false := by
  intro n
  induction n with
  | zero =>
    intro f h0 hn
    rw [h0] at hn
    contradiction
  | succ n ih =>
    intro f h0 hn
    cases h1 : f 1
    · refine ⟨0, by omega, ?_, h1⟩
      intro i hi
      have he : i = 0 := by omega
      simpa only [he] using h0
    · obtain ⟨j, hj, hp, he⟩ := ih (fun i => f (i + 1)) h1
        (by simpa only [Nat.add_comm n 1] using hn)
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · simpa only [hi0] using h0
        · have hh := hp (i - 1) (by omega)
          simpa only [show i - 1 + 1 = i by omega] using hh
      · exact he

/-- Every forced advance whose characteristic ends at a clean center has a first
later erasure. All time, depth, prefix and colour data are retained. -/
theorem advancing_source_first_erasure (Q t k : Nat) (hk : 2 ≤ k)
    (ha : advancingAtDepth Q t k) (hc : leftDefect Q (t + k) 0 = false) :
    ∃ j : Nat, FirstPathErasure Q t k j := by
  have hstart : leftDefect Q (t + 1) (k - 1) = true := by
    simpa only [leftDefect, show -((k - 1 : Nat) : Int) = -(k : Int) + 1 by omega] using
      advancing_collision_step Q t (-(k : Int)) (by simpa only [advancingAtDepth] using ha)
  have hend : leftDefect Q (t + 1 + (k - 1)) (k - ((k - 1) + 1)) = false := by
    simpa only [show t + 1 + (k - 1) = t + k by omega,
      show k - ((k - 1) + 1) = 0 by omega] using hc
  obtain ⟨j, hj, hp, he⟩ := first_drop (k - 1)
    (fun i => leftDefect Q (t + 1 + i) (k - (i + 1))) (by simpa using hstart) hend
  have hin : leftDefect Q (t + 1 + j) ((k - (j + 2)) + 1) = true := by
    simpa only [show k - (j + 1) = k - (j + 2) + 1 by omega] using hp j (Nat.le_refl j)
  have hout : leftDefect Q (t + 1 + j + 1) (k - (j + 2)) = false := by
    simpa only [Nat.add_assoc, show j + 1 + 1 = j + 2 by omega] using he
  exact ⟨j, by omega, hp, erasure_event_of_step Q (t + 1 + j) (k - (j + 2)) hin hout⟩

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

/-- A matching finite center window transports an agreeing left prefix forward.
Consequently a unit defect at the end has a witness in the initial prefix. -/
private theorem left_defect_of_agreeing_window (Q b r : Nat)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ r + 1 ∧ defect Q b (-(k : Int)) = true := by
  apply Classical.byContradiction
  intro hn
  have pref : Rule30UOR.MaskedObservation.LeftPrefixAgree b (b + Q) (r + 1) := by
    intro k hk1 hkr
    have hz : defect Q b (-(k : Int)) = false := by
      cases hh : defect Q b (-(k : Int))
      · rfl
      · exact (hn ⟨k, hk1, hkr, hh⟩).elim
    exact ((difference_eq_false_iff (fun t => cell t (-(k : Int))) Q b).1 hz).symm
  have he := Rule30UOR.MaskedObservation.trace_of_prefix hc pref r (by omega)
  have he' : cell (b + r) (-1) = cell (b + r + Q) (-1) := by
    simpa only [show b + Q + r = b + r + Q by omega] using he
  have hz : leftAdjacentDefect Q (b + r) = false := by
    simp [leftAdjacentDefect, defect, difference, he']
  rw [hz] at hd
  contradiction

/-- Finite causal localization: a unit defect after a shared black center forces
a left-side collision no later than the unit defect, within the first half of the
observation window.
No eventual-periodicity assumption is needed. -/
theorem black_window_forces_advancing_collision (Q b r : Nat) (hr : 0 < r)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hb : Rule30UOR.Core.center b = true)
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ s : Nat, 2 * s ≤ r + 1 ∧ s ≤ r ∧ AdvancingLeftCollision Q (b + s) (r + 1) := by
  obtain ⟨k, hk1, hkr, hdef⟩ := left_defect_of_agreeing_window Q b r hc hd
  have hb' : center b = true := by
    simpa only [Rule30UOR.Scale.center_eq_kit] using hb
  have hbQ : center (b + Q) = true := by
    have he := hc 0 (by omega)
    simp only [Nat.add_zero] at he
    exact he.symm.trans hb'
  obtain ⟨s, hs, x, hx1, hx2, hx3, hadv⟩ := left_advancing_collision_of_defect_and_black Q b k hdef hb' hbQ
  have hcol := advancing_collision_has_source Q (b + s) x hadv
  have hsr : s ≤ r := by omega
  have clean : ∀ j : Nat, j ≤ r + 1 → defect Q (b + j) 0 = false := by
    intro j hj
    change difference (fun t => cell t 0) Q (b + j) = false
    apply (difference_eq_false_iff (fun t => cell t 0) Q (b + j)).2
    simpa only [center, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hc j hj).symm
  have hne : x ≠ -1 := by
    intro he
    rw [he] at hcol
    have hz := Rule30UOR.DefectSource.collision_neg_one_of_agree Q (b + s)
      (clean s (by omega)) (by
        simpa only [Nat.add_assoc] using clean (s + 1) (by omega))
    rw [hz] at hcol
    contradiction
  exact ⟨s, by omega, hsr, x, by omega, by omega, hadv⟩

/-- The original collision interface follows by forgetting the endpoint colours. -/
theorem black_window_forces_left_collision (Q b r : Nat) (hr : 0 < r)
    (hc : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + Q) (r + 1))
    (hb : Rule30UOR.Core.center b = true)
    (hd : leftAdjacentDefect Q (b + r) = true) :
    ∃ s : Nat, 2 * s ≤ r + 1 ∧ s ≤ r ∧ LeftCollision Q (b + s) (r + 1) := by
  obtain ⟨s, hs, hsr, x, hx1, hx2, hadv⟩ := black_window_forces_advancing_collision Q b r hr hc hb hd
  exact ⟨s, hs, hsr, x, hx1, hx2, advancing_collision_has_source Q (b + s) x hadv⟩

/-- The source occurs no later than the unit defect supplied by the moving edge. This
removes the extra future localization allowance from the earlier deadline. -/
theorem periodic_advancing_left_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 2 * P ∧
      AdvancingLeftCollision (m * P) t P := by
  have hp := kit_period hc
  obtain ⟨r, hr0, hr, hd, _, hw⟩ := exists_unit_defect_and_white_center_of_periodic
    hP hp m (N + P) hm (by omega)
  let v := N + P + (r - 1)
  let a := v + 1 - P
  have haT : T ≤ a := by dsimp [a, v]; omega
  have haN : N ≤ a := by dsimp [a, v]; omega
  obtain ⟨j, hj, hb⟩ := black_within_period hP hp a haT
  let b := a + j
  have hbT : T ≤ b := by dsimp [b]; omega
  have hbN : N ≤ b := by dsimp [b]; omega
  have hbv : b ≤ v := by dsimp [b, a]; omega
  have hgap : v - b < P := by dsimp [b, a]; omega
  have hgap0 : 0 < v - b := by
    apply Classical.byContradiction
    intro hn
    have he : v = b := by omega
    have hwhite : center v = false := hw
    have hblack : center b = true := hb
    rw [he, hblack] at hwhite
    contradiction
  have win : Rule30UOR.MaskedObservation.CenterWindowAgree b (b + m * P) (v - b + 1) := by
    intro k hk
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (periodic_mul hp m (b + k) (by omega)).symm
  obtain ⟨s, hs, hsr, x, hx1, hx2, hcol⟩ := black_window_forces_advancing_collision
    (m * P) b (v - b) hgap0 win
    (by simpa only [Rule30UOR.Scale.center_eq_kit] using hb) (by
      simpa only [show b + (v - b) = v by omega, leftAdjacentDefect, v] using hd)
  refine ⟨b + s, by omega, ?_, x, by omega, hx2, hcol⟩
  dsimp [v] at hsr
  omega

/-- Each seed-forced advancing source leads to an erasure within at most P-1
further updates. The erasure target may be the center or a deeper left column. -/
theorem periodic_erasure_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ u d : Nat, N ≤ u ∧ u + 1 ≤ 2 * N + m * P + 3 * P ∧ d + 2 ≤ P ∧
      ErasureEvent (m * P) u d := by
  have hp := kit_period hc
  obtain ⟨t, ht, hb, x, hx1, hx2, hadv⟩ := periodic_advancing_left_collision_window T P m N hP hm hc hN
  let k := (-x).toNat
  have hcast : (k : Int) = -x := Int.toNat_of_nonneg (by omega)
  have ha : advancingAtDepth (m * P) t k := by
    simpa only [advancingAtDepth, hcast, show -(-x) = x by omega] using hadv
  have hclean : leftDefect (m * P) (t + k) 0 = false := by
    simpa only [leftDefect, show -((0 : Nat) : Int) = (0 : Int) by omega] using
      center_defect_zero hp m (t + k) (by omega)
  obtain ⟨j, hj, hprefix, he⟩ := advancing_source_first_erasure (m * P) t k (by omega) ha hclean
  exact ⟨t + 1 + j, k - (j + 2), by omega, by omega, by omega, he⟩

/-- Forgetting the advancing orientation preserves the existing quantitative API. -/
theorem periodic_left_collision_window (T P m N : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (hN : T ≤ N) :
    ∃ t : Nat, N ≤ t ∧ t + 1 ≤ 2 * N + m * P + 2 * P ∧
      LeftCollision (m * P) t P := by
  obtain ⟨t, ht, hb, x, hx1, hx2, hadv⟩ :=
    periodic_advancing_left_collision_window T P m N hP hm hc hN
  exact ⟨t, ht, hb, x, hx1, hx2, advancing_collision_has_source (m * P) t x hadv⟩

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

/-- Finitely many depths and two orientations give a fixed recurring advancing
case. The proof retains the seed-dependent moving-edge witness. -/
theorem periodic_recurrent_advancing_left_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentAdvancingLeftCollision (m * P) P := by
  obtain ⟨i, hi, hf⟩ := finite_recurrent_choice
    (fun i t => AdvancingCollision (m * P) t (-(P : Int) + (i : Int))) (P - 1) (by
      intro N
      obtain ⟨t, ht, _, x, hx1, hx2, hadv⟩ :=
        periodic_advancing_left_collision_window T P m (max T N) hP hm hc (by omega)
      refine ⟨t, by omega, (x + (P : Int)).toNat, by omega, ?_⟩
      simpa only [Int.toNat_of_nonneg (show 0 ≤ x + (P : Int) by omega),
        show -(P : Int) + (x + (P : Int)) = x by omega] using hadv)
  let k := (P : Int) - (i : Int)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkP : k ≤ (P : Int) := by dsimp [k]; omega
  have hcast : (k.toNat : Int) = k := Int.toNat_of_nonneg (by omega)
  have hcases : ∀ N : Nat, ∃ t : Nat, N ≤ t ∧
      (collisionCode (m * P) t k.toNat = 3 ∨ collisionCode (m * P) t k.toNat = 5) := by
    intro N
    obtain ⟨t, ht, hadv⟩ := hf N
    refine ⟨t, ht, (advancing_collision_codes (m * P) t k.toNat).1 ?_⟩
    simpa only [advancingAtDepth, hcast, show -k = -(P : Int) + (i : Int) by dsimp [k]; omega] using hadv
  obtain ⟨j, hj, hcode⟩ := finite_recurrent_choice
    (fun j t => collisionCode (m * P) t k.toNat = (if j = 0 then 3 else 5)) 2 (by
      intro N
      obtain ⟨t, ht, hh⟩ := hcases N
      rcases hh with hh | hh
      · exact ⟨t, ht, 0, by omega, by simpa using hh⟩
      · exact ⟨t, ht, 1, by omega, by simpa using hh⟩)
  refine ⟨k.toNat, (if j = 0 then 3 else 5), by omega, by omega, ?_, hcode⟩
  by_cases hj0 : j = 0 <;> simp [hj0]

/-- Finite choice fixes an entire source-to-first-erasure pattern, including the
OR-gate case and common reset colour, under the hypothetical periodic center. -/
theorem periodic_recurrent_source_erasure (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentSourceErasure (m * P) P := by
  have hp := kit_period hc
  obtain ⟨k, c, hk, hkP, hc0, hf⟩ := periodic_recurrent_advancing_left_column T P m hP hm hc
  obtain ⟨j, hj, hfirst⟩ := finite_recurrent_choice
    (fun j t => collisionCode (m * P) t k = c ∧ FirstPathErasure (m * P) t k j) (k - 1) (by
      intro N
      obtain ⟨t, ht, hcode⟩ := hf (max T N)
      have ha : advancingAtDepth (m * P) t k :=
        (advancing_collision_codes (m * P) t k).2 (by rw [hcode]; exact hc0)
      have hclean : leftDefect (m * P) (t + k) 0 = false := by
        simpa only [leftDefect, show -((0 : Nat) : Int) = (0 : Int) by omega] using
          center_defect_zero hp m (t + k) (by omega)
      obtain ⟨j, hj, hpath⟩ := advancing_source_first_erasure (m * P) t k hk ha hclean
      exact ⟨t, by omega, j, by omega, hcode, hj, hpath⟩)
  obtain ⟨g, hg, hgate⟩ := finite_recurrent_choice
    (fun g t => collisionCode (m * P) t k = c ∧ FirstPathErasure (m * P) t k j ∧
      gateCode (m * P) (t + 1 + j) (k - (j + 2)) = g) 7 (by
      intro N
      obtain ⟨t, ht, hcode, hpath⟩ := hfirst N
      exact ⟨t, ht, gateCode (m * P) (t + 1 + j) (k - (j + 2)), by
        have hb := gate_code_bound (m * P) (t + 1 + j) (k - (j + 2))
        omega, hcode, hpath, rfl⟩)
  have hgpos : 1 ≤ g := by
    obtain ⟨t, ht, hcode, hpath, heq⟩ := hgate 0
    have hn := hpath.2.2.2.2.1
    rw [heq] at hn
    omega
  obtain ⟨i, hi, hreset⟩ := finite_recurrent_choice
    (fun i t => collisionCode (m * P) t k = c ∧ FirstPathErasure (m * P) t k j ∧
      gateCode (m * P) (t + 1 + j) (k - (j + 2)) = g ∧
      leftColour (m * P) (t + 2 + j) (k - (j + 2)) = (if i = 0 then 0 else 3)) 2 (by
      intro N
      obtain ⟨t, ht, hcode, hpath, heq⟩ := hgate N
      have hh := hpath.2.2.2.2.2.2
      have hh' : leftColour (m * P) (t + 2 + j) (k - (j + 2)) = 0 ∨
          leftColour (m * P) (t + 2 + j) (k - (j + 2)) = 3 := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      rcases hh' with hh0 | hh3
      · exact ⟨t, ht, 0, by omega, hcode, hpath, heq, by simpa using hh0⟩
      · exact ⟨t, ht, 1, by omega, hcode, hpath, heq, by simpa using hh3⟩)
  refine ⟨k, c, j, g, (if i = 0 then 0 else 3), hk, hkP, hc0, by omega,
    hgpos, by omega, ?_, hreset⟩
  by_cases hi0 : i = 0 <;> simp [hi0]

/-- The weaker recurring-source interface follows from a fixed advancing type. -/
theorem periodic_recurrent_left_column (T P m : Nat) (hP : 0 < P) (hm : 0 < m)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : RecurrentLeftCollision (m * P) P := by
  obtain ⟨k, c, hk, hkP, hc0, hf⟩ := periodic_recurrent_advancing_left_column T P m hP hm hc
  refine ⟨-(k : Int), by omega, by omega, ?_⟩
  intro N
  obtain ⟨t, ht, hcode⟩ := hf N
  have hne : collisionCode (m * P) t k ≠ 0 := by rw [hcode]; rcases hc0 with h | h <;> omega
  refine ⟨t, ht, ?_⟩
  simpa only [collisionBit] using (collision_code_nonzero (m * P) t k).1 hne

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
