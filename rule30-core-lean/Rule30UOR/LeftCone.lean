module
public import Rule30UOR.Interfaces
public import Rule30UOR.WittDefect
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The left agreement cone

Rule 30 is left-permutive: `cell t (p - 1)` is determined by `cell (t+1) p`,
`cell t p` and `cell t (p+1)`. Read on temporal defects (`defect_step_linear`),
agreement at `(t+1, p)`, `(t, p)` and `(t, p+1)` forces agreement at
`(t, p-1)`. Iterating from the center: if the center agrees on `[t, t+k]` and
column one agrees on `[t, t+k)`, every column `-j` with `j ≤ k` agrees at time
`t`. Under a periodic center the first hypothesis is free, so a left defect at
depth `k` at time `t` is *sourced* by a right column-one defect at some time in
`[t, t+k)`: the left half carries no defect that the right column did not send
through the center within its depth. This is the structural content behind the
coupling law at every depth, and it is the constraint any closing argument for
`aperiodic-compensation` must use. -/

@[expose] public section

namespace Rule30UOR.LeftCone

open Rule30UOR.Core Rule30UOR.TemporalDefect Rule30UOR.Collision Rule30UOR.WittDefect

/-- Left-permutivity on defects: agreement at `(t+1,p)`, `(t,p)`, `(t,p+1)`
forces agreement at `(t,p-1)`. -/
theorem defect_left_of_agree (Q t : Nat) (p : Int)
    (h1 : defect Q (t + 1) p = false) (h0 : defect Q t p = false)
    (hr : defect Q t (p + 1) = false) : defect Q t (p - 1) = false := by
  rw [Rule30UOR.TemporalDefect.defect_step_linear, h0, hr] at h1
  simpa using h1

/-- Column one agrees with its lag-`Q` shift on `[t, t+k)`. -/
def RightAgrees (Q t k : Nat) : Prop := ∀ i, i < k → rightDefect Q (t + i) 1 = false

instance (Q t k : Nat) : Decidable (RightAgrees Q t k) := by
  unfold RightAgrees; infer_instance

theorem rightDefect_eq_defect (Q t : Nat) : rightDefect Q t 1 = defect Q t 1 := rfl

/-- A bounded search: a Boolean sequence that is not `false` on `[0, k)` is
`true` somewhere in `[0, k)`. -/
theorem exists_true_of_not_all_false (k : Nat) (p : Nat → Bool)
    (h : ¬ ∀ i, i < k → p i = false) : ∃ i, i < k ∧ p i = true := by
  induction k with
  | zero => exact absurd (fun i hi => absurd hi (Nat.not_lt_zero i)) h
  | succ k ih =>
    cases hk : p k with
    | false =>
      have hnot : ¬ ∀ i, i < k → p i = false := fun hall => h fun i hi => by
        rcases Nat.lt_or_ge i k with h1 | h1
        · exact hall i h1
        · have hik : i = k := by cfomega
          subst hik; exact hk
      obtain ⟨i, hi, hp⟩ := ih hnot
      exact ⟨i, Nat.lt_succ_of_lt hi, hp⟩
    | true => exact ⟨k, Nat.lt_succ_self k, hk⟩

theorem left_cone_aux (Q t m : Nat)
    (hc : ∀ s, t ≤ s → s ≤ t + m → defect Q s 0 = false)
    (hr : ∀ s, t ≤ s → s < t + m → defect Q s 1 = false) :
    ∀ k s j, t ≤ s → s + k ≤ t + m → j ≤ k → defect Q s (-(j : Int)) = false := by
  intro k
  induction k with
  | zero =>
    intro s j hs hk hj
    have hj0 : j = 0 := by cfomega
    subst hj0
    simpa using hc s hs (by cfomega)
  | succ k ih =>
    intro s j hs hk hj
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact ih s j hs (by cfomega) (by cfomega)
    · have hj' : j = k + 1 := by cfomega
      subst hj'
      have e : (-((k + 1 : Nat) : Int)) = (-(k : Int)) - 1 := by push_cast; cfomega
      rw [e]
      apply defect_left_of_agree
      · exact ih (s + 1) k (by cfomega) (by cfomega) (Nat.le_refl k)
      · exact ih s k hs (by cfomega) (Nat.le_refl k)
      · cases k with
        | zero => simpa using hr s hs (by cfomega)
        | succ k' =>
          have e2 : (-((k' + 1 : Nat) : Int)) + 1 = -((k' : Nat) : Int) := by push_cast; cfomega
          rw [e2]
          exact ih s k' hs (by cfomega) (by cfomega)

theorem kit_periodic_of_centerPeriodic {T P : Nat} (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∀ t, T ≤ t → Ruliology.CellularAutomata.Rule30Prize.center (t + P) =
      Ruliology.CellularAutomata.Rule30Prize.center t := fun t ht => by
  rw [← Rule30UOR.Scale.center_eq_kit, ← Rule30UOR.Scale.center_eq_kit]
  exact hc t ht

/-- Under a periodic center, column-one agreement on `[t, t+k)` forces the whole
left cone of depth `k` at time `t` to agree. -/
theorem left_cone_of_right_agrees (T P m t k : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t)
    (hr : RightAgrees (m * P) t k) : leftDefect (m * P) t k = false := by
  have hc0 : ∀ s, t ≤ s → s ≤ t + k → defect (m * P) s 0 = false := fun s hs _ =>
    Rule30UOR.DefectFront.center_defect_zero (kit_periodic_of_centerPeriodic hc) m s (by cfomega)
  have hr' : ∀ s, t ≤ s → s < t + k → defect (m * P) s 1 = false := by
    intro s hs hsk
    have := hr (s - t) (by cfomega)
    rw [show t + (s - t) = s by cfomega] at this
    exact this
  exact left_cone_aux (m * P) t k hc0 hr' k t k (Nat.le_refl t) (Nat.le_refl _) (Nat.le_refl k)

/-- Under a periodic center, a left defect at depth `k` at time `t` is sourced
by a right column-one defect at a time in `[t, t+k)`. -/
theorem left_defect_sourced (T P m t k : Nat)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t)
    (hd : leftDefect (m * P) t k = true) :
    ∃ s, t ≤ s ∧ s < t + k ∧ rightDefect (m * P) s 1 = true := by
  have hn : ¬ RightAgrees (m * P) t k := fun hr => by
    rw [left_cone_of_right_agrees T P m t k hc ht hr] at hd
    exact Bool.false_ne_true hd
  obtain ⟨i, hi, hp⟩ := exists_true_of_not_all_false k (fun i => rightDefect (m * P) (t + i) 1) hn
  exact ⟨t + i, Nat.le_add_right t i, by cfomega, hp⟩

end Rule30UOR.LeftCone
