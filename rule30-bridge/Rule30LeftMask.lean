module

public import Rule30UOR.KitConstructive
public import Ruliology.CellularAutomata.Rule30DrivenLeft

/-!
# Problem 1 from the left half alone

Where the center is black, column `-1` is fixed by the *next* center value
(`Rule30MaskedJen.left_of_black`): `cell t (-1) = !center (t + 1)`. A later cell acts on an earlier
one. The real left half is the left half driven by the center (`Rule30DrivenLeft.cell_eq_L`), so an
eventually periodic center would give a periodic driver whose driven left half has column `-1`
equal to `!c (t + 1)` at every black time of `c`. No right-half information is used.

* `LeftMask`: no finite nonzero start and no eventually periodic driver that is black infinitely
  often make column `-1` of the driven left half equal `!c (t + 1)` at every late black time `t` of
  `c`.
* `problem1_of_leftMask : LeftMask → Problem1`.

`LeftMask` is the uniform form of the kit's per-word left conditions: for `c = (01)^∞` it is
`Rule30PeriodTwo.Q01` (column `-1` black at every black time of the driver, read through the
effective boundary), and `Rule30PeriodFourSkeleton.C3`, `Rule30EtherThreeLeft.C3w` are its
period-`4` and period-`3` words.
-/

@[expose] public section

namespace Rule30LeftMask

open Ruliology.CellularAutomata Rule30Jen Rule30Prize Rule30MaskedJen Rule30DrivenLeft

/-- **The left-only obligation.** -/
def LeftMask : Prop :=
  ∀ (c : Nat → Bool) (s : Int → Bool) (m : Nat), 0 < m →
    (∀ p : Int, p < -(m : Int) → s p = false) → s (-(m : Int)) = true →
    EventuallyPeriodic c → (∀ T, ∃ t, T ≤ t ∧ c t = true) →
    ¬ ∃ T, ∀ t, T ≤ t → c t = true → L c s t (-1) = !c (t + 1)

/-- **The left half alone decides Problem 1.** -/
theorem problem1_of_leftMask (hL : LeftMask) : Problem1 := by
  intro hEP
  obtain ⟨T, P, hP, hper⟩ := hEP
  -- the center is black infinitely often (otherwise it is eventually white)
  have hrec : ∀ N, ∃ t, N ≤ t ∧ center t = true := by
    intro N
    let M := max N T
    have hb : ∃ r, r < P ∧ center (M + r) = true := by
      refine Decidable.byContradiction fun hno =>
        Rule30UOR.KitConstructive.center_not_eventually_constant ⟨M, false, fun u hu => ?_⟩
      let r := (u - M) % P
      have hr : r < P := Nat.mod_lt _ hP
      have he : (M + r) + ((u - M) / P) * P = u := by
        have hh := Nat.mod_add_div (u - M) P
        rw [Nat.mul_comm P ((u - M) / P)] at hh
        dsimp [r]
        omega
      have hp := periodic_mul hper ((u - M) / P) (M + r) (by omega)
      rw [he] at hp
      rw [hp]
      cases h : center (M + r)
      · rfl
      · exact (hno ⟨r, hr, h⟩).elim
    obtain ⟨r, -, hr⟩ := hb
    exact ⟨M + r, by omega, hr⟩
  let T' := T + 1
  let c : Nat → Bool := fun k => cell (T' + k) 0
  have hc : EventuallyPeriodic c :=
    ⟨0, P, hP, fun k _ => by
      show cell (T' + (k + P)) 0 = cell (T' + k) 0
      have := hper (T' + k) (by omega)
      rw [show T' + (k + P) = T' + k + P by omega]; exact this⟩
  have hcr : ∀ N, ∃ t, N ≤ t ∧ c t = true := by
    intro N
    obtain ⟨t, ht, h⟩ := hrec (T' + N)
    exact ⟨t - T', by omega, by show cell (T' + (t - T')) 0 = true; rw [show T' + (t - T') = t by omega]; exact h⟩
  obtain ⟨he0, he1⟩ := real_edge T'
  refine hL c (fun p => cell T' p) T' (by omega) he0 he1 hc hcr ⟨0, fun k _ hk => ?_⟩
  have e := cell_eq_L T' k (-1) (by omega)
  rw [e]
  have hb := left_of_black (T' + k) 0 hk
  rw [show (0 : Int) - 1 = -1 by rfl] at hb
  rw [hb]
  rfl

end Rule30LeftMask
