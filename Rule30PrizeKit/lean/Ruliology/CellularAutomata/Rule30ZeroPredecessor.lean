module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30WhitePadding

@[expose] public section

/-!
The all-white strip has a unique predecessor under a white boundary,
uniformly in strip width. Induction from the boundary forces every cell
of a predecessor of the vacuum to be white.
-/
namespace Ruliology.CellularAutomata.Rule30ZeroPredecessor
open Rule30Jen Rule30StripCertificates Rule30WhitePadding

theorem stripStep_zero_predecessor {K r : Nat} {z : Bool}
    (hr : r < 2^K) (hstep : stripStep K false z r = 0) : r = 0 := by
  have hbits : ∀ k, k < K → r.testBit k = false := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      have hl : (if k = 0 then false else r.testBit (k-1)) = false := by
        split
        · rfl
        · exact ih (k-1) (by omega) (by omega)
      have h := testBit_stripStep K false z r hr k hk
      rw [hstep, Nat.zero_testBit, hl] at h
      cases hc : r.testBit k
      · rfl
      · simp [rule, hc] at h
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.zero_testBit]
  by_cases hk : k < K
  · exact hbits k hk
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))

theorem stripStep_zero_iff {K r : Nat} {z : Bool} (hK : 1 ≤ K) (hr : r < 2^K) :
    stripStep K false z r = 0 ↔ r = 0 ∧ z = false := by
  constructor
  · intro h
    have hzero := stripStep_zero_predecessor hr h
    subst r
    have hb := testBit_stripStep K false z 0 (by exact Nat.two_pow_pos K) (K-1) (by omega)
    rw [h, Nat.zero_testBit] at hb
    have hz : z = false := by simpa [rule, show K-1+1=K by omega] using hb.symm
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl,rfl⟩
    simp [stripStep]

end Ruliology.CellularAutomata.Rule30ZeroPredecessor
