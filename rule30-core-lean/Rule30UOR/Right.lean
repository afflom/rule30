module

public import Rule30UOR.Core
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# The right system: form and function

**Form** (defined in the LexLean core, `Rule30UOR.Core.rdiag`): the anchored law
`rdiag (k + 2) (s + 1) = bxor (rdiag (k + 2) s) (rdiag (k + 1) s || rdiag k s)`, with
`rdiag 0 ≡ true`, `rdiag 1 (s + 1) = !rdiag 1 s`, and `rdiag j 0 = false` for `j ≥ 1`. No free
bits. `rdiag_eq_R`: it is the kit's right-diagonal array of the single seed.

**Function**: two readouts of the one orbit, the center `rcenter t = rdiag t t`
(`center_eq_rcenter`) and column `1` one step later, `rdiag t (t + 1)` (`col1_readout`).

**Intent**: `MaskPos` (if the center readout has period `P` from `T`, the column-1 readout has
period `P` at the white center times). `problem1_iff_maskPos`: Problem 1 holds exactly when
`MaskPos` does. Masked Jen gives one direction; the other is vacuous.
-/

@[expose] public section

namespace Rule30UOR.Right

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30Prize Rule30MaskedJen
open Rule30UOR.Core (rdiag rcenter)

/-- The LexLean right system is the kit's right-diagonal array. -/
theorem rdiag_eq_R : ∀ t j, rdiag j t = R j t := by
  intro t
  induction t with
  | zero =>
    intro j
    rcases j with _ | j
    · exact (R_zero 0).symm
    · show false = cell 0 (((0 : Nat) : Int) - ((j + 1 : Nat) : Int))
      simp only [cell]; exact (decide_eq_false (by omega)).symm
  | succ t ih =>
    intro j
    rcases j with _ | _ | k
    · exact (R_zero (t + 1)).symm
    · show (!rdiag 1 t) = R 1 (t + 1)
      rw [ih 1, R_one_succ]
    · rw [Rule30UOR.Core.rdiag_step, ih k, ih (k + 1), ih (k + 2), R_step]
      simp only [Rule30UOR.Core.bxor]; cases R (k + 2) t <;> simp

theorem center_eq_rcenter (t : Nat) : center t = rcenter t := by
  show cell t 0 = rdiag t t
  rw [rdiag_eq_R, center_eq_R]

theorem col1_readout (t : Nat) : cell (t + 1) 1 = rdiag t (t + 1) := by
  rw [rdiag_eq_R]; unfold R; exact cell_congr (by omega)

/-- Every right diagonal repeats from time `0` with period `2 ^ j`. -/
theorem rdiag_periodic (j t : Nat) : rdiag j (t + 2 ^ j) = rdiag j t := by
  rw [rdiag_eq_R, rdiag_eq_R]; exact R_periodic j t

/-- `2 ^ j`, named for the paper. -/
def pow2 (j : Nat) : Nat := 2 ^ j

theorem rdiag_periodic_pow2 (j t : Nat) : rdiag j (t + pow2 j) = rdiag j t := rdiag_periodic j t

/-- The center readout repeats with period `P` from `T`. -/
def CenterPer (T P : Nat) : Prop := ∀ t, T ≤ t → rdiag (t + P) (t + P) = rdiag t t

/-- The column-1 readout repeats with period `P` from `T` at the white center times. -/
def MaskedPer (T P : Nat) : Prop :=
  ∀ t, T ≤ t → rdiag (t + 1) (t + 1) = false → rdiag (t + P) (t + P + 1) = rdiag t (t + 1)

/-- **The exact obligation**, stated on the LexLean right system. -/
def MaskPos : Prop := ∀ T P : Nat, 0 < P → CenterPer T P → MaskedPer T P

theorem maskPos_unfold (h : MaskPos) (T P : Nat) (hP : 0 < P) (hc : CenterPer T P) :
    MaskedPer T P := h T P hP hc

theorem maskPos_of_problem1 (h1 : Problem1) : MaskPos := by
  intro T P hP hper
  exact absurd ⟨T, P, hP, fun t ht => by
    rw [center_eq_rcenter, center_eq_rcenter]; exact hper t ht⟩ h1

theorem problem1_of_maskPos (hm : MaskPos) : Problem1 := by
  intro hEP
  obtain ⟨T, P, hP, hper⟩ := hEP
  have hR : ∀ t, T ≤ t → rdiag (t + P) (t + P) = rdiag t t := fun t ht => by
    have := hper t ht
    rwa [center_eq_rcenter, center_eq_rcenter] at this
  refine masked_jen 0 (T := T + 1) hP (fun t ht => hper t (by omega)) (fun t ht hw => ?_)
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hw' : rdiag (s + 1) (s + 1) = false := by
    have : center (s + 1) = false := hw
    rwa [center_eq_rcenter] at this
  have := hm T P hP hR s (by omega) hw'
  rw [show (0 : Int) + 1 = 1 by rfl, show s + 1 + P = (s + P) + 1 by omega, col1_readout,
    col1_readout, this]

/-- **Problem 1 is exactly `MaskPos`.** -/
theorem problem1_iff_maskPos : Problem1 ↔ MaskPos :=
  ⟨maskPos_of_problem1, problem1_of_maskPos⟩


/-! ### The left neighbour: the symmetric form of the obligation -/

/-- Column `-1` at time `t` is diagonal `t + 1` read at time `t`. -/
theorem colm1_readout (t : Nat) : cell t (-1) = rdiag (t + 1) t := by
  rw [rdiag_eq_R]; unfold R; exact cell_congr (by omega)

/-- The column `-1` readout repeats with period `P` from `T`. -/
def LeftPer (T P : Nat) : Prop := ∀ t, T ≤ t → rdiag (t + P + 1) (t + P) = rdiag (t + 1) t

/-- The symmetric obligation: a periodic center readout forces a periodic left readout. -/
def LeftPos : Prop := ∀ T P : Nat, 0 < P → CenterPer T P → LeftPer T P

theorem leftPos_of_problem1 (h1 : Problem1) : LeftPos := by
  intro T P hP hper
  exact absurd ⟨T, P, hP, fun t ht => by
    rw [center_eq_rcenter, center_eq_rcenter]; exact hper t ht⟩ h1

theorem problem1_of_leftPos (hl : LeftPos) : Problem1 := by
  intro hEP
  obtain ⟨T, P, hP, hper⟩ := hEP
  have hR : CenterPer T P := fun t ht => by
    have := hper t ht
    rwa [center_eq_rcenter, center_eq_rcenter] at this
  have hL := hl T P hP hR
  refine not_adjacent (-1) ⟨T, P, hP, fun t ht => ?_⟩ ⟨T, P, hP, fun t ht => ?_⟩
  · show cell (t + P) (-1) = cell t (-1)
    rw [colm1_readout, colm1_readout, show t + P + 1 = (t + 1) + P by omega]
    rw [show (t + 1) + P = t + P + 1 by omega]; exact hL t ht
  · show cell (t + P) (-1 + 1) = cell t (-1 + 1)
    exact hper t ht

/-- **Problem 1 is exactly `LeftPos`.** The three readouts `rdiag (t - 1) t`, `rdiag t t`,
`rdiag (t + 1) t` are columns `1`, `0`, `-1`. -/
theorem problem1_iff_leftPos : Problem1 ↔ LeftPos := ⟨leftPos_of_problem1, problem1_of_leftPos⟩

end Rule30UOR.Right
