module

public import Ruliology.CellularAutomata.Rule30EtherThree
public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Ruliology.CellularAutomata.Rule30PeriodTwo

/-!
# Rule 30, least period 3: reductions to the left half

If the center column is eventually `001^∞` or `011^∞`, the left half (columns `p < 0`) is, from
that time on, rule 30 driven by the *effective boundary* `c'(t) = c(t) && c(t + 1)`
(`Rule30MaskedJen.effective_step`, `Rule30DrivenLeft.cell_eq_L_effective`), and column `-1` is
forced at the black phases of the center by left permutivity.

* `001`: `c' = 000`, so the left half is the zero-boundary left half (ZBL). Column `-1` is black at
  the black phase and equal to column `1` (phase `0`) or its complement (phase `1`) at the white
  phases (`col_m1_001`). The left-only statement is `Q001`: **no start of the ZBL with a leftmost
  black cell keeps column `-1` black at every third step** (the analog of
  `Rule30PeriodTwo.Q01`). `not_eventually_001_of_Q001`: `Q001` excludes `001^∞` for every
  transient. Finiteness is essential: the stripe keeps column `-1` black forever
  (`Q001_stripe`).
* `011`: `c' = 010`, and column `-1` is (`!` column `1`, white, black) at phases (`0, 1, 2`)
  (`col_m1_011`). The left-only statement is `C3w w011` (the analog of
  `Rule30PeriodFourSkeleton.C3`): **no finitely supported left configuration, driven by the
  boundary `010`, keeps column `-1` equal to `(*, 0, 1)` for all large times.**
  `not_eventually_011_of_C3w`. Finiteness is essential here too: the left part of the
  period-3 ether is a solution for ever (`C3w_011_ether`).

Both statements are open. Evidence (a C search, not kernel-checked):
every start of width `W ≤ 37` violates `Q001`'s constraint by time `94`, and every start of width
`W ≤ 70` violates the `011` constraint by time `99` (all three phases).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThree

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30DrivenLeft

theorem wordAt3_001 (x : Nat) : wordAt3 w001 x = decide (x % 3 = 2) := by
  unfold wordAt3
  have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> rfl

theorem wordAt3_011 (x : Nat) : wordAt3 w011 x = decide (1 ≤ x % 3) := by
  unfold wordAt3
  have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> rfl

theorem col_m1 (t : Nat) : cell t (-1) = xor (cell (t + 1) 0) (cell t 0 || cell t 1) := by
  have := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl] at this
  exact this

/-! ### The word `001` -/

/-- **Column `-1` under `001`.** If `c(t) = [ (t - T) % 3 = 2 ]` for `t ≥ T`, column `-1` is
(`=` column `1`, `!` column `1`, black) at the phases (`0, 1, 2`). -/
theorem col_m1_001 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T)) (t : Nat)
    (ht : T ≤ t) :
    ((t - T) % 3 = 0 → cell t (-1) = cell t 1) ∧
    ((t - T) % 3 = 1 → cell t (-1) = !cell t 1) ∧
    ((t - T) % 3 = 2 → cell t (-1) = true) := by
  have c0 := h t ht
  have c1 := h (t + 1) (by omega)
  rw [wordAt3_001] at c0 c1
  rw [show t + 1 - T = (t - T) + 1 by omega] at c1
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 1 by omega, hφ]; cases cell t 1 <;> rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 2 by omega, hφ]; cases cell t 1 <;> rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 0 by omega, hφ]; rfl

/-- **`Q001`** (open). No start of the zero-driven left half with a leftmost black cell (at `-m`,
`m ≥ 1`, white beyond) keeps column `-1` black at every third step. -/
def Q001 : Prop :=
  ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, L (fun _ => false) s (3 * k) (-1) = true

/-- **`Q001` excludes `001^∞`** as a tail of the center column, for every transient. -/
theorem not_eventually_001_of_Q001 (hQ : Q001) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) := by
  rintro ⟨T, hT⟩
  -- start at a black phase, at least one step in
  let T' := T + 5
  have hfun : (fun k => center (T' + k) && center (T' + k + 1)) = fun _ => false := by
    funext k
    show (cell (T' + k) 0 && cell (T' + k + 1) 0) = false
    rw [hT (T' + k) (by omega), hT (T' + k + 1) (by omega), wordAt3_001, wordAt3_001]
    by_cases h2 : (T' + k - T) % 3 = 2
    · rw [show (T' + k + 1 - T) % 3 = 0 by omega]; simp
    · simp [h2]
  refine hQ T' (fun p => cell T' p) (by omega) (fun p hp => cell_eq_false_of_lt T' p hp)
    (cell_left_edge T') (fun k => ?_)
  have e := cell_eq_L_effective T' (3 * k) (-1) (by omega)
  rw [hfun] at e
  rw [e]
  exact (col_m1_001 T hT (T' + 3 * k) (by omega)).2.2 (by omega)

/-- **Finiteness is essential in `Q001`**: from the infinite stripe the zero-driven left half
keeps column `-1` black at every step. -/
theorem Q001_stripe (k : Nat) : L (fun _ => false) Rule30PeriodTwo.stripe (3 * k) (-1) = true :=
  Rule30PeriodTwo.stripe_col _

/-! ### The word `011` and the C3-type statement -/

/-- The 3-periodic effective boundary `c'_w(φ) = w(φ) && w(φ + 1)`. -/
def effWord3 (w : List Bool) : List Bool :=
  (List.range 3).map fun φ => wordAt3 w φ && wordAt3 w (φ + 1)

theorem effWord3_001 : effWord3 w001 = [false, false, false] := by decide
theorem effWord3_011 : effWord3 w011 = [false, true, false] := by decide

theorem wordAt3_effWord3 (w : List Bool) (k : Nat) :
    wordAt3 (effWord3 w) k = (wordAt3 w k && wordAt3 w (k + 1)) := by
  show ((List.range 3).map fun φ => wordAt3 w φ && wordAt3 w (φ + 1)).getD (k % 3) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.mod_lt _ (by decide))]
  simp only [Option.map_some, Option.getD_some]
  unfold wordAt3
  rw [Nat.mod_mod, show (k % 3 + 1) % 3 = (k + 1) % 3 by omega]

/-- Whether `b` fits the pattern `P` at phase `φ` (`none` = unconstrained). -/
def fits3 (P : List (Option Bool)) (φ : Nat) (b : Bool) : Bool :=
  match P.getD φ none with
  | none => true
  | some v => b == v

/-- `P_w`: the values of column `-1` fixed by left permutivity at the black phases of `w`. -/
def colPattern3 : List Bool → List (Option Bool)
  | [false, true, true] => [none, some false, some true]
  | [false, false, true] => [none, none, some true]
  | _ => [none, none, none]

/-- **`C3w w`** (open). No finitely supported left configuration, run as rule 30 on `p ≤ -1` with
column `0` replaced by the 3-periodic effective boundary `c'_w`, keeps column `-1` equal to `P_w`
at its fixed phases for all large times. -/
def C3w (w : List Bool) : Prop :=
  ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
    ¬ ∃ K, ∀ k, K ≤ k → fits3 (colPattern3 w) (k % 3) (L (fun k => wordAt3 (effWord3 w) k) s k (-1)) = true

/-- **Column `-1` under `011`.** If `c(t) = [ (t - T) % 3 ≥ 1 ]` for `t ≥ T`, column `-1` is
(`!` column `1`, white, black) at the phases (`0, 1, 2`). -/
theorem col_m1_011 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T)) (t : Nat)
    (ht : T ≤ t) :
    ((t - T) % 3 = 0 → cell t (-1) = !cell t 1) ∧
    ((t - T) % 3 = 1 → cell t (-1) = false) ∧
    ((t - T) % 3 = 2 → cell t (-1) = true) := by
  have c0 := h t ht
  have c1 := h (t + 1) (by omega)
  rw [wordAt3_011] at c0 c1
  rw [show t + 1 - T = (t - T) + 1 by omega] at c1
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 1 by omega, hφ]; cases cell t 1 <;> rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 2 by omega, hφ]; rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 0 by omega, hφ]; rfl

/-- The common step: a `w`-periodic tail whose column `-1` eventually fits `P_w` contradicts
`C3w w`. -/
theorem not_tail_of_C3w (w : List Bool) (hC : C3w w) (T : Nat)
    (hT : ∀ t, T ≤ t → cell t 0 = wordAt3 w (t - T))
    (hskel : ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → fits3 (colPattern3 w) ((t - T) % 3) (cell t (-1)) = true) :
    False := by
  obtain ⟨T', hT', hP⟩ := hskel
  have hdrv : (fun k => center (T + k) && center (T + k + 1)) = fun k => wordAt3 (effWord3 w) k := by
    funext k
    rw [wordAt3_effWord3]
    show (cell (T + k) 0 && cell (T + k + 1) 0) = _
    rw [hT (T + k) (by omega), hT (T + k + 1) (by omega), show T + k - T = k by omega,
      show T + k + 1 - T = k + 1 by omega]
  refine hC (fun p => cell T p) ⟨T, fun p hp => cell_eq_false_of_lt T p hp⟩ ⟨T' - T, fun k hk => ?_⟩
  have e := cell_eq_L_effective T k (-1) (by omega)
  rw [hdrv] at e
  rw [e]
  have := hP (T + k) (by omega)
  rwa [show T + k - T = k by omega] at this

theorem fits3_011 (φ : Nat) (b : Bool) :
    fits3 (colPattern3 w011) φ b =
      (if φ = 1 then b == false else if φ = 2 then b == true else true) := by
  rcases Nat.lt_or_ge φ 3 with h | h
  · have : φ = 0 ∨ φ = 1 ∨ φ = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  · unfold fits3
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [colPattern3, w011]; omega)]
    simp [show φ ≠ 1 by omega, show φ ≠ 2 by omega]

/-- **`C3w w011` excludes `011^∞`** as a tail of the center column, for every transient. -/
theorem not_eventually_011_of_C3w (hC : C3w w011) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T) := by
  rintro ⟨T, hT⟩
  refine not_tail_of_C3w w011 hC T hT ⟨T, Nat.le_refl T, fun t ht => ?_⟩
  obtain ⟨-, s1, s2⟩ := col_m1_011 T hT t ht
  rw [fits3_011]
  have : (t - T) % 3 = 0 ∨ (t - T) % 3 = 1 ∨ (t - T) % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_left h, s1 h]; rfl
  · rw [ite_eq_right (by omega), ite_eq_left h, s2 h]; rfl

/-! ### Finiteness is essential for `C3w w011`: the ether -/

/-- The left part of the period-3 ether next to its column `2` (a `011` column): position `p < 0`
carries ether column `2 + p` (indices modulo `12`). -/
def etherLeft (p : Int) : Bool := ether3 (((p + 2) % 12).toNat) 0

theorem etherLeft_idx (p : Int) : (((p - 1 + 2) % 12).toNat + 1) % 12 = ((p + 2) % 12).toNat % 12 ∧
    (((p + 2) % 12).toNat + 1) % 12 = ((p + 1 + 2) % 12).toNat % 12 := by
  constructor <;> omega

/-- The ether left half evolves under the boundary `010` (the effective boundary of `011`). -/
theorem etherLeft_evolves : ∀ (k : Nat) (p : Int), p < 0 →
    L (fun k => wordAt3 (effWord3 w011) k) etherLeft k p = ether3 (((p + 2) % 12).toNat) k := by
  intro k
  induction k with
  | zero => intro p hp; rw [L_zero hp]; rfl
  | succ k ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), ih p hp]
    have hl : ether3 (((p - 1 + 2) % 12).toNat) k = ether3 (((p + 2) % 12).toNat + 11) k :=
      ether3_congr (by omega) rfl
    rw [hl]
    by_cases hp1 : p = -1
    · subst hp1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0, wordAt3_effWord3, wordAt3_011, wordAt3_011]
      show rule (ether3 (((-1 + 2 : Int) % 12).toNat + 11) k) (ether3 (((-1 + 2 : Int) % 12).toNat) k)
          (decide (1 ≤ k % 3) && decide (1 ≤ (k + 1) % 3)) = ether3 (((-1 + 2 : Int) % 12).toNat) (k + 1)
      have e1 : ((-1 + 2 : Int) % 12).toNat = 1 := by decide
      rw [e1, ether3_rule 1 k]
      have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hk : ∀ j, ether3 j k = ether3 j (k % 3) := fun j => ether3_congr rfl (by omega)
      rw [hk (1 + 11), hk 1, hk (1 + 1)]
      rcases this with h | h | h <;> rw [h] <;> simp [show (k + 1) % 3 = (k % 3 + 1) % 3 by omega, h] <;> decide
    · rw [ih (p + 1) (by omega)]
      rw [ether3_rule]
      congr 1
      exact ether3_congr (by omega) rfl

/-- **Finiteness is essential in `C3w w011`**: the (infinite) left part of the ether, driven by the
boundary `010`, keeps column `-1` equal to `(*, 0, 1)` for ever. -/
theorem C3w_011_ether (k : Nat) :
    fits3 (colPattern3 w011) (k % 3) (L (fun k => wordAt3 (effWord3 w011) k) etherLeft k (-1)) = true := by
  rw [etherLeft_evolves k (-1) (by omega), fits3_011]
  have e1 : ((-1 + 2 : Int) % 12).toNat = 1 := by decide
  rw [e1]
  have hk : ether3 1 k = ether3 1 (k % 3) := ether3_congr rfl (by omega)
  rw [hk]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> decide

end Rule30EtherThree
end Ruliology.CellularAutomata
