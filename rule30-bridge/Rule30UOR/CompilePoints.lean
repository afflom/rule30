module

public import Rule30UOR.ZeroDiagonals

/-!
# Compile points of the zero-state

A *zero diagonal* `z` (`E z ≡ false`) is where the depth step of the zero-state forgets nothing yet
determines nothing. This file proves what happens around one, at every depth.

* `black_after_zero`: two diagonals past a zero diagonal is an all-black diagonal.
* `zero_before_black`: two diagonals before an all-black diagonal (depth `≥ 2`) is a zero diagonal.
  So the black diagonals past depth `1` are exactly the zero diagonals shifted by `2`.
* `no_adjacent_zero`: two consecutive diagonals are never both zero.
* `twin_before_zero`: the two diagonals just before a zero diagonal are equal.
* `accumulate_after_zero`: just past a zero diagonal, the next diagonal is the running sum of the
  diagonal before it.
* `period_at_most_doubles`, `period_passes`: a common period of all diagonals up to `j + 1` is a
  period of diagonal `j + 2` behind a nonzero diagonal, and twice it is a period in every case.
* `doubling_point`: **for every `P > 0` there is a zero diagonal `z` such that every diagonal up to
  `z` has period `P` and diagonal `z + 1` does not.** The common period of the zero-state changes
  only at zero diagonals, and it changes infinitely often.
* `compile_bit`: the one bit of the zero-state that the depth step leaves free at a zero diagonal
  `z` (the constant of the running sum) is read off the real pattern at the last black cell `τ` of
  diagonal `z`: `E (z + 1) (τ + 1) = !E (z - 1) τ`, and the real diagonal `z + 1` already equals
  the zero-state from time `τ + 1` on.
-/

@[expose] public section

namespace Rule30UOR.CompilePoints

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30UOR.Intent Rule30UOR.ZeroDiagonals

/-- A zero diagonal. -/
def Zero (z : Nat) : Prop := ∀ t, E z t = false

/-- An all-black diagonal. -/
def Black (b : Nat) : Prop := ∀ t, E b t = true

/-! ### Running sums -/

/-- `rs f t n = f t xor f (t+1) xor … xor f (t+n-1)`. -/
def rs (f : Nat → Bool) (t : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (rs f t n) (f (t + n))

theorem rs_add (f : Nat → Bool) (t : Nat) : ∀ m n, rs f t (m + n) = xor (rs f t m) (rs f (t + m) n) := by
  intro m n
  induction n with
  | zero => simp [rs]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega]
    simp only [rs]
    rw [ih, show t + (m + n) = t + m + n by omega]
    cases rs f t m <;> cases rs f (t + m) n <;> cases f (t + m + n) <;> rfl

theorem rs_shift {f : Nat → Bool} {P : Nat} (hf : ∀ t, f (t + P) = f t) (t : Nat) :
    ∀ n, rs f (t + P) n = rs f t n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [rs]; rw [ih, show t + P + n = (t + n) + P by omega, hf]

theorem rs_double {f : Nat → Bool} {P : Nat} (hf : ∀ t, f (t + P) = f t) (t : Nat) :
    rs f t (P + P) = false := by
  rw [rs_add, rs_shift hf]; cases rs f t P <;> rfl

/-- A sequence that adds `f` wherever it steps has increments given by the running sum of `f`. -/
theorem acc_rs {g f : Nat → Bool} {T : Nat} (h : ∀ t, T ≤ t → g (t + 1) = xor (f t) (g t)) :
    ∀ t, T ≤ t → ∀ n, g (t + n) = xor (g t) (rs f t n) := by
  intro t ht n
  induction n with
  | zero => simp [rs]
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 by omega, h _ (by omega), ih]
    simp only [rs]
    cases g t <;> cases rs f t n <;> cases f (t + n) <;> rfl

/-! ### Around a zero diagonal -/

/-- Two diagonals before an all-black diagonal is a zero diagonal. -/
theorem zero_before_black {b : Nat} (hb : Black (b + 2)) : Zero b := by
  intro t; rw [E_back, hb, hb]; cases E (b + 1) t <;> rfl

/-- Two consecutive zero diagonals never occur. -/
theorem no_adjacent_zero (z : Nat) : ¬ (Zero z ∧ Zero (z + 1)) := by
  rintro ⟨h0, h1⟩
  have key : ∀ k, k ≤ z → Zero (z - k) ∧ Zero (z - k + 1) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨h0, h1⟩
    | succ k ih =>
      intro hk
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨fun t => ?_, by rw [show z - (k + 1) + 1 = z - k by omega]; exact a⟩
      rw [E_back, show z - (k + 1) + 2 = z - k + 1 by omega, show z - (k + 1) + 1 = z - k by omega,
        a, b, b]; rfl
  have := (key z (Nat.le_refl z)).1 0
  rw [Nat.sub_self, E_zero'] at this
  exact absurd this (by decide)

/-- Two diagonals past a zero diagonal is an all-black diagonal. -/
theorem black_after_zero {z : Nat} (hz : Zero z) : Black (z + 2) := by
  have hnz : ∃ s, E (z + 1) s = true :=
    nonzero_witness (z + 1) (fun h => no_adjacent_zero z ⟨hz, h⟩)
  obtain ⟨s, hs⟩ := hnz
  have mono : ∀ n, E (z + 2) (s + 1 + n) = true := by
    intro n
    induction n with
    | zero => rw [Nat.add_zero, E_step, hz, hs]; rfl
    | succ n ih =>
      rw [show s + 1 + (n + 1) = (s + 1 + n) + 1 by omega, E_step, hz, ih]
      cases E (z + 1) (s + 1 + n) <;> rfl
  intro t
  rw [← E_per_mul (z + 2) (s + 1) t]
  have hX : 1 ≤ 2 ^ (z + 2) := Nat.two_pow_pos _
  have : s + 1 ≤ (s + 1) * 2 ^ (z + 2) := Nat.le_mul_of_pos_right _ hX
  obtain ⟨n, hn⟩ : ∃ n, t + (s + 1) * 2 ^ (z + 2) = s + 1 + n := ⟨t + (s + 1) * 2 ^ (z + 2) - (s + 1), by omega⟩
  rw [hn, mono]

/-- The two diagonals just before a zero diagonal are equal. -/
theorem twin_before_zero {j : Nat} (hz : Zero (j + 2)) : ∀ t, E j t = E (j + 1) t := by
  intro t
  have h := E_step j t
  rw [hz, hz] at h
  revert h; cases E j t <;> cases E (j + 1) t <;> simp

/-- Just past a zero diagonal, the next diagonal accumulates the diagonal before it. -/
theorem accumulate_after_zero {j : Nat} (hz : Zero (j + 1)) :
    ∀ t, E (j + 2) (t + 1) = xor (E j t) (E (j + 2) t) := by
  intro t; rw [E_step, hz]; rfl

/-! ### The common period changes only at zero diagonals -/

/-- All diagonals up to `j` have period `P`. -/
def CommonPer (P j : Nat) : Prop := ∀ i, i ≤ j → ∀ t, E i (t + P) = E i t

theorem period_passes {P j : Nat} (hP : 0 < P) (h : CommonPer P (j + 1))
    (hnz : ∃ s, E (j + 1) s = true) : CommonPer P (j + 2) := by
  intro i hi
  rcases Nat.lt_or_ge i (j + 2) with h' | h'
  · exact h i (by omega)
  · have : i = j + 2 := by omega
    subst this
    exact period_prop hP (h j (by omega)) (h (j + 1) (Nat.le_refl _)) hnz

theorem period_at_most_doubles {P j : Nat} (hP : 0 < P) (h : CommonPer P (j + 1)) :
    ∀ t, E (j + 2) (t + (P + P)) = E (j + 2) t := by
  by_cases hnz : ∃ s, E (j + 1) s = true
  · have hp := period_prop hP (h j (by omega)) (h (j + 1) (Nat.le_refl _)) hnz
    intro t; rw [← Nat.add_assoc, hp, hp]
  · have hz : Zero (j + 1) := fun t => by
      cases e : E (j + 1) t
      · rfl
      · exact absurd ⟨t, e⟩ hnz
    intro t
    rw [acc_rs (g := E (j + 2)) (f := E j) (T := 0) (fun t _ => accumulate_after_zero hz t) t
      (Nat.zero_le _) (P + P), rs_double (h j (by omega))]
    cases E (j + 2) t <;> rfl

/-- **Bounded doubling point.** The doubling point is found by depth `2 ^ (2 P)`. -/
theorem doubling_point_bounded (P : Nat) (hP : 0 < P) :
    ∃ z, z ≤ 2 ^ (2 * P) ∧
      (Zero z ∧ CommonPer P z ∧ ¬ ∀ t, E (z + 1) (t + P) = E (z + 1) t) := by
  haveI : ∀ z, Decidable (Zero z) := fun z => inferInstanceAs (Decidable (∀ t, E z t = false))
  haveI : ∀ z, Decidable (CommonPer P z) := fun z =>
    inferInstanceAs (Decidable (∀ i, i ≤ z → ∀ t, E i (t + P) = E i t))
  refine Decidable.byContradiction fun hno => ?_
  have h1 : CommonPer P 1 := by
    intro i hi t
    rcases Nat.lt_or_ge i 1 with h | h
    · rw [show i = 0 by omega, E_zero', E_zero']
    · rw [show i = 1 by omega, E_one', E_one']
  have hall : ∀ j, j ≤ 2 ^ (2 * P) → CommonPer P (j + 1) := by
    intro j
    induction j with
    | zero => intro _; exact h1
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      by_cases hz : Zero (j + 1)
      · by_cases hper : ∀ t, E (j + 2) (t + P) = E (j + 2) t
        · intro i hi
          rcases Nat.lt_or_ge i (j + 2) with h' | h'
          · exact ih' i (by omega)
          · rw [show i = j + 2 by omega]; exact hper
        · exact absurd ⟨j + 1, hj, hz, ih', hper⟩ hno
      · exact period_passes hP ih' (nonzero_witness (j + 1) hz)
  exact common_period_fails_by P hP fun j hj t =>
    hall (2 ^ (2 * P)) (Nat.le_refl _) j (by omega) t

/-- **Doubling points.** For every `P > 0` some zero diagonal `z` has every diagonal up to `z`
`P`-periodic while diagonal `z + 1` is not. -/
theorem doubling_point (P : Nat) (hP : 0 < P) :
    ∃ z, Zero z ∧ CommonPer P z ∧ ¬ ∀ t, E (z + 1) (t + P) = E (z + 1) t := by
  obtain ⟨z, -, h⟩ := doubling_point_bounded P hP
  exact ⟨z, h⟩

/-! ### The compile bit is read off the real pattern -/

/-- A real diagonal with a last black cell is a zero diagonal of the zero-state. -/
theorem zero_of_last {j τ : Nat} (hlast : ∀ t, τ < t → D j t = false) : Zero j := by
  intro t
  rw [← E_per_mul j (τ + 1) t]
  unfold E
  have hX : 1 ≤ 2 ^ j := Nat.two_pow_pos _
  have : τ + 1 ≤ (τ + 1) * 2 ^ j := Nat.le_mul_of_pos_right _ hX
  exact hlast _ (by omega)

/-- **The compile bit.** Let `τ` (with diagonal `z` settled by `τ`) be the last black cell of the
real diagonal `z + 1`; by `zero_of_last`, `z + 1` is a zero diagonal. Then the real diagonal `z + 2` equals the
zero-state from time `τ + 1` on, and the free bit is `E (z + 2) (τ + 1) = !E z τ`. -/
theorem compile_bit {z τ : Nat} (hset : settle z ≤ τ)
    (hτ : D (z + 1) τ = true) (hlast : ∀ t, τ < t → D (z + 1) t = false) :
    (∀ t, τ < t → D (z + 2) t = E (z + 2) t) ∧ E (z + 2) (τ + 1) = !E z τ := by
  -- the real diagonal `z` is `2^z`-periodic from `τ` on
  have hDz : ∀ t, τ ≤ t → D z (t + 2 ^ z) = D z t := fun t ht => settle_spec z t (by omega)
  -- the real diagonal `z + 2` accumulates diagonal `z` after `τ`
  have hacc : ∀ t, τ + 1 ≤ t → D (z + 2) (t + 1) = xor (D z t) (D (z + 2) t) := by
    intro t ht; rw [D_step, hlast t (by omega)]; rfl
  have hper : ∀ t, τ + 1 ≤ t → D (z + 2) (t + 2 ^ (z + 2)) = D (z + 2) t := by
    intro t ht
    have e4 : 2 ^ (z + 2) = (2 ^ z + 2 ^ z) + (2 ^ z + 2 ^ z) := by rw [Nat.pow_add]; omega
    rw [acc_rs (g := D (z + 2)) (f := D z) (T := τ + 1) hacc t ht]
    -- the running sum over four periods vanishes
    have hf : ∀ s, (fun s => D z (s + t)) (s + 2 ^ z) = (fun s => D z (s + t)) s := by
      intro s; show D z (s + 2 ^ z + t) = D z (s + t)
      rw [show s + 2 ^ z + t = (s + t) + 2 ^ z by omega, hDz _ (by omega)]
    have shift : ∀ n m, rs (D z) (m + t) n = rs (fun s => D z (s + t)) m n := by
      intro n m
      induction n with
      | zero => rfl
      | succ n ih => simp only [rs]; rw [ih, show m + t + n = (m + n) + t by omega]
    have h0 := shift (2 ^ (z + 2)) 0
    rw [Nat.zero_add] at h0
    rw [h0, e4, rs_add, rs_double hf, rs_double hf]
    cases D (z + 2) t <;> rfl
  have heq : ∀ t, τ < t → D (z + 2) t = E (z + 2) t := by
    intro t ht
    unfold E
    have hpm : ∀ k, D (z + 2) (t + k * 2 ^ (z + 2)) = D (z + 2) t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show t + (k + 1) * 2 ^ (z + 2) = (t + k * 2 ^ (z + 2)) + 2 ^ (z + 2) by
          rw [Nat.succ_mul]; omega, hper _ (by omega), ih]
    rw [hpm]
  refine ⟨heq, ?_⟩
  rw [← heq (τ + 1) (by omega), D_step, hτ, E_eq_D z τ hset]
  cases D z τ <;> rfl

end Rule30UOR.CompilePoints

/-! ### Paper-facing statements -/

namespace Rule30UOR.CompilePoints

open Ruliology.CellularAutomata Rule30Diagonals Rule30UOR.Intent Rule30UOR.ZeroDiagonals

/-- An all-black diagonal of the zero-state. -/
def IsBlackDiag (b : Nat) : Prop := ∀ t, Rule30UOR.Intent.E b t = true

theorem black_after_zero_diag (z : Nat) (h : IsZeroDiag z) : IsBlackDiag (z + 2) :=
  black_after_zero h

theorem zero_before_black_diag (b : Nat) (h : IsBlackDiag (b + 2)) : IsZeroDiag b :=
  zero_before_black h

theorem zero_then_nonzero (z : Nat) (h : IsZeroDiag z) : ¬ IsZeroDiag (z + 1) :=
  fun h1 => no_adjacent_zero z ⟨h, h1⟩

/-- Every diagonal up to `z` has period `P` and diagonal `z + 1` does not. -/
def DoublesAt (P z : Nat) : Prop :=
  CommonPer P z ∧ ¬ ∀ t, Rule30UOR.Intent.E (z + 1) (t + P) = Rule30UOR.Intent.E (z + 1) t

theorem doubling_points (P : Nat) (h : 0 < P) : ∃ z, IsZeroDiag z ∧ DoublesAt P z := by
  obtain ⟨z, hz, hc, hn⟩ := doubling_point P h
  exact ⟨z, hz, hc, hn⟩

/-- The compile-bit law: the last black cell of a real diagonal fixes the free bit two diagonals
on. -/
def CompileBitLaw : Prop :=
  ∀ z τ : Nat, settle z ≤ τ → D (z + 1) τ = true → (∀ t, τ < t → D (z + 1) t = false) →
    Rule30UOR.Intent.E (z + 2) (τ + 1) = !Rule30UOR.Intent.E z τ

theorem compile_bit_law : CompileBitLaw :=
  fun _ _ hset hτ hlast => (compile_bit hset hτ hlast).2

/-! ### Antiperiodicity and reset around doubling compile points -/

theorem rs_succ_left (f : Nat → Bool) (t : Nat) : ∀ n,
    rs f (t + 1) n = xor (rs f t (n + 1)) (f t)
  | 0 => by
    simp only [rs, Nat.add_zero]
    cases f t <;> rfl
  | n + 1 => by
    change xor (rs f (t + 1) n) (f (t + 1 + n)) =
      xor (xor (rs f t (n + 1)) (f (t + (n + 1)))) (f t)
    rw [rs_succ_left f t n, show t + 1 + n = t + (n + 1) by omega]
    cases rs f t (n + 1) <;> cases f t <;> cases f (t + (n + 1)) <;> rfl

theorem rs_periodic_step {f : Nat → Bool} {P : Nat} (hf : ∀ t, f (t + P) = f t) (t : Nat) :
    rs f (t + 1) P = rs f t P := by
  rw [rs_succ_left f t P]
  simp only [rs, hf t]
  cases rs f t P <;> cases f t <;> rfl

theorem rs_periodic_const {f : Nat → Bool} {P : Nat} (hf : ∀ t, f (t + P) = f t) :
    ∀ t, rs f t P = rs f 0 P
  | 0 => rfl
  | t + 1 => by rw [rs_periodic_step hf t, rs_periodic_const hf t]

/-- **Antiperiodicity at a doubling zero diagonal**: if `z` is a zero diagonal where the common period `P` doubles (`DoublesAt P z`), then diagonal `z + 1` flips at every shift by `P`: `E (z + 1) (t + P) = !E (z + 1) t` for all `t`. -/
theorem antiperiodic_of_doubles (P z : Nat) (hz : IsZeroDiag z) (hd : DoublesAt P z) (t : Nat) :
    Rule30UOR.Intent.E (z + 1) (t + P) = !Rule30UOR.Intent.E (z + 1) t := by
  rcases z with _ | j
  · have h0 := hz 0
    rw [E_zero'] at h0
    exact absurd h0 (by decide)
  · obtain ⟨hc, hn⟩ := hd
    have hacc : ∀ s, 0 ≤ s → E (j + 2) (s + 1) = xor (E j s) (E (j + 2) s) :=
      fun s _ => accumulate_after_zero hz s
    have hrs : ∀ s, E (j + 2) (s + P) = xor (E (j + 2) s) (rs (E j) 0 P) := by
      intro s
      rw [acc_rs hacc s (Nat.zero_le s) P, rs_periodic_const (hc j (by omega)) s]
    have hodd : rs (E j) 0 P = true := by
      cases hrs0 : rs (E j) 0 P
      · exfalso
        apply hn
        intro s
        rw [hrs s, hrs0]
        cases E (j + 2) s <;> rfl
      · rfl
    rw [hrs t, hodd]
    cases E (j + 2) t <;> rfl

/-- **Exact reset behind an all-black diagonal**: if diagonal `b + 1` is all-black, then diagonal `b + 2` is the bitwise complement of diagonal `b` shifted by one time step (`E (b + 2) (t + 1) = !E b t`). -/
theorem reset_after_black (b : Nat) (hb : IsBlackDiag (b + 1)) (t : Nat) :
    Rule30UOR.Intent.E (b + 2) (t + 1) = !Rule30UOR.Intent.E b t := by
  rw [E_step b t, hb t, Bool.true_or]
  cases E b t <;> rfl

/-- **Three diagonals past a zero diagonal**: if `z` is a zero diagonal, then `z + 2` is all-black and `E (z + 3) (t + 1) = !E (z + 1) t` for all `t`. -/
theorem reset_three_after_zero (z : Nat) (hz : IsZeroDiag z) (t : Nat) :
    Rule30UOR.Intent.E (z + 3) (t + 1) = !Rule30UOR.Intent.E (z + 1) t :=
  reset_after_black (z + 1) (black_after_zero_diag z hz) t

/-- Diagonal `j` of the zero-state is antiperiodic of half-period `P` (`E j (t + P) = !E j t`). -/
def IsAntiperiodicDiag (P j : Nat) : Prop :=
  ∀ t, Rule30UOR.Intent.E j (t + P) = !Rule30UOR.Intent.E j t

theorem antiperiodic_after_doubles (P z : Nat) (hz : IsZeroDiag z) (hd : DoublesAt P z) :
    IsAntiperiodicDiag P (z + 1) :=
  antiperiodic_of_doubles P z hz hd

end Rule30UOR.CompilePoints
