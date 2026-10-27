module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Every diagonal of rule 30 is periodic

The rule-30 pattern from a single black cell, read along diagonals parallel to its two edges:

* `R j t = cell t (t − j)`, the `j`-th diagonal from the right edge, and
* `D j t = cell t (j − t)`, the `j`-th diagonal from the left edge.

Both families obey a recurrence that feeds each diagonal from the two before it:

    R_{j+2}(t + 1) = R_{j+2}(t) xor (R_{j+1}(t) or R_j(t))
    D_{j+2}(t + 1) = D_j(t) xor (D_{j+1}(t) or D_{j+2}(t))

* `R_periodic`: **every right diagonal is periodic from the start**, with period `2^j`. The
  diagonal accumulates the parity of its input, and a periodic input adds the same parity over
  each period, so two periods return to the start.
* `D_periodic`: **every left diagonal is eventually periodic**, with period `2^j`. A one-bit state
  driven by an eventually periodic input: among the three states one and two input periods apart,
  two agree, and from then on they agree forever.
* `center_eq_parity`: unrolling the right-diagonal recurrence, the center cell at time `t ≥ 2` is
  the parity of the number of rows `s < t` with a black cell at `s − t + 1` or `s − t + 2`.

The center column is the diagonal of diagonals: `center t = R t t = D t t`
(`center_eq_R`, `center_eq_D`). The period bound `2^j` exceeds `j`, so these theorems say nothing
about the center column. Wolfram notes the left-side periods grow very slowly and the right-side
ones exponentially; Rowland (*Local Nested Structure in Rule 30*, Complex Systems 16 (2006))
proves the left-side period doubling.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Diagonals

open Rule30Jen

/-- The `j`-th diagonal from the right edge. -/
def R (j t : Nat) : Bool := cell t ((t : Int) - j)

/-- The `j`-th diagonal from the left edge. -/
def D (j t : Nat) : Bool := cell t ((j : Int) - t)

theorem center_eq_R (t : Nat) : cell t 0 = R t t := by simp [R]

theorem center_eq_D (t : Nat) : cell t 0 = D t t := by simp [D]

/-! ### Local rule, with positions up to arithmetic -/

theorem cell_congr {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

theorem cell_succ' (t : Nat) (p a b c : Int) (ha : a = p - 1) (hb : b = p) (hc : c = p + 1) :
    cell (t + 1) p = rule (cell t a) (cell t b) (cell t c) := by
  subst ha hb hc; rfl

theorem cell_eq_false_of_gt : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_gt t (p - 1) (by omega), cell_eq_false_of_gt t p (by omega),
      cell_eq_false_of_gt t (p + 1) (by omega)]
    rfl

/-! ### The right edge -/

/-- The rightmost black cell is at `t`. -/
theorem R_zero : ∀ t, R 0 t = true
  | 0 => rfl
  | t + 1 => by
    have e : R 0 (t + 1) = rule (R 0 t) (cell t ((t : Int) + 1)) (cell t ((t : Int) + 2)) :=
      cell_succ' t _ _ _ _ (by omega) (by omega) (by omega)
    rw [e, R_zero t, cell_eq_false_of_gt t _ (by omega), cell_eq_false_of_gt t _ (by omega)]
    rfl

theorem R_one_succ (t : Nat) : R 1 (t + 1) = !R 1 t := by
  have e : R 1 (t + 1) = rule (R 1 t) (R 0 t) (cell t ((t : Int) + 1)) :=
    cell_succ' t _ _ _ _ (by omega) (by omega) (by omega)
  rw [e, R_zero t, cell_eq_false_of_gt t _ (by omega)]
  cases R 1 t <;> rfl

theorem R_step (j t : Nat) : R (j + 2) (t + 1) = xor (R (j + 2) t) (R (j + 1) t || R j t) :=
  cell_succ' t _ _ _ _ (by omega) (by omega)
    (by omega)

/-! ### Periodicity of the right diagonals -/

/-- A sequence that accumulates the parity of a periodic input is periodic with twice the
period. -/
theorem xor_accum_periodic {x g : Nat → Bool} {L : Nat} (hx : ∀ t, x (t + 1) = xor (x t) (g t))
    (hg : ∀ t, g (t + L) = g t) : ∀ t, x (t + 2 * L) = x t := by
  -- `h t` is the parity that one period adds; it does not depend on `t`
  have hconst : ∀ t, xor (x (t + L)) (x t) = xor (x L) (x 0) := by
    intro t
    induction t with
    | zero => rw [Nat.zero_add]
    | succ t ih =>
      rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L), hx t, hg t, ← ih]
      cases x (t + L) <;> cases x t <;> cases g t <;> rfl
  intro t
  have h1 := hconst t
  have h2 := hconst (t + L)
  rw [show t + L + L = t + 2 * L by omega] at h2
  revert h1 h2
  cases x (t + 2 * L) <;> cases x (t + L) <;> cases x t <;> cases xor (x L) (x 0) <;> simp

theorem periodic_double {f : Nat → Bool} {L : Nat} (h : ∀ t, f (t + L) = f t) :
    ∀ t, f (t + 2 * L) = f t := by
  intro t; rw [show t + 2 * L = (t + L) + L by omega, h, h]

/-- **Every right diagonal is periodic from the start, with period `2^j`.** -/
theorem R_periodic : ∀ j t, R j (t + 2 ^ j) = R j t := by
  have pair : ∀ j, (∀ t, R j (t + 2 ^ j) = R j t) ∧ (∀ t, R (j + 1) (t + 2 ^ (j + 1)) = R (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun t => by rw [R_zero, R_zero], fun t => ?_⟩
      rw [show t + 2 ^ (0 + 1) = (t + 1) + 1 by simp, R_one_succ, R_one_succ]
      cases R 1 t <;> rfl
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hg : ∀ t, (R (j + 1) (t + 2 ^ (j + 1)) || R j (t + 2 ^ (j + 1))) =
          (R (j + 1) t || R j t) := by
        intro t
        rw [ih.2 t, show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ]; omega,
          periodic_double ih.1 t]
      have := xor_accum_periodic (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t)
        (L := 2 ^ (j + 1)) (fun t => R_step j t) hg
      intro t
      rw [show 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact this t
  exact fun j => (pair j).1

/-! ### The left edge and the left diagonals -/

/-- The leftmost black cell is at `−t`. -/
theorem D_zero (t : Nat) : D 0 t = true := by
  have e : D 0 t = cell t (-(t : Int)) := cell_congr (by omega)
  rw [e]; exact cell_left_edge t

theorem D_one (t : Nat) : D 1 (t + 1) = true := by
  have e : D 1 (t + 1) = rule (cell t (-(t : Int) - 1)) (D 0 t) (D 1 t) :=
    cell_succ' t _ _ _ _ (by omega) (by omega)
      (by omega)
  rw [e, D_zero t, cell_eq_false_of_lt t _ (by omega)]
  rfl

theorem D_step (j t : Nat) : D (j + 2) (t + 1) = xor (D j t) (D (j + 1) t || D (j + 2) t) :=
  cell_succ' t _ _ _ _ (by omega) (by omega)
    (by omega)

/-- A one-bit state driven by an eventually periodic transition is eventually periodic with
twice the period. Among the states `L` and `2L` steps after `T`, two agree, and two runs of the
same recurrence that agree once agree from then on. -/
theorem transducer_periodic {x : Nat → Bool} {F : Nat → Bool → Bool} {T L : Nat}
    (hx : ∀ t, T ≤ t → x (t + 1) = F t (x t)) (hF : ∀ t, T ≤ t → F (t + L) = F t) :
    ∀ t, T + L ≤ t → x (t + 2 * L) = x t := by
  have hFk : ∀ k t, T ≤ t → F (t + k * L) = F t := by
    intro k
    induction k with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      rw [show t + (k + 1) * L = (t + k * L) + L by rw [Nat.succ_mul]; omega,
        hF _ (by omega), ih t ht]
  -- runs started `a` and `b` periods after `T` that agree once agree forever
  have agree : ∀ a b, x (T + a * L) = x (T + b * L) →
      ∀ s, x (T + a * L + s) = x (T + b * L + s) := by
    intro a b hab s
    induction s with
    | zero => exact hab
    | succ s ih =>
      rw [← Nat.add_assoc, ← Nat.add_assoc, hx _ (by omega), hx _ (by omega),
        show T + a * L + s = (T + s) + a * L by omega, show T + b * L + s = (T + s) + b * L by omega,
        hFk a (T + s) (by omega), hFk b (T + s) (by omega)]
      rw [show (T + s) + a * L = T + a * L + s by omega,
        show (T + s) + b * L = T + b * L + s by omega, ih]
  intro t ht
  -- pigeonhole on the three states at `T`, `T + L`, `T + 2L`
  have h01 := agree 0 1; have h12 := agree 1 2; have h02 := agree 0 2
  simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] at h01 h12 h02
  have pig : x T = x (T + L) ∨ x (T + L) = x (T + 2 * L) ∨ x T = x (T + 2 * L) := by
    cases x T <;> cases x (T + L) <;> cases x (T + 2 * L) <;> simp
  rcases pig with e | e | e
  · have hA := h01 e (t - T)
    have hB := h01 e (t - T + L)
    rw [show T + (t - T) = t by omega, show T + L + (t - T) = t + L by omega] at hA
    rw [show T + (t - T + L) = t + L by omega, show T + L + (t - T + L) = t + 2 * L by omega] at hB
    rw [← hB, ← hA]
  · have hA := h12 e (t - T - L)
    have hB := h12 e (t - T)
    rw [show T + L + (t - T - L) = t by omega, show T + 2 * L + (t - T - L) = t + L by omega] at hA
    rw [show T + L + (t - T) = t + L by omega, show T + 2 * L + (t - T) = t + 2 * L by omega] at hB
    rw [← hB, ← hA]
  · have h := h02 e (t - T)
    rw [show T + (t - T) = t by omega, show T + 2 * L + (t - T) = t + 2 * L by omega] at h
    exact h.symm

/-- **Every left diagonal is eventually periodic, with period `2^j`.** -/
theorem D_periodic : ∀ j, ∃ T, ∀ t, T ≤ t → D j (t + 2 ^ j) = D j t := by
  have pair : ∀ j, (∃ T, ∀ t, T ≤ t → D j (t + 2 ^ j) = D j t) ∧
      (∃ T, ∀ t, T ≤ t → D (j + 1) (t + 2 ^ (j + 1)) = D (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨0, fun t _ => by rw [D_zero, D_zero]⟩, ⟨1, fun t ht => ?_⟩⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [show s + 1 + 2 ^ (0 + 1) = (s + 2) + 1 by simp, D_one, D_one]
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨⟨Ta, ha⟩, ⟨Tb, hb⟩⟩ := ih
      have hp := Nat.two_pow_pos j
      have ha2 : ∀ t, Ta ≤ t → D j (t + 2 ^ (j + 1)) = D j t := by
        intro t ht
        rw [show t + 2 ^ (j + 1) = (t + 2 ^ j) + 2 ^ j by rw [Nat.pow_succ]; omega,
          ha _ (by omega), ha t ht]
      refine ⟨max Ta Tb + 2 ^ (j + 1), fun t ht => ?_⟩
      have := transducer_periodic (x := D (j + 2))
        (F := fun t b => xor (D j t) (D (j + 1) t || b)) (T := max Ta Tb) (L := 2 ^ (j + 1))
        (fun t _ => D_step j t)
        (fun t ht => by
          funext b
          rw [ha2 t (by omega), hb t (by omega)])
        t (by omega)
      rw [show 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact this
  exact fun j => (pair j).1

/-! ### The center column as a parity -/

theorem parity_succ (n : Nat) : ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (n + 1) % 2 = 0 := by omega
    simp [h, h']

/-- A sequence that starts at `false` and accumulates `g` is the parity of the number of times
`g` was true. -/
theorem xor_accum_parity {x g : Nat → Bool} (h0 : x 0 = false)
    (hx : ∀ t, x (t + 1) = xor (x t) (g t)) :
    ∀ t, x t = (((List.range t).filter g).length % 2 == 1) := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rw [hx t, ih, List.range_succ, List.filter_append, List.length_append]
    cases hg : g t
    · simp [hg]
    · simp only [List.filter_cons, hg, ↓reduceIte, List.filter_nil, List.length_cons,
        List.length_nil, Nat.zero_add, Bool.xor_true]
      exact (parity_succ _).symm

/-- Each right diagonal (from the third on) is the parity of how often one of the two diagonals
before it was black. -/
theorem R_eq_parity (j t : Nat) :
    R (j + 2) t = (((List.range t).filter (fun s => R (j + 1) s || R j s)).length % 2 == 1) :=
  xor_accum_parity (x := R (j + 2)) (by simp [R, cell]; omega) (fun t => R_step j t) t

/-- **The center column as a parity**: for `t ≥ 2`, the center cell at time `t` is black exactly
when an odd number of earlier rows `s < t` have a black cell at position `s − t + 1` or
`s − t + 2`. -/
theorem center_eq_parity (t : Nat) (ht : 2 ≤ t) :
    cell t 0 = (((List.range t).filter
      (fun s => cell s ((s : Int) - t + 1) || cell s ((s : Int) - t + 2))).length % 2 == 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 2 := ⟨t - 2, by omega⟩
  rw [center_eq_R, R_eq_parity]
  congr 3
  apply List.filter_congr
  intro s _
  rw [cell_congr (show (s : Int) - ((j + 2 : Nat) : Int) + 1 = (s : Int) - ((j + 1 : Nat) : Int)
      by omega),
    cell_congr (show (s : Int) - ((j + 2 : Nat) : Int) + 2 = (s : Int) - (j : Int) by omega)]
  rfl

end Rule30Diagonals
end Ruliology.CellularAutomata
