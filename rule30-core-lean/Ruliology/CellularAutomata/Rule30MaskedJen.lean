module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: masked, effective-boundary and window forms of Jen's theorem

Jen's adjacent-column theorem (`Rule30Jen.not_adjacent`) says that two adjacent columns of the
single-seed pattern are never both eventually periodic. Its proof rebuilds column `i - 1` from
columns `i` and `i + 1`, because rule 30 is left-permutive:

    cell t (i - 1) = cell (t + 1) i xor (cell t i || cell t (i + 1)).

Column `i + 1` enters only through `cell t i || cell t (i + 1)`, so it matters only at the times
when column `i` is white. This module states the sharper forms that follow.

* `masked_jen`: **masked Jen.** If column `i` has period `P` from time `T`, then column `i + 1`
  does not have period `P` from `T` on the white times of column `i`: it is false that
  `cell (t + P) (i + 1) = cell t (i + 1)` for every `t ≥ T` with `cell t i = false`.
  `masked_jen_center` and `center_masked_not_eventually_periodic` are the case `i = 0`.
* `orCol_not_eventuallyPeriodic`: the same in `or` form. If column `i` is eventually periodic,
  then `orCol i = column i || column (i + 1)` is not.
* `left_of_black`, `left_of_white`: column `i - 1` at a black or a white cell of column `i`.
* `effective_boundary`, `effective_step`: **effective boundary.** The left half sees the center
  column `c` only through `c t && c (t + 1)`:
  `cell t (-1) || c t = cell t (-1) || (c t && c (t + 1))`, hence
  `cell (t + 1) (-1) = rule (cell t (-2)) (cell t (-1)) (c t && c (t + 1))`.
  If `c` alternates from some time on, this effective boundary is white from then on.
* `determine`, `window_jen`, `window_jen_col`: **window form, no periodicity assumed.** Two times
  `t₁ < t₂` never carry the same values of column `0` on `[t, t + t₂]` and of `orCol 0` on
  `[t, t + t₂)` (for `t = t₁` and `t = t₂`). Otherwise the reconstruction would make the cell at
  `-t₂` white at time `t₁` (left of the edge) and black at time `t₂` (on the edge).
* `periodic_window`: **doubling window.** If the center column has period `P` from `T`, every
  interval `[n, 2n)` with `n ≥ T + P` contains a time `s` with `c s = false` and
  `cell s 1 ≠ cell (s - P) 1`.
* `finitary_jen`: for `0 < P ≤ n`, the center column and `orCol 0` are never both `P`-periodic
  on the whole interval `[n - P, 2n]`.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242, for the
adjacent-column argument; the masked, effective-boundary and window forms refine it.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30MaskedJen

open Rule30Jen Rule30Prize

/-! ### Column `i - 1` from columns `i` and `i + 1` -/

/-- Where column `i` is black, column `i - 1` is forced by the next value of column `i`. -/
theorem left_of_black (t : Nat) (i : Int) (h : cell t i = true) :
    cell t (i - 1) = !cell (t + 1) i := by
  rw [cell_left, h]
  cases cell (t + 1) i <;> rfl

/-- Where column `i` is white, column `i - 1` is `cell (t + 1) i xor cell t (i + 1)`. -/
theorem left_of_white (t : Nat) (i : Int) (h : cell t i = false) :
    cell t (i - 1) = xor (cell (t + 1) i) (cell t (i + 1)) := by
  rw [cell_left, h]
  rfl

/-! ### Masked Jen -/

/-- **Masked Jen.** If column `i` has period `P` from time `T`, column `i + 1` does not have
period `P` from `T` on the white times of column `i`. -/
theorem masked_jen (i : Int) {T P : Nat} (hP : 0 < P)
    (h0 : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + P) (i + 1) = cell t (i + 1)) : False := by
  have hm1 : ∀ t, T ≤ t → cell (t + P) (i - 1) = cell t (i - 1) := by
    intro t ht
    rw [cell_left, cell_left t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
      h0 t ht]
    cases hc : cell t i
    · rw [h1 t ht hc]
    · rfl
  refine not_adjacent (i - 1) ⟨T, P, hP, hm1⟩ ⟨T, P, hP, ?_⟩
  rw [show i - 1 + 1 = i by omega]
  exact h0

/-- **Masked Jen at the center**, from any start: if the center column has period `P` from `T`,
then for every `T'` column `1` is not `P`-periodic from `T'` on the white times of the center. -/
theorem masked_jen_center {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (T' : Nat) :
    ¬ ∀ t, T' ≤ t → cell t 0 = false → cell (t + P) 1 = cell t 1 := by
  intro h1
  exact masked_jen 0 (T := max T T') hP (fun t ht => hc t (by omega))
    (fun t ht hw => h1 t (by omega) hw)

/-- The masked pair `(c t, column 1 at the white times of c)` is not eventually periodic. -/
theorem center_masked_not_eventually_periodic :
    ¬ ∃ T Q : Nat, 0 < Q ∧ ∀ t, T ≤ t →
      cell (t + Q) 0 = cell t 0 ∧ (cell t 0 = false → cell (t + Q) 1 = cell t 1) := by
  rintro ⟨T, Q, hQ, h⟩
  exact masked_jen 0 hQ (fun t ht => (h t ht).1) (fun t ht hc => by simpa using (h t ht).2 hc)

/-! ### The `or` column -/

/-- `column i || column (i + 1)`: everything the left-permutive reconstruction uses of column
`i + 1`. -/
def orCol (i : Int) (t : Nat) : Bool := cell t i || cell t (i + 1)

theorem cell_left' (t : Nat) (i : Int) : cell t (i - 1) = xor (cell (t + 1) i) (orCol i t) :=
  cell_left t i

/-- **Masked Jen, `or` form.** If column `i` is eventually periodic, `orCol i` is not. -/
theorem orCol_not_eventuallyPeriodic (i : Int) (hc : EventuallyPeriodic fun t => cell t i) :
    ¬ EventuallyPeriodic fun t => orCol i t := by
  intro he
  obtain ⟨T, P, hP, hpc, hpe⟩ := common_period hc he
  refine not_adjacent (i - 1) ⟨T, P, hP, fun t ht => ?_⟩
    (by rw [show i - 1 + 1 = i by omega]; exact hc)
  show cell (t + P) (i - 1) = cell t (i - 1)
  rw [cell_left', cell_left', show t + P + 1 = (t + 1) + P by omega]
  have h1 : cell ((t + 1) + P) i = cell (t + 1) i := hpc (t + 1) (by omega)
  have h2 : orCol i (t + P) = orCol i t := hpe t ht
  rw [h1, h2]

/-! ### The effective boundary of the left half -/

/-- **Effective boundary.** The left half sees the center column only through
`c t && c (t + 1)`. -/
theorem effective_boundary (t : Nat) :
    (cell t (-1) || center t) = (cell t (-1) || (center t && center (t + 1))) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center
  rw [hl]
  cases cell (t + 1) 0 <;> cases cell t 0 <;> cases cell t (0 + 1) <;> rfl

/-- Column `-1` evolves with the effective boundary `c t && c (t + 1)` in place of `c t`. -/
theorem effective_step (t : Nat) :
    cell (t + 1) (-1) = rule (cell t (-2)) (cell t (-1)) (center t && center (t + 1)) := by
  show rule (cell t (-1 - 1)) (cell t (-1)) (cell t (-1 + 1)) = _
  rw [show (-1 : Int) - 1 = -2 by rfl, show (-1 : Int) + 1 = 0 by rfl]
  unfold rule
  rw [show cell t 0 = center t from rfl, effective_boundary]

/-! ### Window forms: no periodicity assumed -/

/-- **Determination lemma.** If column `i` agrees at times `t₁ + s`, `t₂ + s` for `s ≤ m`, and
`orCol i` agrees for `s < m`, then column `i - k` agrees for `s + k ≤ m`. -/
theorem determine {t₁ t₂ : Nat} {i : Int} (m : Nat)
    (hc : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (he : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) :
    ∀ k s, s + k ≤ m → cell (t₁ + s) (i - k) = cell (t₂ + s) (i - k) ∧
      (s + k < m → orCol (i - k) (t₁ + s) = orCol (i - k) (t₂ + s)) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [show i - ((0 : Nat) : Int) = i by omega]
    exact ⟨hc s (by omega), fun h => he s (by omega)⟩
  | succ k ih =>
    intro s hs
    have hA : cell (t₁ + s) (i - ((k + 1 : Nat) : Int)) =
        cell (t₂ + s) (i - ((k + 1 : Nat) : Int)) := by
      have e : i - ((k + 1 : Nat) : Int) = (i - (k : Int)) - 1 := by omega
      rw [e, cell_left', cell_left', show t₁ + s + 1 = t₁ + (s + 1) by omega,
        show t₂ + s + 1 = t₂ + (s + 1) by omega, (ih (s + 1) (by omega)).1,
        (ih s (by omega)).2 (by omega)]
    refine ⟨hA, fun h => ?_⟩
    have hB := (ih s (by omega)).1
    unfold orCol
    rw [hA, show i - ((k + 1 : Nat) : Int) + 1 = i - (k : Int) by omega, hB]

/-- **Window form of Jen's theorem.** No periodicity is assumed: two times `t₁ < t₂` never carry
the same (center column, `orCol 0`) window of length `t₂`. -/
theorem window_jen {t₁ t₂ : Nat} (h : t₁ < t₂)
    (hc : ∀ s, s ≤ t₂ → cell (t₁ + s) 0 = cell (t₂ + s) 0)
    (he : ∀ s, s < t₂ → orCol 0 (t₁ + s) = orCol 0 (t₂ + s)) : False := by
  have key := (determine (i := 0) t₂ hc he t₂ 0 (by omega)).1
  simp only [Nat.add_zero, Int.zero_sub] at key
  rw [cell_eq_false_of_lt t₁ (-(t₂ : Int)) (by omega), cell_left_edge t₂] at key
  exact absurd key (by decide)

/-- The window form for any column `i`: two times `t₁ < t₂` never carry the same
(column `i`, `orCol i`) window of length `m` when `i - m = -t₂`. -/
theorem window_jen_col {t₁ t₂ : Nat} {i : Int} (m : Nat) (h : t₁ < t₂)
    (hm : i - (m : Int) = -(t₂ : Int))
    (hc : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (he : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) : False := by
  have key := (determine m hc he m 0 (by omega)).1
  simp only [Nat.add_zero] at key
  rw [hm, cell_eq_false_of_lt t₁ (-(t₂ : Int)) (by omega), cell_left_edge t₂] at key
  exact absurd key (by decide)

/-- **Doubling window.** If the center column has period `P` from `T`, every interval `[n, 2n)`
with `n ≥ T + P` contains a time where the center is white and column 1 breaks period `P`. -/
theorem periodic_window {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (n : Nat) (hn : T + P ≤ n) :
    ∃ s, n ≤ s ∧ s < 2 * n ∧ cell s 0 = false ∧ cell s 1 ≠ cell (s - P) 1 := by
  refine Classical.byContradiction fun hne => ?_
  refine window_jen (t₁ := n - P) (t₂ := n) (by omega) (fun s _ => ?_) (fun s hs => ?_)
  · have := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · have hper := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at hper
    unfold orCol
    rw [hper]
    cases h0 : cell (n - P + s) 0
    · have h0' : cell (n + s) 0 = false := hper.trans h0
      have h1 : cell (n + s) 1 = cell (n + s - P) 1 :=
        Classical.byContradiction fun h1 => hne ⟨n + s, by omega, by omega, h0', h1⟩
      rw [show n + s - P = n - P + s by omega] at h1
      simp only [Int.zero_add, Bool.false_or, h1]
    · rfl

/-- **Finitary Jen.** For `0 < P ≤ n`, the center column and `orCol 0` are never both
`P`-periodic on the whole time interval `[n - P, 2n]`. -/
theorem finitary_jen {P n : Nat} (hP : 0 < P) (hn : P ≤ n)
    (hc : ∀ x, n - P ≤ x → x + P ≤ 2 * n → cell (x + P) 0 = cell x 0)
    (he : ∀ x, n - P ≤ x → x + P < 2 * n → orCol 0 (x + P) = orCol 0 x) : False := by
  refine window_jen (t₁ := n - P) (t₂ := n) (by omega) (fun s hs => ?_) (fun s hs => ?_)
  · have := hc (n - P + s) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · have := he (n - P + s) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm

end Rule30MaskedJen
end Ruliology.CellularAutomata
