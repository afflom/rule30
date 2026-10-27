module

public import Rule30ZeroState

/-!
# The frozen left structure is universal up to a 2-adic phase

Take any configuration that is white left of a black cell, and run rule 30 on it (any start, any
behaviour on the right: in particular the left half driven by any center column). Its left diagonals
are eventually periodic, and their eventual patterns are the single seed's, shifted in time.

* `rot_rigid`: if two configurations' diagonals `j`, `j + 1` agree eventually up to a time shift `a`,
  and diagonal `j + 1` is black infinitely often, diagonal `j + 2` agrees up to the same shift.
* `rot_zero`: behind an eventually white diagonal, if the next diagonal has an antiperiod `L`, the
  agreement continues with shift `a` or `a + L`. At a doubling zero diagonal the one free bit
  (`zero_diag_xor_const`) is a half-period rotation: one binary digit of a phase.
* `phase_universal`: **every configuration white left of a black cell agrees eventually, on every
  left diagonal of depth `≤ 401`, with the single seed's diagonal shifted by one time offset per
  consecutive pair.** The offsets change only at the doubling zero diagonals 2, 7, 28, 399, each
  time by the half period 1, 2, 4, 8: the phase is read in binary, one digit per doubling.

The frozen left structure carries no information about the driver beyond this phase.
-/

@[expose] public section

namespace Rule30Phase

open Ruliology.CellularAutomata
open Rule30Jen Rule30Diagonals Rule30FiniteDiagonals Rule30Realization Rule30ZeroState

/-- Eventual agreement of `f` with `g` shifted by `a`. -/
def EvRot (f g : Nat → Bool) (a : Nat) : Prop := ∃ T, ∀ t, T ≤ t → f t = g (t + a)

theorem rot_rigid {x y : Int → Bool} {lo lo' : Int} {j a : Nat}
    (h0 : EvRot (Ld y lo' j) (Ld x lo j) a) (h1 : EvRot (Ld y lo' (j + 1)) (Ld x lo (j + 1)) a)
    (hr : Recurrent (Ld x lo (j + 1))) : EvRot (Ld y lo' (j + 2)) (Ld x lo (j + 2)) a := by
  obtain ⟨T0, h0⟩ := h0
  obtain ⟨T1, h1⟩ := h1
  obtain ⟨s, hs, hst⟩ := hr (max T0 T1 + a)
  refine ⟨s - a + 1, fun t ht => ?_⟩
  refine agree_after_reset (x := Ld y lo' (j + 2)) (y := fun t => Ld x lo (j + 2) (t + a))
    (F := fun t b => xor (Ld y lo' j t) (Ld y lo' (j + 1) t || b)) (T := max T0 T1)
    (fun t _ => Ld_step j t)
    (fun t ht => by
      show Ld x lo (j + 2) (t + 1 + a) = _
      rw [show t + 1 + a = (t + a) + 1 by omega, Ld_step, h0 t (by omega), h1 t (by omega)])
    (show max T0 T1 ≤ s - a by omega) ?_ t (by omega)
  have : Ld y lo' (j + 1) (s - a) = true := by
    rw [h1 (s - a) (by omega), show s - a + a = s by omega]; exact hst
  simp [this]

theorem rot_zero {x y : Int → Bool} {lo lo' : Int} {j a L : Nat}
    (h0 : EvRot (Ld y lo' j) (Ld x lo j) a) (h1 : EvRot (Ld y lo' (j + 1)) (Ld x lo (j + 1)) a)
    (hz : EvEq (Ld x lo (j + 1)) (fun _ => false))
    (hanti : ∃ T, ∀ t, T ≤ t → Ld x lo (j + 2) (t + L) = !Ld x lo (j + 2) t) :
    ∃ b, (b = a ∨ b = a + L) ∧ EvRot (Ld y lo' (j + 2)) (Ld x lo (j + 2)) b := by
  obtain ⟨A, hA⟩ := h0
  obtain ⟨B, hB⟩ := h1
  obtain ⟨C, hC⟩ := hz
  simp only at hC
  obtain ⟨T, hT⟩ := hanti
  let M := max A (max B C)
  -- the two runs toggle by the same input from `M` on, so they differ by a constant
  have hconst : ∀ t, M ≤ t →
      xor (Ld y lo' (j + 2) t) (Ld x lo (j + 2) (t + a)) =
        xor (Ld y lo' (j + 2) M) (Ld x lo (j + 2) (M + a)) := by
    intro t ht
    induction t, ht using le_induction with
    | base => rfl
    | succ t ht ih =>
      have hy1 : Ld y lo' (j + 1) t = false := by rw [hB t (by omega)]; exact hC _ (by omega)
      have hx1 : Ld x lo (j + 1) (t + a) = false := hC _ (by omega)
      rw [show t + 1 + a = (t + a) + 1 by omega, Ld_step j t, Ld_step j (t + a), hy1, hx1,
        hA t (by omega), ← ih]
      cases Ld x lo j (t + a) <;> cases Ld y lo' (j + 2) t <;> cases Ld x lo (j + 2) (t + a) <;> rfl
  cases hc : xor (Ld y lo' (j + 2) M) (Ld x lo (j + 2) (M + a))
  · refine ⟨a, Or.inl rfl, M, fun t ht => ?_⟩
    have := hconst t ht
    rw [hc] at this
    revert this; cases Ld y lo' (j + 2) t <;> cases Ld x lo (j + 2) (t + a) <;> simp
  · refine ⟨a + L, Or.inr rfl, max M T, fun t ht => ?_⟩
    have := hconst t (by omega)
    rw [hc] at this
    show Ld y lo' (j + 2) t = Ld x lo (j + 2) (t + (a + L))
    rw [← Nat.add_assoc, hT (t + a) (by omega)]
    revert this; cases Ld y lo' (j + 2) t <;> cases Ld x lo (j + 2) (t + a) <;> simp

/-! ### The single seed as the reference -/

theorem Ld_seed (j t : Nat) : Ld seed 0 j t = D j t := by
  show evol seed t (0 - (t : Int) + (j : Int)) = cell t ((j : Int) - (t : Int))
  rw [evol_seed]; exact cell_congr (by omega)

theorem seed_edge : (∀ p : Int, p < 0 → seed p = false) ∧ seed 0 = true :=
  ⟨fun p hp => by simp [seed]; omega, by simp [seed]⟩

theorem pat_nonzero : (List.range 402).all (fun k =>
    k == 2 || k == 7 || k == 28 || k == 399 || (List.range 16).any (fun φ => pat k φ)) = true := by
  decide +kernel

theorem recurrent_D (k : Nat) (hk : k ≤ 401) (h2 : k ≠ 2) (h7 : k ≠ 7) (h28 : k ≠ 28)
    (h399 : k ≠ 399) : Recurrent (D k) := by
  have h := pat_nonzero
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨φ, hφ, hp⟩ : ∃ φ, φ < 16 ∧ pat k φ = true := by
    rcases h k (by omega) with ((((e | e) | e) | e) | e)
    all_goals first | omega | exact e
  intro T
  refine ⟨16 * (T + T0) + φ, by omega, ?_⟩
  rw [D_eq_pat _ (by unfold T0; omega) k hk, show (16 * (T + T0) + φ) % 16 = φ by omega]
  exact hp

/-- The eventual common period of the single seed's diagonals below depth `n` (to depth 401). -/
def pb (n : Nat) : Nat :=
  if n ≤ 2 then 1 else if n ≤ 7 then 2 else if n ≤ 28 then 4 else if n ≤ 399 then 8 else 16

theorem pb_mono (n : Nat) : pb (n + 1) ≤ pb (n + 2) := by
  unfold pb; repeat' split
  all_goals omega

/-- **The frozen left structure is universal up to a phase.** For every configuration `y` that is
white left of a black cell at `lo'`, every consecutive pair of left diagonals of depth `≤ 401`
agrees eventually with the single seed's pair shifted by one time offset. -/
theorem phase_universal {y : Int → Bool} {lo' : Int} (hy : ∀ p, p < lo' → y p = false)
    (hyl : y lo' = true) :
    ∀ n, n ≤ 400 → ∃ a, a < pb (n + 1) ∧
      EvRot (Ld y lo' n) (D n) a ∧ EvRot (Ld y lo' (n + 1)) (D (n + 1)) a := by
  have toD : ∀ j a, EvRot (Ld y lo' j) (Ld seed 0 j) a → EvRot (Ld y lo' j) (D j) a := by
    intro j a ⟨T, h⟩; exact ⟨T, fun t ht => by rw [h t ht, Ld_seed]⟩
  have ofD : ∀ j a, EvRot (Ld y lo' j) (D j) a → EvRot (Ld y lo' j) (Ld seed 0 j) a := by
    intro j a ⟨T, h⟩; exact ⟨T, fun t ht => by rw [h t ht, Ld_seed]⟩
  have recL : ∀ k, k ≤ 401 → k ≠ 2 → k ≠ 7 → k ≠ 28 → k ≠ 399 → Recurrent (Ld seed 0 k) := by
    intro k hk a b c d T
    obtain ⟨t, ht, h⟩ := recurrent_D k hk a b c d T
    exact ⟨t, ht, by rw [Ld_seed]; exact h⟩
  have zeroL : ∀ k, (k = 2 ∨ k = 7 ∨ k = 28 ∨ k = 399) → EvEq (Ld seed 0 k) (fun _ => false) := by
    intro k hk
    refine ⟨T0, fun t ht => ?_⟩
    rw [Ld_seed]
    have := zero_diagonals t ht
    rcases hk with rfl | rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2.1
    · exact this.2.2.2
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨u0, u1⟩ := universal seed_edge.1 seed_edge.2 hy hyl 0 (fun k hk => absurd hk (by omega))
    obtain ⟨A, hA⟩ := u0
    obtain ⟨B, hB⟩ := u1
    exact ⟨0, by unfold pb; simp, toD 0 0 ⟨A, fun t ht => (hA t ht).symm⟩,
      toD 1 0 ⟨B, fun t ht => (hB t ht).symm⟩⟩
  | succ n ih =>
    intro hn
    obtain ⟨a, ha, h0, h1⟩ := ih (by omega)
    by_cases hz : n + 1 = 2 ∨ n + 1 = 7 ∨ n + 1 = 28 ∨ n + 1 = 399
    · -- a doubling zero diagonal: the antiperiod of the next diagonal
      have hzL := zeroL (n + 1) hz
      have key : ∀ L, pb (n + 2) = 2 * pb (n + 1) → L = pb (n + 1) →
          (∃ T, ∀ t, T ≤ t → Ld seed 0 (n + 2) (t + L) = !Ld seed 0 (n + 2) t) →
          ∃ b, b < pb (n + 2) ∧ EvRot (Ld y lo' (n + 1)) (D (n + 1)) b ∧
            EvRot (Ld y lo' (n + 2)) (D (n + 2)) b := by
        intro L hpb hLe hL
        obtain ⟨b, hbab, hb⟩ := rot_zero (ofD n a h0) (ofD (n + 1) a h1) hzL hL
        refine ⟨b, by rcases hbab with rfl | rfl <;> omega, ?_, toD _ _ hb⟩
        obtain ⟨B, hB⟩ := h1
        obtain ⟨C, hC⟩ := hzL
        refine ⟨max B C, fun t ht => ?_⟩
        rw [hB t (by omega), ← Ld_seed, ← Ld_seed, hC _ (by omega), hC _ (by omega)]
      rcases hz with h | h | h | h
      · obtain rfl : n = 1 := by omega
        exact key 1 (by decide) (by decide) ⟨T0, fun t ht => by
          rw [Ld_seed, Ld_seed]; exact (antiperiods t ht).1⟩
      · obtain rfl : n = 6 := by omega
        exact key 2 (by decide) (by decide) ⟨T0, fun t ht => by
          rw [Ld_seed, Ld_seed]; exact (antiperiods t ht).2.1⟩
      · obtain rfl : n = 27 := by omega
        exact key 4 (by decide) (by decide) ⟨T0, fun t ht => by
          rw [Ld_seed, Ld_seed]; exact (antiperiods t ht).2.2.1⟩
      · obtain rfl : n = 398 := by omega
        exact key 8 (by decide) (by decide) ⟨T0, fun t ht => by
          rw [Ld_seed, Ld_seed]; exact (antiperiods t ht).2.2.2⟩
    · have hr := recL (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hmono : pb (n + 1) ≤ pb (n + 2) := pb_mono n
      exact ⟨a, Nat.lt_of_lt_of_le ha hmono, h1, toD _ _ (rot_rigid (ofD n a h0) (ofD (n + 1) a h1) hr)⟩

end Rule30Phase
