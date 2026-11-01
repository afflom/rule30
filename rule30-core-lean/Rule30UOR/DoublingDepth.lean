module
public import Rule30UOR.Interfaces
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Doubling depth, and Route B (`single-row-agreement`) decided

`DoublesAt Q z` says the zero-state diagonals `0..z` are `Q`-periodic and diagonal `z + 1` is not.
Diagonal `j` of the zero state has period `2^j` (`ZeroDiagonals.E_per_mul`), and this file reads
off the consequences.

* `doublesAt_not_twopow_succ_dvd` and `le_of_doublesAt_mul_twopow`: a doubling of a lag `Q` sits
  strictly beyond diagonal `v₂(Q)`. For a lag `w * 2^K`, the doubling diagonal satisfies `K ≤ z`.
* `doublesAt_odd_mul_iff`: the doubling diagonal depends only on the 2-adic part of the lag.
  `doublesAt_unique` and `doublesAt_odd_mul_twopow_eq` follow, and so does the monotonicity
  `doublesAt_mul_le` along multiples. `doublesAt_two_mul_lt`: doubling the lag moves the doubling
  diagonal strictly outward. `isZeroDiag_of_doublesAt`: a doubling always sits on a zero diagonal,
  so the `IsZeroDiag z` hypothesis of the doubling engines is implied by `DoublesAt Q z` with
  `Q > 0`. Measured: the doubling diagonals of `2^0, …, 2^3` are `2, 7, 28, 399`.
* Route B, scale clause. `two_scale_prefix_scale_doubles_unsat` is the prefix form of 9.1562–9.1565:
  the doubling hypothesis `DoublesAt ((c * 2^K) * P) z` contradicts the scale clause
  `(z + (p + 1)) + p ≤ K`. `two_scale_corridor_scale_doubles_unsat` is the corridor form of 9.1496,
  its `rdrv` sibling and Part16's `not_centerPeriodic_of_two_scale_single_row_at_zero_diag_doubles`:
  the same doubling hypothesis contradicts `((z + (p + 1)) + S) + 1 ≤ K`.
* Route B, tail clause: `rhRowTailDefect_of_doubles` and `rdrvRowTailDefect_of_doubles`. The tail
  window of the two-scale right-half row carries a lag-`Q` spatial defect at every doubling zero
  diagonal. This needs no period, no prefix and no `K`. It is 9.1572 moved into the dyadic row, so the
  tail hypothesis `htail` of 9.1563/9.1565 is false wherever its side conditions hold.
* Audits: `two_scale_single_rh_row_tail_hypotheses_unsat` and
  `two_scale_single_rdrv_row_tail_hypotheses_unsat` refute the tail clause.
  `two_scale_single_rh_row_engine_hypotheses_unsat` and
  `two_scale_single_rdrv_row_engine_hypotheses_unsat` show that the whole hypothesis bundle of
  9.1563/9.1565, minus `CenterPeriodic`, is unsatisfiable (9.1562/9.1564, then 9.1571).
-/

@[expose] public section

namespace Rule30UOR.DoublingDepth

open Rule30UOR.Core
open Rule30UOR.ZeroDiagonals (IsZeroDiag)
open Rule30UOR.CompilePoints (DoublesAt)
open Rule30UOR.Interfaces (rhCenter rdrv SettledUpTo LhBandAgree)

/-! ## Where a doubling sits -/

/-- Diagonal `i` of the zero state is `Q`-periodic. -/
def DiagPer (Q i : Nat) : Prop := ∀ t, Rule30UOR.Intent.E i (t + Q) = Rule30UOR.Intent.E i t

/-- A period passes to its multiples. -/
theorem diagPer_mul (Q i m : Nat) (h : DiagPer Q i) : DiagPer (m * Q) i := by
  induction m with
  | zero => intro t; rw [Nat.zero_mul, Nat.add_zero]
  | succ m ih =>
    intro t
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, h (t + m * Q)]
    exact ih t

/-- Odd multiples of a lag do not change the periodicity of a zero-state diagonal: diagonal `i`
    is `2^i`-periodic, and an odd `w` is invertible modulo `2^i`. -/
theorem diagPer_of_odd_mul (w Q i : Nat) (hw : w % 2 = 1) (h : DiagPer (w * Q) i) :
    DiagPer Q i := by
  have hinv : ∀ n : Nat, ∃ m k : Nat, w * m = 1 + k * 2 ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, w - 1, by rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one]; cfomega⟩
    | succ n ih =>
      obtain ⟨m, k, hmk⟩ := ih
      have hk2 := Nat.div_add_mod k 2
      have hkw := Nat.div_add_mod (k + w) 2
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · refine ⟨m, k / 2, ?_⟩
        have e : k = (k / 2) * 2 := by cfomega
        calc w * m = 1 + k * 2 ^ n := hmk
          _ = 1 + ((k / 2) * 2) * 2 ^ n := by rw [← e]
          _ = 1 + (k / 2) * 2 ^ (n + 1) := by
            rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ n)]
      · refine ⟨m + 2 ^ n, (k + w) / 2, ?_⟩
        have e : k + w = 2 * ((k + w) / 2) := by cfomega
        calc w * (m + 2 ^ n) = w * m + w * 2 ^ n := Nat.mul_add w m (2 ^ n)
          _ = 1 + (k + w) * 2 ^ n := by rw [hmk, Nat.add_mul, Nat.add_assoc]
          _ = 1 + ((k + w) / 2) * 2 ^ (n + 1) := by
            rw [e, Nat.mul_div_cancel_left ((k + w) / 2) (by cfomega : 0 < 2), Nat.pow_succ,
              Nat.mul_comm 2 ((k + w) / 2), Nat.mul_assoc, Nat.mul_comm 2 (2 ^ n)]
  obtain ⟨m, k, hmk⟩ := hinv i
  intro t
  have e1 : m * (w * Q) = Q * (w * m) := by
    rw [Nat.mul_comm m (w * Q), Nat.mul_comm w Q, Nat.mul_assoc]
  have e2 : Q * (w * m) = Q + (k * Q) * 2 ^ i := by
    rw [hmk, Nat.mul_add, Nat.mul_one, Nat.mul_comm k Q, Nat.mul_assoc]
  have e : (t + Q) + (k * Q) * 2 ^ i = t + m * (w * Q) := by
    rw [e1, e2, Nat.add_assoc]
  rw [← Rule30UOR.ZeroDiagonals.E_per_mul i (k * Q) (t + Q), e]
  exact diagPer_mul (w * Q) i m h t

/-- The doubling diagonal of a lag is unique. -/
theorem doublesAt_unique (Q z y : Nat) (hz : DoublesAt Q z) (hy : DoublesAt Q y) : z = y := by
  rcases Nat.lt_or_ge z y with h | h
  · exact absurd (hy.1 (z + 1) (by cfomega)) hz.2
  · rcases Nat.lt_or_ge y z with h2 | h2
    · exact absurd (hz.1 (y + 1) (by cfomega)) hy.2
    · cfomega

/-- The doubling diagonal depends only on the 2-adic part of the lag. -/
theorem doublesAt_odd_mul_iff (w Q z : Nat) (hw : w % 2 = 1) :
    DoublesAt (w * Q) z ↔ DoublesAt Q z := by
  constructor
  · intro h
    exact ⟨fun i hi t => diagPer_of_odd_mul w Q i hw (h.1 i hi) t,
      fun hper => h.2 (diagPer_mul Q (z + 1) w hper)⟩
  · intro h
    exact ⟨fun i hi t => diagPer_mul Q i w (h.1 i hi) t,
      fun hper => h.2 (diagPer_of_odd_mul w Q (z + 1) hw hper)⟩

/-- For an odd `w`, the lags `w * 2^K` and `2^K` double on the same diagonal. -/
theorem doublesAt_odd_mul_twopow_eq (w K z y : Nat) (hw : w % 2 = 1)
    (hz : DoublesAt (w * twopow K) z) (hy : DoublesAt (twopow K) y) : z = y :=
  doublesAt_unique (twopow K) z y ((doublesAt_odd_mul_iff w (twopow K) z hw).mp hz) hy

/-- The doubling diagonal is monotone along multiples of the lag. -/
theorem doublesAt_mul_le (m Q z y : Nat) (hz : DoublesAt Q z) (hy : DoublesAt (m * Q) y) :
    z ≤ y := by
  refine Decidable.byContradiction (fun hlt => ?_)
  exact hy.2 (diagPer_mul Q (y + 1) m (hz.1 (y + 1) (by cfomega)))

/-- A doubling sits on a zero diagonal: the hypothesis `IsZeroDiag z` of the doubling engines is
    implied by `DoublesAt Q z` for every lag `Q > 0`. -/
theorem isZeroDiag_of_doublesAt (Q z : Nat) (hQ : 0 < Q) (hd : DoublesAt Q z) : IsZeroDiag z := by
  obtain ⟨y, hy, hdy⟩ := Rule30UOR.CompilePoints.doubling_points Q hQ
  rw [doublesAt_unique Q z y hd hdy]
  exact hy

/-- Doubling the lag moves the doubling diagonal strictly outward: diagonal `z + 1` is
    `Q`-antiperiodic, hence `2Q`-periodic. -/
theorem doublesAt_two_mul_lt (Q z y : Nat) (hQ : 0 < Q) (hd : DoublesAt Q z)
    (hy : DoublesAt (2 * Q) y) : z < y := by
  have hz := isZeroDiag_of_doublesAt Q z hQ hd
  have hanti : DiagPer (2 * Q) (z + 1) := by
    intro t
    rw [Nat.two_mul, ← Nat.add_assoc, Rule30UOR.CompilePoints.antiperiodic_of_doubles Q z hz hd (t + Q),
      Rule30UOR.CompilePoints.antiperiodic_of_doubles Q z hz hd t, Bool.not_not]
  refine Decidable.byContradiction (fun hle => ?_)
  rcases Nat.lt_or_ge (y + 1) (z + 1) with h | h
  · exact hy.2 (diagPer_mul Q (y + 1) 2 (hd.1 (y + 1) (by cfomega)))
  · have hyz : y = z := by cfomega
    rw [hyz] at hy
    exact hy.2 hanti

/-- **Dyadic location of a doubling**: diagonal `j` of the zero state has period `2^j`, so a
    doubling at `z` forbids `2^(z+1) ∣ Q`. -/
theorem doublesAt_not_twopow_succ_dvd (Q z : Nat) (hd : DoublesAt Q z) :
    ¬ twopow (z + 1) ∣ Q := by
  intro hdvd
  obtain ⟨w, hw⟩ := hdvd
  apply hd.2
  intro t
  rw [hw, Rule30UOR.Interfaces.twopow_eq_pow, Nat.mul_comm]
  exact Rule30UOR.ZeroDiagonals.E_per_mul (z + 1) w t

/-- **Doubling depth**: a doubling at a dyadic multiple `w * 2^K` lies at or beyond diagonal `K`. -/
theorem le_of_doublesAt_mul_twopow (w K z : Nat) (hd : DoublesAt (w * twopow K) z) : K ≤ z := by
  refine Decidable.byContradiction (fun hlt => ?_)
  apply doublesAt_not_twopow_succ_dvd (w * twopow K) z hd
  refine ⟨w * twopow (K - (z + 1)), ?_⟩
  simp only [Rule30UOR.Interfaces.twopow_eq_pow]
  have hpow : 2 ^ K = 2 ^ (z + 1) * 2 ^ (K - (z + 1)) := by
    rw [← Nat.pow_add, show (z + 1) + (K - (z + 1)) = K by cfomega]
  rw [hpow, Nat.mul_left_comm]

/-! ## Route B, scale clause -/

/-- **Prefix scale clause**: `DoublesAt ((c * 2^K) * P) z` and `(z + (p + 1)) + p ≤ K` (the
    hypotheses `hd`, `hK` of 9.1562–9.1565) are jointly unsatisfiable. -/
theorem two_scale_prefix_scale_doubles_unsat (P c z p K : Nat)
    (hd : DoublesAt ((c * twopow K) * P) z) (hK : (z + (p + 1)) + p ≤ K) : False := by
  rw [Nat.mul_right_comm c (twopow K) P] at hd
  have h := le_of_doublesAt_mul_twopow (c * P) K z hd
  cfomega

/-- **Corridor scale clause**: `DoublesAt ((c * 2^K) * P) z` and `((z + (p + 1)) + S) + 1 ≤ K` (the
    hypotheses `hd`, `hK` of 9.1496, its `rdrv` sibling and Part16's
    `not_centerPeriodic_of_two_scale_single_row_at_zero_diag_doubles`) are jointly unsatisfiable. -/
theorem two_scale_corridor_scale_doubles_unsat (P c z p S K : Nat)
    (hd : DoublesAt ((c * twopow K) * P) z) (hK : ((z + (p + 1)) + S) + 1 ≤ K) : False := by
  rw [Nat.mul_right_comm c (twopow K) P] at hd
  have h := le_of_doublesAt_mul_twopow (c * P) K z hd
  cfomega

/-! ## Route B, tail clause -/

/-- The prefix clause `hpref` of 9.1563 for the right-half row `(t + u 2^L) + Q`. -/
def RhRowPrefixAgree (t Q L u p : Nat) : Prop :=
  ∀ i : Nat, i < p →
    rhCenter ((t + u * twopow L) + Q) ((u * twopow L) - (1 + i)) =
      rhCenter ((t + u * twopow L) + Q) (((u * twopow L) + Q) - (1 + i))

/-- The tail clause `htail` of 9.1563 for the right-half row `(t + u 2^L) + Q`. -/
def RhRowTailAgree (t Q L u p S : Nat) : Prop :=
  ∀ i : Nat, p ≤ i → i ≤ S →
    rhCenter ((t + u * twopow L) + Q) ((u * twopow L) - (1 + i)) =
      rhCenter ((t + u * twopow L) + Q) ((u * twopow L) - ((1 + i) + Q))

/-- A lag-`Q` spatial defect in the tail window of the right-half row `(t + u 2^L) + Q`. -/
def RhRowTailDefect (t Q L u p S : Nat) : Prop :=
  ∃ i : Nat, p ≤ i ∧ i ≤ S ∧
    rhCenter ((t + u * twopow L) + Q) ((u * twopow L) - (1 + i)) =
      !rhCenter ((t + u * twopow L) + Q) ((u * twopow L) - ((1 + i) + Q))

/-- The prefix clause `hpref` of 9.1565 for the pure-drive row `rdrv td (u 2^L) (t + Q)`. -/
def RdrvRowPrefixAgree (td t Q L u p : Nat) : Prop :=
  ∀ i : Nat, i < p →
    rdrv td (u * twopow L) (t + Q) ((u * twopow L) - (1 + i)) =
      rdrv td (u * twopow L) (t + Q) (((u * twopow L) + Q) - (1 + i))

/-- The tail clause `htail` of 9.1565 for the pure-drive row `rdrv td (u 2^L) (t + Q)`. -/
def RdrvRowTailAgree (td t Q L u p S : Nat) : Prop :=
  ∀ i : Nat, p ≤ i → i ≤ S →
    rdrv td (u * twopow L) (t + Q) ((u * twopow L) - (1 + i)) =
      rdrv td (u * twopow L) (t + Q) ((u * twopow L) - ((1 + i) + Q))

/-- A lag-`Q` spatial defect in the tail window of the pure-drive row `rdrv td (u 2^L) (t + Q)`. -/
def RdrvRowTailDefect (td t Q L u p S : Nat) : Prop :=
  ∃ i : Nat, p ≤ i ∧ i ≤ S ∧
    rdrv td (u * twopow L) (t + Q) ((u * twopow L) - (1 + i)) =
      !rdrv td (u * twopow L) (t + Q) ((u * twopow L) - ((1 + i) + Q))

theorem bool_ne_not_self (b : Bool) (h : b = !b) : False := by
  cases b
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h

theorem not_rhRowTailAgree_of_rhRowTailDefect (t Q L u p S : Nat)
    (h : RhRowTailDefect t Q L u p S) : ¬ RhRowTailAgree t Q L u p S := by
  intro hagree
  obtain ⟨i, hpi, hiS, hdis⟩ := h
  rw [hagree i hpi hiS] at hdis
  exact bool_ne_not_self _ hdis

theorem not_rdrvRowTailAgree_of_rdrvRowTailDefect (td t Q L u p S : Nat)
    (h : RdrvRowTailDefect td t Q L u p S) : ¬ RdrvRowTailAgree td t Q L u p S := by
  intro hagree
  obtain ⟨i, hpi, hiS, hdis⟩ := h
  rw [hagree i hpi hiS] at hdis
  exact bool_ne_not_self _ hdis

/-- **Tail defect, right-half row**: at a doubling zero diagonal `z`, the tail window `[p, S]` of the
    two-scale right-half row carries a lag-`Q` spatial defect. No period, no prefix, no `K`
    (9.1572 moved into the dyadic row by 9.1388). -/
theorem rhRowTailDefect_of_doubles (Q z p S L u : Nat) (hQ : 1 ≤ Q)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * Q ≤ S + 1) (hu : 1 ≤ u)
    (hL : ((z + (p + 1)) + Q) + ((1 + S) + Q) ≤ L) :
    RhRowTailDefect (z + (p + 1)) Q L u p S := by
  obtain ⟨j, hj, hdis⟩ :=
    Rule30UOR.Interfaces.exists_lh_row_spatial_disagree_of_doubles_settledUpTo Q z p hQ hz hd hbt
  refine ⟨(p + Q + j) - 1, by cfomega, by cfomega, ?_⟩
  have h1 := Rule30UOR.Interfaces.rhCenter_dyadic_sub_shift_eq_lhCenter ((z + (p + 1)) + Q) L u
    (1 + ((p + Q + j) - 1)) 0 hu (by cfomega)
  have h2 := Rule30UOR.Interfaces.rhCenter_dyadic_sub_shift_eq_lhCenter ((z + (p + 1)) + Q) L u
    ((1 + ((p + Q + j) - 1)) + Q) 0 hu (by cfomega)
  simp only [Nat.add_zero] at h1 h2
  rw [show ((z + (p + 1)) + u * twopow L) + Q = ((z + (p + 1)) + Q) + u * twopow L by cfomega,
    h1, h2, show 1 + ((p + Q + j) - 1) = (p + Q) + j by cfomega]
  exact hdis

/-- **Tail defect, pure-drive row**: the same for `rdrv td (u 2^L)`, for every drive offset `td`
    (9.1572 moved into the row by 9.1460). -/
theorem rdrvRowTailDefect_of_doubles (td Q z p S L u : Nat) (hQ : 1 ≤ Q)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * Q ≤ S + 1) (hu : 1 ≤ u)
    (hL : ((z + (p + 1)) + Q) + ((1 + S) + Q) ≤ L) :
    RdrvRowTailDefect td (z + (p + 1)) Q L u p S := by
  obtain ⟨j, hj, hdis⟩ :=
    Rule30UOR.Interfaces.exists_lh_row_spatial_disagree_of_doubles_settledUpTo Q z p hQ hz hd hbt
  refine ⟨(p + Q + j) - 1, by cfomega, by cfomega, ?_⟩
  rw [Rule30UOR.Interfaces.rdrv_dyadic_exact_row_shift_left_eq td L u (1 + ((p + Q + j) - 1))
      ((z + (p + 1)) + Q) hu (by cfomega),
    Rule30UOR.Interfaces.rdrv_dyadic_exact_row_shift_left_eq td L u ((1 + ((p + Q + j) - 1)) + Q)
      ((z + (p + 1)) + Q) hu (by cfomega),
    show 1 + ((p + Q + j) - 1) = (p + Q) + j by cfomega]
  exact hdis

theorem not_rhRowTailAgree_of_doubles (Q z p S L u : Nat) (hQ : 1 ≤ Q)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * Q ≤ S + 1) (hu : 1 ≤ u)
    (hL : ((z + (p + 1)) + Q) + ((1 + S) + Q) ≤ L) :
    ¬ RhRowTailAgree (z + (p + 1)) Q L u p S :=
  not_rhRowTailAgree_of_rhRowTailDefect (z + (p + 1)) Q L u p S
    (rhRowTailDefect_of_doubles Q z p S L u hQ hz hd hbt hS hu hL)

theorem not_rdrvRowTailAgree_of_doubles (td Q z p S L u : Nat) (hQ : 1 ≤ Q)
    (hz : IsZeroDiag z) (hd : DoublesAt Q z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * Q ≤ S + 1) (hu : 1 ≤ u)
    (hL : ((z + (p + 1)) + Q) + ((1 + S) + Q) ≤ L) :
    ¬ RdrvRowTailAgree td (z + (p + 1)) Q L u p S :=
  not_rdrvRowTailAgree_of_rdrvRowTailDefect td (z + (p + 1)) Q L u p S
    (rdrvRowTailDefect_of_doubles td Q z p S L u hQ hz hd hbt hS hu hL)

/-! ## Audits: the hypotheses of 9.1563 and 9.1565 without `CenterPeriodic` -/

/-- **Audit (9.1563, tail clause)**: the tail hypothesis with its doubling, settlement, width and
    row-scale side conditions is unsatisfiable. This needs no `CenterPeriodic`, no `hpref` and no `hK`. -/
theorem two_scale_single_rh_row_tail_hypotheses_unsat (P c z p S K L u : Nat)
    (hP : 0 < P) (hc : 0 < c)
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1) (hu : 1 ≤ u)
    (hL : ((z + (p + 1)) + (c * twopow K) * P) + ((1 + S) + (c * twopow K) * P) ≤ L)
    (htail : RhRowTailAgree (z + (p + 1)) ((c * twopow K) * P) L u p S) : False := by
  have hgt : K < twopow K := Rule30UOR.Interfaces.twopow_gt_self K
  have hQ : 1 ≤ (c * twopow K) * P := Nat.mul_pos (Nat.mul_pos hc (by cfomega)) hP
  exact not_rhRowTailAgree_of_doubles ((c * twopow K) * P) z p S L u hQ hz hd hbt hS hu hL htail

/-- **Audit (9.1565, tail clause)**: the same for the pure-drive row. -/
theorem two_scale_single_rdrv_row_tail_hypotheses_unsat (P td c z p S K L u : Nat)
    (hP : 0 < P) (hc : 0 < c)
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1) (hu : 1 ≤ u)
    (hL : ((z + (p + 1)) + (c * twopow K) * P) + ((1 + S) + (c * twopow K) * P) ≤ L)
    (htail : RdrvRowTailAgree td (z + (p + 1)) ((c * twopow K) * P) L u p S) : False := by
  have hgt : K < twopow K := Rule30UOR.Interfaces.twopow_gt_self K
  have hQ : 1 ≤ (c * twopow K) * P := Nat.mul_pos (Nat.mul_pos hc (by cfomega)) hP
  exact not_rdrvRowTailAgree_of_doubles td ((c * twopow K) * P) z p S L u hQ hz hd hbt hS hu hL htail

/-- **Audit (9.1563, whole bundle)**: every hypothesis of
    `not_centerPeriodic_of_two_scale_single_rh_row_prefix_and_tail_settleBound` except
    `CenterPeriodic T P` and `T ≤ z + (p + 1)` together imply `False` (by 9.1562, then 9.1571). Its
    `CenterPeriodic` premise carries no information. -/
theorem two_scale_single_rh_row_engine_hypotheses_unsat (P c z p S K L u : Nat)
    (hP : 0 < P) (hc : 0 < c)
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : (z + (p + 1)) + p ≤ K)
    (hL : ((z + (p + 1)) + (c * twopow K) * P) + ((1 + S) + (c * twopow K) * P) ≤ L) (hKL : K ≤ L)
    (hpref : RhRowPrefixAgree (z + (p + 1)) ((c * twopow K) * P) L u p)
    (htail : RhRowTailAgree (z + (p + 1)) ((c * twopow K) * P) L u p S) : False := by
  have hgt : K < twopow K := Rule30UOR.Interfaces.twopow_gt_self K
  have hQ : 1 ≤ (c * twopow K) * P := Nat.mul_pos (Nat.mul_pos hc (by cfomega)) hP
  have hmul : (c * twopow K) * P = (c * P) * twopow K := Nat.mul_right_comm c (twopow K) P
  apply Rule30UOR.Interfaces.not_lhBandAgree_one_at_zero_diag_of_doubles_settledUpTo
    ((c * twopow K) * P) z p S hQ hz hd hbt hS
  unfold RhRowPrefixAgree at hpref
  unfold RhRowTailAgree at htail
  rw [hmul] at hd hL hpref htail ⊢
  exact Rule30UOR.Interfaces.lhBandAgree_one_at_zero_diag_of_two_scale_single_rh_row_prefix_and_tail_settleBound
    z p S K L u (c * P) hd hbt hu hK hL hKL hpref htail

/-- **Audit (9.1565, whole bundle)**: the same for
    `not_centerPeriodic_of_two_scale_single_rdrv_row_prefix_and_tail_settleBound` (by 9.1564, then
    9.1571). -/
theorem two_scale_single_rdrv_row_engine_hypotheses_unsat (P td c z p S K L u : Nat)
    (hP : 0 < P) (hc : 0 < c)
    (hz : IsZeroDiag z) (hd : DoublesAt ((c * twopow K) * P) z)
    (hbt : SettledUpTo (z + 1) (z + (p + 1)))
    (hS : p + 3 * ((c * twopow K) * P) ≤ S + 1)
    (hu : 1 ≤ u) (hK : (z + (p + 1)) + p ≤ K)
    (hL : ((z + (p + 1)) + (c * twopow K) * P) + ((1 + S) + (c * twopow K) * P) ≤ L) (hKL : K ≤ L)
    (hpref : RdrvRowPrefixAgree td (z + (p + 1)) ((c * twopow K) * P) L u p)
    (htail : RdrvRowTailAgree td (z + (p + 1)) ((c * twopow K) * P) L u p S) : False := by
  have hgt : K < twopow K := Rule30UOR.Interfaces.twopow_gt_self K
  have hQ : 1 ≤ (c * twopow K) * P := Nat.mul_pos (Nat.mul_pos hc (by cfomega)) hP
  have hmul : (c * twopow K) * P = (c * P) * twopow K := Nat.mul_right_comm c (twopow K) P
  apply Rule30UOR.Interfaces.not_lhBandAgree_one_at_zero_diag_of_doubles_settledUpTo
    ((c * twopow K) * P) z p S hQ hz hd hbt hS
  unfold RdrvRowPrefixAgree at hpref
  unfold RdrvRowTailAgree at htail
  rw [hmul] at hd hL hpref htail ⊢
  exact Rule30UOR.Interfaces.lhBandAgree_one_at_zero_diag_of_two_scale_single_rdrv_row_prefix_and_tail_settleBound
    td z p S K L u (c * P) hd hbt hu hK hL hKL hpref htail

end Rule30UOR.DoublingDepth

