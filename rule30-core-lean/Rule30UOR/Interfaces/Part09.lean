module

public import Rule30UOR.Interfaces.Part08

/-!
# `Rule30UOR.Interfaces`, part 9

* Batch 23: Outer Left-Strip & Sector-2 Center-Slot `WinWittAgree` Invariance, `zcenter` Shift Laws & Refutations, and Post-Black Reset Spatial `Q`-Flips at Doubling Diagonals (9.637–9.651)
* Batch 24: Cross-Center `lhCenter` Step Law, Forced Two-Cell OR Gates & Twin Pinning Under `WinWittAgree` at Doubling Zero Diagonals, and Upward `Q`-Transported Reset Flips (9.652–9.666)
* Batch 25: Upward OR Gates, Period-2 Doubling Triple-Zero Pinning, Below-Threshold Spatial `Q`-Periodicity, and Single-Time `WinWittAgree` Post-Black Reset Transport (9.667–9.681)
* Batch 26: Single-Time `WinWittAgree` Sector-2 Bit Transport, Simultaneous Adjacent Bit Flips, Single-Time Twin Pinning, and Period-2 / Doubling Refutations (9.682–9.696)
-/

@[expose] public section

namespace Rule30UOR.Interfaces
open Rule30UOR.Core (phi carry phiLinear)
open Rule30UOR.Core (phi carry phiLinear row rowCenter bit rdiag rcenter bxor)
open Rule30UOR.Core (phiLinearPow phiScale winWitt wittResponse twopow twopow_succ)
open Rule30UOR.Core (ldiag)
open Rule30UOR.Intent (settle E)
open Rule30UOR.ZeroDiagonals (IsZeroDiag)
open Rule30UOR.CompilePoints (IsBlackDiag DoublesAt black_after_zero_diag antiperiodic_of_doubles)

/-! ### Batch 23: Outer Left-Strip & Sector-2 Center-Slot `WinWittAgree` Invariance, `zcenter` Shift Laws & Refutations, and Post-Black Reset Spatial `Q`-Flips at Doubling Diagonals (9.637–9.651) -/

/-- **Same-column late `lhCenter (· + 2^k) (p + 2^k)` invariance under outer left-strip `WinWittAgree` (9.637)**:
for all `t, k, Q, p, a, L ∈ ℕ` with `(t + Q) + p < 2^k` and `a ≤ (t + p) + 2^(k+1) ≤ a + L`, if `lhCenter (t + Q) p = lhCenter t p` and `WinWittAgree t k Q a L`, then `lhCenter ((t + Q) + 2^k) (p + 2^k) = lhCenter (t + 2^k) (p + 2^k)`. -/
theorem lhCenter_late_shift_eq_of_winWittAgree_outer_left_strip (t k Q p a L : Nat)
    (hcone : (t + Q) + p < twopow k)
    (ha : a ≤ (t + p) + twopow (k + 1))
    (hL : (t + p) + twopow (k + 1) ≤ a + L)
    (hp : lhCenter (t + Q) p = lhCenter t p)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (p + twopow k) =
      lhCenter (t + twopow k) (p + twopow k) := by
  have hi := hw (((t + p) + twopow (k + 1)) - a) (by omega)
  rw [show a + (((t + p) + twopow (k + 1)) - a) = (t + p) + twopow (k + 1) by omega,
    show ((t + p) + twopow (k + 1)) + Q = ((t + Q) + p) + twopow (k + 1) by omega,
    winWitt_testBit_outer_left_strip (t + Q) k p (by omega),
    winWitt_testBit_outer_left_strip t k p (by omega),
    hp] at hi
  revert hi
  simp only [bxor_eq_xor]
  cases lhCenter ((t + Q) + twopow k) (p + twopow k) <;>
    cases lhCenter (t + twopow k) (p + twopow k) <;>
    cases lhCenter t p <;> decide

theorem lhCenter_late_shift_eq_of_winWittAgree_outer_left_strip_prop (t k Q p a L : Nat)
    (hcone : (t + Q) + p < twopow k)
    (ha : a ≤ (t + p) + twopow (k + 1))
    (hL : (t + p) + twopow (k + 1) ≤ a + L)
    (hp : lhCenter (t + Q) p = lhCenter t p)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (p + twopow k) =
      lhCenter (t + twopow k) (p + twopow k) :=
  lhCenter_late_shift_eq_of_winWittAgree_outer_left_strip t k Q p a L hcone ha hL hp hw

/-- **Refutation of `WinWittAgree t k 2 a L` in the outer left strip across any settled zero diagonal `t - p` (9.638)**:
for all `t, k, p, a, L ∈ ℕ` with `p ≤ t` and `(t - p) + 2 ≤ k`, if `t - p` is a zero diagonal, `settle (t - p) ≤ t + 2^k`, `settle ((t - p) + 2) ≤ (t + 2) + 2^k`, `a ≤ (t + p) + 2^(k+1) ≤ a + L`, and `lhCenter (t + 2) p = lhCenter t p`, then `¬ WinWittAgree t k 2 a L`. -/
theorem not_winWittAgree_two_outer_left_strip_of_zero_diag (t k p a L : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset0 : settle (t - p) ≤ t + twopow k)
    (hset2 : settle ((t - p) + 2) ≤ (t + 2) + twopow k)
    (ha : a ≤ (t + p) + twopow (k + 1))
    (hL : (t + p) + twopow (k + 1) ≤ a + L)
    (hcol : lhCenter (t + 2) p = lhCenter t p) :
    ¬ WinWittAgree t k 2 a L := by
  intro hw
  have h7 := gt_twopow_of_zero_diag_le (t - p) k (by omega) hz
  have h0 := lhCenter_late_shift_of_zero_diag t k p hp (by omega) hz hset0
  have h2 := lhCenter_late_shift_after_zero_diag t k p hp hk hz hset2
  have hw0 := winWitt_testBit_outer_left_strip t k p (by omega)
  have hw2 := winWitt_testBit_outer_left_strip (t + 2) k p (by omega)
  have hi := hw (((t + p) + twopow (k + 1)) - a) (by omega)
  rw [show a + (((t + p) + twopow (k + 1)) - a) = (t + p) + twopow (k + 1) by omega,
    show ((t + p) + twopow (k + 1)) + 2 = ((t + 2) + p) + twopow (k + 1) by omega,
    hw0, hw2, h0, h2, hcol] at hi
  revert hi
  simp only [bxor_eq_xor]
  cases lhCenter t p <;> decide

theorem not_winWittAgree_two_outer_left_strip_of_zero_diag_prop (t k p a L : Nat)
    (hp : p ≤ t) (hk : (t - p) + 2 ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset0 : SettledBy (t - p) (t + twopow k))
    (hset2 : SettledBy ((t - p) + 2) ((t + 2) + twopow k))
    (ha : a ≤ (t + p) + twopow (k + 1))
    (hL : (t + p) + twopow (k + 1) ≤ a + L)
    (hcol : lhCenter (t + 2) p = lhCenter t p) :
    ¬ WinWittAgree t k 2 a L :=
  not_winWittAgree_two_outer_left_strip_of_zero_diag t k p a L hp hk hz hset0 hset2 ha hL hcol

/-- **Exact `zcenter` shift XOR from Sector-2 center-slot `WinWittAgree` (9.639)**:
for all `t, k, Q, a, L ∈ ℕ` with `t + Q ≤ k`, `settle t ≤ t + 2^k`, `settle (t + Q) ≤ (t + Q) + 2^k`, and `a ≤ t + 2^(k+1) ≤ a + L`, if `WinWittAgree t k Q a L` holds, then `zcenter (t + Q) ⊕ zcenter t = center (t + Q) ⊕ center t`. -/
theorem zcenter_shift_xor_eq_center_xor_of_winWittAgree_sector_two_center_slot
    (t k Q a L : Nat)
    (hk : t + Q ≤ k)
    (hset0 : settle t ≤ t + twopow k)
    (hsetQ : settle (t + Q) ≤ (t + Q) + twopow k)
    (ha : a ≤ t + twopow (k + 1))
    (hL : t + twopow (k + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    bxor (zcenter (t + Q)) (zcenter t) =
      bxor (Rule30UOR.Core.center (t + Q)) (Rule30UOR.Core.center t) := by
  have hi := hw ((t + twopow (k + 1)) - a) (by omega)
  rw [show a + ((t + twopow (k + 1)) - a) = t + twopow (k + 1) by omega,
    show (t + twopow (k + 1)) + Q = (t + Q) + twopow (k + 1) by omega] at hi
  rw [winWitt_testBit_sector_two_center_slot_zcenter (t + Q) k hk hsetQ,
    winWitt_testBit_sector_two_center_slot_zcenter t k (by omega) hset0,
    hi]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit (t + twopow (k + 1)) <;>
    cases Rule30UOR.Core.center (t + Q) <;>
    cases Rule30UOR.Core.center t <;> decide

theorem zcenter_shift_xor_eq_center_xor_of_winWittAgree_sector_two_center_slot_prop
    (t k Q a L : Nat)
    (hk : t + Q ≤ k)
    (hset0 : SettledBy t (t + twopow k))
    (hsetQ : SettledBy (t + Q) ((t + Q) + twopow k))
    (ha : a ≤ t + twopow (k + 1))
    (hL : t + twopow (k + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    ZCenterXorEq (t + Q) t
      (bxor (Rule30UOR.Core.center (t + Q)) (Rule30UOR.Core.center t)) :=
  zcenter_shift_xor_eq_center_xor_of_winWittAgree_sector_two_center_slot
    t k Q a L hk hset0 hsetQ ha hL hw

/-- **Exact `zcenter` shift equality from Sector-2 center-slot `WinWittAgree` at equal centers (9.640)**:
for all `t, k, Q, a, L ∈ ℕ` with `t + Q ≤ k`, `settle t ≤ t + 2^k`, `settle (t + Q) ≤ (t + Q) + 2^k`, and `a ≤ t + 2^(k+1) ≤ a + L`, if `center (t + Q) = center t` and `WinWittAgree t k Q a L`, then `zcenter (t + Q) = zcenter t`. -/
theorem zcenter_shift_eq_of_winWittAgree_sector_two_center_slot
    (t k Q a L : Nat)
    (hk : t + Q ≤ k)
    (hset0 : settle t ≤ t + twopow k)
    (hsetQ : settle (t + Q) ≤ (t + Q) + twopow k)
    (ha : a ≤ t + twopow (k + 1))
    (hL : t + twopow (k + 1) ≤ a + L)
    (hc : Rule30UOR.Core.center (t + Q) = Rule30UOR.Core.center t)
    (hw : WinWittAgree t k Q a L) :
    zcenter (t + Q) = zcenter t := by
  have hx := zcenter_shift_xor_eq_center_xor_of_winWittAgree_sector_two_center_slot
    t k Q a L hk hset0 hsetQ ha hL hw
  simp only [hc, bxor_eq_xor, Bool.xor_self] at hx
  revert hx
  cases zcenter (t + Q) <;> cases zcenter t <;> decide

theorem zcenter_shift_eq_of_winWittAgree_sector_two_center_slot_prop
    (t k Q a L : Nat)
    (hk : t + Q ≤ k)
    (hset0 : SettledBy t (t + twopow k))
    (hsetQ : SettledBy (t + Q) ((t + Q) + twopow k))
    (ha : a ≤ t + twopow (k + 1))
    (hL : t + twopow (k + 1) ≤ a + L)
    (hc : Rule30UOR.Core.center (t + Q) = Rule30UOR.Core.center t)
    (hw : WinWittAgree t k Q a L) :
    ZCenterXorEq (t + Q) t false := by
  unfold ZCenterXorEq
  rw [zcenter_shift_eq_of_winWittAgree_sector_two_center_slot t k Q a L hk hset0 hsetQ ha hL hc hw,
    bxor_eq_xor, Bool.xor_self]

/-- **Periodic `zcenter (t + m * P) = zcenter t` from Sector-2 center-slot `WinWittAgree` under `CenterPeriodic T P` (9.641)**:
under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, a, L ∈ ℕ` with `T ≤ t`, `t + m * P ≤ k`, `settle t ≤ t + 2^k`, `settle (t + m * P) ≤ (t + m * P) + 2^k`, and `a ≤ t + 2^(k+1) ≤ a + L`, if `WinWittAgree t k (m * P) a L` holds, then `zcenter (t + m * P) = zcenter t`. -/
theorem periodic_zcenter_shift_eq_of_winWittAgree_sector_two_center_slot
    (T P : Nat) (_hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k a L : Nat)
    (ht : T ≤ t) (hk : t + m * P ≤ k)
    (hset0 : settle t ≤ t + twopow k)
    (hsetQ : settle (t + m * P) ≤ (t + m * P) + twopow k)
    (ha : a ≤ t + twopow (k + 1))
    (hL : t + twopow (k + 1) ≤ a + L)
    (hw : WinWittAgree t k (m * P) a L) :
    zcenter (t + m * P) = zcenter t := by
  have hc := Rule30UOR.Scale.center_mul h m t ht
  exact zcenter_shift_eq_of_winWittAgree_sector_two_center_slot
    t k (m * P) a L hk hset0 hsetQ ha hL hc hw

theorem periodic_zcenter_shift_eq_of_winWittAgree_sector_two_center_slot_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k a L : Nat)
    (ht : T ≤ t) (hk : t + m * P ≤ k)
    (hset0 : SettledBy t (t + twopow k))
    (hsetQ : SettledBy (t + m * P) ((t + m * P) + twopow k))
    (ha : a ≤ t + twopow (k + 1))
    (hL : t + twopow (k + 1) ≤ a + L)
    (hw : WinWittAgree t k (m * P) a L) :
    ZCenterXorEq (t + m * P) t false := by
  unfold ZCenterXorEq
  rw [periodic_zcenter_shift_eq_of_winWittAgree_sector_two_center_slot
    T P hP h m t k a L ht hk hset0 hsetQ ha hL hw,
    bxor_eq_xor, Bool.xor_self]

/-- **Refutation of `WinWittAgree z k 2 a L` at the Sector-2 center slot `z + 2^(k+1)` of any settled zero diagonal (9.642)**:
for all `z, k, a, L ∈ ℕ` with `z + 2 ≤ k`, if `z` is a zero diagonal, `settle z ≤ z + 2^k`, `settle (z + 2) ≤ (z + 2) + 2^k`, `a ≤ z + 2^(k+1) ≤ a + L`, and `center (z + 2) = center z`, then `¬ WinWittAgree z k 2 a L`. -/
theorem not_winWittAgree_two_sector_two_center_slot_of_zero_diag
    (z k a L : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z)
    (hset0 : settle z ≤ z + twopow k)
    (hset2 : settle (z + 2) ≤ (z + 2) + twopow k)
    (ha : a ≤ z + twopow (k + 1))
    (hL : z + twopow (k + 1) ≤ a + L)
    (hc : Rule30UOR.Core.center (z + 2) = Rule30UOR.Core.center z) :
    ¬ WinWittAgree z k 2 a L := by
  intro hw
  have heq := zcenter_shift_eq_of_winWittAgree_sector_two_center_slot
    z k 2 a L hk hset0 hset2 ha hL hc hw
  rw [zcenter_of_zero_diag z hz, zcenter_after_zero_diag z hz] at heq
  exact Bool.noConfusion heq

theorem not_winWittAgree_two_sector_two_center_slot_of_zero_diag_prop
    (z k a L : Nat)
    (hk : z + 2 ≤ k) (hz : IsZeroDiag z)
    (hset0 : SettledBy z (z + twopow k))
    (hset2 : SettledBy (z + 2) ((z + 2) + twopow k))
    (ha : a ≤ z + twopow (k + 1))
    (hL : z + twopow (k + 1) ≤ a + L)
    (hc : Rule30UOR.Core.center (z + 2) = Rule30UOR.Core.center z) :
    ¬ WinWittAgree z k 2 a L :=
  not_winWittAgree_two_sector_two_center_slot_of_zero_diag
    z k a L hk hz hset0 hset2 ha hL hc

/-- **Periodic refutation of `WinWittAgree z1 k (m * P) a L` at the Sector-2 center slot when `z1` is a zero diagonal and `z1 + m * P = z2 + 2` (9.643)**:
under `CenterPeriodic T P` (`0 < P`), if `z1` and `z2` are zero diagonals with `z1 + m * P = z2 + 2`, `T ≤ z1`, `z1 + m * P ≤ k`, `settle z1 ≤ z1 + 2^k`, `settle (z2 + 2) ≤ (z2 + 2) + 2^k`, and `a ≤ z1 + 2^(k+1) ≤ a + L`, then `¬ WinWittAgree z1 k (m * P) a L`. -/
theorem not_periodic_winWittAgree_sector_two_center_slot_of_zero_and_after_zero_diag
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k a L : Nat)
    (ht : T ≤ z1) (hk : z1 + m * P ≤ k)
    (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2)
    (hrel : z1 + m * P = z2 + 2)
    (hset1 : settle z1 ≤ z1 + twopow k)
    (hset2 : settle (z2 + 2) ≤ (z2 + 2) + twopow k)
    (ha : a ≤ z1 + twopow (k + 1))
    (hL : z1 + twopow (k + 1) ≤ a + L) :
    ¬ WinWittAgree z1 k (m * P) a L := by
  intro hw
  have hsetQ : settle (z1 + m * P) ≤ (z1 + m * P) + twopow k := by
    rw [hrel]
    exact hset2
  have heq := periodic_zcenter_shift_eq_of_winWittAgree_sector_two_center_slot
    T P hP h m z1 k a L ht hk hset1 hsetQ ha hL hw
  rw [hrel, zcenter_of_zero_diag z1 hz1, zcenter_after_zero_diag z2 hz2] at heq
  exact Bool.noConfusion heq

theorem not_periodic_winWittAgree_sector_two_center_slot_of_zero_and_after_zero_diag_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (m z1 z2 k a L : Nat)
    (ht : T ≤ z1) (hk : z1 + m * P ≤ k)
    (hz1 : IsZeroDiag z1) (hz2 : IsZeroDiag z2)
    (hrel : z1 + m * P = z2 + 2)
    (hset1 : SettledBy z1 (z1 + twopow k))
    (hset2 : SettledBy (z2 + 2) ((z2 + 2) + twopow k))
    (ha : a ≤ z1 + twopow (k + 1))
    (hL : z1 + twopow (k + 1) ≤ a + L) :
    ¬ WinWittAgree z1 k (m * P) a L :=
  not_periodic_winWittAgree_sector_two_center_slot_of_zero_and_after_zero_diag
    T P hP h m z1 z2 k a L ht hk hz1 hz2 hrel hset1 hset2 ha hL

/-- **Late-window spatial `Q`-flip in `winWitt (t + Q) (2^k)` at a doubling zero diagonal under `WinWittAgree` (9.644)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 1 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles (`DoublesAt Q ((t + Q) + r)`), `((t + Q) + r) + 1` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt (t + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - (r + 1)) = !(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have hi := hw (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hcone : ((t + Q) + r) + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [show a + (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) =
      (t + twopow (k + 1)) - ((r + Q) + 1) by omega,
    show ((t + twopow (k + 1)) - ((r + Q) + 1)) + Q =
      (t + twopow (k + 1)) - (r + 1) by omega] at hi
  rw [winWitt_scale_cross_zero_gap_antiperiodic_of_doubles Q t k r hr hk hz hd hset, ← hi]

theorem winWitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset ha hL hw

theorem two_mul_le_twopow : ∀ k : Nat, 2 ≤ k → 2 * k ≤ twopow k
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | k + 3, _ => by
    have ih := two_mul_le_twopow (k + 2) (by omega)
    have hstep : twopow (k + 3) = twopow (k + 2) + twopow (k + 2) :=
      Rule30UOR.Core.twopow_succ (k + 2)
    omega

/-- **Late-row spatial `Q`-flip in `lhCenter ((t + Q) + 2^k)` at a doubling zero diagonal under Sector-2 zero-gap `WinWittAgree` (9.645)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 1 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `lhCenter ((t + Q) + 2^k) (2^k - (r + 1)) = !lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 1))`. -/
theorem lhCenter_late_cross_late_shift_flip_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + 1)) =
      !lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) := by
  have hz0 : (t + Q) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q ((r + Q) + 1) a L
    (by omega) (by omega) ha hL hw
  rw [lhCenter_late_cross_antiperiodic_of_doubles Q t k r hk hz hd hset, ← heq]

theorem lhCenter_late_cross_late_shift_flip_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + Q) + twopow k) (twopow k - (r + 1)) =
      !lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) :=
  lhCenter_late_cross_late_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Same-bit temporal `Q`-flip of `winWitt` at `(t + 2^(k+1)) - (r + 1)` at a doubling zero diagonal under `WinWittAgree` (9.646)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 1 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hcone : ((t + Q) + r) + 1 < twopow k := by
    have := twopow_gt_self k
    omega
  have hi := hw (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) (by omega)
  rw [show a + (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) =
      (t + twopow (k + 1)) - ((r + Q) + 1) by omega,
    show ((t + twopow (k + 1)) - ((r + Q) + 1)) + Q =
      (t + twopow (k + 1)) - (r + 1) by omega] at hi
  have hflip := winWitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset (by omega) hL hw
  rw [hi, hflip, Bool.not_not]

theorem winWitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset ha hL hw

/-- **Post-black reset single-window spatial `Q`-flip in `winWitt (t + 1) (2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` (9.647)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k` (with NO settlement hypothesis on `z + 3`!), `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree (t + 1) k Q a L` holds, then `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))`. -/
theorem winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  have hi := hw (((t + twopow (k + 1)) - (r + 1)) - a) (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hcone : ((t + Q) + r) + 2 < twopow k := by
    have := twopow_gt_self k
    omega
  rw [show a + (((t + twopow (k + 1)) - (r + 1)) - a) = (t + twopow (k + 1)) - (r + 1) by omega,
    show ((t + twopow (k + 1)) - (r + 1)) + Q = ((t + Q) + twopow (k + 1)) - (r + 1) by omega,
    winWitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles Q t k r hr hk hz hd hset1 hset2] at hi
  exact hi.symm

theorem winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1))) :=
  winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset single-row spatial `Q`-flip in `lhCenter ((t + 1) + 2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` (9.648)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree (t + 1) k Q a L` holds, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2))`. -/
theorem lhCenter_late_cross_reset_shift_flip_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k (by omega) hz
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap (t + 1) k Q (r + 2) a L
    (by omega) (by omega)
    (by rw [show ((t + 1) + twopow (k + 1)) - (r + 2) = (t + twopow (k + 1)) - (r + 1) by omega]; exact ha)
    (by rw [show ((t + 1) + twopow (k + 1)) - (r + 2) = (t + twopow (k + 1)) - (r + 1) by omega]; exact hL)
    hw
  rw [lhCenter_late_cross_reset_antiperiodic_of_doubles Q t k r hk hz hd hset1 hset2] at heq
  exact heq.symm

theorem lhCenter_late_cross_reset_shift_flip_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) :=
  lhCenter_late_cross_reset_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Space-time equality between `(t, (t + 2^(k+1)) - (r + 1))` and `(t + 1, (t + 2^(k+1)) - ((r + Q) + 1))` at a doubling zero diagonal under `WinWittAgree` (9.649)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = (winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))`. -/
theorem winWitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  have hflip1 := winWitt_scale_cross_zero_gap_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr (by omega) hz hd hset1 ha hL hw
  have hflip2 := winWitt_sector_two_step_flip_zero_gap_after_zero_diag t k (r + Q)
    (by omega)
    (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by omega]; exact hk)
    (by rw [show t + (r + Q) = (t + Q) + r by omega]; exact hz)
    (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by omega]; exact hset2)
  rw [hflip1, hflip2]

theorem winWitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1)) :=
  winWitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **1-step temporal Sector-2 bit flip at `(t + 2^(k+1)) - (r + 1)` (`Q` diagonals below `z + 1`) under `WinWittAgree` at `t` and `t + 1` (9.650)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_step_flip_at_shift_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  rw [winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winWittAgree
      Q t k r a L hr hk hz hd hset1 hset2 ha hL hw1,
    winWitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winWittAgree
      Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0]

theorem winWitt_scale_cross_zero_gap_step_flip_at_shift_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_step_flip_at_shift_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **1-step temporal `lhCenter` complementation `Q` diagonals below `z + 1` under Sector-2 zero-gap `WinWittAgree` at `t` and `t + 1` (9.651)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`. -/
theorem lhCenter_late_cross_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  rw [lhCenter_late_cross_reset_shift_flip_of_doubles_and_winWittAgree_zero_gap
      Q t k r a L hr hk hz hd hset1 hset2 ha hL hw1,
    lhCenter_late_cross_reset_after_zero_diag t k (r + Q)
      (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by omega]; exact hk)
      (by rw [show t + (r + Q) = (t + Q) + r by omega]; exact hz)
      (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by omega]; exact hset2),
    lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
      Q t k r a L hr (by omega) hz hd hset1 ha hL hw0,
    Bool.not_not]

theorem lhCenter_late_cross_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-! ### Batch 24: Cross-Center `lhCenter` Step Law, Forced Two-Cell OR Gates & Twin Pinning Under `WinWittAgree` at Doubling Zero Diagonals, and Upward `Q`-Transported Reset Flips (9.652–9.666) -/

/-- **Exact 1-step local Rule 30 law for `lhCenter` in cross-center coordinates `2^k - (r + 2)` (9.652)**:
for all `t, k, r ∈ ℕ` with `r + 3 ≤ 2^k`, `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = lhCenter (t + 2^k) (2^k - (r + 1)) ⊕ (lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3)))`. -/
theorem lhCenter_late_cross_step (t k r : Nat)
    (hr : r + 3 ≤ twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      bxor (lhCenter (t + twopow k) (twopow k - (r + 1)))
        (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
          lhCenter (t + twopow k) (twopow k - (r + 3))) := by
  have hstep := lhCenter_step_succ (t + twopow k) (twopow k - (r + 3))
  rw [show (t + twopow k) + 1 = (t + 1) + twopow k by omega,
    show (twopow k - (r + 3)) + 1 = twopow k - (r + 2) by omega,
    show (twopow k - (r + 3)) + 2 = twopow k - (r + 1) by omega] at hstep
  exact hstep

theorem lhCenter_late_cross_step_prop (t k r : Nat)
    (hr : r + 3 ≤ twopow k) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      bxor (lhCenter (t + twopow k) (twopow k - (r + 1)))
        (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
          lhCenter (t + twopow k) (twopow k - (r + 3))) :=
  lhCenter_late_cross_step t k r hr

/-- **Forced two-cell OR gate `(lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3))) = true` from 1-step cross-center complementation (9.653)**:
for all `t, k, r ∈ ℕ` with `r + 3 ≤ 2^k`, if `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`, then `(lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3))) = true`. -/
theorem lhCenter_late_cross_or_eq_true_of_step_flip (t k r : Nat)
    (hr : r + 3 ≤ twopow k)
    (hflip : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1))) :
    (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
      lhCenter (t + twopow k) (twopow k - (r + 3))) = true := by
  rw [lhCenter_late_cross_step t k r hr] at hflip
  revert hflip
  simp only [bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;>
    cases (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
      lhCenter (t + twopow k) (twopow k - (r + 3))) <;> decide

theorem lhCenter_late_cross_or_eq_true_of_step_flip_prop (t k r : Nat)
    (hr : r + 3 ≤ twopow k)
    (hflip : lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1))) :
    (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
      lhCenter (t + twopow k) (twopow k - (r + 3))) = true :=
  lhCenter_late_cross_or_eq_true_of_step_flip t k r hr hflip

/-- **Forced two-cell `lhCenter` OR gate `Q` diagonals below `z + 2` at a doubling zero diagonal under `WinWittAgree` at `t` and `t + 1` (9.654)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `(lhCenter (t + 2^k) (2^k - (r + 2)) || lhCenter (t + 2^k) (2^k - (r + 3))) = true`. -/
theorem lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
      lhCenter (t + twopow k) (twopow k - (r + 3))) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  exact lhCenter_late_cross_or_eq_true_of_step_flip t k r (by omega)
    (lhCenter_late_cross_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap
      Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1)

theorem lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (lhCenter (t + twopow k) (twopow k - (r + 2)) ||
      lhCenter (t + twopow k) (twopow k - (r + 3))) = true :=
  lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Forced two-bit Sector-2 `winWitt t (2^k)` OR gate at `(t + 2^(k+1)) - (r + 2)` and `(t + 2^(k+1)) - (r + 3)` under `WinWittAgree` at `t` and `t + 1` (9.655)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `((winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) || (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 3))) = true`. -/
theorem winWitt_scale_cross_zero_gap_or_eq_true_at_shift_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) ||
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 3))) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 2) (by omega) (by omega),
    winWitt_testBit_scale_cross_zero_gap t k (r + 3) (by omega) (by omega)]
  exact lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

theorem winWitt_scale_cross_zero_gap_or_eq_true_at_shift_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) ||
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 3))) = true :=
  winWitt_scale_cross_zero_gap_or_eq_true_at_shift_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Exact pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` when `(t + r) + 2` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` (9.656)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `(t + r) + 2` is a zero diagonal, `(t + r) + 2`, `((t + Q) + r) + 1`, and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `lhCenter (t + 2^k) (2^k - (r + 3)) = true`. -/
theorem lhCenter_late_cross_pin_r_plus_three_of_doubles_and_winWittAgree_and_zero_diag_two
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz2 : IsZeroDiag ((t + r) + 2))
    (hset0 : settle ((t + r) + 2) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true := by
  have hor := lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 2)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 2) (by omega)
      (by rw [show t + (r + 2) = (t + r) + 2 by omega]; exact hz2)
      (by rw [show t + (r + 2) = (t + r) + 2 by omega]; exact hset0)
  rw [hfalse, Bool.false_or] at hor
  exact hor

theorem lhCenter_late_cross_pin_r_plus_three_of_doubles_and_winWittAgree_and_zero_diag_two_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz2 : IsZeroDiag ((t + r) + 2))
    (hset0 : SettledBy ((t + r) + 2) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_pin_r_plus_three_of_doubles_and_winWittAgree_and_zero_diag_two
    Q t k r a L hr hk hz hd hz2 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Exact pinning `lhCenter (t + 2^k) (2^k - (r + 2)) = true` when `(t + r) + 3` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` (9.657)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `1 ≤ Q`, `t + Q ≤ r`, and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `(t + r) + 3` is a zero diagonal, `(t + r) + 3`, `((t + Q) + r) + 1`, and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `lhCenter (t + 2^k) (2^k - (r + 2)) = true`. -/
theorem lhCenter_late_cross_pin_r_plus_two_of_doubles_and_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset0 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true := by
  have hor := lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 3)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 3) (by omega)
      (by rw [show t + (r + 3) = (t + r) + 3 by omega]; exact hz3)
      (by rw [show t + (r + 3) = (t + r) + 3 by omega]; exact hset0)
  rw [hfalse, Bool.or_false] at hor
  exact hor

theorem lhCenter_late_cross_pin_r_plus_two_of_doubles_and_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset0 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_pin_r_plus_two_of_doubles_and_winWittAgree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Twin-propagated pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` when `(t + r) + 3` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` (9.658)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `1 ≤ Q`, `t + Q ≤ r`, and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `(t + r) + 3` is a zero diagonal, `(t + r) + 3`, `((t + Q) + r) + 1`, and `((t + Q) + r) + 2` have settled by `t + 2^k` (with NO settling hypothesis on `(t + r) + 1` or `(t + r) + 2`!), `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `lhCenter (t + 2^k) (2^k - (r + 1)) = true`. -/
theorem lhCenter_late_cross_pin_r_plus_one_of_doubles_and_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset0 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k (r + 1) (by omega)
    (by rw [show (t + (r + 1)) + 2 = (t + r) + 3 by omega]; exact hz3)
    (by rw [show (t + (r + 1)) + 2 = (t + r) + 3 by omega]; exact hset0)
  rw [htwin, show (r + 1) + 1 = r + 2 by omega]
  exact lhCenter_late_cross_pin_r_plus_two_of_doubles_and_winWittAgree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

theorem lhCenter_late_cross_pin_r_plus_one_of_doubles_and_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset0 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_pin_r_plus_one_of_doubles_and_winWittAgree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Doubling-diagonal pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` when `(t + r) + 3` is a settled zero diagonal under `WinWittAgree` at `t` and `t + 1` (9.659)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `1 ≤ Q`, `t + Q ≤ r`, and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `(t + r) + 3` is a zero diagonal, `(t + r) + 3`, `((t + Q) + r) + 1`, and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false`. -/
theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset0 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) = false := by
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr (by omega) hz hd hset1 ha hL hw0
  have hpin := lhCenter_late_cross_pin_r_plus_one_of_doubles_and_winWittAgree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1
  rw [hpin] at hflip
  revert hflip
  cases lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) <;> decide

theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hQ : 1 ≤ Q) (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset0 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) = false :=
  lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_winWittAgree_and_zero_diag_three
    Q t k r a L hQ hr hk hz hd hz3 hset0 hset1 hset2 ha hL hw0 hw1

/-- **Period-3 doubling pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` from `DoublesAt 3 ((t + 3) + r)` and `WinWittAgree` at `t` and `t + 1` (9.660)**:
when `Q = 3`, `(t + 3) + r = (t + r) + 3` is the doubling zero diagonal itself, so `WinWittAgree t k 3 a L` and `WinWittAgree (t + 1) k 3 a L` at `(t + 2^(k+1)) - (r + 1)` automatically pin `lhCenter (t + 2^k) (2^k - (r + 1)) = true` (requiring only settlement of `z`, `z + 1`, and `z + 2`). -/
theorem lhCenter_late_cross_pin_before_zero_diag_of_doubles_three_and_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 3 a L)
    (hw1 : WinWittAgree (t + 1) k 3 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_pin_r_plus_one_of_doubles_and_winWittAgree_and_zero_diag_three
    3 t k r a L (by omega) hr hk hz hd
    (by rw [show (t + r) + 3 = (t + 3) + r by omega]; exact hz)
    (by rw [show (t + r) + 3 = (t + 3) + r by omega]; exact hset0)
    hset1 hset2 ha hL hw0 hw1

theorem lhCenter_late_cross_pin_before_zero_diag_of_doubles_three_and_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 3 a L)
    (hw1 : WinWittAgree (t + 1) k 3 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_pin_before_zero_diag_of_doubles_three_and_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Refutation of the 2-step pair `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` when `lhCenter (t + 2^k) (2^k - (r + 2))` and `lhCenter (t + 2^k) (2^k - (r + 3))` are both `false` (9.661)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 1) ≤ a + L`, `lhCenter (t + 2^k) (2^k - (r + 2)) = false`, `lhCenter (t + 2^k) (2^k - (r + 3)) = false`, and `WinWittAgree t k Q a L` holds, then `¬ WinWittAgree (t + 1) k Q a L`. -/
theorem not_winWittAgree_step_pair_at_shift_of_doubles_and_both_false
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hf2 : lhCenter (t + twopow k) (twopow k - (r + 2)) = false)
    (hf3 : lhCenter (t + twopow k) (twopow k - (r + 3)) = false)
    (hw0 : WinWittAgree t k Q a L) :
    ¬ WinWittAgree (t + 1) k Q a L := by
  intro hw1
  have hor := lhCenter_late_cross_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1
  rw [hf2, hf3] at hor
  exact Bool.noConfusion hor

theorem not_winWittAgree_step_pair_at_shift_of_doubles_and_both_false_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hf2 : lhCenter (t + twopow k) (twopow k - (r + 2)) = false)
    (hf3 : lhCenter (t + twopow k) (twopow k - (r + 3)) = false)
    (hw0 : WinWittAgree t k Q a L) :
    ¬ WinWittAgree (t + 1) k Q a L :=
  not_winWittAgree_step_pair_at_shift_of_doubles_and_both_false
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hf2 hf3 hw0

/-- **Post-black reset late-window spatial `Q`-flip in `winWitt ((t + 1) + Q) (2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` (9.662)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k` (with NO settlement hypothesis on `z + 3`!), `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and `WinWittAgree (t + 1) k Q a L` holds, then `(winWitt ((t + 1) + Q) (2^k)).testBit (((t + Q) + 2^(k+1)) - (r + 1)) = !(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    (winWitt ((t + 1) + Q) (twopow k)).testBit (((t + Q) + twopow (k + 1)) - (r + 1)) =
      !(winWitt ((t + 1) + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have hi := hw (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  rw [show a + (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) =
      (t + twopow (k + 1)) - ((r + Q) + 1) by omega,
    show ((t + twopow (k + 1)) - ((r + Q) + 1)) + Q =
      (t + twopow (k + 1)) - (r + 1) by omega] at hi
  rw [winWitt_scale_cross_zero_gap_reset_antiperiodic_of_doubles Q t k r hr hk hz hd hset1 hset2, ← hi]

theorem winWitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    wittBitBool (winWitt ((t + 1) + Q) (twopow k)) (((t + Q) + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt ((t + 1) + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset late-row spatial `Q`-flip in `lhCenter (((t + 1) + Q) + 2^k)` at a doubling zero diagonal under `WinWittAgree (t + 1)` without settling `z + 3` (9.663)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and `WinWittAgree (t + 1) k Q a L` holds, then `lhCenter (((t + 1) + Q) + 2^k) (2^k - (r + 2)) = !lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 2))`. -/
theorem lhCenter_late_cross_reset_late_shift_flip_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) := by
  have hz0 : (t + Q) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap (t + 1) k Q ((r + Q) + 2) a L
    (by omega) (by omega)
    (by rw [show ((t + 1) + twopow (k + 1)) - ((r + Q) + 2) =
      (t + twopow (k + 1)) - ((r + Q) + 1) by omega]; exact ha)
    (by rw [show ((t + 1) + twopow (k + 1)) - ((r + Q) + 2) =
      (t + twopow (k + 1)) - ((r + Q) + 1) by omega]; exact hL)
    hw
  rw [lhCenter_late_cross_reset_antiperiodic_of_doubles Q t k r hk hz hd hset1 hset2, ← heq]

theorem lhCenter_late_cross_reset_late_shift_flip_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) :=
  lhCenter_late_cross_reset_late_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset same-bit temporal `Q`-flip of `winWitt` at `t + 1` and `(t + 2^(k+1)) - (r + 1)` without settling `z + 3` (9.664)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree (t + 1) k Q a L` holds, then `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_reset_same_bit_flip_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    (winWitt ((t + 1) + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have hi := hw (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) (by omega)
  rw [show a + (((t + twopow (k + 1)) - ((r + Q) + 1)) - a) =
      (t + twopow (k + 1)) - ((r + Q) + 1) by omega,
    show ((t + twopow (k + 1)) - ((r + Q) + 1)) + Q =
      (t + twopow (k + 1)) - (r + 1) by omega] at hi
  have hflip := winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 (by omega) hL hw
  rw [hi, hflip, Bool.not_not]

theorem winWitt_scale_cross_zero_gap_reset_same_bit_flip_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree (t + 1) k Q a L) :
    wittBitBool (winWitt ((t + 1) + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_reset_same_bit_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Upward `Q`-transported 1-step Sector-2 bit flip at `t + Q` and `(t + 2^(k+1)) - (r + 1)` (`Q` diagonals beyond `z + 1`) under `WinWittAgree` at `t` and `t + 1` (9.665)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `(winWitt ((t + 1) + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_late_step_flip_at_shift_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (winWitt ((t + 1) + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h0 := winWitt_scale_cross_zero_gap_late_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr (by omega) hz hd hset1 ha hL hw0
  have h1 := winWitt_scale_cross_zero_gap_reset_late_shift_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw1
  have hstep := winWitt_sector_two_step_flip_zero_gap_after_zero_diag (t + Q) k r
    hr hk hz (by omega)
  rw [show (t + Q) + 1 = (t + 1) + Q by omega] at hstep
  rw [hstep, h0] at h1
  revert h1
  cases (winWitt ((t + 1) + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;>
    cases (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;> decide

theorem winWitt_scale_cross_zero_gap_late_step_flip_at_shift_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    wittBitBool (winWitt ((t + 1) + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_late_step_flip_at_shift_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Upward `Q`-transported 1-step `lhCenter` complementation `Q` diagonals beyond `z + 1` under Sector-2 zero-gap `WinWittAgree` at `t` and `t + 1` (9.666)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `lhCenter (((t + 1) + Q) + 2^k) (2^k - ((r + Q) + 2)) = !lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 1))`. -/
theorem lhCenter_late_cross_late_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) =
      !lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) := by
  have h0 := lhCenter_late_cross_late_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr (by omega) hz hd hset1 ha hL hw0
  have h1 := lhCenter_late_cross_reset_late_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw1
  have hstep := lhCenter_late_cross_reset_after_zero_diag (t + Q) k r hk hz (by omega)
  rw [show (t + Q) + 1 = (t + 1) + Q by omega] at hstep
  rw [hstep, h0] at h1
  revert h1
  cases lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) <;>
    cases lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) <;> decide

theorem lhCenter_late_cross_late_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    lhCenter (((t + 1) + Q) + twopow k) (twopow k - ((r + Q) + 2)) =
      !lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 1)) :=
  lhCenter_late_cross_late_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-! ### Batch 25: Upward OR Gates, Period-2 Doubling Triple-Zero Pinning, Below-Threshold Spatial `Q`-Periodicity, and Single-Time `WinWittAgree` Post-Black Reset Transport (9.667–9.681) -/

/-- **Upward `Q`-transported two-cell `lhCenter` OR gate at `(t + Q) + 2^k` and `Q` diagonals beyond `z + 2` under `WinWittAgree` at `t` and `t + 1` (9.667)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `(lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 2)) || lhCenter ((t + Q) + 2^k) (2^k - ((r + Q) + 3))) = true`. -/
theorem lhCenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 2)) ||
      lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 3))) = true := by
  have hz0 : (t + Q) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have hflip := lhCenter_late_cross_late_step_flip_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1
  rw [show (t + 1) + Q = (t + Q) + 1 by omega] at hflip
  exact lhCenter_late_cross_or_eq_true_of_step_flip (t + Q) k (r + Q) (by omega) hflip

theorem lhCenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 2)) ||
      lhCenter ((t + Q) + twopow k) (twopow k - ((r + Q) + 3))) = true :=
  lhCenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Upward `Q`-transported two-bit Sector-2 OR gate in `winWitt (t + Q) (2^k)` at `(t + 2^(k+1)) - (r + 2)` and `(t + 2^(k+1)) - (r + 3)` under `WinWittAgree` at `t` and `t + 1` (9.668)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - ((r + Q) + 1) ≤ a + L`, and both `WinWittAgree t k Q a L` and `WinWittAgree (t + 1) k Q a L` hold, then `((winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) || (winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 3))) = true`. -/
theorem winWitt_scale_cross_zero_gap_late_or_eq_true_at_shift_of_doubles_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    ((winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) ||
      (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 3))) = true := by
  have hz0 : (t + Q) + r ≠ 0 := fun h => not_isZeroDiag_zero (h ▸ hz)
  have h2k_le : 2 * k ≤ twopow k := two_mul_le_twopow k (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - (r + 2) = ((t + Q) + twopow (k + 1)) - ((r + Q) + 2) by omega,
    show (t + twopow (k + 1)) - (r + 3) = ((t + Q) + twopow (k + 1)) - ((r + Q) + 3) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + Q) k ((r + Q) + 2) (by omega) (by omega),
    winWitt_testBit_scale_cross_zero_gap (t + Q) k ((r + Q) + 3) (by omega) (by omega)]
  exact lhCenter_late_cross_late_or_eq_true_at_shift_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

theorem winWitt_scale_cross_zero_gap_late_or_eq_true_at_shift_of_doubles_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - ((r + Q) + 1) ≤ a + L)
    (hw0 : WinWittAgree t k Q a L)
    (hw1 : WinWittAgree (t + 1) k Q a L) :
    (wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 2)) ||
      wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 3))) = true :=
  winWitt_scale_cross_zero_gap_late_or_eq_true_at_shift_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw0 hw1

/-- **Period-2 doubling pinning `lhCenter (t + 2^k) (2^k - (r + 3)) = true` on the doubling diagonal `z + 1` from `DoublesAt 2 ((t + 2) + r)` and `WinWittAgree` at `t` and `t + 1` (9.669)**:
when `Q = 2`, `(t + 2) + r = (t + r) + 2` is the doubling zero diagonal itself, so `WinWittAgree t k 2 a L` and `WinWittAgree (t + 1) k 2 a L` at `(t + 2^(k+1)) - (r + 1)` automatically pin `lhCenter (t + 2^k) (2^k - (r + 3)) = true`. -/
theorem lhCenter_late_cross_pin_r_plus_three_of_doubles_two_and_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r)) (hd : DoublesAt 2 ((t + 2) + r))
    (hset0 : settle ((t + 2) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 2) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 2) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 2 a L)
    (hw1 : WinWittAgree (t + 1) k 2 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_pin_r_plus_three_of_doubles_and_winWittAgree_and_zero_diag_two
    2 t k r a L hr hk hz hd
    (by rw [show (t + r) + 2 = (t + 2) + r by omega]; exact hz)
    (by rw [show (t + r) + 2 = (t + 2) + r by omega]; exact hset0)
    hset1 hset2 ha hL hw0 hw1

theorem lhCenter_late_cross_pin_r_plus_three_of_doubles_two_and_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r)) (hd : DoublesAt 2 ((t + 2) + r))
    (hset0 : SettledBy ((t + 2) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 2) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 2) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 2 a L)
    (hw1 : WinWittAgree (t + 1) k 2 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 3)) = true :=
  lhCenter_late_cross_pin_r_plus_three_of_doubles_two_and_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Period-2 doubling pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = false` on diagonal `z - 1` from `DoublesAt 2 ((t + 2) + r)` and `WinWittAgree` at `t` and `t + 1` (9.670)**:
combining `9.669` (`lhCenter (t + 2^k) (2^k - (r + 3)) = true`) with the spatial 2-flip `9.636` pins `lhCenter (t + 2^k) (2^k - (r + 1)) = false` without requiring `z - 1` to settle. -/
theorem lhCenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r)) (hd : DoublesAt 2 ((t + 2) + r))
    (hset0 : settle ((t + 2) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 2) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 2) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 2 a L)
    (hw1 : WinWittAgree (t + 1) k 2 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = false := by
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    2 t k r a L hr (by omega) hz hd hset1 ha hL hw0
  have hpin := lhCenter_late_cross_pin_r_plus_three_of_doubles_two_and_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1
  rw [show (r + 2) + 1 = r + 3 by omega, hpin] at hflip
  exact hflip

theorem lhCenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r)) (hd : DoublesAt 2 ((t + 2) + r))
    (hset0 : SettledBy ((t + 2) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 2) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 2) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 2 a L)
    (hw1 : WinWittAgree (t + 1) k 2 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = false :=
  lhCenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Twin-propagated Period-2 doubling pinning `lhCenter (t + 2^k) (2^k - r) = false` on diagonal `z - 2` from `DoublesAt 2 ((t + 2) + r)` and `WinWittAgree` at `t` and `t + 1` (9.671)**:
combining `9.670` (`lhCenter (t + 2^k) (2^k - (r + 1)) = false`) with the Twin Identity Before a Zero Diagonal (`9.592`) pins `lhCenter (t + 2^k) (2^k - r) = false` without requiring `z - 2` or `z - 1` to settle. -/
theorem lhCenter_late_cross_pin_r_false_of_doubles_two_and_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r)) (hd : DoublesAt 2 ((t + 2) + r))
    (hset0 : settle ((t + 2) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 2) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 2) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 2 a L)
    (hw1 : WinWittAgree (t + 1) k 2 a L) :
    lhCenter (t + twopow k) (twopow k - r) = false := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k r (by omega)
    (by rw [show (t + r) + 2 = (t + 2) + r by omega]; exact hz)
    (by rw [show (t + r) + 2 = (t + 2) + r by omega]; exact hset0)
  rw [htwin]
  exact lhCenter_late_cross_pin_r_plus_one_false_of_doubles_two_and_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

theorem lhCenter_late_cross_pin_r_false_of_doubles_two_and_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r)) (hd : DoublesAt 2 ((t + 2) + r))
    (hset0 : SettledBy ((t + 2) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 2) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 2) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw0 : WinWittAgree t k 2 a L)
    (hw1 : WinWittAgree (t + 1) k 2 a L) :
    lhCenter (t + twopow k) (twopow k - r) = false :=
  lhCenter_late_cross_pin_r_false_of_doubles_two_and_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw0 hw1

/-- **Single-window below-threshold spatial `Q`-periodicity in `winWitt t (2^k)` from `DoublesAt Q z` and `WinWittAgree` (9.672)**:
for all `Q, z, t, k, r, a, L ∈ ℕ` with `t + Q < r`, `(t + Q) + r ≤ z`, and `z ≤ k`, if period `Q` doubles at `z` (`DoublesAt Q z`), `(t + Q) + r` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + Q))`. -/
theorem winWitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winWittAgree
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt Q z)
    (hset : settle ((t + Q) + r) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + Q)) := by
  have hi := hw (((t + twopow (k + 1)) - r) - a) (by omega)
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hcone : (t + Q) + r < twopow k := by
    have := twopow_gt_self k
    omega
  rw [show a + (((t + twopow (k + 1)) - r) - a) = (t + twopow (k + 1)) - r by omega,
    show ((t + twopow (k + 1)) - r) + Q = ((t + Q) + twopow (k + 1)) - r by omega,
    winWitt_scale_cross_zero_gap_periodic_of_doubles_le Q z t k r hr hle hk hd hset] at hi
  exact hi.symm

theorem winWitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winWittAgree_prop
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt Q z)
    (hset : SettledBy ((t + Q) + r) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + Q)) :=
  winWitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winWittAgree
    Q z t k r a L hr hle hk hd hset ha hL hw

/-- **Single-row below-threshold spatial `Q`-periodicity in `lhCenter (t + 2^k)` from `DoublesAt Q z` and Sector-2 zero-gap `WinWittAgree` (9.673)**:
for all `Q, z, t, k, r, a, L ∈ ℕ` with `t + Q < r`, `(t + Q) + r ≤ z`, and `z ≤ k`, if `DoublesAt Q z`, `(t + Q) + r` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `lhCenter (t + 2^k) (2^k - r) = lhCenter (t + 2^k) (2^k - (r + Q))`. -/
theorem lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt Q z)
    (hset : settle ((t + Q) + r) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + Q)) := by
  have hcone : (t + Q) + r < twopow k := by
    have := twopow_gt_self k
    omega
  have heq := lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q r a L hr hcone ha hL hw
  rw [lhCenter_late_cross_periodic_of_doubles_le Q z t k r hle hk hd hset] at heq
  exact heq.symm

theorem lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap_prop
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt Q z)
    (hset : SettledBy ((t + Q) + r) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - r) =
      lhCenter (t + twopow k) (twopow k - (r + Q)) :=
  lhCenter_late_cross_shift_eq_of_doubles_le_and_winWittAgree_zero_gap
    Q z t k r a L hr hle hk hd hset ha hL hw

/-- **Same-bit temporal `Q`-invariance of `winWitt` at `(t + 2^(k+1)) - r` below a doubling threshold under `WinWittAgree` (9.674)**:
for all `Q, z, t, k, r, a, L ∈ ℕ` with `t + Q < r`, `(t + Q) + r ≤ z`, and `z ≤ k`, if `DoublesAt Q z`, `(t + Q) + r` has settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + Q)`, `(t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - r) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)`. -/
theorem winWitt_scale_cross_zero_gap_same_bit_eq_of_doubles_le_and_winWittAgree
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt Q z)
    (hset : settle ((t + Q) + r) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + Q))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hcone : (t + Q) + r < twopow k := by
    have := twopow_gt_self k
    omega
  have hi := hw (((t + twopow (k + 1)) - (r + Q)) - a) (by omega)
  rw [show a + (((t + twopow (k + 1)) - (r + Q)) - a) =
      (t + twopow (k + 1)) - (r + Q) by omega,
    show ((t + twopow (k + 1)) - (r + Q)) + Q =
      (t + twopow (k + 1)) - r by omega] at hi
  rw [hi, ← winWitt_scale_cross_zero_gap_shift_eq_of_doubles_le_and_winWittAgree
    Q z t k r a L hr hle hk hd hset (by omega) hL hw]

theorem winWitt_scale_cross_zero_gap_same_bit_eq_of_doubles_le_and_winWittAgree_prop
    (Q z t k r a L : Nat)
    (hr : t + Q < r) (hle : (t + Q) + r ≤ z) (hk : z ≤ k)
    (hd : DoublesAt Q z)
    (hset : SettledBy ((t + Q) + r) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + Q))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - r) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) :=
  winWitt_scale_cross_zero_gap_same_bit_eq_of_doubles_le_and_winWittAgree
    Q z t k r a L hr hle hk hd hset ha hL hw

/-- **Exact zero-diagonal transport `lhCenter (t + 2^k) (2^k - r) = false` (`Q` diagonals below `z`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap (9.675)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q < r` and `(t + Q) + r ≤ k`, if `(t + Q) + r` is a zero diagonal that has settled by `(t + Q) + 2^k` (with NO `DoublesAt` hypothesis!), `a ≤ (t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `lhCenter (t + 2^k) (2^k - r) = false`. -/
theorem lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - r) = false := by
  have hcone : (t + Q) + r < twopow k := by
    have := twopow_gt_self k
    omega
  rw [← lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q r a L hr hcone ha hL hw]
  exact lhCenter_late_cross_of_zero_diag (t + Q) k r hk hz hset

theorem lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - r) = false :=
  lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact post-zero black-diagonal transport `lhCenter (t + 2^k) (2^k - (r + 2)) = true` (`Q` diagonals below `z + 2`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap (9.676)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r + 1` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal and `((t + Q) + r) + 2` has settled by `(t + Q) + 2^k` (with NO `DoublesAt` hypothesis!), `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `lhCenter (t + 2^k) (2^k - (r + 2)) = true`. -/
theorem lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true := by
  have hcone : (t + Q) + (r + 2) < twopow k := by
    have := twopow_gt_self k
    omega
  rw [← lhCenter_late_cross_eq_of_winWittAgree_zero_gap t k Q (r + 2) a L
    (by omega) hcone ha hL hw]
  exact lhCenter_late_cross_after_zero_diag (t + Q) k r hk hz hset2

theorem lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 2)) = true :=
  lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **1-step `lhCenter` complementation `Q` diagonals below `z + 1` from a SINGLE `WinWittAgree t k Q a L` at time `t` and bit `(t + 2^(k+1)) - (r + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.677)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r + 1` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal, `((t + Q) + r) + 2` has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`. -/
theorem lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have htrue := lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw
  rw [lhCenter_late_cross_step t k r (by omega), htrue, Bool.true_or, bxor_eq_xor]
  cases lhCenter (t + twopow k) (twopow k - (r + 1)) <;> decide

theorem lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter (t + twopow k) (twopow k - (r + 1)) :=
  lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

/-- **1-step Sector-2 `winWitt` bit flip at `(t + 2^(k+1)) - (r + 1)` from a SINGLE `WinWittAgree t k Q a L` at time `t` and bit `(t + 2^(k+1)) - (r + 2)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.678)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t ≤ r`, `t + Q ≤ r + 1`, and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal, `((t + Q) + r) + 2` has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`. -/
theorem winWitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winWittAgree
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 1) (by omega) (by omega),
    show (t + twopow (k + 1)) - (r + 1) = ((t + 1) + twopow (k + 1)) - (r + 2) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :=
  winWitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winWittAgree
    Q t k r a L ht hr hk hz hset2 ha hL hw

/-- **Exact pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true` (`Q` diagonals below `z + 2` at `t + 1`) from a SINGLE `WinWittAgree t k Q a L` across `(t + 2^(k+1)) - (r + 2)` and `(t + 2^(k+1)) - r` without `DoublesAt` (9.679)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q < r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal, `(t + Q) + r` and `((t + Q) + r) + 2` have settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2)`, `(t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 1)) = true`. -/
theorem lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hfalse := lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr (by omega) hz hset0 (by omega) hL hw
  have htrue := lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L (by omega) hk hz hset2 ha (by omega) hw
  have hstep := lhCenter_step_succ (t + twopow k) (twopow k - (r + 2))
  rw [show (t + twopow k) + 1 = (t + 1) + twopow k by omega,
    show (twopow k - (r + 2)) + 1 = twopow k - (r + 1) by omega,
    show (twopow k - (r + 2)) + 2 = twopow k - r by omega,
    hfalse, htrue, Bool.or_true] at hstep
  exact hstep

theorem lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Post-black reset spatial `Q`-flip in `winWitt (t + 1) (2^k)` at a doubling zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` (9.680)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - ((r + Q) + 1))`. -/
theorem winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      !(winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - ((r + Q) + 1)) := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_flip_at_shift_after_zero_diag_of_single_winWittAgree
      Q t k r a L (by omega) (by omega) hk hz (by omega) ha (by omega) hw,
    winWitt_scale_cross_zero_gap_shift_eq_step_one_of_doubles_and_winWittAgree
      Q t k r a L hr hk hz hd hset1 hset2 (by omega) hL hw]

theorem winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      !(wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - ((r + Q) + 1))) :=
  winWitt_scale_cross_zero_gap_reset_shift_flip_of_doubles_and_single_winWittAgree
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-- **Post-black reset spatial `Q`-flip in `lhCenter ((t + 1) + 2^k)` at a doubling zero diagonal from a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` (9.681)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal where period `Q` doubles, `((t + Q) + r) + 1` and `((t + Q) + r) + 2` have settled by `t + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2)`, `(t + 2^(k+1)) - (r + 1) ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2))`. -/
theorem lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
      Q t k r a L (by omega) hk hz (by omega) ha (by omega) hw,
    lhCenter_late_cross_reset_after_zero_diag t k (r + Q)
      (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by omega]; exact hk)
      (by rw [show t + (r + Q) = (t + Q) + r by omega]; exact hz)
      (by rw [show (t + (r + Q)) + 2 = ((t + Q) + r) + 2 by omega]; exact hset2),
    lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
      Q t k r a L hr (by omega) hz hd hset1 (by omega) hL hw]

theorem lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) =
      !lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) :=
  lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hd hset1 hset2 ha hL hw

/-! ### Batch 26: Single-Time `WinWittAgree` Sector-2 Bit Transport, Simultaneous Adjacent Bit Flips, Single-Time Twin Pinning, and Period-2 / Doubling Refutations (9.682–9.696) -/

/-- **Exact Sector-2 bit transport `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false` (`Q` diagonals below `z`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap (9.682)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q < r` and `(t + Q) + r ≤ k`, if `(t + Q) + r` is a zero diagonal that has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false`. -/
theorem winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) = false := by
  have hcone : (t + Q) + r < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_zero_gap t k r (by omega) (by omega)]
  exact lhCenter_late_cross_eq_false_at_shift_of_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset ha hL hw

theorem winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : (t + Q) + r ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - r)
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) = false :=
  winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree
    Q t k r a L hr hk hz hset ha hL hw

/-- **Exact Sector-2 post-zero black-diagonal transport `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true` (`Q` diagonals below `z + 2`) from a single `WinWittAgree t k Q a L` in the Sector-2 zero gap (9.683)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t ≤ r`, `t + Q ≤ r + 1`, and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal, `((t + Q) + r) + 2` has settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, and `WinWittAgree t k Q a L` holds, then `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 2)) = true`. -/
theorem winWitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winWittAgree
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 2)) = true := by
  have hcone : (t + Q) + (r + 2) < twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_scale_cross_zero_gap t k (r + 2) (by omega) (by omega)]
  exact lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winWittAgree_prop
    (Q t k r a L : Nat)
    (ht : t ≤ r) (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 2)) = true :=
  winWitt_scale_cross_zero_gap_eq_true_at_shift_after_zero_diag_and_winWittAgree
    Q t k r a L ht hr hk hz hset2 ha hL hw

/-- **Exact Sector-2 bit pinning `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = true` at `t + 1` from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.684)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q < r` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` is a zero diagonal, `(t + Q) + r` and `((t + Q) + r) + 2` have settled by `(t + Q) + 2^k`, `a ≤ (t + 2^(k+1)) - (r + 2)`, `(t + 2^(k+1)) - r ≤ a + L`, and `WinWittAgree t k Q a L` holds at time `t` alone, then `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = true`. -/
theorem winWitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) = true := by
  have h7 := gt_twopow_of_zero_diag_le ((t + Q) + r) k hk hz
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [show (t + twopow (k + 1)) - r = ((t + 1) + twopow (k + 1)) - (r + 1) by omega,
    winWitt_testBit_scale_cross_zero_gap (t + 1) k (r + 1) (by omega) (by omega)]
  exact lhCenter_late_cross_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

theorem winWitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) = true :=
  winWitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **1-step Sector-2 zero-to-one bit flip at `(t + 2^(k+1)) - r` (`Q` diagonals below `z`) from a SINGLE `WinWittAgree t k Q a L` at time `t` without `DoublesAt` or `WinWittAgree (t + 1)` (9.685)**:
combining `9.682` (`= false` at `t`) and `9.684` (`= true` at `t + 1`) proves `(winWitt (t + 1) (2^k)).testBit ((t + 2^(k+1)) - r) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` from `WinWittAgree t k Q a L` at time `t` alone. -/
theorem winWitt_scale_cross_zero_gap_step_flip_at_shift_of_zero_diag_and_single_winWittAgree
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : settle ((t + Q) + r) ≤ (t + Q) + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    (winWitt (t + 1) (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      !(winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  rw [winWitt_scale_cross_zero_gap_step_one_eq_true_at_shift_of_zero_diag_and_single_winWittAgree
      Q t k r a L hr hk hz hset0 hset2 ha hL hw,
    winWitt_scale_cross_zero_gap_eq_false_at_shift_of_zero_diag_and_winWittAgree
      Q t k r a L hr (by omega) hz hset0 (by omega) hL hw]
  rfl

theorem winWitt_scale_cross_zero_gap_step_flip_at_shift_of_zero_diag_and_single_winWittAgree_prop
    (Q t k r a L : Nat)
    (hr : t + Q < r) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hset0 : SettledBy ((t + Q) + r) ((t + Q) + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - r ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + twopow (k + 1)) - r) =
      !(wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) :=
  winWitt_scale_cross_zero_gap_step_flip_at_shift_of_zero_diag_and_single_winWittAgree
    Q t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Refutation of `WinWittAgree t k Q a L` at `(t + 2^(k+1)) - (r + 2)` when both `(t + Q) + r` and `(t + r) + 2` are zero diagonals (9.686)**:
for all `Q, t, k, r, a, L ∈ ℕ` with `t + Q ≤ r + 1` and `((t + Q) + r) + 2 ≤ k`, if `(t + Q) + r` and `(t + r) + 2` are zero diagonals, `(t + r) + 2` has settled by `t + 2^k`, `((t + Q) + r) + 2` has settled by `(t + Q) + 2^k`, and `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`, then `¬ WinWittAgree t k Q a L`. -/
theorem not_winWittAgree_at_shift_after_zero_diag_of_zero_diag_two
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz2 : IsZeroDiag ((t + r) + 2))
    (hset_z2 : settle ((t + r) + 2) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L) :
    ¬ WinWittAgree t k Q a L := by
  intro hw
  have htrue := lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr hk hz hset2 ha hL hw
  have hfalse : lhCenter (t + twopow k) (twopow k - (r + 2)) = false :=
    lhCenter_late_cross_of_zero_diag t k (r + 2) (by omega)
      (by rw [show t + (r + 2) = (t + r) + 2 by omega]; exact hz2)
      (by rw [show t + (r + 2) = (t + r) + 2 by omega]; exact hset_z2)
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem not_winWittAgree_at_shift_after_zero_diag_of_zero_diag_two_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz2 : IsZeroDiag ((t + r) + 2))
    (hset_z2 : SettledBy ((t + r) + 2) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L) :
    ¬ WinWittAgree t k Q a L :=
  not_winWittAgree_at_shift_after_zero_diag_of_zero_diag_two
    Q t k r a L hr hk hz hz2 hset_z2 hset2 ha hL

/-- **Twin-propagated exact pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` (`Q` diagonals below `z + 1`) from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.687)**:
combining `9.676` (`lhCenter (t + 2^k) (2^k - (r + 2)) = true`) with the Twin Identity Before a Zero Diagonal (`9.592`) for `(t + r) + 3` pins `lhCenter (t + 2^k) (2^k - (r + 1)) = true` without requiring `(t + r) + 1` or `(t + r) + 2` to settle and without `DoublesAt` or `WinWittAgree (t + 1)`. -/
theorem lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k (r + 1) (by omega)
    (by rw [show (t + (r + 1)) + 2 = (t + r) + 3 by omega]; exact hz3)
    (by rw [show (t + (r + 1)) + 2 = (t + r) + 3 by omega]; exact hset_z3)
  rw [htwin, show (r + 1) + 1 = r + 2 by omega]
  exact lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    Q t k r a L hr (by omega) hz hset2 ha hL hw

theorem lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact 1-step pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` (`Q` diagonals below `z + 3` at `t + 1`) from a SINGLE `WinWittAgree t k Q a L` at time `t` and `IsZeroDiag ((t + r) + 3)` without `DoublesAt` or `WinWittAgree (t + 1)` (9.688)**:
combining `9.677` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = !lhCenter (t + 2^k) (2^k - (r + 1))`) with `9.687` (`lhCenter (t + 2^k) (2^k - (r + 1)) = true`) pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false`. -/
theorem lhCenter_late_cross_step_one_pin_r_plus_two_false_of_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ (t + Q) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = false := by
  rw [lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
      Q t k r a L hr (by omega) hz hset2 ha hL hw,
    lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
      Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw]
  rfl

theorem lhCenter_late_cross_step_one_pin_r_plus_two_false_of_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r + 1) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) ((t + Q) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = false :=
  lhCenter_late_cross_step_one_pin_r_plus_two_false_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hz3 hset_z3 hset2 ha hL hw

/-- **Exact pinning `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` on the doubling diagonal `z + 1` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` (9.689)**:
combining `9.687` (`lhCenter (t + 2^k) (2^k - (r + 1)) = true`) with the spatial `Q`-flip `9.636` pins `lhCenter (t + 2^k) (2^k - ((r + Q) + 1)) = false` from `WinWittAgree t k Q a L` at time `t` alone. -/
theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) = false := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    Q t k r a L hr (by omega) hz hd hset1 (by omega) hL hw
  have hpin := lhCenter_late_cross_pin_r_plus_one_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L (by omega) hk hz hz3 hset_z3 (by omega) ha (by omega) hw
  rw [hpin] at hflip
  cases h : lhCenter (t + twopow k) (twopow k - ((r + Q) + 1))
  · rfl
  · rw [h] at hflip
    exact absurd hflip (by decide)

theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter (t + twopow k) (twopow k - ((r + Q) + 1)) = false :=
  lhCenter_late_cross_pin_doubling_diag_false_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **Exact post-black reset pinning `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = true` on diagonal `z + 3` from `DoublesAt Q ((t + Q) + r)`, `IsZeroDiag ((t + r) + 3)`, and a SINGLE `WinWittAgree t k Q a L` at time `t` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.690)**:
combining `9.688` (`lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false`) with `9.681` pins `lhCenter ((t + 1) + 2^k) (2^k - ((r + Q) + 2)) = true`. -/
theorem lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : settle ((t + r) + 3) ≤ t + twopow k)
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + Q) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) = true := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hflip := lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap
    Q t k r a L hr (by omega) hz hd hset1 hset2 ha hL hw
  have hpin := lhCenter_late_cross_step_one_pin_r_plus_two_false_of_single_winWittAgree_and_zero_diag_three
    Q t k r a L (by omega) hk hz hz3 hset_z3 (by omega) ha (by omega) hw
  rw [hpin] at hflip
  cases h : lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2))
  · rw [h] at hflip
    exact absurd hflip (by decide)
  · rfl

theorem lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 3 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hz3 : IsZeroDiag ((t + r) + 3))
    (hset_z3 : SettledBy ((t + r) + 3) (t + twopow k))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + Q) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k Q a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - ((r + Q) + 2)) = true :=
  lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_and_single_winWittAgree_and_zero_diag_three
    Q t k r a L hr hk hz hd hz3 hset_z3 hset1 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 1)) = true` two diagonals before ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.691)**:
when `Q = 3`, `(t + 3) + r = (t + r) + 3` is the zero diagonal itself, so a single `WinWittAgree t k 3 a L` at time `t` and bit `(t + 2^(k+1)) - (r + 2)` automatically pins `lhCenter (t + 2^k) (2^k - (r + 1)) = true`. -/
theorem lhCenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true := by
  have htwin := lhCenter_late_cross_twin_before_zero_diag t k (r + 1) (by omega)
    (by rw [show (t + (r + 1)) + 2 = (t + 3) + r by omega]; exact hz)
    (by rw [show (t + (r + 1)) + 2 = (t + 3) + r by omega]; exact hset0)
  rw [htwin, show (r + 1) + 1 = r + 2 by omega]
  exact lhCenter_late_cross_eq_true_at_shift_after_zero_diag_and_winWittAgree_zero_gap
    3 t k r a L (by omega) hk hz hset2 ha hL hw

theorem lhCenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 1)) = true :=
  lhCenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 single-time `WinWittAgree` 1-step pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` on ANY zero diagonal `z = (t + 3) + r` without `DoublesAt` or `WinWittAgree (t + 1)` (9.692)**:
combining `9.677` (`Q = 3`) with `9.691` pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 2)) = false` requiring only `settle ((t + 3) + r) ≤ t + 2^k` and `settle (((t + 3) + r) + 2) ≤ (t + 3) + 2^k`. -/
theorem lhCenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ (t + 3) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = false := by
  rw [lhCenter_late_cross_step_flip_at_shift_after_zero_diag_of_single_winWittAgree_zero_gap
      3 t k r a L (by omega) hk hz hset2 ha hL hw,
    lhCenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
      t k r a L hr hk hz hset0 hset2 ha hL hw]
  rfl

theorem lhCenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 2 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) ((t + 3) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 2)) = false :=
  lhCenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winWittAgree
    t k r a L hr hk hz hset0 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` pinning `lhCenter (t + 2^k) (2^k - (r + 4)) = false` on the doubling diagonal `z + 1` without `WinWittAgree (t + 1)` (9.693)**:
combining `9.691` with `9.636` (`Q = 3`) pins `lhCenter (t + 2^k) (2^k - (r + 4)) = false` from `WinWittAgree t k 3 a L` at time `t` alone. -/
theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 4)) = false := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hflip := lhCenter_late_cross_shift_flip_of_doubles_and_winWittAgree_zero_gap
    3 t k r a L hr (by omega) hz hd hset1 (by omega) hL hw
  have hpin := lhCenter_late_cross_pin_before_zero_diag_of_zero_diag_three_and_single_winWittAgree
    t k r a L (by omega) hk hz hset0 (by omega) ha (by omega) hw
  rw [hpin, show (r + 3) + 1 = r + 4 by omega] at hflip
  cases h : lhCenter (t + twopow k) (twopow k - (r + 4))
  · rfl
  · rw [h] at hflip
    exact absurd hflip (by decide)

theorem lhCenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter (t + twopow k) (twopow k - (r + 4)) = false :=
  lhCenter_late_cross_pin_doubling_diag_false_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Period-3 doubling single-time `WinWittAgree` post-black reset pinning `lhCenter ((t + 1) + 2^k) (2^k - (r + 5)) = true` on diagonal `z + 3` without `WinWittAgree (t + 1)` or `settle (z + 3)` (9.694)**:
combining `9.692` with `9.681` (`Q = 3`) pins `lhCenter ((t + 1) + 2^k) (2^k - (r + 5)) = true` from `WinWittAgree t k 3 a L` at time `t` alone. -/
theorem lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : settle ((t + 3) + r) ≤ t + twopow k)
    (hset1 : settle (((t + 3) + r) + 1) ≤ t + twopow k)
    (hset2 : settle (((t + 3) + r) + 2) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 5)) = true := by
  have h2k : twopow k ≤ twopow (k + 1) := by
    rw [twopow_succ]
    omega
  have hflip := lhCenter_late_cross_reset_shift_flip_of_doubles_and_single_winWittAgree_zero_gap
    3 t k r a L hr hk hz hd hset1 hset2 ha hL hw
  have hpin := lhCenter_late_cross_step_one_pin_r_plus_two_false_of_zero_diag_three_and_single_winWittAgree
    t k r a L (by omega) hk hz hset0 (by omega) ha (by omega) hw
  rw [hpin, show (r + 3) + 2 = r + 5 by omega] at hflip
  cases h : lhCenter ((t + 1) + twopow k) (twopow k - (r + 5))
  · rw [h] at hflip
    exact absurd hflip (by decide)
  · rfl

theorem lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree_prop
    (t k r a L : Nat)
    (hr : t + 3 ≤ r) (hk : ((t + 3) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 3) + r)) (hd : DoublesAt 3 ((t + 3) + r))
    (hset0 : SettledBy ((t + 3) + r) (t + twopow k))
    (hset1 : SettledBy (((t + 3) + r) + 1) (t + twopow k))
    (hset2 : SettledBy (((t + 3) + r) + 2) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (hw : WinWittAgree t k 3 a L) :
    lhCenter ((t + 1) + twopow k) (twopow k - (r + 5)) = true :=
  lhCenter_late_cross_step_one_pin_reset_diag_true_of_doubles_three_and_single_winWittAgree
    t k r a L hr hk hz hd hset0 hset1 hset2 ha hL hw

/-- **Refutation of `WinWittAgree t k 2 a L` at `(t + 2^(k+1)) - (r + 2)` across ANY zero diagonal `z = (t + 2) + r` without `DoublesAt` (9.695)**:
specializing `9.686` to `Q = 2` (where `(t + r) + 2 = (t + 2) + r = z` is the zero diagonal itself!) proves `¬ WinWittAgree t k 2 a L` whenever `(t + 2) + r` has settled by `t + 2^k`, `((t + 2) + r) + 2` has settled by `(t + 2) + 2^k`, and `a ≤ (t + 2^(k+1)) - (r + 2) ≤ a + L`. -/
theorem not_winWittAgree_two_at_shift_after_zero_diag
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r))
    (hset0 : settle ((t + 2) + r) ≤ t + twopow k)
    (hset2 : settle (((t + 2) + r) + 2) ≤ (t + 2) + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L) :
    ¬ WinWittAgree t k 2 a L :=
  not_winWittAgree_at_shift_after_zero_diag_of_zero_diag_two
    2 t k r a L (by omega) hk hz
    (by rw [show (t + r) + 2 = (t + 2) + r by omega]; exact hz)
    (by rw [show (t + r) + 2 = (t + 2) + r by omega]; exact hset0)
    hset2 ha hL

theorem not_winWittAgree_two_at_shift_after_zero_diag_prop
    (t k r a L : Nat)
    (hr : t + 1 ≤ r) (hk : ((t + 2) + r) + 2 ≤ k)
    (hz : IsZeroDiag ((t + 2) + r))
    (hset0 : SettledBy ((t + 2) + r) (t + twopow k))
    (hset2 : SettledBy (((t + 2) + r) + 2) ((t + 2) + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - (r + 2))
    (hL : (t + twopow (k + 1)) - (r + 2) ≤ a + L) :
    ¬ WinWittAgree t k 2 a L :=
  not_winWittAgree_two_at_shift_after_zero_diag
    t k r a L hr hk hz hset0 hset2 ha hL

/-- **Refutation of `WinWittAgree t k Q a L` across a `Q`-span at a doubling zero diagonal when `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = (winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))` (9.696)**:
by `9.646`, `WinWittAgree t k Q a L` across `[(t + 2^(k+1)) - ((r + Q) + 1), (t + 2^(k+1)) - (r + 1)]` forces `(winWitt (t + Q) (2^k)).testBit ((t + 2^(k+1)) - (r + 1)) = !(winWitt t (2^k)).testBit ((t + 2^(k+1)) - (r + 1))`, contradicting same-bit temporal `Q`-equality. -/
theorem not_winWittAgree_of_doubles_and_same_bit_eq
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : settle (((t + Q) + r) + 1) ≤ t + twopow k)
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (heq : (winWitt (t + Q) (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) =
      (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1))) :
    ¬ WinWittAgree t k Q a L := by
  intro hw
  have hflip := winWitt_scale_cross_zero_gap_same_bit_flip_of_doubles_and_winWittAgree
    Q t k r a L hr hk hz hd hset1 ha hL hw
  rw [heq] at hflip
  cases h : (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - (r + 1)) <;>
    rw [h] at hflip <;> exact absurd hflip (by decide)

theorem not_winWittAgree_of_doubles_and_same_bit_eq_prop
    (Q t k r a L : Nat)
    (hr : t + Q ≤ r) (hk : ((t + Q) + r) + 1 ≤ k)
    (hz : IsZeroDiag ((t + Q) + r)) (hd : DoublesAt Q ((t + Q) + r))
    (hset1 : SettledBy (((t + Q) + r) + 1) (t + twopow k))
    (ha : a ≤ (t + twopow (k + 1)) - ((r + Q) + 1))
    (hL : (t + twopow (k + 1)) - (r + 1) ≤ a + L)
    (heq : wittBitBool (winWitt (t + Q) (twopow k)) ((t + twopow (k + 1)) - (r + 1)) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - (r + 1))) :
    ¬ WinWittAgree t k Q a L :=
  not_winWittAgree_of_doubles_and_same_bit_eq
    Q t k r a L hr hk hz hd hset1 ha hL heq

end Rule30UOR.Interfaces
