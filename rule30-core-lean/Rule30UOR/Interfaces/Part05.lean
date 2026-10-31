module

public import Rule30UOR.Interfaces.Part04

/-!
# `Rule30UOR.Interfaces`, part 5

* Carrying `Q`-Periodicity from the Sector Times via Neighbourhood Agreement and Window Step 9.204
* Leftward Bijectivity, Symmetric Doubling of Right-Half Agreement Across the Periodic Center, and Window-Step 9.204 Sector Transport
* The Driven Right Half `rhCenter`, the `Φ` Fixed-Point Law from §6 (`Rule30UOR.Fixed`), Inward Right-Half Agreement (`RhBandAgree`), and Window-Step 9.204 Sector Refutations
* Multi-Step Right-Half Window Determination (`RhOrAgree`), Unconditional Right-Edge `RhBandAgree`, and `2^k`-Scale Band Transport
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

/-! ### Carrying `Q`-Periodicity from the Sector Times via Neighbourhood Agreement and Window Step 9.204 -/

/-- **Left-wing settled `restart` (`ldiag_settled_restart`)**: for every left diagonal `j ≤ k`, once `settle j ≤ t`, `ldiag j` repeats at every multiple `v * 2^k` uniformly for all `v : Nat`. -/
theorem ldiag_settled_restart (k j v t : Nat) (hj : j ≤ k) (hset : settle j ≤ t) :
    ldiag j (t + v * twopow k) = ldiag j t := by
  have hset' : settle j ≤ t + v * twopow k := by omega
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Kit.ldiag_eq_D,
    ← Rule30UOR.Intent.E_eq_D j (t + v * twopow k) hset',
    ← Rule30UOR.Intent.E_eq_D j t hset,
    twopow_eq_pow k,
    show v * 2 ^ k = (v * 2 ^ (k - j)) * 2 ^ j by
      rw [Nat.mul_assoc, ← Nat.pow_add, show k - j + j = k by omega]]
  exact Rule30UOR.ZeroDiagonals.E_per_mul j (v * 2 ^ (k - j)) t

/-- **Zero-state center `restart` in `ldiag` coordinates (`zcenter_restart_ldiag`)**: for every `d ≤ k` with `SettledAt d k` and every positive multiple `u ≥ 1`, `ldiag d (d + u * 2^k) = zcenter d`. -/
theorem zcenter_restart_ldiag (k d u : Nat) (hd : d ≤ k) (hu : 1 ≤ u) (hset : SettledAt d k) :
    ldiag d (d + u * twopow k) = zcenter d := by
  have h1 : d + u * twopow k = (d + twopow k) + (u - 1) * twopow k := by
    have hmul : u * twopow k = 1 * twopow k + (u - 1) * twopow k := by
      rw [← Nat.right_distrib, show 1 + (u - 1) = u by omega]
    omega
  rw [h1, ldiag_settled_restart k d (u - 1) (d + twopow k) hd hset]
  exact ldiag_settled_eq_zcenter d k hd hset

/-- **Unmasking the Late Center-Slot Frobenius Defect at `zcenter (d + 1) = true` (`frobDefect_row_late_center_slot_of_zcenter_true`)**: for `d + 1 ≤ k` and `SettledAt (d + 1) k` at a sector residue with `zcenter (d + 1) = true` and white centers at `d + 1` and `(d + 1) + 2^k`, the `zcenter (d + 1)` factor is `true`, unmasking `maskparity ((d + 1) + 2^k) 0 ⊕ maskparity (d + 1) 0` directly as bit `(d + 1) + 2^(k+1)` of `frobDefect k (row ((d + 1) + 2^k))`. -/
theorem frobDefect_row_late_center_slot_of_zcenter_true
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hz : zcenter (d + 1) = true)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    (frobDefect k (row ((d + 1) + twopow k))).testBit (((d + 1) + twopow k) + twopow k) =
      bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0) := by
  rw [frobDefect_row_late_center_slot_at_both_white_centers_eq_zcenter_and_maskparity_jump
    d k hk hset hw1 hw2, hz, Bool.true_and]

/-- **Unmasking the Window Step Triality of `maskparity · 0` at `zcenter (d + 1) = true` (`periodic_winWitt_step_late_center_slot_of_zcenter_true`)**: under `CenterPeriodic T P` (`0 < P`), for `T ≤ d + 1`, `d + 1 ≤ k`, `SettledAt (d + 1) k`, and `zcenter (d + 1) = true` with white centers at `d + 1`, `(d + 1) + lag P k`, and `(d + 1) + lag P (k + 1)`, the `maskparity · 0` triality is unmasked and equals the window step increment `wittRespBool ((d + 2) + 2^k) k ⊕ (phi (winWitt ((d + 1) + 2^k) (2^k))).testBit (((d + 2) + 2^k) + 2^k)`. -/
theorem periodic_winWitt_step_late_center_slot_of_zcenter_true
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hz : zcenter (d + 1) = true)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
      (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0)) =
      bxor (wittRespBool ((d + 2) + twopow k) k)
        ((phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k)) := by
  have hs := periodic_winWitt_step_late_center_slot_at_white_centers_eq_zcenter_and_maskparity_triality
    T P hP h d k ht hk hset hw0 hw1 hw2
  rw [hz, Bool.true_and] at hs
  rw [hs]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 2) + twopow k) + twopow k) <;>
    cases (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0 ^^
      (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0 ^^
        Rule30UOR.Scale.maskparity (d + 1) 0)) <;> rfl

/-- **Unmasking the Window Step Triality of Column `-1` at `zcenter (d + 1) = true` (`periodic_winWitt_step_late_colm1_slot_of_zcenter_true`)**: under `CenterPeriodic T P` (`0 < P`), for `T ≤ d + 1`, `d + 2 ≤ k`, `SettledAt (d + 1) k`, and `zcenter (d + 1) = true` with white centers at `d + 1`, `(d + 1) + lag P k`, and `(d + 1) + lag P (k + 1)`, the column-`-1` triality is unmasked and equals the window step increment at `((d + 3) + 2^k) + 2^k`. -/
theorem periodic_winWitt_step_late_colm1_slot_of_zcenter_true
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hz : zcenter (d + 1) = true)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
      (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1))) =
      bxor ((winWitt ((d + 2) + twopow k) (twopow k)).testBit (((d + 3) + twopow k) + twopow k))
        ((phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 3) + twopow k) + twopow k)) := by
  have hs := periodic_winWitt_step_late_colm1_slot_at_white_centers_eq_zcenter_and_colm1_triality
    T P hP h d k ht hk hset hw0 hw1 hw2
  rw [hz, Bool.true_and] at hs
  rw [hs]
  simp only [bxor_eq_xor]
  cases (phi (winWitt ((d + 1) + twopow k) (twopow k))).testBit (((d + 3) + twopow k) + twopow k) <;>
    cases (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)) ^^
      (ldiag (d + twopow k) ((d + 1) + twopow k) ^^ ldiag d (d + 1))) <;> rfl

/-- Neighbourhood `Q`-agreement of `row`: at time `t` and `t + Q`, `row (t + Q)` at bits `[a + Q, a + L + Q]` agrees with `row t` at bits `[a, a + L]`. -/
def RowAgree (t Q a L : Nat) : Prop :=
  ∀ i, i ≤ L → (row (t + Q)).testBit (a + i + Q) = (row t).testBit (a + i)

/-- Neighbourhood `Q`-agreement of `winWitt · (2^k)`: at time `t` and `t + Q`, `winWitt (t + Q) (2^k)` at bits `[a + Q, a + L + Q]` agrees with `winWitt t (2^k)` at bits `[a, a + L]`. -/
def WinWittAgree (t k Q a L : Nat) : Prop :=
  ∀ i, i ≤ L →
    (winWitt (t + Q) (twopow k)).testBit (a + i + Q) =
      (winWitt t (twopow k)).testBit (a + i)

/-- **Sub-interval monotonicity of `RowAgree` (`rowAgree_mono`)**: if `RowAgree t Q a L` holds on `[a, a + L]` and `[a', a' + L'] ⊆ [a, a + L]`, then `RowAgree t Q a' L'` holds. -/
theorem rowAgree_mono (t Q a L a' L' : Nat) (ha : a ≤ a') (hL : a' + L' ≤ a + L)
    (h : RowAgree t Q a L) : RowAgree t Q a' L' := by
  intro i hi
  have hj : (a' - a) + i ≤ L := by omega
  have heq := h ((a' - a) + i) hj
  rwa [show a + ((a' - a) + i) = a' + i by omega] at heq

/-- **Sub-interval monotonicity of `WinWittAgree` (`winWittAgree_mono`)**: if `WinWittAgree t k Q a L` holds on `[a, a + L]` and `[a', a' + L'] ⊆ [a, a + L]`, then `WinWittAgree t k Q a' L'` holds. -/
theorem winWittAgree_mono (t k Q a L a' L' : Nat) (ha : a ≤ a') (hL : a' + L' ≤ a + L)
    (h : WinWittAgree t k Q a L) : WinWittAgree t k Q a' L' := by
  intro i hi
  have hj : (a' - a) + i ≤ L := by omega
  have heq := h ((a' - a) + i) hj
  rwa [show a + ((a' - a) + i) = a' + i by omega] at heq

/-- **One-step Rule 30 propagation of `RowAgree` (`rowAgree_step`)**: each step `t ↦ t + 1` loses one cell of agreement on each side around the moving center (`[a, a + L + 2] ↦ [a + 2, (a + 2) + L]`). -/
theorem rowAgree_step (t Q a L : Nat) (h : RowAgree t Q a (L + 2)) :
    RowAgree (t + 1) Q (a + 2) L := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 1) (by omega)
  have h2 := h (i + 2) (by omega)
  rw [show (t + 1) + Q = (t + Q) + 1 by omega]
  change (phi (row (t + Q))).testBit ((a + 2) + i + Q) = (phi (row t)).testBit ((a + 2) + i)
  rw [show (a + 2) + i + Q = (a + i + Q) + 2 by omega,
    show (a + 2) + i = (a + i) + 2 by omega,
    phi_testBit_add_two (row (t + Q)) (a + i + Q),
    phi_testBit_add_two (row t) (a + i),
    show (a + i + Q) + 2 = a + (i + 2) + Q by omega,
    show (a + i + Q) + 1 = a + (i + 1) + Q by omega,
    show (a + i) + 2 = a + (i + 2) by omega,
    show (a + i) + 1 = a + (i + 1) by omega,
    h0, h1, h2]

/-- **`s`-step Rule 30 propagation of `RowAgree` (`rowAgree_steps`)**: advancing `s` steps from `t` to `t + s` carries `Q`-agreement from `[a, a + L + 2 * s]` to `[a + 2 * s, a + 2 * s + L]`. -/
theorem rowAgree_steps (t Q a L s : Nat) (h : RowAgree t Q a (L + 2 * s)) :
    RowAgree (t + s) Q (a + 2 * s) L := by
  induction s generalizing t a L with
  | zero =>
    simpa using h
  | succ s ih =>
    have h' : RowAgree t Q a ((L + 2 * s) + 2) := by
      simpa [Nat.mul_succ, Nat.add_assoc] using h
    have hstep := rowAgree_step t Q a (L + 2 * s) h'
    have ih' := ih (t + 1) (a + 2) L hstep
    intro i hi
    have heq := ih' i hi
    rwa [show (t + 1) + s = t + (s + 1) by omega,
      show (a + 2) + 2 * s + i = a + 2 * (s + 1) + i by omega] at heq

/-- **Scaled-row (`phiScale k (row t)`) agreement from three-sector `RowAgree` (`phiScale_row_testBit_eq_of_rowAgree`)**: for `2^(k+1) ≤ a` and `i ≤ L`, if `RowAgree` holds on the three shifted intervals `a - 2^(k+1)`, `a - 2^k`, and `a`, then `S_k(row (t + Q))` at bit `a + i + Q` agrees with `S_k(row t)` at bit `a + i`. -/
theorem phiScale_row_testBit_eq_of_rowAgree (t k Q a L i : Nat)
    (ha : twopow (k + 1) ≤ a) (hi : i ≤ L)
    (h0 : RowAgree t Q (a - twopow (k + 1)) L)
    (h1 : RowAgree t Q (a - twopow k) L)
    (h2 : RowAgree t Q a L) :
    (phiScale k (row (t + Q))).testBit (a + i + Q) =
      (phiScale k (row t)).testBit (a + i) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  change (((row (t + Q)) ^^^ ((row (t + Q)) <<< twopow k)) ^^^
    ((row (t + Q)) <<< (twopow k + twopow k))).testBit (a + i + Q) =
    (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit (a + i)
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (a + i + Q ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (a + i + Q ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  have d3 : decide (a + i ≥ twopow k) = true := decide_eq_true (by omega)
  have d4 : decide (a + i ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [d1, d2, d3, d4,
    show a + i + Q - twopow k = (a - twopow k) + i + Q by omega,
    show a + i + Q - (twopow k + twopow k) = (a - twopow (k + 1)) + i + Q by omega,
    show a + i - twopow k = (a - twopow k) + i by omega,
    show a + i - (twopow k + twopow k) = (a - twopow (k + 1)) + i by omega,
    h2 i hi, h1 i hi, h0 i hi]

/-- **Frobenius defect (`frobDefect k (row t)`) agreement from three-sector `RowAgree` (`frobDefect_row_testBit_eq_of_rowAgree`)**: for `2^(k+1) ≤ a` and `i ≤ L`, if `RowAgree` holds with width `L + 1` on `a - 2^(k+1)`, `a - 2^k`, and `a`, then `δ_k(row (t + Q))` at bit `a + i + 1 + Q` agrees with `δ_k(row t)` at bit `a + i + 1`. -/
theorem frobDefect_row_testBit_eq_of_rowAgree (t k Q a L i : Nat)
    (ha : twopow (k + 1) ≤ a) (hi : i ≤ L)
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1)) :
    (frobDefect k (row (t + Q))).testBit (a + i + 1 + Q) =
      (frobDefect k (row t)).testBit (a + i + 1) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hfQ := frobDefect_row_testBit_outside_cone (t + Q) k ((a - twopow k) + i + Q) (by omega)
  have hf0 := frobDefect_row_testBit_outside_cone t k ((a - twopow k) + i) (by omega)
  rw [show ((a - twopow k) + i + Q + 1) + twopow k = a + i + 1 + Q by omega,
    show (a - twopow k) + i + Q + 1 = (a - twopow k) + (i + 1) + Q by omega,
    show ((a - twopow k) + i + Q) - twopow k = (a - twopow (k + 1)) + i + Q by omega,
    show ((a - twopow k) + i + Q) + twopow k = a + i + Q by omega,
    show ((a - twopow k) + (i + 1) + Q) - twopow k = (a - twopow (k + 1)) + (i + 1) + Q by omega] at hfQ
  rw [show ((a - twopow k) + i + 1) + twopow k = a + i + 1 by omega,
    show (a - twopow k) + i + 1 = (a - twopow k) + (i + 1) by omega,
    show ((a - twopow k) + i) - twopow k = (a - twopow (k + 1)) + i by omega,
    show ((a - twopow k) + i) + twopow k = a + i by omega,
    show ((a - twopow k) + (i + 1)) - twopow k = (a - twopow (k + 1)) + (i + 1) by omega] at hf0
  have hr2_0 := h2 i (by omega)
  have hr2_1 := h2 (i + 1) (by omega)
  have hr1_0 := h1 i (by omega)
  have hr1_1 := h1 (i + 1) (by omega)
  have hr0_0 := h0 i (by omega)
  have hr0_1 := h0 (i + 1) (by omega)
  simp only [row_testBit] at hr2_0 hr2_1 hr1_0 hr1_1 hr0_0 hr0_1
  rw [hfQ, hf0,
    show a + i + 1 + Q = a + (i + 1) + Q by omega,
    show a + i + 1 = a + (i + 1) by omega,
    hr2_0, hr2_1, hr1_0, hr1_1, hr0_0, hr0_1]

/-- **Cross-carry (`crossCarry (phiScale k (row t)) (winWitt t (2^k))`) agreement from three-sector `RowAgree` and `WinWittAgree` (`crossCarry_testBit_eq_of_rowAgree_winWittAgree`)**: for `2^(k+1) ≤ a` and `i ≤ L`, if `WinWittAgree` and the three-sector `RowAgree` hold with width `L + 1`, then the cross-carry at `(t + Q, a + i + 1 + Q)` agrees with `(t, a + i + 1)`. -/
theorem crossCarry_testBit_eq_of_rowAgree_winWittAgree (t k Q a L i : Nat)
    (ha : twopow (k + 1) ≤ a) (hi : i ≤ L)
    (hw : WinWittAgree t k Q a (L + 1))
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1)) :
    (crossCarry (phiScale k (row (t + Q))) (winWitt (t + Q) (twopow k))).testBit (a + i + 1 + Q) =
      (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit (a + i + 1) := by
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hs0 := phiScale_row_testBit_eq_of_rowAgree t k Q a (L + 1) i ha (by omega) h0 h1 h2
  have hs1 := phiScale_row_testBit_eq_of_rowAgree t k Q a (L + 1) (i + 1) ha (by omega) h0 h1 h2
  have hw0 := hw i (by omega)
  have hw1 := hw (i + 1) (by omega)
  let SQ := phiScale k (row (t + Q))
  let S0 := phiScale k (row t)
  let WQ := winWitt (t + Q) (twopow k)
  let W0 := winWitt t (twopow k)
  change ((SQ &&& (WQ <<< 1)) ^^^ (WQ &&& (SQ <<< 1))).testBit (a + i + 1 + Q) =
    ((S0 &&& (W0 <<< 1)) ^^^ (W0 &&& (S0 <<< 1))).testBit (a + i + 1)
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  have d1 : decide (a + i + 1 + Q ≥ 1) = true := decide_eq_true (by omega)
  have d2 : decide (a + i + 1 ≥ 1) = true := decide_eq_true (by omega)
  rw [d1, d2, Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and,
    show a + i + 1 + Q - 1 = a + i + Q by omega,
    show a + i + 1 - 1 = a + i by omega,
    show a + i + 1 + Q = a + (i + 1) + Q by omega,
    show a + i + 1 = a + (i + 1) by omega,
    hs0, hs1, hw0, hw1]

/-- **One-Step Window Propagation of `WinWittAgree` via Theorem 9.204 (`winWittAgree_step`)**:
    for `2^(k+1) ≤ a`, each step `t ↦ t + 1` of the window step 9.204 (`winWitt_step_frobDefect_testBit_succ`) loses one cell of agreement on each side, advancing `WinWittAgree t k Q a (L + 2)` to `WinWittAgree (t + 1) k Q (a + 2) L` whenever the rows at `t` and `t + Q` agree on the three-sector stencil of width `L + 1`! -/
theorem winWittAgree_step (t k Q a L : Nat) (ha : twopow (k + 1) ≤ a)
    (hw : WinWittAgree t k Q a (L + 2))
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1)) :
    WinWittAgree (t + 1) k Q (a + 2) L := by
  intro i hi
  have hstepQ := winWitt_step_frobDefect_testBit_succ (t + Q) k (a + i + 1 + Q)
  have hstep0 := winWitt_step_frobDefect_testBit_succ t k (a + i + 1)
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show (a + 2) + i + Q = (a + i + 1 + Q) + 1 by omega,
    show (a + 2) + i = (a + i + 1) + 1 by omega,
    hstepQ, hstep0]
  have hphi :
      (phi (winWitt (t + Q) (twopow k))).testBit ((a + i + 1 + Q) + 1) =
        (phi (winWitt t (twopow k))).testBit ((a + i + 1) + 1) := by
    rw [show (a + i + 1 + Q) + 1 = (a + i + Q) + 2 by omega,
      show (a + i + 1) + 1 = (a + i) + 2 by omega,
      phi_testBit_add_two (winWitt (t + Q) (twopow k)) (a + i + Q),
      phi_testBit_add_two (winWitt t (twopow k)) (a + i),
      show (a + i + Q) + 2 = a + (i + 2) + Q by omega,
      show (a + i + Q) + 1 = a + (i + 1) + Q by omega,
      show (a + i) + 2 = a + (i + 2) by omega,
      show (a + i) + 1 = a + (i + 1) by omega,
      hw i (by omega), hw (i + 1) (by omega), hw (i + 2) (by omega)]
  have hhw' : WinWittAgree t k Q a (L + 1) :=
    winWittAgree_mono t k Q a (L + 2) a (L + 1) (by omega) (by omega) hw
  have hcc := crossCarry_testBit_eq_of_rowAgree_winWittAgree t k Q a L i ha hi hhw' h0 h1 h2
  have hdf := frobDefect_row_testBit_eq_of_rowAgree t k Q a L i ha hi h0 h1 h2
  rw [hphi, hcc, hdf]

/-- **`s`-Step Window Propagation of `WinWittAgree` via Theorem 9.204 (`winWittAgree_steps`)**:
    for `2^(k+1) ≤ a` and any `s : Nat`, advancing `s` steps via the window step 9.204 carries `Q`-agreement from width `L + 2 * s` at time `t` to `[a + 2 * s, a + 2 * s + L]` at time `t + s`! -/
theorem winWittAgree_steps (t k Q a L s : Nat) (ha : twopow (k + 1) ≤ a)
    (hw : WinWittAgree t k Q a (L + 2 * s))
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 2 * s))
    (h1 : RowAgree t Q (a - twopow k) (L + 2 * s))
    (h2 : RowAgree t Q a (L + 2 * s)) :
    WinWittAgree (t + s) k Q (a + 2 * s) L := by
  induction s generalizing t a L with
  | zero =>
    simpa using hw
  | succ s ih =>
    have hw' : WinWittAgree t k Q a ((L + 2 * s) + 2) := by
      simpa [Nat.mul_succ, Nat.add_assoc] using hw
    have h0' : RowAgree t Q (a - twopow (k + 1)) ((L + 2 * s) + 2) := by
      simpa [Nat.mul_succ, Nat.add_assoc] using h0
    have h1' : RowAgree t Q (a - twopow k) ((L + 2 * s) + 2) := by
      simpa [Nat.mul_succ, Nat.add_assoc] using h1
    have h2' : RowAgree t Q a ((L + 2 * s) + 2) := by
      simpa [Nat.mul_succ, Nat.add_assoc] using h2
    have h0_sub : RowAgree t Q (a - twopow (k + 1)) ((L + 2 * s) + 1) :=
      rowAgree_mono t Q (a - twopow (k + 1)) ((L + 2 * s) + 2) (a - twopow (k + 1)) ((L + 2 * s) + 1)
        (by omega) (by omega) h0'
    have h1_sub : RowAgree t Q (a - twopow k) ((L + 2 * s) + 1) :=
      rowAgree_mono t Q (a - twopow k) ((L + 2 * s) + 2) (a - twopow k) ((L + 2 * s) + 1)
        (by omega) (by omega) h1'
    have h2_sub : RowAgree t Q a ((L + 2 * s) + 1) :=
      rowAgree_mono t Q a ((L + 2 * s) + 2) a ((L + 2 * s) + 1)
        (by omega) (by omega) h2'
    have hw_step := winWittAgree_step t k Q a (L + 2 * s) ha hw' h0_sub h1_sub h2_sub
    have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
    have h0_step : RowAgree (t + 1) Q ((a + 2) - twopow (k + 1)) (L + 2 * s) := by
      rw [show (a + 2) - twopow (k + 1) = (a - twopow (k + 1)) + 2 by omega]
      exact rowAgree_step t Q (a - twopow (k + 1)) (L + 2 * s) h0'
    have h1_step : RowAgree (t + 1) Q ((a + 2) - twopow k) (L + 2 * s) := by
      rw [show (a + 2) - twopow k = (a - twopow k) + 2 by omega]
      exact rowAgree_step t Q (a - twopow k) (L + 2 * s) h1'
    have h2_step : RowAgree (t + 1) Q (a + 2) (L + 2 * s) :=
      rowAgree_step t Q a (L + 2 * s) h2'
    have ih' := ih (t + 1) (a + 2) L (by omega) hw_step h0_step h1_step h2_step
    intro i hi
    have heq := ih' i hi
    rwa [show (t + 1) + s = t + (s + 1) by omega,
      show (a + 2) + 2 * s + i = a + 2 * (s + 1) + i by omega] at heq

/-- **Carrying `Q`-Periodicity of `wittRespBool` Forward by `s` Steps via Window Step 9.204 (`wittRespBool_eq_of_winWittAgree_steps`)**:
    if at a time `t0` with `2^k + s ≤ t0`, `WinWittAgree` and the three-sector `RowAgree` hold on the symmetric neighbourhood of radius `s` (`width = 2 * s`) around the center slot `t0 + 2^k`, then `s` steps of 9.204 carry `Q`-periodicity to the center slot at time `t0 + s`: `wittRespBool (t0 + s + Q) k = wittRespBool (t0 + s) k`. -/
theorem wittRespBool_eq_of_winWittAgree_steps (t0 k Q s : Nat)
    (ht0 : twopow k + s ≤ t0)
    (hw : WinWittAgree t0 k Q ((t0 + twopow k) - s) (2 * s))
    (h0 : RowAgree t0 Q (((t0 + twopow k) - s) - twopow (k + 1)) (2 * s))
    (h1 : RowAgree t0 Q (((t0 + twopow k) - s) - twopow k) (2 * s))
    (h2 : RowAgree t0 Q ((t0 + twopow k) - s) (2 * s)) :
    wittRespBool ((t0 + s) + Q) k = wittRespBool (t0 + s) k := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hsteps := winWittAgree_steps t0 k Q ((t0 + twopow k) - s) 0 s (by omega)
    (by simpa using hw) (by simpa using h0) (by simpa using h1) (by simpa using h2)
  have h0_eq := hsteps 0 (by omega)
  rw [show ((t0 + twopow k) - s) + 2 * s + 0 + Q = ((t0 + s) + Q) + twopow k by omega,
    show ((t0 + twopow k) - s) + 2 * s + 0 = (t0 + s) + twopow k by omega] at h0_eq
  exact h0_eq

/-- **Carrying `Q`-Periodicity of Column `-1` Forward by `s` Steps from Neighbourhood Agreement (`colm1_eq_of_rowAgree_steps`)**:
    for `s ≤ t0 + 2`, if `RowAgree (t0 + 1) Q ((t0 + 2) - s) (2 * s)` holds on the radius-`s` neighbourhood around column `-1` at time `t0 + 1`, then `s` steps of Rule 30 carry `Q`-agreement to column `-1` at time `t0 + s + 1`: `ldiag ((t0 + s) + Q) ((t0 + s + 1) + Q) = ldiag (t0 + s) (t0 + s + 1)`. -/
theorem colm1_eq_of_rowAgree_steps (t0 Q s : Nat) (hs : s ≤ t0 + 2)
    (h : RowAgree (t0 + 1) Q ((t0 + 2) - s) (2 * s)) :
    ldiag ((t0 + s) + Q) ((t0 + s + 1) + Q) = ldiag (t0 + s) (t0 + s + 1) := by
  have hsteps := rowAgree_steps (t0 + 1) Q ((t0 + 2) - s) 0 s (by simpa using h)
  have h0_eq := hsteps 0 (by omega)
  rw [show (t0 + 1) + s + Q = ((t0 + s) + Q) + 1 by omega,
    show (t0 + 1) + s = (t0 + s) + 1 by omega,
    show ((t0 + 2) - s) + 2 * s + 0 + Q = ((t0 + s) + Q) + 2 * 1 by omega,
    show ((t0 + 2) - s) + 2 * s + 0 = (t0 + s) + 2 * 1 by omega,
    row_testBit, row_testBit,
    ← ldiag_eq_rdiag ((t0 + s) + Q) 1,
    ← ldiag_eq_rdiag (t0 + s) 1,
    show ((t0 + s) + Q) + 1 = (t0 + s + 1) + Q by omega] at h0_eq
  exact h0_eq

/-- **Carrying `m * P`-Periodicity of `maskparity · 0` Forward by `s` Steps from Neighbourhood Agreement (`maskparity_zero_eq_of_rowAgree_steps`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ t0 + s + 1` and `s ≤ t0 + 2`, if `RowAgree (t0 + 1) (m * P) ((t0 + 2) - s) (2 * s)` holds at time `t0 + 1`, then `s` steps carry `m * P`-agreement to `maskparity · 0` at time `t0 + s + 1`! -/
theorem maskparity_zero_eq_of_rowAgree_steps
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t0 s : Nat) (ht : T ≤ t0 + s + 1) (hs : s ≤ t0 + 2)
    (h : RowAgree (t0 + 1) (m * P) ((t0 + 2) - s) (2 * s)) :
    Rule30UOR.Scale.maskparity ((t0 + s + 1) + m * P) 0 =
      Rule30UOR.Scale.maskparity (t0 + s + 1) 0 := by
  have hcol := colm1_eq_of_rowAgree_steps t0 (m * P) s hs h
  have hdef := periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul T P hP hper m (t0 + s) ht
  rw [show ((t0 + s) + m * P) + 1 = (t0 + s + 1) + m * P by omega] at hdef
  rw [hcol, bxor_eq_xor, bxor_eq_xor, Bool.xor_self] at hdef
  revert hdef
  cases Rule30UOR.Scale.maskparity ((t0 + s + 1) + m * P) 0 <;>
    cases Rule30UOR.Scale.maskparity (t0 + s + 1) 0 <;> decide

/-- **Carrying `Q`-Periodicity from a Sector Residue Class `d + 1 (mod 2^k)` to Every Residue `mod 2^k` (`colNegOnePeriodic_of_sector_rowAgree`)**:
    if at a fixed scale `k` and sector residue `d + 1`, the radius-`2^k` neighbourhood agreement `RowAgree ((d + u * 2^k) + 1) Q (((d + u * 2^k) + 2) - 2^k) (2 * 2^k)` holds at all sector times `(d + 1) + u * 2^k` for `u ≥ U` (`1 ≤ U`), then advancing by `s = (t - (d + U * 2^k)) % 2^k < 2^k` steps carries `Q`-periodicity of column `-1` to EVERY residue `mod 2^k`, establishing `ColNegOnePeriodic (d + U * 2^k) Q`! -/
theorem colNegOnePeriodic_of_sector_rowAgree (k d U Q : Nat) (hU : 1 ≤ U)
    (hsec : ∀ u, U ≤ u →
      RowAgree ((d + u * twopow k) + 1) Q
        (((d + u * twopow k) + 2) - twopow k) (2 * twopow k)) :
    ColNegOnePeriodic (d + U * twopow k) Q := by
  intro t ht
  have hpos : 0 < twopow k := by
    have := twopow_gt_self k
    omega
  obtain ⟨delta, hdelta⟩ : ∃ delta, t = (d + U * twopow k) + delta := ⟨t - (d + U * twopow k), by omega⟩
  obtain ⟨q, s, hdiv, hs_lt⟩ : ∃ q s, delta = q * twopow k + s ∧ s < twopow k :=
    ⟨delta / twopow k, delta % twopow k,
      by rw [Nat.mul_comm, Nat.div_add_mod],
      Nat.mod_lt delta hpos⟩
  have hu : U ≤ U + q := by omega
  have ht0_eq : t = (d + (U + q) * twopow k) + s := by
    rw [Nat.add_mul]
    omega
  have hs_le : s ≤ (d + (U + q) * twopow k) + 2 := by
    have h1 : 1 * twopow k ≤ (U + q) * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
    omega
  have h_u := hsec (U + q) hu
  have h_sub : RowAgree ((d + (U + q) * twopow k) + 1) Q
      (((d + (U + q) * twopow k) + 2) - s) (2 * s) :=
    rowAgree_mono ((d + (U + q) * twopow k) + 1) Q
      (((d + (U + q) * twopow k) + 2) - twopow k) (2 * twopow k)
      (((d + (U + q) * twopow k) + 2) - s) (2 * s)
      (by omega) (by omega) h_u
  have hcol := colm1_eq_of_rowAgree_steps (d + (U + q) * twopow k) Q s hs_le h_sub
  rwa [← ht0_eq] at hcol

/-- **Refutation of Sector-Time Radius-`2^k` Neighbourhood Agreement at Any Multiple `Q = m * P` (`not_sector_rowAgree_mul`)**:
    under `CenterPeriodic T P` (`0 < P`), for any scale `k`, sector residue `d + 1`, threshold `U ≥ 1`, and positive multiple `m > 0`, the radius-`2^k` neighbourhood agreement `RowAgree ((d + u * 2^k) + 1) (m * P) (((d + u * 2^k) + 2) - 2^k) (2 * 2^k)` cannot hold for all `u ≥ U`, because carrying it across all residues `mod 2^k` yields `ColNegOnePeriodic`, refuted by `not_periodic_colm1_mul`! -/
theorem not_sector_rowAgree_mul
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (hU : 1 ≤ U) (hm : 0 < m)
    (hsec : ∀ u, U ≤ u →
      RowAgree ((d + u * twopow k) + 1) (m * P)
        (((d + u * twopow k) + 2) - twopow k) (2 * twopow k)) :
    False := by
  have hcol := colNegOnePeriodic_of_sector_rowAgree k d U (m * P) hU hsec
  exact not_periodic_colm1_mul T P hP h (d + U * twopow k) m hm hcol

/-- Paper-facing predicate `SectorRowAgree k d U Q`: for all `u ≥ U`, `RowAgree ((d + u * 2^k) + 1) Q (((d + u * 2^k) + 2) - 2^k) (2 * 2^k)` holds at the sector time `(d + 1) + u * 2^k`. -/
def SectorRowAgree (k d U Q : Nat) : Prop :=
  ∀ u, U ≤ u →
    RowAgree ((d + u * twopow k) + 1) Q
      (((d + u * twopow k) + 2) - twopow k) (2 * twopow k)

theorem colNegOnePeriodic_of_sector_rowAgree_prop (k d U Q : Nat) (hU : 1 ≤ U)
    (hsec : SectorRowAgree k d U Q) :
    ColNegOnePeriodic (d + U * twopow k) Q :=
  colNegOnePeriodic_of_sector_rowAgree k d U Q hU hsec

theorem not_sector_rowAgree_mul_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (hU : 1 ≤ U) (hm : 0 < m) :
    ¬ SectorRowAgree k d U (m * P) :=
  not_sector_rowAgree_mul T P hP h k d U m hU hm

theorem zcenter_restart_ldiag_prop (k d u : Nat) (hd : d ≤ k) (hu : 1 ≤ u) (hset : SettledAt d k) :
    ZCenterEq d (ldiag d (d + u * twopow k)) := by
  unfold ZCenterEq
  exact (zcenter_restart_ldiag k d u hd hu hset).symm

theorem frobDefect_row_late_center_slot_of_zcenter_true_prop
    (d k : Nat) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hz : ZCenterEq (d + 1) true)
    (hw1 : Rule30UOR.Core.center (d + 1) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + twopow k) = false) :
    BitFrobDefectEq k (row ((d + 1) + twopow k)) (((d + 1) + twopow k) + twopow k)
      (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0)) := by
  unfold BitFrobDefectEq
  rw [bit_eq_bton_testBit,
    frobDefect_row_late_center_slot_of_zcenter_true d k hk hset hz hw1 hw2]

theorem periodic_winWitt_step_late_center_slot_of_zcenter_true_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 1 ≤ k) (hset : SettledAt (d + 1) k)
    (hz : ZCenterEq (d + 1) true)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow (k + 1)) 0)
      (bxor (Rule30UOR.Scale.maskparity ((d + 1) + twopow k) 0)
        (Rule30UOR.Scale.maskparity (d + 1) 0)) =
      bxor (wittRespBool ((d + 2) + twopow k) k)
        (wittBitBool (phi (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 2) + twopow k) + twopow k)) := by
  unfold wittBitBool
  exact periodic_winWitt_step_late_center_slot_of_zcenter_true
    T P hP h d k ht hk hset hz hw0 hw1 hw2

theorem periodic_winWitt_step_late_colm1_slot_of_zcenter_true_prop
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (ht : T ≤ d + 1) (hk : d + 2 ≤ k) (hset : SettledAt (d + 1) k)
    (hz : ZCenterEq (d + 1) true)
    (hw0 : Rule30UOR.Core.center (d + 1) = false)
    (hw1 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P k) = false)
    (hw2 : Rule30UOR.Core.center ((d + 1) + Rule30UOR.Scale.lag P (k + 1)) = false) :
    bxor (ldiag (d + twopow (k + 1)) ((d + 1) + twopow (k + 1)))
      (bxor (ldiag (d + twopow k) ((d + 1) + twopow k)) (ldiag d (d + 1))) =
      bxor (wittBitBool (winWitt ((d + 2) + twopow k) (twopow k)) (((d + 3) + twopow k) + twopow k))
        (wittBitBool (phi (winWitt ((d + 1) + twopow k) (twopow k))) (((d + 3) + twopow k) + twopow k)) := by
  unfold wittBitBool
  exact periodic_winWitt_step_late_colm1_slot_of_zcenter_true
    T P hP h d k ht hk hset hz hw0 hw1 hw2

theorem phiScale_row_testBit_eq_of_rowAgree_prop (t k Q a L i : Nat)
    (ha : twopow (k + 1) ≤ a) (hi : i ≤ L)
    (h0 : RowAgree t Q (a - twopow (k + 1)) L)
    (h1 : RowAgree t Q (a - twopow k) L)
    (h2 : RowAgree t Q a L) :
    wittBitBool (phiScale k (row (t + Q))) (a + i + Q) =
      wittBitBool (phiScale k (row t)) (a + i) := by
  unfold wittBitBool
  exact phiScale_row_testBit_eq_of_rowAgree t k Q a L i ha hi h0 h1 h2

theorem frobDefect_row_testBit_eq_of_rowAgree_prop (t k Q a L i : Nat)
    (ha : twopow (k + 1) ≤ a) (hi : i ≤ L)
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1)) :
    BitFrobDefectEq k (row (t + Q)) (a + i + 1 + Q)
      (wittBitBool (frobDefect k (row t)) (a + i + 1)) := by
  unfold BitFrobDefectEq wittBitBool
  rw [bit_eq_bton_testBit,
    frobDefect_row_testBit_eq_of_rowAgree t k Q a L i ha hi h0 h1 h2]

theorem crossCarry_testBit_eq_of_rowAgree_winWittAgree_prop (t k Q a L i : Nat)
    (ha : twopow (k + 1) ≤ a) (hi : i ≤ L)
    (hw : WinWittAgree t k Q a (L + 1))
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1)) :
    BitCrossCarryEq (phiScale k (row (t + Q))) (winWitt (t + Q) (twopow k)) (a + i + 1 + Q)
      (wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k))) (a + i + 1)) := by
  unfold BitCrossCarryEq wittBitBool
  rw [bit_eq_bton_testBit,
    crossCarry_testBit_eq_of_rowAgree_winWittAgree t k Q a L i ha hi hw h0 h1 h2]

/-- The least common multiple `Q = lcm(P, 2^k) = (P / gcd(P, 2^k)) * 2^k`. -/
def lcmPeriod (P k : Nat) : Nat :=
  (P / Nat.gcd P (twopow k)) * twopow k

theorem lcmPeriod_eq_mul_twopow (P k : Nat) :
    lcmPeriod P k = (P / Nat.gcd P (twopow k)) * twopow k := rfl

theorem lcmPeriod_eq_mul_period (P k : Nat) :
    lcmPeriod P k = (twopow k / Nat.gcd P (twopow k)) * P := by
  unfold lcmPeriod
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left P (twopow k)
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right P (twopow k)
  rcases Nat.eq_zero_or_pos (Nat.gcd P (twopow k)) with hg0 | hg
  · rw [hg0, Nat.div_zero, Nat.div_zero, Nat.zero_mul, Nat.zero_mul]
  · have ha_div : P / Nat.gcd P (twopow k) = a := by
      have h0 : Nat.gcd P (twopow k) * a / Nat.gcd P (twopow k) = a := Nat.mul_div_right a hg
      rwa [← ha] at h0
    have hb_div : twopow k / Nat.gcd P (twopow k) = b := by
      have h0 : Nat.gcd P (twopow k) * b / Nat.gcd P (twopow k) = b := Nat.mul_div_right b hg
      rwa [← hb] at h0
    have hmul : a * twopow k = b * P := by
      have h1 : a * (Nat.gcd P (twopow k) * b) = b * (Nat.gcd P (twopow k) * a) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a (Nat.gcd P (twopow k)),
          Nat.mul_comm (Nat.gcd P (twopow k) * a) b]
      rwa [← hb, ← ha] at h1
    rw [ha_div, hb_div, hmul]

theorem lcmPeriod_div_pos (P k : Nat) (hP : 0 < P) :
    0 < twopow k / Nat.gcd P (twopow k) := by
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right P (twopow k)
  have hpos : 0 < twopow k := by
    have := twopow_gt_self k
    omega
  have hg : 0 < Nat.gcd P (twopow k) := Nat.gcd_pos_of_pos_left (twopow k) hP
  have hb_div : twopow k / Nat.gcd P (twopow k) = b := by
    have h0 : Nat.gcd P (twopow k) * b / Nat.gcd P (twopow k) = b := Nat.mul_div_right b hg
    rwa [← hb] at h0
  rw [hb_div]
  rcases Nat.eq_zero_or_pos b with rfl | hb_pos
  · rw [Nat.mul_zero] at hb
    omega
  · exact hb_pos

/-- **Right-wing `Q`-invariance at `Q = lcm(P, 2^k)` (`rdiag_lcmPeriod_eq`)**: for every `P, k, j, t : Nat` with `j ≤ k`, `rdiag j (t + lcmPeriod P k) = rdiag j t`. -/
theorem rdiag_lcmPeriod_eq (P k j t : Nat) (hj : j ≤ k) :
    rdiag j (t + lcmPeriod P k) = rdiag j t :=
  rdiag_restart k j (P / Nat.gcd P (twopow k)) t hj

/-- **Left-wing settled `Q`-invariance at `Q = lcm(P, 2^k)` (`ldiag_lcmPeriod_eq`)**: for every `P, k, j, t : Nat` with `j ≤ k` and `settle j ≤ t`, `ldiag j (t + lcmPeriod P k) = ldiag j t`. -/
theorem ldiag_lcmPeriod_eq (P k j t : Nat) (hj : j ≤ k) (hset : settle j ≤ t) :
    ldiag j (t + lcmPeriod P k) = ldiag j t :=
  ldiag_settled_restart k j (P / Nat.gcd P (twopow k)) t hj hset

theorem ldiag_settled_restart_prop (k j v t : Nat) (hj : j ≤ k) (hset : SettledBy j t) :
    ldiag j (t + v * twopow k) = ldiag j t :=
  ldiag_settled_restart k j v t hj hset

theorem ldiag_lcmPeriod_eq_prop (P k j t : Nat) (hj : j ≤ k) (hset : SettledBy j t) :
    ldiag j (t + lcmPeriod P k) = ldiag j t :=
  ldiag_lcmPeriod_eq P k j t hj hset

/-- **Center `Q`-invariance at `Q = lcm(P, 2^k)` (`center_lcmPeriod_eq`)**: under `CenterPeriodic T P` (`0 < P`), for every `k, t : Nat` with `T ≤ t`, `center (t + lcmPeriod P k) = center t`. -/
theorem center_lcmPeriod_eq (T P : Nat) (_hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k t : Nat) (ht : T ≤ t) :
    Rule30UOR.Core.center (t + lcmPeriod P k) = Rule30UOR.Core.center t := by
  rw [lcmPeriod_eq_mul_period P k]
  exact Rule30UOR.Scale.center_mul h (twopow k / Nat.gcd P (twopow k)) t ht

/-- **Refutation of Sector-Time Radius-`2^k` Neighbourhood Agreement at `Q = lcm(P, 2^k)` (`not_sector_rowAgree_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for any scale `k`, sector residue `d + 1`, and threshold `U ≥ 1`, `SectorRowAgree k d U (lcmPeriod P k)` is false! -/
theorem not_sector_rowAgree_lcmPeriod
    (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) :
    ¬ SectorRowAgree k d U (lcmPeriod P k) := by
  rw [lcmPeriod_eq_mul_period P k]
  exact not_sector_rowAgree_mul T P hP h k d U (twopow k / Nat.gcd P (twopow k)) hU
    (lcmPeriod_div_pos P k hP)

/-! ### Leftward Bijectivity, Symmetric Doubling of Right-Half Agreement Across the Periodic Center, and Window-Step 9.204 Sector Transport -/

/-- Leftward bijectivity of a single Rule 30 step on `row`: bit `j + 2` at time `t` equals bit `j + 2` at time `t + 1` XORed with the OR of bits `j + 1` and `j` at time `t`. -/
theorem row_testBit_add_two_of_step (t j : Nat) :
    (row t).testBit (j + 2) =
      bxor ((row (t + 1)).testBit (j + 2))
        ((row t).testBit (j + 1) || (row t).testBit j) := by
  have hstep : (row (t + 1)).testBit (j + 2) =
      bxor ((row t).testBit (j + 2)) ((row t).testBit (j + 1) || (row t).testBit j) := by
    rw [bxor_eq_xor]
    change (phi (row t)).testBit (j + 2) = _
    exact phi_testBit_add_two (row t) j
  rw [hstep, bxor_eq_xor, bxor_eq_xor]
  cases (row t).testBit (j + 2) <;>
    cases ((row t).testBit (j + 1) || (row t).testBit j) <;> rfl

/-- **1-Cell Leftward Spatial Extension of `RowAgree` (`rowAgree_extend_right`)**:
    if `RowAgree t Q a (L + 1)` holds on `[a, a + L + 1]` at time `t` and bit `a + L + 2` agrees between `t + 1` and `(t + 1) + Q`, then leftward bijectivity of Rule 30 forces bit `a + L + 2` to agree at time `t`, establishing `RowAgree t Q a (L + 2)`! -/
theorem rowAgree_extend_right (t Q a L : Nat)
    (h : RowAgree t Q a (L + 1))
    (hstep : (row ((t + 1) + Q)).testBit (a + L + 2 + Q) =
      (row (t + 1)).testBit (a + L + 2)) :
    RowAgree t Q a (L + 2) := by
  intro i hi
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · exact h i (by omega)
  · have h0 := h L (by omega)
    have h1 := h (L + 1) (by omega)
    rw [show a + (L + 2) + Q = (a + L + Q) + 2 by omega,
      show a + (L + 2) = (a + L) + 2 by omega,
      row_testBit_add_two_of_step (t + Q) (a + L + Q),
      row_testBit_add_two_of_step t (a + L),
      show (t + Q) + 1 = (t + 1) + Q by omega,
      show (a + L + Q) + 2 = a + L + 2 + Q by omega,
      show (a + L) + 2 = a + L + 2 by omega,
      show (a + L + Q) + 1 = a + (L + 1) + Q by omega,
      show (a + L) + 1 = a + (L + 1) by omega,
      hstep, h1, h0]

/-- **Unconditional Radius-`0` Center `RowAgree` under `CenterPeriodic T P` (`periodic_rowAgree_center`)**:
    under `CenterPeriodic T P` (`0 < P`), for every multiple `m` and every `t ≥ T`, `RowAgree t (m * P) t 0` holds at the center column `x = 0` (`bit t`). -/
theorem periodic_rowAgree_center
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    RowAgree t (m * P) t 0 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  rw [Nat.add_zero, row_testBit, row_testBit,
    ← core_center_eq_rdiag (t + m * P), ← core_center_eq_rdiag t]
  exact Rule30UOR.Scale.center_mul hper m t ht

/-- **Unconditional Column-`0` and Column-`-1` `RowAgree` at Every Black Center (`periodic_rowAgree_black_center`)**:
    under `CenterPeriodic T P` (`0 < P`), at every `t + 1 ≥ T` with `center (t + 1) = true`, the black center shields column `-1` (`ldiag t (t + 1)`) from column `+1`, so `RowAgree (t + 1) (m * P) (t + 1) 1` (agreement at both column `0` and column `-1` at time `t + 1`) holds unconditionally! -/
theorem periodic_rowAgree_black_center
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t + 1) (hblk : Rule30UOR.Core.center (t + 1) = true) :
    RowAgree (t + 1) (m * P) (t + 1) 1 := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact periodic_rowAgree_center T P hP hper m (t + 1) ht 0 (by omega)
  · have hi1 : i = 1 := by omega
    subst hi1
    have hdef := periodic_maskparity_zero_defect_mul_eq_colm1_defect_mul T P hP hper m t ht
    have hblk_mP : Rule30UOR.Core.center ((t + m * P) + 1) = true := by
      rw [show (t + m * P) + 1 = (t + 1) + m * P by omega,
        Rule30UOR.Scale.center_mul hper m (t + 1) ht, hblk]
    have hm0 : Rule30UOR.Scale.maskparity (t + 1) 0 = false := by
      have hand := maskparity_zero_and_center_eq_false (t + 1)
      rw [hblk, Bool.and_true] at hand
      exact hand
    have hm_mP : Rule30UOR.Scale.maskparity ((t + m * P) + 1) 0 = false := by
      have hand := maskparity_zero_and_center_eq_false ((t + m * P) + 1)
      rw [hblk_mP, Bool.and_true] at hand
      exact hand
    rw [hm0, hm_mP, bxor_eq_xor, Bool.xor_self] at hdef
    have hcol : ldiag (t + m * P) ((t + m * P) + 1) = ldiag t (t + 1) := by
      revert hdef
      rw [bxor_eq_xor]
      cases ldiag (t + m * P) ((t + m * P) + 1) <;> cases ldiag t (t + 1) <;> decide
    have hl1 : (row ((t + 1) + m * P)).testBit (t + 1 + 1 + m * P) =
        ldiag (t + m * P) ((t + m * P) + 1) := by
      rw [row_testBit,
        show (t + 1) + m * P = (t + m * P) + 1 by omega,
        show t + 1 + 1 + m * P = (t + m * P) + 2 * 1 by omega,
        ← ldiag_eq_rdiag (t + m * P) 1]
    have hl2 : (row (t + 1)).testBit (t + 1 + 1) = ldiag t (t + 1) := by
      rw [row_testBit,
        show t + 1 + 1 = t + 2 * 1 by omega,
        ← ldiag_eq_rdiag t 1]
    rw [hl1, hl2, hcol]

/-- **Symmetric Doubling of Right-Half `RowAgree` Across the Periodic Center (`periodic_rowAgree_symm_of_right`)**:
    under `CenterPeriodic T P` (`0 < P`), for every multiple `m`, time `t ≥ T`, and radius `R ≤ t`, if `RowAgree t (m * P) (t - R) R` holds on the one-sided right-wing neighbourhood `[t - R, t]` (spatial columns `x ∈ [0, R]`), then `RowAgree t (m * P) (t - R) (2 * R)` holds on the full two-sided symmetric neighbourhood `[t - R, t + R]` (spatial columns `x ∈ [-R, +R]`)! -/
theorem periodic_rowAgree_symm_of_right
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m R : Nat) :
    ∀ t : Nat, T ≤ t → R ≤ t →
      RowAgree t (m * P) (t - R) R →
      RowAgree t (m * P) (t - R) (2 * R) := by
  induction R with
  | zero =>
    intro t ht _ _
    simpa using periodic_rowAgree_center T P hP hper m t ht
  | succ R ih =>
    intro t ht hR hright
    have h_sub : RowAgree t (m * P) (t - R) R :=
      rowAgree_mono t (m * P) (t - (R + 1)) (R + 1) (t - R) R
        (by omega) (by omega) hright
    have h_symm_R : RowAgree t (m * P) (t - R) (2 * R) :=
      ih t ht (by omega) h_sub
    have h_2R1 : RowAgree t (m * P) (t - (R + 1)) (2 * R + 1) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact hright 0 (by omega)
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hj := h_symm_R j (by omega)
        rwa [show (t - R) + j = (t - (R + 1)) + (j + 1) by omega] at hj
    have h_step_bit :
        (row ((t + 1) + m * P)).testBit ((t - (R + 1)) + 2 * R + 2 + m * P) =
          (row (t + 1)).testBit ((t - (R + 1)) + 2 * R + 2) := by
      rcases Nat.eq_zero_or_pos R with rfl | hRpos
      · have hc := periodic_rowAgree_center T P hP hper m (t + 1) (by omega) 0 (by omega)
        simpa [show (t - 1) + 2 = t + 1 by omega] using hc
      · have h_2R1' : RowAgree t (m * P) (t - (R + 1)) ((2 * R - 1) + 2) := by
          intro i hi
          exact h_2R1 i (by omega)
        have h_step := rowAgree_step t (m * P) (t - (R + 1)) (2 * R - 1) h_2R1'
        have h_next_right : RowAgree (t + 1) (m * P) ((t + 1) - R) R :=
          rowAgree_mono (t + 1) (m * P) ((t - (R + 1)) + 2) (2 * R - 1) ((t + 1) - R) R
            (by omega) (by omega) h_step
        have h_next_symm : RowAgree (t + 1) (m * P) ((t + 1) - R) (2 * R) :=
          ih (t + 1) (by omega) (by omega) h_next_right
        have h_end := h_next_symm (2 * R) (by omega)
        rwa [show ((t + 1) - R) + 2 * R = (t - (R + 1)) + 2 * R + 2 by omega] at h_end
    have h_ext := rowAgree_extend_right t (m * P) (t - (R + 1)) (2 * R) h_2R1 h_step_bit
    simpa [Nat.mul_succ, Nat.add_assoc] using h_ext

/-- **Symmetric Doubling of Right-Half `RowAgree` at `Q = lcm(P, 2^k)` (`periodic_rowAgree_lcmPeriod_symm_of_right`)**:
    under `CenterPeriodic T P` (`0 < P`), for every scale `k`, time `t ≥ T`, and radius `R ≤ t`, one-sided right-wing agreement `RowAgree t (lcmPeriod P k) (t - R) R` implies full two-sided symmetric agreement `RowAgree t (lcmPeriod P k) (t - R) (2 * R)`. -/
theorem periodic_rowAgree_lcmPeriod_symm_of_right
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k R t : Nat) (ht : T ≤ t) (hR : R ≤ t)
    (hright : RowAgree t (lcmPeriod P k) (t - R) R) :
    RowAgree t (lcmPeriod P k) (t - R) (2 * R) := by
  rw [lcmPeriod_eq_mul_period P k] at hright ⊢
  exact periodic_rowAgree_symm_of_right T P hP hper (twopow k / Nat.gcd P (twopow k)) R t ht hR hright

/-- Paper-facing predicate `SectorRightRowAgree k d U Q`: at all sector times `(d + u * 2^k) + 1` (`u ≥ U`), the one-sided right-wing neighbourhood of width `2^k + 1` (`[((d + u * 2^k) + 1) - (2^k + 1), (d + u * 2^k) + 1]`, columns `x ∈ [0, 2^k + 1]`) agrees between `t` and `t + Q`. -/
def SectorRightRowAgree (k d U Q : Nat) : Prop :=
  ∀ u, U ≤ u →
    RowAgree ((d + u * twopow k) + 1) Q
      (((d + u * twopow k) + 1) - (twopow k + 1)) (twopow k + 1)

/-- **Carrying One-Sided Right Sector Agreement to Every Residue `mod 2^k` (`colNegOnePeriodic_of_sector_right_rowAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), if `SectorRightRowAgree k d U (m * P)` holds (`1 ≤ U`, `1 ≤ d`, `T ≤ d + U * 2^k`), then symmetric doubling across the periodic center yields `SectorRowAgree k d U (m * P)` and hence `ColNegOnePeriodic (d + U * 2^k) (m * P)` across all residues `mod 2^k`! -/
theorem colNegOnePeriodic_of_sector_right_rowAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * twopow k)
    (hsec : SectorRightRowAgree k d U (m * P)) :
    ColNegOnePeriodic (d + U * twopow k) (m * P) := by
  refine colNegOnePeriodic_of_sector_rowAgree k d U (m * P) hU (fun u hu => ?_)
  have h1 : 1 * twopow k ≤ u * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
  have hU_le : U * twopow k ≤ u * twopow k := Nat.mul_le_mul_right (twopow k) hu
  have hright := hsec u hu
  have hsymm := periodic_rowAgree_symm_of_right T P hP hper m (twopow k + 1)
    ((d + u * twopow k) + 1) (by omega) (by omega) hright
  exact rowAgree_mono ((d + u * twopow k) + 1) (m * P)
    (((d + u * twopow k) + 1) - (twopow k + 1)) (2 * (twopow k + 1))
    (((d + u * twopow k) + 2) - twopow k) (2 * twopow k)
    (by omega) (by omega) hsymm

/-- **Refutation of One-Sided Right Sector Agreement at `Q = lcm(P, 2^k)` (`not_sector_right_rowAgree_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for `1 ≤ U`, `1 ≤ d`, and `T ≤ d + U * 2^k`, `SectorRightRowAgree k d U (lcmPeriod P k)` is false! -/
theorem not_sector_right_rowAgree_lcmPeriod
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * twopow k) :
    ¬ SectorRightRowAgree k d U (lcmPeriod P k) := by
  intro hsec
  rw [lcmPeriod_eq_mul_period P k] at hsec
  have hcol := colNegOnePeriodic_of_sector_right_rowAgree T P hP hper
    k d U (twopow k / Nat.gcd P (twopow k)) hU hd ht hsec
  exact not_periodic_colm1_mul T P hP hper (d + U * twopow k)
    (twopow k / Nat.gcd P (twopow k)) (lcmPeriod_div_pos P k hP) hcol

/-- **1-Cell Leftward Spatial Extension of `WinWittAgree` via Theorem 9.204 (`winWittAgree_extend_right`)**:
    for `2^(k+1) ≤ a`, if `WinWittAgree t k Q a (L + 1)` and the three-sector `RowAgree` hold on width `L + 1` at time `t`, and bit `a + L + 2` of `winWitt · (2^k)` agrees at time `t + 1`, then Theorem 9.204 (`winWitt_step_frobDefect_testBit_succ`) forces bit `a + L + 2` of `winWitt · (2^k)` to agree at time `t`, establishing `WinWittAgree t k Q a (L + 2)`! -/
theorem winWittAgree_extend_right (t k Q a L : Nat)
    (ha : twopow (k + 1) ≤ a)
    (hw : WinWittAgree t k Q a (L + 1))
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1))
    (hstep : (winWitt ((t + 1) + Q) (twopow k)).testBit (a + L + 2 + Q) =
      (winWitt (t + 1) (twopow k)).testBit (a + L + 2)) :
    WinWittAgree t k Q a (L + 2) := by
  intro i hi
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · exact hw i (by omega)
  · have hw0 := hw L (by omega)
    have hw1 := hw (L + 1) (by omega)
    have hcc := crossCarry_testBit_eq_of_rowAgree_winWittAgree t k Q a L L ha (by omega) hw h0 h1 h2
    have hfd := frobDefect_row_testBit_eq_of_rowAgree t k Q a L L ha (by omega) h0 h1 h2
    have hs_Q := winWitt_step_frobDefect_testBit_succ (t + Q) k (a + L + 1 + Q)
    have hs_0 := winWitt_step_frobDefect_testBit_succ t k (a + L + 1)
    rw [show a + (L + 1) + Q = a + L + 1 + Q by omega] at hw1
    rw [show a + (L + 1) = a + L + 1 by omega] at hw1
    rw [show (t + Q) + 1 = (t + 1) + Q by omega,
      show (a + L + 1 + Q) + 1 = (a + L + Q) + 2 by omega,
      phi_testBit_add_two (winWitt (t + Q) (twopow k)) (a + L + Q),
      show (a + L + Q) + 2 = a + L + 2 + Q by omega,
      show (a + L + Q) + 1 = a + L + 1 + Q by omega] at hs_Q
    rw [show (a + L + 1) + 1 = (a + L) + 2 by omega,
      phi_testBit_add_two (winWitt t (twopow k)) (a + L),
      show (a + L) + 2 = a + L + 2 by omega] at hs_0
    rw [hs_Q, hs_0, hcc, hfd, hw1, hw0] at hstep
    rw [show a + (L + 2) + Q = a + L + 2 + Q by omega,
      show a + (L + 2) = a + L + 2 by omega]
    revert hstep
    simp only [bxor_eq_xor]
    cases (winWitt (t + Q) (twopow k)).testBit (a + L + 2 + Q) <;>
      cases (winWitt t (twopow k)).testBit (a + L + 2) <;>
      cases ((winWitt t (twopow k)).testBit (a + L + 1) || (winWitt t (twopow k)).testBit (a + L)) <;>
      cases (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit (a + L + 1) <;>
      cases (frobDefect k (row t)).testBit (a + L + 1) <;> decide

/-- **Equivalence of `WinWittAgree` and Late `RowAgree` under Three-Sector `RowAgree` (`winWittAgree_of_rowAgree_three_and_late`)**:
    for `2^(k+1) ≤ a`, if the three-sector `RowAgree` holds at time `t` and `RowAgree (t + 2^k) Q a L` holds at time `t + 2^k`, then `WinWittAgree t k Q a L` holds at time `t`. -/
theorem winWittAgree_of_rowAgree_three_and_late (t k Q a L : Nat)
    (ha : twopow (k + 1) ≤ a)
    (h0 : RowAgree t Q (a - twopow (k + 1)) L)
    (h1 : RowAgree t Q (a - twopow k) L)
    (h2 : RowAgree t Q a L)
    (hlate : RowAgree (t + twopow k) Q a L) :
    WinWittAgree t k Q a L := by
  intro i hi
  have hphi := phiScale_row_testBit_eq_of_rowAgree t k Q a L i ha hi h0 h1 h2
  have hrow := hlate i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hrow
  have hw_Q : (winWitt (t + Q) (twopow k)).testBit (a + i + Q) =
      bxor ((row ((t + Q) + twopow k)).testBit (a + i + Q))
        ((phiScale k (row (t + Q))).testBit (a + i + Q)) := by
    have hsc := congrArg (fun n => n.testBit (a + i + Q)) (row_scale (t + Q) k)
    rw [Nat.testBit_xor] at hsc
    revert hsc
    simp only [bxor_eq_xor]
    cases (row ((t + Q) + twopow k)).testBit (a + i + Q) <;>
      cases (phiScale k (row (t + Q))).testBit (a + i + Q) <;>
      cases (winWitt (t + Q) (twopow k)).testBit (a + i + Q) <;> decide
  have hw_0 : (winWitt t (twopow k)).testBit (a + i) =
      bxor ((row (t + twopow k)).testBit (a + i))
        ((phiScale k (row t)).testBit (a + i)) := by
    have hsc := congrArg (fun n => n.testBit (a + i)) (row_scale t k)
    rw [Nat.testBit_xor] at hsc
    revert hsc
    simp only [bxor_eq_xor]
    cases (row (t + twopow k)).testBit (a + i) <;>
      cases (phiScale k (row t)).testBit (a + i) <;>
      cases (winWitt t (twopow k)).testBit (a + i) <;> decide
  rw [hw_Q, hw_0, hrow, hphi]

/-- **Converse Equivalence (`rowAgree_late_of_winWittAgree_and_three`)**:
    for `2^(k+1) ≤ a`, if the three-sector `RowAgree` and `WinWittAgree t k Q a L` hold at time `t`, then `RowAgree (t + 2^k) Q a L` holds at the late time `t + 2^k`. -/
theorem rowAgree_late_of_winWittAgree_and_three (t k Q a L : Nat)
    (ha : twopow (k + 1) ≤ a)
    (hw : WinWittAgree t k Q a L)
    (h0 : RowAgree t Q (a - twopow (k + 1)) L)
    (h1 : RowAgree t Q (a - twopow k) L)
    (h2 : RowAgree t Q a L) :
    RowAgree (t + twopow k) Q a L := by
  intro i hi
  have hphi := phiScale_row_testBit_eq_of_rowAgree t k Q a L i ha hi h0 h1 h2
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    row_scale (t + Q) k, row_scale t k,
    Nat.testBit_xor, Nat.testBit_xor, hphi, hwi]

/-- Paper-facing predicate `SectorWinWittAgree k d U Q`: at all sector times `t_u = d + u * 2^k` (`u ≥ U`), `WinWittAgree` and the three-sector `RowAgree` hold on the radius-`2^k` neighbourhood (`width = 2 * 2^k`) around the center slot `t_u + 2^k`. -/
def SectorWinWittAgree (k d U Q : Nat) : Prop :=
  ∀ u, U ≤ u →
    WinWittAgree (d + u * twopow k) k Q (((d + u * twopow k) + twopow k) - twopow k) (2 * twopow k) ∧
    RowAgree (d + u * twopow k) Q ((((d + u * twopow k) + twopow k) - twopow k) - twopow (k + 1)) (2 * twopow k) ∧
    RowAgree (d + u * twopow k) Q ((((d + u * twopow k) + twopow k) - twopow k) - twopow k) (2 * twopow k) ∧
    RowAgree (d + u * twopow k) Q (((d + u * twopow k) + twopow k) - twopow k) (2 * twopow k)

/-- **Carrying `wittRespBool` `Q`-Periodicity from Sector Times Across Every Residue `mod 2^k` via Window Step 9.204 (`wittRespBool_periodic_of_sector_winWittAgree`)**:
    if `SectorWinWittAgree k d U Q` holds (`2 ≤ U`), then advancing by `s = (t - (d + U * 2^k)) % 2^k < 2^k` steps of the window step 9.204 (`wittRespBool_eq_of_winWittAgree_steps`) carries `wittRespBool (t + Q) k = wittRespBool t k` to EVERY residue `mod 2^k` (`∀ t ≥ d + U * 2^k`)! -/
theorem wittRespBool_periodic_of_sector_winWittAgree (k d U Q : Nat) (hU : 2 ≤ U)
    (hsec : SectorWinWittAgree k d U Q) :
    ∀ t, d + U * twopow k ≤ t → wittRespBool (t + Q) k = wittRespBool t k := by
  intro t ht
  have hpos : 0 < twopow k := by
    have := twopow_gt_self k
    omega
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  obtain ⟨delta, hdelta⟩ : ∃ delta, t = (d + U * twopow k) + delta := ⟨t - (d + U * twopow k), by omega⟩
  obtain ⟨q, s, hdiv, hs_lt⟩ : ∃ q s, delta = q * twopow k + s ∧ s < twopow k :=
    ⟨delta / twopow k, delta % twopow k,
      by rw [Nat.mul_comm, Nat.div_add_mod],
      Nat.mod_lt delta hpos⟩
  have hu : U ≤ U + q := by omega
  let t0 := d + (U + q) * twopow k
  have ht0_eq : t = t0 + s := by
    dsimp [t0]
    rw [Nat.add_mul]
    omega
  have h2_le : 2 * twopow k ≤ (U + q) * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
  have ht0_bound : twopow k + s ≤ t0 := by
    dsimp [t0]
    omega
  obtain ⟨hw, h0, h1, h2⟩ := hsec (U + q) hu
  have hw_sub : WinWittAgree t0 k Q ((t0 + twopow k) - s) (2 * s) :=
    winWittAgree_mono t0 k Q ((t0 + twopow k) - twopow k) (2 * twopow k)
      ((t0 + twopow k) - s) (2 * s) (by omega) (by omega) hw
  have h0_sub : RowAgree t0 Q (((t0 + twopow k) - s) - twopow (k + 1)) (2 * s) :=
    rowAgree_mono t0 Q (((t0 + twopow k) - twopow k) - twopow (k + 1)) (2 * twopow k)
      (((t0 + twopow k) - s) - twopow (k + 1)) (2 * s) (by omega) (by omega) h0
  have h1_sub : RowAgree t0 Q (((t0 + twopow k) - s) - twopow k) (2 * s) :=
    rowAgree_mono t0 Q (((t0 + twopow k) - twopow k) - twopow k) (2 * twopow k)
      (((t0 + twopow k) - s) - twopow k) (2 * s) (by omega) (by omega) h1
  have h2_sub : RowAgree t0 Q ((t0 + twopow k) - s) (2 * s) :=
    rowAgree_mono t0 Q ((t0 + twopow k) - twopow k) (2 * twopow k)
      ((t0 + twopow k) - s) (2 * s) (by omega) (by omega) h2
  have hresp := wittRespBool_eq_of_winWittAgree_steps t0 k Q s ht0_bound hw_sub h0_sub h1_sub h2_sub
  rwa [← ht0_eq] at hresp

/-- **Right-Boundary Row Neighbourhood `Q`-Invariance at `Q = lcm(P, 2^k)` (`right_boundary_row_lcmPeriod_eq`)**:
    for every `P, k, j, t : Nat` with `j ≤ k`, bit `j` of `row (t + lcmPeriod P k)` equals bit `j` of `row t`. -/
theorem right_boundary_row_lcmPeriod_eq (P k j t : Nat) (hj : j ≤ k) :
    (row (t + lcmPeriod P k)).testBit j = (row t).testBit j := by
  rw [row_testBit, row_testBit]
  exact rdiag_lcmPeriod_eq P k j t hj

/-- **Left-Boundary Settled Row Neighbourhood `Q`-Invariance at `Q = lcm(P, 2^k)` (`left_boundary_row_lcmPeriod_eq`)**:
    for every `P, k, j, t : Nat` with `j ≤ k`, `j ≤ t`, and `settle j ≤ t`, bit `2 * (t + lcmPeriod P k) - j` of `row (t + lcmPeriod P k)` equals bit `2 * t - j` of `row t`. -/
theorem left_boundary_row_lcmPeriod_eq (P k j t : Nat)
    (hj : j ≤ k) (hjt : j ≤ t) (hset : settle j ≤ t) :
    (row (t + lcmPeriod P k)).testBit (2 * (t + lcmPeriod P k) - j) =
      (row t).testBit (2 * t - j) := by
  have h1 : (row (t + lcmPeriod P k)).testBit (2 * (t + lcmPeriod P k) - j) =
      ldiag j (t + lcmPeriod P k) := by
    have hd := ldiag_eq_rdiag j ((t + lcmPeriod P k) - j)
    rw [show j + ((t + lcmPeriod P k) - j) = t + lcmPeriod P k by omega,
      show j + 2 * ((t + lcmPeriod P k) - j) = 2 * (t + lcmPeriod P k) - j by omega,
      ← row_testBit (t + lcmPeriod P k) (2 * (t + lcmPeriod P k) - j)] at hd
    exact hd.symm
  have h2 : (row t).testBit (2 * t - j) = ldiag j t := by
    have hd := ldiag_eq_rdiag j (t - j)
    rw [show j + (t - j) = t by omega,
      show j + 2 * (t - j) = 2 * t - j by omega,
      ← row_testBit t (2 * t - j)] at hd
    exact hd.symm
  rw [h1, h2]
  exact ldiag_lcmPeriod_eq P k j t hj hset

/-- **Sector-1 `frobDefect` `Q`-Difference Factored by `Q = lcm(P, 2^k)` at Sector Times (`frobDefect_row_sector_one_lcmPeriod_xor`)**:
    for `d + 1 ≤ k` and every sector time `t_u = (d + 1) + u * 2^k`, because `2^k ∣ lcmPeriod P k`, both `t_u` and `t_u + lcmPeriod P k` share the exact same Sector-0 boundary bits `center (d + 1)` and `rdiag d (d + 1)`, so their Sector-1 `frobDefect` difference factors cleanly! -/
theorem frobDefect_row_sector_one_lcmPeriod_xor (P d k u : Nat) (hk : d + 1 ≤ k) :
    bxor
      ((frobDefect k (row (((d + 1) + u * twopow k) + lcmPeriod P k))).testBit ((d + 1) + twopow k))
      ((frobDefect k (row ((d + 1) + u * twopow k))).testBit ((d + 1) + twopow k)) =
      bxor
        (bxor
          (rdiag ((d + 1) + twopow k) (((d + 1) + u * twopow k) + lcmPeriod P k))
          (rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k)) && rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) &&
          bxor
            (rdiag (d + twopow k) (((d + 1) + u * twopow k) + lcmPeriod P k))
            (rdiag (d + twopow k) ((d + 1) + u * twopow k))) := by
  have hQ : ((d + 1) + u * twopow k) + lcmPeriod P k =
      (d + 1) + (u + P / Nat.gcd P (twopow k)) * twopow k := by
    rw [lcmPeriod_eq_mul_twopow, Nat.add_mul, Nat.add_assoc]
  rw [hQ,
    frobDefect_row_sector_one_restart d k (u + P / Nat.gcd P (twopow k)) hk,
    frobDefect_row_sector_one_restart d k u hk]
  simp only [bxor_eq_xor]
  cases rdiag ((d + 1) + twopow k) ((d + 1) + (u + P / Nat.gcd P (twopow k)) * twopow k) <;>
    cases rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k) <;>
    cases rdiag d (d + 1) <;>
    cases Rule30UOR.Core.center (d + 1) <;>
    cases rdiag (d + twopow k) ((d + 1) + (u + P / Nat.gcd P (twopow k)) * twopow k) <;>
    cases rdiag (d + twopow k) ((d + 1) + u * twopow k) <;> rfl

theorem rowAgree_extend_right_prop (t Q a L : Nat)
    (h : RowAgree t Q a (L + 1))
    (hstep : wittBitBool (row ((t + 1) + Q)) (a + L + 2 + Q) =
      wittBitBool (row (t + 1)) (a + L + 2)) :
    RowAgree t Q a (L + 2) :=
  rowAgree_extend_right t Q a L h hstep

theorem winWittAgree_extend_right_prop (t k Q a L : Nat)
    (ha : twopow (k + 1) ≤ a)
    (hw : WinWittAgree t k Q a (L + 1))
    (h0 : RowAgree t Q (a - twopow (k + 1)) (L + 1))
    (h1 : RowAgree t Q (a - twopow k) (L + 1))
    (h2 : RowAgree t Q a (L + 1))
    (hstep : wittBitBool (winWitt ((t + 1) + Q) (twopow k)) (a + L + 2 + Q) =
      wittBitBool (winWitt (t + 1) (twopow k)) (a + L + 2)) :
    WinWittAgree t k Q a (L + 2) :=
  winWittAgree_extend_right t k Q a L ha hw h0 h1 h2 hstep

theorem right_boundary_row_lcmPeriod_eq_prop (P k j t : Nat) (hj : j ≤ k) :
    wittBitBool (row (t + lcmPeriod P k)) j = wittBitBool (row t) j :=
  right_boundary_row_lcmPeriod_eq P k j t hj

theorem left_boundary_row_lcmPeriod_eq_prop (P k j t : Nat)
    (hj : j ≤ k) (hjt : j ≤ t) (hset : SettledBy j t) :
    wittBitBool (row (t + lcmPeriod P k)) (2 * (t + lcmPeriod P k) - j) =
      wittBitBool (row t) (2 * t - j) :=
  left_boundary_row_lcmPeriod_eq P k j t hj hjt hset

theorem frobDefect_row_sector_one_lcmPeriod_xor_prop (P d k u : Nat) (hk : d + 1 ≤ k) :
    bxor
      (wittBitBool (frobDefect k (row (((d + 1) + u * twopow k) + lcmPeriod P k))) ((d + 1) + twopow k))
      (wittBitBool (frobDefect k (row ((d + 1) + u * twopow k))) ((d + 1) + twopow k)) =
      bxor
        (bxor
          (rdiag ((d + 1) + twopow k) (((d + 1) + u * twopow k) + lcmPeriod P k))
          (rdiag ((d + 1) + twopow k) ((d + 1) + u * twopow k)) && rdiag d (d + 1))
        (Rule30UOR.Core.center (d + 1) &&
          bxor
            (rdiag (d + twopow k) (((d + 1) + u * twopow k) + lcmPeriod P k))
            (rdiag (d + twopow k) ((d + 1) + u * twopow k))) :=
  frobDefect_row_sector_one_lcmPeriod_xor P d k u hk

/-! ### The Driven Right Half `rhCenter`, the `Φ` Fixed-Point Law from §6 (`Rule30UOR.Fixed`), Inward Right-Half Agreement (`RhBandAgree`), and Window-Step 9.204 Sector Refutations -/

/-- Paper-facing readout of the driven right half `Rh center` at time `t` and non-negative column `p`:
    `rhCenter t p = Rule30UOR.Fixed.Rh Rule30Prize.center t (p : Int)`. -/
def rhCenter (t p : Nat) : Bool :=
  Rule30UOR.Fixed.Rh Ruliology.CellularAutomata.Rule30Prize.center t (p : Int)

/-- Paper-facing readout of the driven left half `Lh center` at time `t` and non-positive column `-p`:
    `lhCenter t p = Rule30UOR.Fixed.Lh Rule30Prize.center t (- (p : Int))`. -/
def lhCenter (t p : Nat) : Bool :=
  Rule30UOR.Fixed.Lh Ruliology.CellularAutomata.Rule30Prize.center t (- (p : Int))

/-- Band `Q`-agreement of the driven right half `rhCenter`: at time `t` and `t + Q`, `rhCenter` agrees on columns `[p0, p0 + L]`. -/
def RhBandAgree (t Q p0 L : Nat) : Prop :=
  ∀ i, i ≤ L → rhCenter (t + Q) (p0 + i) = rhCenter t (p0 + i)

/-- **Exact Identity Between the Driven Right Half `rhCenter` and `rdiag` (`rhCenter_eq_rdiag`)**:
    for all `t, p : Nat` with `p ≤ t`, column `p` of the driven right half `rhCenter t p` equals right diagonal `rdiag (t - p) t`. -/
theorem rhCenter_eq_rdiag (t p : Nat) (hp : p ≤ t) :
    rhCenter t p = rdiag (t - p) t := by
  unfold rhCenter
  rw [Rule30UOR.Fixed.Rh_center t (p : Int) (by omega),
    Rule30UOR.Right.rdiag_eq_R]
  unfold Ruliology.CellularAutomata.Rule30Diagonals.R
  exact congrArg (Ruliology.CellularAutomata.Rule30Jen.cell t) (by omega)

/-- **Exact Identity Between `rhCenter` and `row` Bit Readout (`rhCenter_eq_row_testBit`)**:
    for all `t, p : Nat` with `p ≤ t`, `rhCenter t p = (row t).testBit (t - p)`. -/
theorem rhCenter_eq_row_testBit (t p : Nat) (hp : p ≤ t) :
    rhCenter t p = (row t).testBit (t - p) := by
  rw [row_testBit, rhCenter_eq_rdiag t p hp]

/-- **Exact Identity Between the Driven Left Half `lhCenter` and `ldiag` (`lhCenter_eq_ldiag`)**:
    for all `t, p : Nat` with `p ≤ t`, column `-p` of the driven left half `lhCenter t p` equals left diagonal `ldiag (t - p) t`. -/
theorem lhCenter_eq_ldiag (t p : Nat) (hp : p ≤ t) :
    lhCenter t p = ldiag (t - p) t := by
  unfold lhCenter
  rw [Rule30UOR.Fixed.Lh_center t (- (p : Int)) (by omega)]
  have h0 := ldiag_eq_cell_neg (t - p) p
  rw [show t - p + p = t by omega, Rule30UOR.Scale.cell_eq_kit] at h0
  exact h0.symm

/-- **Exact Identity Between `lhCenter` and `row` Bit Readout (`lhCenter_eq_row_testBit`)**:
    for all `t, p : Nat` with `p ≤ t`, `lhCenter t p = (row t).testBit (t + p)`. -/
theorem lhCenter_eq_row_testBit (t p : Nat) (hp : p ≤ t) :
    lhCenter t p = (row t).testBit (t + p) := by
  have hd := ldiag_eq_rdiag (t - p) p
  rw [show t - p + p = t by omega,
    show t - p + 2 * p = t + p by omega] at hd
  rw [lhCenter_eq_ldiag t p hp, row_testBit, hd]

/-- **Boundary Readouts of `rhCenter` (`rhCenter_zero_eq_center`, `rhCenter_self_eq_true`, `rhCenter_gt_eq_false`)**:
    at `p = 0`, `rhCenter t 0 = center t`; at the right edge `p = t`, `rhCenter t t = true`; and outside the light cone (`t < p`), `rhCenter t p = false`. -/
theorem rhCenter_zero_eq_center (t : Nat) :
    rhCenter t 0 = Rule30UOR.Core.center t := by
  rw [rhCenter_eq_rdiag t 0 (by omega), Nat.sub_zero, core_center_eq_rcenter]
  rfl

theorem rhCenter_self_eq_true (t : Nat) :
    rhCenter t t = true := by
  rw [rhCenter_eq_rdiag t t (by omega), Nat.sub_self]
  rcases t with _ | t <;> rfl

theorem rhCenter_gt_eq_false (t p : Nat) (h : t < p) :
    rhCenter t p = false := by
  unfold rhCenter
  induction t generalizing p with
  | zero =>
    simp [Rule30UOR.Fixed.Rh]
    omega
  | succ t ih =>
    rcases p with _ | p
    · omega
    · have hpos : (0 : Int) < ((p + 1 : Nat) : Int) := by omega
      simp only [Rule30UOR.Fixed.Rh, if_pos hpos, Ruliology.CellularAutomata.Rule30Jen.rule]
      rw [show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega,
        show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega,
        ih p (by omega), ih (p + 1) (by omega), ih (p + 2) (by omega)]
      rfl

/-- **Structural Unfolding of the §6 `Φ` Recombination Operator (`phiCenter_eq_lhCenter_rhCenter`)**:
    for every `t : Nat`, `phiCenter t` is the Rule 30 recombination `bxor (lhCenter t 1) (center t || rhCenter t 1)` of the driven left half at `-1`, the center at `0`, and the driven right half at `+1`. -/
theorem phiCenter_eq_lhCenter_rhCenter (t : Nat) :
    Rule30UOR.Fixed.phiCenter t =
      bxor (lhCenter t 1) (Rule30UOR.Core.center t || rhCenter t 1) := by
  unfold Rule30UOR.Fixed.phiCenter Rule30UOR.Fixed.Phi lhCenter rhCenter Ruliology.CellularAutomata.Rule30Jen.rule
  rw [← Rule30UOR.Scale.center_eq_kit t, bxor_eq_xor]
  rfl

/-- **The §6 `Φ` Fixed-Point Law Solved for the Left-Half Neighbour (`lhCenter_one_eq_of_center_fixed`)**:
    combining `center (t + 1) = phiCenter t` (`Rule30UOR.Fixed.center_fixed_readout`) with `phiCenter_eq_lhCenter_rhCenter` expresses `lhCenter t 1` directly in terms of `center (t + 1)`, `center t`, and `rhCenter t 1`! -/
theorem lhCenter_one_eq_of_center_fixed (t : Nat) :
    lhCenter t 1 =
      bxor (Rule30UOR.Core.center (t + 1))
        (Rule30UOR.Core.center t || rhCenter t 1) := by
  have hfix := Rule30UOR.Fixed.center_fixed_readout t
  rw [← Rule30UOR.Scale.center_eq_kit (t + 1), phiCenter_eq_lhCenter_rhCenter t] at hfix
  rw [hfix, bxor_eq_xor, bxor_eq_xor]
  cases lhCenter t 1 <;>
    cases (Rule30UOR.Core.center t || rhCenter t 1) <;> rfl

/-- **Period-Shift Defect of the §6 `Φ` Fixed-Point Law (`periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect`)**:
    under `CenterPeriodic T P` (`0 < P`), for every multiple `m` and `t ≥ T`, the `Φ` fixed-point law `center (t + 1) = phiCenter t` equates the `m * P`-defect of `lhCenter · 1` with `!center t && (rhCenter (t + m * P) 1 ⊕ rhCenter t 1)`! -/
theorem periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t) :
    bxor (lhCenter (t + m * P) 1) (lhCenter t 1) =
      (!Rule30UOR.Core.center t &&
        bxor (rhCenter (t + m * P) 1) (rhCenter t 1)) := by
  have hc0 : Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t :=
    Rule30UOR.Scale.center_mul hper m t ht
  have hc1 : Rule30UOR.Core.center ((t + m * P) + 1) = Rule30UOR.Core.center (t + 1) := by
    rw [show (t + m * P) + 1 = (t + 1) + m * P by omega]
    exact Rule30UOR.Scale.center_mul hper m (t + 1) (by omega)
  rw [lhCenter_one_eq_of_center_fixed (t + m * P),
    lhCenter_one_eq_of_center_fixed t,
    hc0, hc1]
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center (t + 1) <;>
    cases Rule30UOR.Core.center t <;>
    cases rhCenter (t + m * P) 1 <;>
    cases rhCenter t 1 <;> rfl

/-- **Evolution Law of the Driven Right Half `rhCenter` (`rhCenter_step_succ`)**:
    for all `t, p : Nat`, column `p + 1 > 0` of `rhCenter (t + 1)` evolves by Rule 30 from columns `p, p + 1, p + 2` of `rhCenter t`. -/
theorem rhCenter_step_succ (t p : Nat) :
    rhCenter (t + 1) (p + 1) =
      bxor (rhCenter t p) (rhCenter t (p + 1) || rhCenter t (p + 2)) := by
  unfold rhCenter
  have hpos : (0 : Int) < ((p + 1 : Nat) : Int) := by omega
  simp only [Rule30UOR.Fixed.Rh, if_pos hpos]
  rw [show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega,
    show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega]
  unfold Ruliology.CellularAutomata.Rule30Jen.rule
  rw [bxor_eq_xor]

/-- **Inward Step Law of the Driven Right Half from the Right Edge Toward Column 1 (`rhCenter_inward_step`)**:
    for all `t, p : Nat`, solving `rhCenter_step_succ` for `rhCenter t p` expresses column `p` at time `t` in terms of columns `p + 1, p + 2` (further toward the right edge) at time `t` and column `p + 1` at time `t + 1`! -/
theorem rhCenter_inward_step (t p : Nat) :
    rhCenter t p =
      bxor (rhCenter (t + 1) (p + 1))
        (rhCenter t (p + 1) || rhCenter t (p + 2)) := by
  rw [rhCenter_step_succ t p, bxor_eq_xor, bxor_eq_xor]
  cases rhCenter t p <;>
    cases (rhCenter t (p + 1) || rhCenter t (p + 2)) <;> rfl

/-- **1-Column Inward Extension of `RhBandAgree` Toward Column 1 (`rhBandAgree_extend_inward`)**:
    if `RhBandAgree t Q (p0 + 1) (L + 1)` holds on columns `[p0 + 1, p0 + L + 2]` at time `t`, and column `p0 + 1` agrees at time `t + 1`, then `rhCenter_inward_step` forces column `p0` to agree at time `t`, establishing `RhBandAgree t Q p0 (L + 2)`! -/
theorem rhBandAgree_extend_inward (t Q p0 L : Nat)
    (h : RhBandAgree t Q (p0 + 1) (L + 1))
    (hstep : rhCenter ((t + 1) + Q) (p0 + 1) = rhCenter (t + 1) (p0 + 1)) :
    RhBandAgree t Q p0 (L + 2) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h1 := h 0 (by omega)
    have h2 := h 1 (by omega)
    rw [Nat.add_zero,
      rhCenter_inward_step (t + Q) p0,
      rhCenter_inward_step t p0,
      show (t + Q) + 1 = (t + 1) + Q by omega,
      show p0 + 1 = (p0 + 1) + 0 by omega,
      show p0 + 2 = (p0 + 1) + 1 by omega]
    rw [show (p0 + 1) + 0 = p0 + 1 by omega] at h1 ⊢
    rw [hstep, h1, h2]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj := h j (by omega)
    rwa [show p0 + (j + 1) = (p0 + 1) + j by omega]

/-- **One-Step Forward Propagation of `RhBandAgree` (`rhBandAgree_step`)**:
    each step `t ↦ t + 1` in the driven right half carries `RhBandAgree t Q p0 (L + 2)` on `[p0, p0 + L + 2]` to `RhBandAgree (t + 1) Q (p0 + 1) L` on `[p0 + 1, p0 + 1 + L]`. -/
theorem rhBandAgree_step (t Q p0 L : Nat)
    (h : RhBandAgree t Q p0 (L + 2)) :
    RhBandAgree (t + 1) Q (p0 + 1) L := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 1) (by omega)
  have h2 := h (i + 2) (by omega)
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show (p0 + 1) + i = (p0 + i) + 1 by omega,
    rhCenter_step_succ (t + Q) (p0 + i),
    rhCenter_step_succ t (p0 + i),
    show (p0 + i) + 1 = p0 + (i + 1) by omega,
    show (p0 + i) + 2 = p0 + (i + 2) by omega,
    h0, h1, h2]

/-- **Equivalence of Right-Half `RhBandAgree` and `RowAgree` (`rowAgree_right_of_rhBandAgree`)**:
    for `p0 + L ≤ t`, `RhBandAgree t Q p0 L` on columns `[p0, p0 + L]` in the driven right half implies `RowAgree t Q (t - (p0 + L)) L` on `[t - (p0 + L), t - p0]`. -/
theorem rowAgree_right_of_rhBandAgree (t Q p0 L : Nat)
    (hp : p0 + L ≤ t) (h : RhBandAgree t Q p0 L) :
    RowAgree t Q (t - (p0 + L)) L := by
  intro i hi
  have hrh := h (L - i) (by omega)
  rw [rhCenter_eq_row_testBit (t + Q) (p0 + (L - i)) (by omega),
    rhCenter_eq_row_testBit t (p0 + (L - i)) (by omega),
    show (t + Q) - (p0 + (L - i)) = (t - (p0 + L)) + i + Q by omega,
    show t - (p0 + (L - i)) = (t - (p0 + L)) + i by omega] at hrh
  exact hrh

/-- **Converse Equivalence (`rhBandAgree_of_rowAgree_right`)**:
    for `p0 + L ≤ t`, `RowAgree t Q (t - (p0 + L)) L` implies `RhBandAgree t Q p0 L`. -/
theorem rhBandAgree_of_rowAgree_right (t Q p0 L : Nat)
    (hp : p0 + L ≤ t) (h : RowAgree t Q (t - (p0 + L)) L) :
    RhBandAgree t Q p0 L := by
  intro i hi
  have hrow := h (L - i) (by omega)
  rw [rhCenter_eq_row_testBit (t + Q) (p0 + i) (by omega),
    rhCenter_eq_row_testBit t (p0 + i) (by omega),
    show (t + Q) - (p0 + i) = (t - (p0 + L)) + (L - i) + Q by omega,
    show t - (p0 + i) = (t - (p0 + L)) + (L - i) by omega]
  exact hrow

/-- Paper-facing predicate `SectorRhBandAgree k d U Q`: at all sector times `t_u = (d + u * 2^k) + 1` (`u ≥ U`), `RhBandAgree t_u Q 0 (2^k + 1)` holds across the driven right half from column `0` to column `2^k + 1`. -/
def SectorRhBandAgree (k d U Q : Nat) : Prop :=
  ∀ u, U ≤ u → RhBandAgree ((d + u * twopow k) + 1) Q 0 (twopow k + 1)

/-- **Establishing `SectorRightRowAgree` from Driven Right-Half Band Agreement (`sectorRightRowAgree_of_rhBandAgree`)**:
    if at every sector time `t_u = (d + u * 2^k) + 1` (`u ≥ U`, `1 ≤ U`, `1 ≤ d`), `RhBandAgree t_u Q 0 (2^k + 1)` holds across the right half from column `0` to column `2^k + 1`, then `SectorRightRowAgree k d U Q` holds! -/
theorem sectorRightRowAgree_of_rhBandAgree (k d U Q : Nat)
    (hU : 1 ≤ U) (hd : 1 ≤ d)
    (hsec : SectorRhBandAgree k d U Q) :
    SectorRightRowAgree k d U Q := by
  intro u hu
  have h1 : 1 * twopow k ≤ u * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
  have hrh := hsec u hu
  have hrow := rowAgree_right_of_rhBandAgree ((d + u * twopow k) + 1) Q 0 (twopow k + 1)
    (by omega) hrh
  simpa using hrow

/-- **Refutation of Driven Right-Half Band Agreement at Sector Times for `Q = lcm(P, 2^k)` (`not_sector_rhBandAgree_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for `1 ≤ U`, `1 ≤ d`, and `T ≤ d + U * 2^k`, `SectorRhBandAgree k d U (lcmPeriod P k)` is false! -/
theorem not_sector_rhBandAgree_lcmPeriod
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * twopow k) :
    ¬ SectorRhBandAgree k d U (lcmPeriod P k) := by
  intro hsec
  have hsr := sectorRightRowAgree_of_rhBandAgree k d U (lcmPeriod P k) hU hd hsec
  exact not_sector_right_rowAgree_lcmPeriod T P hP hper k d U hU hd ht hsr

/-- **Right-Edge Band `Q`-Invariance of `rhCenter` at `Q = lcm(P, 2^k)` (`rhCenter_right_edge_lcmPeriod_eq`)**:
    for every `P, k, j, t : Nat` with `j ≤ k` and `j ≤ t`, column `(t + lcmPeriod P k) - j` of `rhCenter (t + lcmPeriod P k)` equals column `t - j` of `rhCenter t`. -/
theorem rhCenter_right_edge_lcmPeriod_eq (P k j t : Nat) (hj : j ≤ k) (hjt : j ≤ t) :
    rhCenter (t + lcmPeriod P k) ((t + lcmPeriod P k) - j) = rhCenter t (t - j) := by
  rw [rhCenter_eq_rdiag (t + lcmPeriod P k) ((t + lcmPeriod P k) - j) (by omega),
    rhCenter_eq_rdiag t (t - j) (by omega),
    show (t + lcmPeriod P k) - ((t + lcmPeriod P k) - j) = j by omega,
    show t - (t - j) = j by omega]
  exact rdiag_lcmPeriod_eq P k j t hj

/-- **Carrying `SectorWinWittAgree` to `ColNegOnePeriodic` Across Every Residue `mod 2^k` via Window Step 9.204 (`colNegOnePeriodic_of_sector_winWittAgree`)**:
    if `SectorWinWittAgree k d U Q` holds (`2 ≤ U`), then for every `t ≥ d + (U + 1) * 2^k`, writing `(t + 1) - 2^k = t_u + s` with `u ≥ U` and `s < 2^k`, the sub-interval `[(t_u + 2^k) - s, (t_u + 2^k) - s + 1 + 2 * s] ⊆ [t_u, t_u + 2 * 2^k]` advances by `s` steps of Window Step 9.204 (`winWittAgree_steps` with `L = 1`) and `rowAgree_steps` to establish `RowAgree ((t + 1)) Q (t + 1) 1`, yielding `ColNegOnePeriodic (d + (U + 1) * 2^k) Q` across all residues `mod 2^k`! -/
theorem colNegOnePeriodic_of_sector_winWittAgree (k d U Q : Nat) (hU : 2 ≤ U)
    (hsec : SectorWinWittAgree k d U Q) :
    ColNegOnePeriodic (d + (U + 1) * twopow k) Q := by
  intro t ht
  have hpos : 0 < twopow k := by
    have := twopow_gt_self k
    omega
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have ht_ge : d + U * twopow k + twopow k ≤ t := by
    have hm : (U + 1) * twopow k = U * twopow k + twopow k := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  have h_base1 : d + U * twopow k ≤ (t + 1) - twopow k := by omega
  obtain ⟨delta, hdelta⟩ : ∃ delta, (t + 1) - twopow k = (d + U * twopow k) + delta :=
    ⟨((t + 1) - twopow k) - (d + U * twopow k), by omega⟩
  obtain ⟨q, s, hdiv, hs_lt⟩ : ∃ q s, delta = q * twopow k + s ∧ s < twopow k :=
    ⟨delta / twopow k, delta % twopow k,
      by rw [Nat.mul_comm, Nat.div_add_mod],
      Nat.mod_lt delta hpos⟩
  have hu : U ≤ U + q := by omega
  let t0 := d + (U + q) * twopow k
  have ht1_eq : t + 1 = (t0 + s) + twopow k := by
    dsimp [t0]
    rw [Nat.add_mul]
    omega
  have h2_le : 2 * twopow k ≤ (U + q) * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
  obtain ⟨hw, h0, h1, h2⟩ := hsec (U + q) hu
  have hw_sub : WinWittAgree t0 k Q ((t0 + twopow k) - s) (1 + 2 * s) :=
    winWittAgree_mono t0 k Q ((t0 + twopow k) - twopow k) (2 * twopow k)
      ((t0 + twopow k) - s) (1 + 2 * s) (by omega) (by omega) hw
  have h0_sub : RowAgree t0 Q (((t0 + twopow k) - s) - twopow (k + 1)) (1 + 2 * s) :=
    rowAgree_mono t0 Q (((t0 + twopow k) - twopow k) - twopow (k + 1)) (2 * twopow k)
      (((t0 + twopow k) - s) - twopow (k + 1)) (1 + 2 * s) (by omega) (by omega) h0
  have h1_sub : RowAgree t0 Q (((t0 + twopow k) - s) - twopow k) (1 + 2 * s) :=
    rowAgree_mono t0 Q (((t0 + twopow k) - twopow k) - twopow k) (2 * twopow k)
      (((t0 + twopow k) - s) - twopow k) (1 + 2 * s) (by omega) (by omega) h1
  have h2_sub : RowAgree t0 Q ((t0 + twopow k) - s) (1 + 2 * s) :=
    rowAgree_mono t0 Q ((t0 + twopow k) - twopow k) (2 * twopow k)
      ((t0 + twopow k) - s) (1 + 2 * s) (by omega) (by omega) h2
  have hw_steps := winWittAgree_steps t0 k Q ((t0 + twopow k) - s) 1 s (by omega)
    hw_sub h0_sub h1_sub h2_sub
  have h0_steps := rowAgree_steps t0 Q (((t0 + twopow k) - s) - twopow (k + 1)) 1 s h0_sub
  have h1_steps := rowAgree_steps t0 Q (((t0 + twopow k) - s) - twopow k) 1 s h1_sub
  have h2_steps := rowAgree_steps t0 Q ((t0 + twopow k) - s) 1 s h2_sub
  rw [show ((t0 + twopow k) - s) + 2 * s = (t0 + s) + twopow k by omega] at hw_steps h2_steps
  rw [show (((t0 + twopow k) - s) - twopow (k + 1)) + 2 * s =
      ((t0 + s) + twopow k) - twopow (k + 1) by omega] at h0_steps
  rw [show (((t0 + twopow k) - s) - twopow k) + 2 * s =
      ((t0 + s) + twopow k) - twopow k by omega] at h1_steps
  have hlate := rowAgree_late_of_winWittAgree_and_three (t0 + s) k Q
    ((t0 + s) + twopow k) 1 (by omega) hw_steps h0_steps h1_steps h2_steps
  have hbit1 := hlate 1 (by omega)
  rw [← ht1_eq] at hbit1
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    ldiag_eq_rdiag (t + Q) 1,
    ldiag_eq_rdiag t 1,
    ← row_testBit ((t + Q) + 1) ((t + Q) + 2 * 1),
    ← row_testBit (t + 1) (t + 2 * 1)]
  rwa [show (t + 1) + Q = (t + Q) + 1 by omega,
    show (t + 1) + 1 + Q = (t + Q) + 2 * 1 by omega,
    show (t + 1) + 1 = t + 2 * 1 by omega] at hbit1

/-- **Refutation of `SectorWinWittAgree` at `Q = lcm(P, 2^k)` via Window Step 9.204 (`not_sector_winWittAgree_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for any `k, d, U : Nat` with `2 ≤ U`, `SectorWinWittAgree k d U (lcmPeriod P k)` is false! -/
theorem not_sector_winWittAgree_lcmPeriod
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 2 ≤ U) :
    ¬ SectorWinWittAgree k d U (lcmPeriod P k) := by
  intro hsec
  have hcol := colNegOnePeriodic_of_sector_winWittAgree k d U (lcmPeriod P k) hU hsec
  rw [lcmPeriod_eq_mul_period P k] at hcol
  exact not_periodic_colm1_mul T P hP hper (d + (U + 1) * twopow k)
    (twopow k / Nat.gcd P (twopow k)) (lcmPeriod_div_pos P k hP) hcol

/-- Paper-facing predicate `SectorWideRowAgree k d U Q`: at all sector times `t_u = d + u * 2^k` (`u ≥ U`), the two-sided symmetric neighbourhood of radius `2^(k+1)` (`[t_u - 2^(k+1), t_u + 2^(k+1)]`) agrees between `t_u` and `t_u + Q`. -/
def SectorWideRowAgree (k d U Q : Nat) : Prop :=
  ∀ u, U ≤ u →
    RowAgree (d + u * twopow k) Q
      ((d + u * twopow k) - twopow (k + 1)) (2 * twopow (k + 1))

/-- Paper-facing predicate `SectorWideRightRowAgree k d U Q`: at all sector times `t_u = d + u * 2^k` (`u ≥ U`), the one-sided right-wing neighbourhood of width `2^(k+1)` (`[t_u - 2^(k+1), t_u]`, columns `p ∈ [0, 2^(k+1)]` of `rhCenter`) agrees between `t_u` and `t_u + Q`. -/
def SectorWideRightRowAgree (k d U Q : Nat) : Prop :=
  ∀ u, U ≤ u →
    RowAgree (d + u * twopow k) Q
      ((d + u * twopow k) - twopow (k + 1)) (twopow (k + 1))

/-- **Establishing `SectorWinWittAgree` from Pure Sector-Time Row Agreement (`sectorWinWittAgree_of_sectorWideRowAgree`)**:
    for `2 ≤ U`, because `t_u + 2^k = d + (u + 1) * 2^k = t_{u+1}` is the next sector time, `SectorWideRowAgree k d U Q` supplies both the three-sector `RowAgree` at `t_u` and the late `RowAgree` at `t_u + 2^k = t_{u+1}`, establishing `SectorWinWittAgree k d U Q` via `winWittAgree_of_rowAgree_three_and_late`! -/
theorem sectorWinWittAgree_of_sectorWideRowAgree (k d U Q : Nat) (hU : 2 ≤ U)
    (hsec : SectorWideRowAgree k d U Q) :
    SectorWinWittAgree k d U Q := by
  intro u hu
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h2_le : 2 * twopow k ≤ u * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
  have hu_row := hsec u hu
  have hu1_row := hsec (u + 1) (by omega)
  have h0 : RowAgree (d + u * twopow k) Q
      ((((d + u * twopow k) + twopow k) - twopow k) - twopow (k + 1)) (2 * twopow k) :=
    rowAgree_mono (d + u * twopow k) Q
      ((d + u * twopow k) - twopow (k + 1)) (2 * twopow (k + 1))
      ((((d + u * twopow k) + twopow k) - twopow k) - twopow (k + 1)) (2 * twopow k)
      (by omega) (by omega) hu_row
  have h1 : RowAgree (d + u * twopow k) Q
      ((((d + u * twopow k) + twopow k) - twopow k) - twopow k) (2 * twopow k) :=
    rowAgree_mono (d + u * twopow k) Q
      ((d + u * twopow k) - twopow (k + 1)) (2 * twopow (k + 1))
      ((((d + u * twopow k) + twopow k) - twopow k) - twopow k) (2 * twopow k)
      (by omega) (by omega) hu_row
  have h2 : RowAgree (d + u * twopow k) Q
      (((d + u * twopow k) + twopow k) - twopow k) (2 * twopow k) :=
    rowAgree_mono (d + u * twopow k) Q
      ((d + u * twopow k) - twopow (k + 1)) (2 * twopow (k + 1))
      (((d + u * twopow k) + twopow k) - twopow k) (2 * twopow k)
      (by omega) (by omega) hu_row
  have hlate : RowAgree ((d + u * twopow k) + twopow k) Q
      (((d + u * twopow k) + twopow k) - twopow k) (2 * twopow k) := by
    have h_eq : (d + u * twopow k) + twopow k = d + (u + 1) * twopow k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [h_eq]
    exact rowAgree_mono (d + (u + 1) * twopow k) Q
      ((d + (u + 1) * twopow k) - twopow (k + 1)) (2 * twopow (k + 1))
      ((d + (u + 1) * twopow k) - twopow k) (2 * twopow k)
      (by omega) (by omega) hu1_row
  have hw := winWittAgree_of_rowAgree_three_and_late (d + u * twopow k) k Q
    (((d + u * twopow k) + twopow k) - twopow k) (2 * twopow k)
    (by omega) h0 h1 h2 hlate
  exact ⟨hw, h0, h1, h2⟩

/-- **Establishing `SectorWinWittAgree` from One-Sided Right-Wing Sector Row Agreement (`sectorWinWittAgree_of_sectorWideRightRowAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `2 ≤ U` and `T ≤ d + U * 2^k`, one-sided right-wing `SectorWideRightRowAgree k d U (m * P)` doubles across the periodic center via `periodic_rowAgree_symm_of_right` (`Φ` fixed-point reflection!) to `SectorWideRowAgree k d U (m * P)` and hence implies `SectorWinWittAgree k d U (m * P)`! -/
theorem sectorWinWittAgree_of_sectorWideRightRowAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (hU : 2 ≤ U) (ht : T ≤ d + U * twopow k)
    (hsec : SectorWideRightRowAgree k d U (m * P)) :
    SectorWinWittAgree k d U (m * P) := by
  refine sectorWinWittAgree_of_sectorWideRowAgree k d U (m * P) hU (fun u hu => ?_)
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have h2_le : 2 * twopow k ≤ u * twopow k := Nat.mul_le_mul_right (twopow k) (by omega)
  have hU_le : U * twopow k ≤ u * twopow k := Nat.mul_le_mul_right (twopow k) hu
  exact periodic_rowAgree_symm_of_right T P hP hper m (twopow (k + 1))
    (d + u * twopow k) (by omega) (by omega) (hsec u hu)

/-- **Refutation of One-Sided Wide Right-Wing Sector Agreement at `Q = lcm(P, 2^k)` via Window Step 9.204 (`not_sectorWideRightRowAgree_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for `2 ≤ U` and `T ≤ d + U * 2^k`, `SectorWideRightRowAgree k d U (lcmPeriod P k)` is false! -/
theorem not_sectorWideRightRowAgree_lcmPeriod
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 2 ≤ U) (ht : T ≤ d + U * twopow k) :
    ¬ SectorWideRightRowAgree k d U (lcmPeriod P k) := by
  intro hsec
  rw [lcmPeriod_eq_mul_period P k] at hsec
  have hwin := sectorWinWittAgree_of_sectorWideRightRowAgree T P hP hper
    k d U (twopow k / Nat.gcd P (twopow k)) hU ht hsec
  rw [← lcmPeriod_eq_mul_period P k] at hwin
  exact not_sector_winWittAgree_lcmPeriod T P hP hper k d U hU hwin

theorem rhCenter_eq_row_testBit_prop (t p : Nat) (hp : p ≤ t) :
    rhCenter t p = wittBitBool (row t) (t - p) :=
  rhCenter_eq_row_testBit t p hp

theorem lhCenter_eq_row_testBit_prop (t p : Nat) (hp : p ≤ t) :
    lhCenter t p = wittBitBool (row t) (t + p) :=
  lhCenter_eq_row_testBit t p hp

theorem not_sector_rhBandAgree_lcmPeriod_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * twopow k) :
    ¬ (∀ u, U ≤ u → RhBandAgree ((d + u * twopow k) + 1) (lcmPeriod P k) 0 (twopow k + 1)) :=
  not_sector_rhBandAgree_lcmPeriod T P hP hper k d U hU hd ht

/-- **Boundary Readouts of the Driven Left Half `lhCenter` (`lhCenter_zero_eq_center`, `lhCenter_self_eq_true`, `lhCenter_gt_eq_false`)**:
    at `p = 0`, `lhCenter t 0 = center t`; at the left edge `p = t`, `lhCenter t t = true`; and outside the light cone (`t < p`), `lhCenter t p = false`. -/
theorem lhCenter_zero_eq_center (t : Nat) :
    lhCenter t 0 = Rule30UOR.Core.center t := by
  have h1 := lhCenter_eq_row_testBit t 0 (by omega)
  have h2 := rhCenter_eq_row_testBit t 0 (by omega)
  rw [Nat.add_zero] at h1
  rw [Nat.sub_zero] at h2
  rw [h1, ← h2, rhCenter_zero_eq_center]

theorem lhCenter_self_eq_true (t : Nat) :
    lhCenter t t = true := by
  rw [lhCenter_eq_ldiag t t (by omega), Nat.sub_self]
  rcases t with _ | t <;> rfl

theorem lhCenter_gt_eq_false (t p : Nat) (h : t < p) :
    lhCenter t p = false := by
  unfold lhCenter
  induction t generalizing p with
  | zero =>
    simp [Rule30UOR.Fixed.Lh]
    omega
  | succ t ih =>
    rcases p with _ | p
    · omega
    · have hneg : (- ((p + 1 : Nat) : Int)) < 0 := by omega
      simp only [Rule30UOR.Fixed.Lh, if_pos hneg, Ruliology.CellularAutomata.Rule30Jen.rule]
      rw [show (- ((p + 1 : Nat) : Int)) - 1 = (- ((p + 2 : Nat) : Int)) by omega,
        show (- ((p + 1 : Nat) : Int)) + 1 = (- (p : Int)) by omega,
        ih (p + 2) (by omega), ih (p + 1) (by omega), ih p (by omega)]
      rfl

/-- **Evolution Law of the Driven Left Half `lhCenter` (`lhCenter_step_succ`)**:
    for all `t, p : Nat`, column `-(p + 1)` of `lhCenter (t + 1)` evolves by Rule 30 from columns `-(p + 2), -(p + 1), -p` of `lhCenter t`. -/
theorem lhCenter_step_succ (t p : Nat) :
    lhCenter (t + 1) (p + 1) =
      bxor (lhCenter t (p + 2)) (lhCenter t (p + 1) || lhCenter t p) := by
  unfold lhCenter
  have hneg : (- ((p + 1 : Nat) : Int)) < 0 := by omega
  simp only [Rule30UOR.Fixed.Lh, if_pos hneg]
  rw [show (- ((p + 1 : Nat) : Int)) - 1 = (- ((p + 2 : Nat) : Int)) by omega,
    show (- ((p + 1 : Nat) : Int)) + 1 = (- (p : Int)) by omega]
  unfold Ruliology.CellularAutomata.Rule30Jen.rule
  rw [bxor_eq_xor]

/-- **Outward Step Law of the Driven Left Half from the Center Toward the Left Edge (`lhCenter_outward_step`)**:
    for all `t, p : Nat`, solving `lhCenter_step_succ` for `lhCenter t (p + 2)` expresses column `-(p + 2)` at time `t` in terms of column `-(p + 1)` at time `t + 1` and columns `-(p + 1), -p` at time `t`. -/
theorem lhCenter_outward_step (t p : Nat) :
    lhCenter t (p + 2) =
      bxor (lhCenter (t + 1) (p + 1)) (lhCenter t (p + 1) || lhCenter t p) := by
  rw [lhCenter_step_succ t p, bxor_eq_xor, bxor_eq_xor]
  cases lhCenter t (p + 2) <;>
    cases (lhCenter t (p + 1) || lhCenter t p) <;> rfl

/-- **Pure Right-Half Unfolding of the Center Column (`center_eq_rhCenter_inward_zero`)**:
    evaluating `rhCenter_inward_step` at `p = 0` expresses `center t` purely in terms of the driven right half `rhCenter (t + 1) 1`, `rhCenter t 1`, and `rhCenter t 2`! -/
theorem center_eq_rhCenter_inward_zero (t : Nat) :
    Rule30UOR.Core.center t =
      bxor (rhCenter (t + 1) 1) (rhCenter t 1 || rhCenter t 2) := by
  rw [← rhCenter_zero_eq_center t, rhCenter_inward_step t 0]

/-- **Periodic Center-Bounce Equivalence at Column 1 (`periodic_rhCenter_step_one_eq_of_or_eq` and `periodic_rhCenter_or_eq_of_step_one_eq`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `t ≥ T` and `m : Nat`, `rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1` holds if and only if `(rhCenter (t + m * P) 1 || rhCenter (t + m * P) 2) = (rhCenter t 1 || rhCenter t 2)`. -/
theorem periodic_rhCenter_step_one_eq_of_or_eq
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hor : (rhCenter (t + m * P) 1 || rhCenter (t + m * P) 2) =
      (rhCenter t 1 || rhCenter t 2)) :
    rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1 := by
  have hc : rhCenter (t + m * P) 0 = rhCenter t 0 := by
    rw [rhCenter_zero_eq_center, rhCenter_zero_eq_center]
    exact Rule30UOR.Scale.center_mul hper m t ht
  rw [show (t + 1) + m * P = (t + m * P) + 1 by omega,
    rhCenter_step_succ (t + m * P) 0,
    rhCenter_step_succ t 0,
    hc, hor]

theorem periodic_rhCenter_or_eq_of_step_one_eq
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t : Nat) (ht : T ≤ t)
    (hstep : rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1) :
    (rhCenter (t + m * P) 1 || rhCenter (t + m * P) 2) =
      (rhCenter t 1 || rhCenter t 2) := by
  have hc0 := center_eq_rhCenter_inward_zero t
  have hcQ := center_eq_rhCenter_inward_zero (t + m * P)
  have hcm : Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t :=
    Rule30UOR.Scale.center_mul hper m t ht
  rw [show (t + m * P) + 1 = (t + 1) + m * P by omega, hstep, hcm] at hcQ
  rw [hc0] at hcQ
  revert hcQ
  simp only [bxor_eq_xor]
  cases rhCenter (t + 1) 1 <;>
    cases (rhCenter (t + m * P) 1 || rhCenter (t + m * P) 2) <;>
    cases (rhCenter t 1 || rhCenter t 2) <;> decide

/-- **Multi-Step Forward Propagation of Right-Half Band Agreement (`rhBandAgree_steps`)**:
    by induction on `s : Nat`, `RhBandAgree t Q p0 (L + 2 * s)` implies `RhBandAgree (t + s) Q (p0 + s) L`. -/
theorem rhBandAgree_steps (t Q p0 L s : Nat)
    (h : RhBandAgree t Q p0 (L + 2 * s)) :
    RhBandAgree (t + s) Q (p0 + s) L := by
  induction s generalizing t p0 L with
  | zero =>
    simpa using h
  | succ s ih =>
    have h' : RhBandAgree t Q p0 ((L + 2 * s) + 2) := by
      intro i hi
      exact h i (by omega)
    have h1 := rhBandAgree_step t Q p0 (L + 2 * s) h'
    have h2 := ih (t + 1) (p0 + 1) L h1
    rw [show (t + 1) + s = t + (s + 1) by omega,
      show (p0 + 1) + s = p0 + (s + 1) by omega] at h2
    exact h2

/-- **Free Inward Extension of `RhBandAgree` from Column 1 to Column 0 under `CenterPeriodic` (`periodic_rhBandAgree_zero_of_one`)**:
    under `CenterPeriodic T P` (`0 < P`), for `t ≥ T`, `RhBandAgree t (m * P) 1 L` automatically extends inward to `RhBandAgree t (m * P) 0 (L + 1)` because `rhCenter · 0 = center ·` is `m * P`-periodic! -/
theorem periodic_rhBandAgree_zero_of_one
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : RhBandAgree t (m * P) 1 L) :
    RhBandAgree t (m * P) 0 (L + 1) := by
  intro i hi
  rcases i with _ | i
  · simp only [Nat.zero_add, rhCenter_zero_eq_center]
    exact Rule30UOR.Scale.center_mul hper m t ht
  · have hi' : i ≤ L := by omega
    have h1 := h i hi'
    rw [show 1 + i = 0 + (i + 1) by omega] at h1
    exact h1

/-- **Center-Anchored Forward Step of `RhBandAgree` at `p0 = 0` (`periodic_rhBandAgree_zero_step` and `periodic_rhBandAgree_zero_steps`)**:
    under `CenterPeriodic T P` (`0 < P`), for `t ≥ T`, `RhBandAgree t (m * P) 0 (L + 1)` steps forward in time to `RhBandAgree (t + 1) (m * P) 0 L`, keeping `p0 = 0` fixed and losing only 1 column on the right (instead of 2) because column 0 is resupplied at `t + 1` by the periodic center! -/
theorem periodic_rhBandAgree_zero_step
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L : Nat) (ht : T ≤ t)
    (h : RhBandAgree t (m * P) 0 (L + 1)) :
    RhBandAgree (t + 1) (m * P) 0 L := by
  rcases L with _ | L
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [Nat.zero_add, rhCenter_zero_eq_center]
    exact Rule30UOR.Scale.center_mul hper m (t + 1) (by omega)
  · have hstep := rhBandAgree_step t (m * P) 0 L h
    exact periodic_rhBandAgree_zero_of_one T P hP hper m (t + 1) L (by omega) hstep

theorem periodic_rhBandAgree_zero_steps
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t L s : Nat) (ht : T ≤ t)
    (h : RhBandAgree t (m * P) 0 (L + s)) :
    RhBandAgree (t + s) (m * P) 0 L := by
  induction s generalizing t L with
  | zero =>
    simpa using h
  | succ s ih =>
    have h' : RhBandAgree t (m * P) 0 ((L + s) + 1) := by
      intro i hi
      exact h i (by omega)
    have h1 := periodic_rhBandAgree_zero_step T P hP hper m t (L + s) ht h'
    have h2 := ih (t + 1) L (by omega) h1
    rw [show (t + 1) + s = t + (s + 1) by omega] at h2
    exact h2

/-- **Multi-Step Inward Extension of `RhBandAgree` from the Right Edge Toward the Center (`rhBandAgree_extend_inward_steps`)**:
    if `RhBandAgree t Q (p0 + S) (L + 1)` holds at the right end of `[p0, p0 + S + L + 1]` at time `t` and `RhBandAgree (t + 1) Q (p0 + 1) S` holds at time `t + 1`, then `S` applications of `rhBandAgree_extend_inward` yield `RhBandAgree t Q p0 (L + 1 + S)` across the entire band at time `t`! -/
theorem rhBandAgree_extend_inward_steps (t Q p0 S L : Nat)
    (h : RhBandAgree t Q (p0 + S) (L + 1))
    (hstep : RhBandAgree (t + 1) Q (p0 + 1) S) :
    RhBandAgree t Q p0 (L + 1 + S) := by
  induction S generalizing L with
  | zero =>
    simpa using h
  | succ S ih =>
    have h_ext : RhBandAgree t Q (p0 + S) ((L + 1) + 1) := by
      have h_in := rhBandAgree_extend_inward t Q (p0 + S) L
      apply h_in
      · intro i hi
        have := h i hi
        rw [show p0 + (S + 1) + i = (p0 + S + 1) + i by omega] at this
        exact this
      · have hs := hstep (S + 1) (by omega)
        rw [show (p0 + 1) + (S + 1) = (p0 + S) + 1 + 1 by omega] at hs
        have hs0 := hstep S (by omega)
        rw [show (p0 + 1) + S = (p0 + S) + 1 by omega] at hs0
        exact hs0
    have hstep' : RhBandAgree (t + 1) Q (p0 + 1) S := by
      intro i hi
      exact hstep i (by omega)
    have hres := ih (L + 1) h_ext hstep'
    intro i hi
    exact hres i (by omega)

/-- **Right-to-Center Full Band Agreement from Right-Boundary Pair and Next-Step Interior (`rhBandAgree_zero_of_edge_and_succ`)**:
    specializing `rhBandAgree_extend_inward_steps` to `p0 = 0` yields `RhBandAgree t Q 0 (L + 1 + S)` from `RhBandAgree t Q S (L + 1)` at time `t` and `RhBandAgree (t + 1) Q 1 S` at time `t + 1`. -/
theorem rhBandAgree_zero_of_edge_and_succ (t Q S L : Nat)
    (h : RhBandAgree t Q S (L + 1))
    (hstep : RhBandAgree (t + 1) Q 1 S) :
    RhBandAgree t Q 0 (L + 1 + S) := by
  have h0 : RhBandAgree t Q (0 + S) (L + 1) := by simpa using h
  have h1 : RhBandAgree (t + 1) Q (0 + 1) S := by simpa using hstep
  exact rhBandAgree_extend_inward_steps t Q 0 S L h0 h1

/-- **Center-Bounce Inward Extension of `RhBandAgree` (`periodic_rhBandAgree_bounce_zero` and `periodic_rhBandAgree_bounce_succ`)**:
    under `CenterPeriodic T P` (`0 < P`), for `t ≥ T`, agreement starting at column `2` at time `t + 1` (`RhBandAgree (t + 1) (m * P) 2 S`) combined with `RhBandAgree t (m * P) (S + 1) (L + 1)` at time `t` marches inward to column `1` at time `t`, picks up column `0` from the periodic center to give `RhBandAgree t (m * P) 0 (L + 2 + S)` at time `t`, and bounces forward off `(t, 0)` to give `RhBandAgree (t + 1) (m * P) 0 (L + 1 + S)` at time `t + 1`! -/
theorem periodic_rhBandAgree_bounce_zero
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S L : Nat) (ht : T ≤ t)
    (h : RhBandAgree t (m * P) (S + 1) (L + 1))
    (hstep : RhBandAgree (t + 1) (m * P) 2 S) :
    RhBandAgree t (m * P) 0 (L + 2 + S) := by
  have h_in := rhBandAgree_extend_inward_steps t (m * P) 1 S L
    (by intro i hi; have := h i hi; rw [show S + 1 + i = 1 + S + i by omega] at this; exact this)
    hstep
  have h_zero := periodic_rhBandAgree_zero_of_one T P hP hper m t (L + 1 + S) ht h_in
  intro i hi
  exact h_zero i (by omega)

theorem periodic_rhBandAgree_bounce_succ
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S L : Nat) (ht : T ≤ t)
    (h : RhBandAgree t (m * P) (S + 1) (L + 1))
    (hstep : RhBandAgree (t + 1) (m * P) 2 S) :
    RhBandAgree (t + 1) (m * P) 0 (L + 1 + S) := by
  have hb := periodic_rhBandAgree_bounce_zero T P hP hper m t S L ht h hstep
  have hb' : RhBandAgree t (m * P) 0 ((L + 1 + S) + 1) := by
    intro i hi
    exact hb i (by omega)
  exact periodic_rhBandAgree_zero_step T P hP hper m t (L + 1 + S) ht hb'

/-- **Direct Right-Half Propagation of `SectorRhBandAgree` to Every-Time Column `+1` Periodicity (`rhCenter_one_periodic_of_sector_rhBandAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ d + U * 2^k`, `SectorRhBandAgree k d U (m * P)` implies that `rhCenter (t + m * P) 1 = rhCenter t 1` holds for EVERY time `t ≥ (d + U * 2^k) + 1` (every residue `mod 2^k`) via `periodic_rhBandAgree_zero_steps` purely inside the right half! -/
theorem rhCenter_one_periodic_of_sector_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (ht : T ≤ d + U * twopow k)
    (hsec : SectorRhBandAgree k d U (m * P)) :
    ∀ t, (d + U * twopow k) + 1 ≤ t →
      rhCenter (t + m * P) 1 = rhCenter t 1 := by
  intro t ht_ge
  have hpos : 0 < twopow k := by
    have := twopow_gt_self k
    omega
  obtain ⟨delta, hdelta⟩ : ∃ delta, t = ((d + U * twopow k) + 1) + delta :=
    ⟨t - ((d + U * twopow k) + 1), by omega⟩
  obtain ⟨q, s, hdiv, hs_lt⟩ : ∃ q s, delta = q * twopow k + s ∧ s < twopow k :=
    ⟨delta / twopow k, delta % twopow k,
      by rw [Nat.mul_comm, Nat.div_add_mod],
      Nat.mod_lt delta hpos⟩
  have hu : U ≤ U + q := by omega
  let t0 := (d + (U + q) * twopow k) + 1
  have ht0_eq : t = t0 + s := by
    dsimp [t0]
    rw [hdelta, hdiv, Nat.add_mul]
    omega
  have h_u := hsec (U + q) hu
  have h_sub : RhBandAgree t0 (m * P) 0 (1 + s) := by
    intro i hi
    exact h_u i (by omega)
  have hU_le : U * twopow k ≤ (U + q) * twopow k := Nat.mul_le_mul_right (twopow k) hu
  have h_steps := periodic_rhBandAgree_zero_steps T P hP hper m t0 1 s (by omega) h_sub
  rw [← ht0_eq] at h_steps
  exact h_steps 1 (by omega)

/-- **Direct Right-Half-to-`Φ`-Fixed-Point Propagation of `SectorRhBandAgree` to Every-Time Column `-1` Periodicity (`lhCenter_one_periodic_of_sector_rhBandAgree`)**:
    under `CenterPeriodic T P` (`0 < P`), for `T ≤ d + U * 2^k`, combining `rhCenter_one_periodic_of_sector_rhBandAgree` with the §6 `Φ` fixed-point law `lhCenter_one_eq_of_center_fixed` proves `lhCenter (t + m * P) 1 = lhCenter t 1` for EVERY time `t ≥ (d + U * 2^k) + 1` without reflecting row segments to the left half! -/
theorem lhCenter_one_periodic_of_sector_rhBandAgree
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U m : Nat) (ht : T ≤ d + U * twopow k)
    (hsec : SectorRhBandAgree k d U (m * P)) :
    ∀ t, (d + U * twopow k) + 1 ≤ t →
      lhCenter (t + m * P) 1 = lhCenter t 1 := by
  intro t ht_ge
  have hrh := rhCenter_one_periodic_of_sector_rhBandAgree T P hP hper k d U m ht hsec t ht_ge
  have hc0 : Rule30UOR.Core.center (t + m * P) = Rule30UOR.Core.center t :=
    Rule30UOR.Scale.center_mul hper m t (by omega)
  have hc1 : Rule30UOR.Core.center ((t + m * P) + 1) = Rule30UOR.Core.center (t + 1) := by
    rw [show (t + m * P) + 1 = (t + 1) + m * P by omega]
    exact Rule30UOR.Scale.center_mul hper m (t + 1) (by omega)
  rw [lhCenter_one_eq_of_center_fixed (t + m * P),
    lhCenter_one_eq_of_center_fixed t,
    hc0, hc1, hrh]

/-- **Unconditional Right-Edge Diagonal `2^k`-Shift Invariance of `rhCenter` (`rhCenter_diag_shift_twopow_eq` and `rhCenter_sector_diag_eq_center`)**:
    for all `k, t, p, v : Nat` with `p ≤ t` and `t - p ≤ k` (no settling condition required!), `rhCenter (t + v * 2^k) (p + v * 2^k) = rhCenter t p`, and in particular `rhCenter (j + u * 2^k) (u * 2^k) = center j` for all `j ≤ k`. -/
theorem rhCenter_diag_shift_twopow_eq (k t p v : Nat)
    (hp : p ≤ t) (hj : t - p ≤ k) :
    rhCenter (t + v * twopow k) (p + v * twopow k) = rhCenter t p := by
  rw [rhCenter_eq_rdiag (t + v * twopow k) (p + v * twopow k) (by omega),
    rhCenter_eq_rdiag t p hp,
    show (t + v * twopow k) - (p + v * twopow k) = t - p by omega]
  exact rdiag_restart k (t - p) v t hj

theorem rhCenter_sector_diag_eq_center (j k u : Nat) (hj : j ≤ k) :
    rhCenter (j + u * twopow k) (u * twopow k) = Rule30UOR.Core.center j := by
  have h := rhCenter_diag_shift_twopow_eq k j 0 u (by omega) (by omega)
  rw [Nat.zero_add, rhCenter_zero_eq_center] at h
  exact h

/-- **Exact `2^k`-Scale Forward and Inward Step Laws of the Driven Right Half `rhCenter` (`rhCenter_scale_step` and `rhCenter_scale_inward_step`)**:
    for `p + 2^(k+1) ≤ t`, `rhCenter (t + 2^k) (p + 2^k)` evolves linearly (via `bxor`) from `rhCenter t p`, `rhCenter t (p + 2^k)`, and `rhCenter t (p + 2^(k+1))` corrected by bit `t - p` of `winWitt t (2^k)`! -/
theorem rhCenter_scale_step (t k p : Nat) (hp : p + twopow (k + 1) ≤ t) :
    rhCenter (t + twopow k) (p + twopow k) =
      bxor
        (bxor (bxor (rhCenter t p) (rhCenter t (p + twopow k)))
          (rhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t - p)) := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  rw [rhCenter_eq_row_testBit (t + twopow k) (p + twopow k) (by omega),
    show (t + twopow k) - (p + twopow k) = t - p by omega,
    row_scale t k, Nat.testBit_xor]
  have hphi : (phiScale k (row t)).testBit (t - p) =
      bxor (bxor (rhCenter t p) (rhCenter t (p + twopow k)))
        (rhCenter t (p + twopow (k + 1))) := by
    change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit (t - p) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, bxor_eq_xor]
    have d1 : decide (t - p ≥ twopow k) = true := decide_eq_true (by omega)
    have d2 : decide (t - p ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.true_and,
      show t - p - twopow k = t - (p + twopow k) by omega,
      show t - p - (twopow k + twopow k) = t - (p + twopow (k + 1)) by omega,
      ← rhCenter_eq_row_testBit t p (by omega),
      ← rhCenter_eq_row_testBit t (p + twopow k) (by omega),
      ← rhCenter_eq_row_testBit t (p + twopow (k + 1)) (by omega)]
  rw [hphi]
  simp only [bxor_eq_xor]

theorem rhCenter_scale_inward_step (t k p : Nat) (hp : p + twopow (k + 1) ≤ t) :
    rhCenter t p =
      bxor
        (bxor (bxor (rhCenter (t + twopow k) (p + twopow k)) (rhCenter t (p + twopow k)))
          (rhCenter t (p + twopow (k + 1))))
        ((winWitt t (twopow k)).testBit (t - p)) := by
  rw [rhCenter_scale_step t k p hp]
  simp only [bxor_eq_xor]
  cases rhCenter t p <;>
    cases rhCenter t (p + twopow k) <;>
    cases rhCenter t (p + twopow (k + 1)) <;>
    cases (winWitt t (twopow k)).testBit (t - p) <;> rfl

/-! ### Multi-Step Right-Half Window Determination (`RhOrAgree`), Unconditional Right-Edge `RhBandAgree`, and `2^k`-Scale Band Transport -/

/-- Time-trace `Q`-agreement of column `p0` of `rhCenter`:
    at times `t + s` and `(t + s) + Q` (`s ≤ S`), column `p0` of `rhCenter` agrees. -/
def RhColAgree (t Q p0 S : Nat) : Prop :=
  ∀ s, s ≤ S →
    rhCenter ((t + s) + Q) p0 = rhCenter (t + s) p0

instance (t Q p0 S : Nat) : Decidable (RhColAgree t Q p0 S) := by
  unfold RhColAgree
  infer_instance

/-- Band `Q`-agreement of the right-half `OR` input `rhCenter · p0 || rhCenter · (p0 + 1)`:
    at times `t + s` and `(t + s) + Q` (`s < S`), the right-half OR inputs agree at column `p0`. -/
def RhOrAgree (t Q p0 S : Nat) : Prop :=
  ∀ s, s < S →
    (rhCenter ((t + s) + Q) p0 || rhCenter ((t + s) + Q) (p0 + 1)) =
      (rhCenter (t + s) p0 || rhCenter (t + s) (p0 + 1))

/-- **Sub-interval Monotonicity of `RhBandAgree` (`rhBandAgree_mono`)**:
    if `RhBandAgree t Q p0 L` holds on `[p0, p0 + L]` and `[p0', p0' + L'] ⊆ [p0, p0 + L]`, then `RhBandAgree t Q p0' L'` holds. -/
theorem rhBandAgree_mono (t Q p0 L p0' L' : Nat)
    (hp : p0 ≤ p0') (hL : p0' + L' ≤ p0 + L)
    (h : RhBandAgree t Q p0 L) :
    RhBandAgree t Q p0' L' := by
  intro i hi
  have hj : (p0' - p0) + i ≤ L := by omega
  have heq := h ((p0' - p0) + i) hj
  rwa [show p0 + ((p0' - p0) + i) = p0' + i by omega] at heq

/-- **Sub-interval Monotonicity of `RhColAgree` (`rhColAgree_mono`)**:
    if `RhColAgree t Q p0 S` holds on `[t, t + S]` and `[t + s0, t + s0 + S'] ⊆ [t, t + S]`, then `RhColAgree (t + s0) Q p0 S'` holds. -/
theorem rhColAgree_mono (t Q p0 S s0 S' : Nat)
    (hs : s0 + S' ≤ S)
    (h : RhColAgree t Q p0 S) :
    RhColAgree (t + s0) Q p0 S' := by
  intro s hs'
  have heq := h (s0 + s) (by omega)
  rwa [show t + (s0 + s) = (t + s0) + s by omega] at heq

/-- **Sub-interval Monotonicity of `RhOrAgree` (`rhOrAgree_mono`)**:
    if `RhOrAgree t Q p0 S` holds on `[t, t + S)` and `[t + s0, t + s0 + S') ⊆ [t, t + S)`, then `RhOrAgree (t + s0) Q p0 S'` holds. -/
theorem rhOrAgree_mono (t Q p0 S s0 S' : Nat)
    (hs : s0 + S' ≤ S)
    (h : RhOrAgree t Q p0 S) :
    RhOrAgree (t + s0) Q p0 S' := by
  intro s hs'
  have heq := h (s0 + s) (by omega)
  rwa [show t + (s0 + s) = (t + s0) + s by omega] at heq

/-- **Right-Half `RhOrAgree` from Column-`p0` Time-Trace Agreement (`rhOrAgree_of_col_agree`)**:
    if `RhColAgree t Q p0 S` holds on `[t, t + S]` and column `p0 + 1` agrees at times `t + 1 + s` (`s < S`), then `rhCenter_inward_step` forces `RhOrAgree t Q (p0 + 1) S`! -/
theorem rhOrAgree_of_col_agree (t Q p0 S : Nat)
    (hcol : RhColAgree t Q p0 S)
    (hnext : ∀ s, s < S →
      rhCenter ((t + (s + 1)) + Q) (p0 + 1) = rhCenter (t + (s + 1)) (p0 + 1)) :
    RhOrAgree t Q (p0 + 1) S := by
  intro s hs
  have hc := hcol s (by omega)
  have hn := hnext s hs
  have hinQ := rhCenter_inward_step ((t + s) + Q) p0
  have hin0 := rhCenter_inward_step (t + s) p0
  rw [show ((t + s) + Q) + 1 = (t + (s + 1)) + Q by omega] at hinQ
  rw [show (t + s) + 1 = t + (s + 1) by omega] at hin0
  rw [hinQ, hin0, hn] at hc
  rw [show (p0 + 1) + 1 = p0 + 2 by omega]
  revert hc
  simp only [bxor_eq_xor]
  cases rhCenter (t + (s + 1)) (p0 + 1) <;>
    cases (rhCenter ((t + s) + Q) (p0 + 1) || rhCenter ((t + s) + Q) (p0 + 2)) <;>
    cases (rhCenter (t + s) (p0 + 1) || rhCenter (t + s) (p0 + 2)) <;> decide

/-- **Center `RhOrAgree` Equivalence (`periodic_rhOrAgree_one_of_col_one` and `periodic_col_one_of_rhOrAgree_one`)**:
    under `CenterPeriodic T P` (`0 < P`), for `t ≥ T`, `RhOrAgree t (m * P) 1 S` holds if and only if column `1` of `rhCenter` agrees on `[t + 1, t + S]`. -/
theorem periodic_rhOrAgree_one_of_col_one
    (T P : Nat) (_hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (h1 : ∀ s, s < S → rhCenter ((t + (s + 1)) + m * P) 1 = rhCenter (t + (s + 1)) 1) :
    RhOrAgree t (m * P) 1 S := by
  have h := rhOrAgree_of_col_agree t (m * P) 0 S (fun s _ => by
    rw [rhCenter_zero_eq_center, rhCenter_zero_eq_center]
    exact Rule30UOR.Scale.center_mul hper m (t + s) (by omega)) h1
  simpa using h

theorem periodic_col_one_of_rhOrAgree_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t S : Nat) (ht : T ≤ t)
    (hor : RhOrAgree t (m * P) 1 S) :
    ∀ s, s < S → rhCenter ((t + (s + 1)) + m * P) 1 = rhCenter (t + (s + 1)) 1 := by
  intro s hs
  have h_or := hor s hs
  rw [show t + (s + 1) = (t + s) + 1 by omega]
  exact periodic_rhCenter_step_one_eq_of_or_eq T P hP hper m (t + s) (by omega) h_or

/-- **1-Column Inward Step of Right-Half Window Determination (`rhCenter_inward_determine_step`)**:
    if `RhColAgree t Q (p0 + 1) (S + 1)` and `RhOrAgree t Q (p0 + 1) (S + 1)` hold, then `RhColAgree t Q p0 S` and `RhOrAgree t Q p0 S` hold! -/
theorem rhCenter_inward_determine_step (t Q p0 S : Nat)
    (hcol : RhColAgree t Q (p0 + 1) (S + 1))
    (hor : RhOrAgree t Q (p0 + 1) (S + 1)) :
    RhColAgree t Q p0 S ∧ RhOrAgree t Q p0 S := by
  have hcol0 : RhColAgree t Q p0 S := by
    intro s hs
    have h1 := hcol (s + 1) (by omega)
    have h_or := hor s (by omega)
    rw [show (p0 + 1) + 1 = p0 + 2 by omega] at h_or
    rw [rhCenter_inward_step ((t + s) + Q) p0,
      rhCenter_inward_step (t + s) p0,
      show ((t + s) + Q) + 1 = (t + (s + 1)) + Q by omega,
      show (t + s) + 1 = t + (s + 1) by omega,
      h1, h_or]
  refine ⟨hcol0, fun s hs => ?_⟩
  rw [hcol0 s (by omega), hcol s (by omega)]

/-- **Multi-Column Inward Right-Half Window Determination (`rhCenter_inward_determine`)**:
    in the driven right half `rhCenter`, if `RhColAgree t Q (p0 + K) (S + K)` and `RhOrAgree t Q (p0 + K) (S + K)` hold, then marching `K` columns inward toward column 0 determines `RhColAgree t Q p0 S` and `RhOrAgree t Q p0 S`! -/
theorem rhCenter_inward_determine (t Q p0 S K : Nat)
    (hcol : RhColAgree t Q (p0 + K) (S + K))
    (hor : RhOrAgree t Q (p0 + K) (S + K)) :
    RhColAgree t Q p0 S ∧ RhOrAgree t Q p0 S := by
  induction K generalizing p0 S with
  | zero =>
    simpa using And.intro hcol hor
  | succ K ih =>
    have hcol' : RhColAgree t Q ((p0 + 1) + K) ((S + 1) + K) := by
      intro s hs
      have := hcol s (by omega)
      rwa [show p0 + (K + 1) = (p0 + 1) + K by omega] at this
    have hor' : RhOrAgree t Q ((p0 + 1) + K) ((S + 1) + K) := by
      intro s hs
      have := hor s (by omega)
      rwa [show p0 + (K + 1) = (p0 + 1) + K by omega] at this
    obtain ⟨hc1, ho1⟩ := ih (p0 + 1) (S + 1) hcol' hor'
    exact rhCenter_inward_determine_step t Q p0 S hc1 ho1

/-- **Right-Half Spatial Band Agreement from Right-Boundary Column Trace (`rhBandAgree_of_inward_determine`)**:
    if `RhColAgree t Q (p0 + L) L` holds on `[t, t + L]` and `RhOrAgree t Q (p0 + L) L` holds on `[t, t + L)`, then `rhCenter_inward_determine` at `s = 0` proves `RhBandAgree t Q p0 L` across the entire spatial band `[p0, p0 + L]` at time `t`! -/
theorem rhBandAgree_of_inward_determine (t Q p0 L : Nat)
    (hcol : RhColAgree t Q (p0 + L) L)
    (hor : RhOrAgree t Q (p0 + L) L) :
    RhBandAgree t Q p0 L := by
  intro i hi
  have hcol_i : RhColAgree t Q ((p0 + i) + (L - i)) (i + (L - i)) := by
    intro s hs
    have := hcol s (by omega)
    rwa [show p0 + L = (p0 + i) + (L - i) by omega] at this
  have hor_i : RhOrAgree t Q ((p0 + i) + (L - i)) (i + (L - i)) := by
    intro s hs
    have := hor s (by omega)
    rwa [show p0 + L = (p0 + i) + (L - i) by omega] at this
  have hdet := (rhCenter_inward_determine t Q (p0 + i) i (L - i) hcol_i hor_i).1 0 (by omega)
  simpa using hdet

/-- **Unconditional Right-Edge `RhBandAgree` Outside the Light Cone (`rhBandAgree_outside_cone`)**:
    for `t + Q < p0`, `RhBandAgree t Q p0 L` holds unconditionally. -/
theorem rhBandAgree_outside_cone (t Q p0 L : Nat) (h : t + Q < p0) :
    RhBandAgree t Q p0 L := by
  intro i _
  rw [rhCenter_gt_eq_false (t + Q) (p0 + i) (by omega),
    rhCenter_gt_eq_false t (p0 + i) (by omega)]

/-- **`2^k`-Scale Forward Band Transport of `RhBandAgree` (`rhBandAgree_scale_step`)**:
    for `p0 + L + 2^(k+1) ≤ t`, if `RhBandAgree` holds on the three `2^k`-spaced bands `[p0, p0 + L]`, `[p0 + 2^k, p0 + 2^k + L]`, and `[p0 + 2^(k+1), p0 + 2^(k+1) + L]` at time `t`, and `WinWittAgree t k Q (t - (p0 + L)) L` holds at time `t`, then `rhCenter_scale_step` transports agreement forward by `2^k` steps to `RhBandAgree (t + 2^k) Q (p0 + 2^k) L`! -/
theorem rhBandAgree_scale_step (t k Q p0 L : Nat)
    (hp : p0 + L + twopow (k + 1) ≤ t)
    (h0 : RhBandAgree t Q p0 L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t - (p0 + L)) L) :
    RhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  intro i hi
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hsQ := rhCenter_scale_step (t + Q) k (p0 + i) (by omega)
  have hs0 := rhCenter_scale_step t k (p0 + i) (by omega)
  have hb0 := h0 i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw (L - i) (by omega)
  rw [show (t - (p0 + L)) + (L - i) + Q = (t + Q) - (p0 + i) by omega,
    show (t - (p0 + L)) + (L - i) = t - (p0 + i) by omega] at hwi
  rw [show ((t + twopow k) + Q) = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega,
    hsQ, hs0,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    hb0, hb1, hb2, hwi]

/-- **`2^k`-Scale Inward Band Transport of `RhBandAgree` (`rhBandAgree_scale_inward_step`)**:
    for `p0 + L + 2^(k+1) ≤ t`, if `RhBandAgree (t + 2^k) Q (p0 + 2^k) L` holds at time `t + 2^k`, `RhBandAgree` holds on `[p0 + 2^k, p0 + 2^k + L]` and `[p0 + 2^(k+1), p0 + 2^(k+1) + L]` at time `t`, and `WinWittAgree t k Q (t - (p0 + L)) L` holds at time `t`, then `rhCenter_scale_inward_step` transports agreement inward by `2^k` columns to `RhBandAgree t Q p0 L`! -/
theorem rhBandAgree_scale_inward_step (t k Q p0 L : Nat)
    (hp : p0 + L + twopow (k + 1) ≤ t)
    (hlate : RhBandAgree (t + twopow k) Q (p0 + twopow k) L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hw : WinWittAgree t k Q (t - (p0 + L)) L) :
    RhBandAgree t Q p0 L := by
  intro i hi
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hsQ := rhCenter_scale_inward_step (t + Q) k (p0 + i) (by omega)
  have hs0 := rhCenter_scale_inward_step t k (p0 + i) (by omega)
  have hbl := hlate i hi
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  have hwi := hw (L - i) (by omega)
  rw [show (t - (p0 + L)) + (L - i) + Q = (t + Q) - (p0 + i) by omega,
    show (t - (p0 + L)) + (L - i) = t - (p0 + i) by omega] at hwi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    show (p0 + twopow k) + i = (p0 + i) + twopow k by omega] at hbl
  rw [hsQ, hs0, hbl,
    show (p0 + i) + twopow k = (p0 + twopow k) + i by omega,
    show (p0 + i) + twopow (k + 1) = (p0 + twopow (k + 1)) + i by omega,
    hb1, hb2, hwi]

/-- **`WinWittAgree` from `RhBandAgree` on Three `2^k`-Bands and Late Band (`winWittAgree_of_rhBandAgree_scale`)**:
    for `p0 + L + 2^(k+1) ≤ t`, if `RhBandAgree` holds on `[p0, p0 + L]`, `[p0 + 2^k, p0 + 2^k + L]`, and `[p0 + 2^(k+1), p0 + 2^(k+1) + L]` at time `t` and `RhBandAgree (t + 2^k) Q (p0 + 2^k) L` holds at time `t + 2^k`, then `WinWittAgree t k Q (t - (p0 + L)) L` holds at time `t`! -/
theorem winWittAgree_of_rhBandAgree_scale (t k Q p0 L : Nat)
    (hp : p0 + L + twopow (k + 1) ≤ t)
    (h0 : RhBandAgree t Q p0 L)
    (h1 : RhBandAgree t Q (p0 + twopow k) L)
    (h2 : RhBandAgree t Q (p0 + twopow (k + 1)) L)
    (hlate : RhBandAgree (t + twopow k) Q (p0 + twopow k) L) :
    WinWittAgree t k Q (t - (p0 + L)) L := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hr0 : RowAgree t Q ((t - (p0 + L)) - twopow (k + 1)) L := by
    have := rowAgree_right_of_rhBandAgree t Q (p0 + twopow (k + 1)) L (by omega) h2
    rwa [show t - ((p0 + twopow (k + 1)) + L) = (t - (p0 + L)) - twopow (k + 1) by omega] at this
  have hr1 : RowAgree t Q ((t - (p0 + L)) - twopow k) L := by
    have := rowAgree_right_of_rhBandAgree t Q (p0 + twopow k) L (by omega) h1
    rwa [show t - ((p0 + twopow k) + L) = (t - (p0 + L)) - twopow k by omega] at this
  have hr2 : RowAgree t Q (t - (p0 + L)) L :=
    rowAgree_right_of_rhBandAgree t Q p0 L (by omega) h0
  have hrl : RowAgree (t + twopow k) Q (t - (p0 + L)) L := by
    have := rowAgree_right_of_rhBandAgree (t + twopow k) Q (p0 + twopow k) L (by omega) hlate
    rwa [show (t + twopow k) - ((p0 + twopow k) + L) = t - (p0 + L) by omega] at this
  exact winWittAgree_of_rowAgree_three_and_late t k Q (t - (p0 + L)) L
    (by omega) hr0 hr1 hr2 hrl

/-- **Establishing `SectorRhBandAgree` from Right-Half Window Determination at Sector Times (`sectorRhBandAgree_of_inward_determine`)**:
    if at every sector time `t_u = (d + u * 2^k) + 1` (`u ≥ U`), `RhColAgree t_u Q (2^k + 1) (2^k + 1)` and `RhOrAgree t_u Q (2^k + 1) (2^k + 1)` hold, then `SectorRhBandAgree k d U Q` holds! -/
theorem sectorRhBandAgree_of_inward_determine (k d U Q : Nat)
    (hcol : ∀ u, U ≤ u → RhColAgree ((d + u * twopow k) + 1) Q (twopow k + 1) (twopow k + 1))
    (hor : ∀ u, U ≤ u → RhOrAgree ((d + u * twopow k) + 1) Q (twopow k + 1) (twopow k + 1)) :
    SectorRhBandAgree k d U Q := by
  intro u hu
  have hcol_u : RhColAgree ((d + u * twopow k) + 1) Q (0 + (twopow k + 1)) (twopow k + 1) := by
    simpa using hcol u hu
  have hor_u : RhOrAgree ((d + u * twopow k) + 1) Q (0 + (twopow k + 1)) (twopow k + 1) := by
    simpa using hor u hu
  exact rhBandAgree_of_inward_determine ((d + u * twopow k) + 1) Q 0 (twopow k + 1) hcol_u hor_u

/-- **Refutation of Right-Half Window Agreement at Column `2^k + 1` for `Q = lcm(P, 2^k)` (`not_sector_inward_determine_lcmPeriod`)**:
    under `CenterPeriodic T P` (`0 < P`), for `1 ≤ U`, `1 ≤ d`, and `T ≤ d + U * 2^k`, if `RhColAgree ((d + u * 2^k) + 1) (lcmPeriod P k) (2^k + 1) (2^k + 1)` holds for all `u ≥ U`, then it is impossible that `RhOrAgree ((d + u * 2^k) + 1) (lcmPeriod P k) (2^k + 1) (2^k + 1)` holds for all `u ≥ U`! -/
theorem not_sector_inward_determine_lcmPeriod
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * twopow k)
    (hcol : ∀ u, U ≤ u → RhColAgree ((d + u * twopow k) + 1) (lcmPeriod P k) (twopow k + 1) (twopow k + 1))
    (hor : ∀ u, U ≤ u → RhOrAgree ((d + u * twopow k) + 1) (lcmPeriod P k) (twopow k + 1) (twopow k + 1)) :
    False := by
  have hsec := sectorRhBandAgree_of_inward_determine k d U (lcmPeriod P k) hcol hor
  exact not_sector_rhBandAgree_lcmPeriod T P hP hper k d U hU hd ht hsec

theorem not_sector_inward_determine_lcmPeriod_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (k d U : Nat) (hU : 1 ≤ U) (hd : 1 ≤ d) (ht : T ≤ d + U * twopow k)
    (hcol : ∀ u, U ≤ u → RhColAgree ((d + u * twopow k) + 1) (lcmPeriod P k) (twopow k + 1) (twopow k + 1)) :
    ¬ (∀ u, U ≤ u → RhOrAgree ((d + u * twopow k) + 1) (lcmPeriod P k) (twopow k + 1) (twopow k + 1)) := by
  intro hor
  exact not_sector_inward_determine_lcmPeriod T P hP hper k d U hU hd ht hcol hor

end Rule30UOR.Interfaces
