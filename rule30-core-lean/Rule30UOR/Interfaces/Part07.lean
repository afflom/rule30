module

public import Rule30UOR.Interfaces.Part06

/-!
# `Rule30UOR.Interfaces`, part 7

* Batch 12: Sector-1 Same-Column `$2^k$`-Scale Left-Half Calculus, Vanishing Frobenius Defect, and Linearized Periodic Window Defect Law
* Batch 13: Same-Column `$2^k$`-Scale Right-Half Calculus, Inter-Cone Right Readout, and Symmetric Doubling of `RhBandAgree` & `WinWittAgree`
* Batch 14: Universal Inter-Cone & Sector-1 `frobDefect` Vanishing, Right-Half Window Step, and `Φ`-Coupled Sector-1 Window Defect Laws
* Batch 15: Universal Sideways (Left-Permutive) Inversion of `winWitt`, Unconditional Zero-Gap Window Propagation, and Multi-Step Sector-1 Window Calculus
* Batch 16: Raw Inter-Cone Pure-`Φ` Window Evolution, Non-Overlapping 3-Sector Copy Laws of `phiScale`, and Early-Free Cross-Sector Window Duality
* Batch 17: Scale-Independent Left-Diagonal Coordinates at `t + 2^k`, Zero-State Center Cross-Sector Readout, and Zero-Diagonal Window Mirrors
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

/-! ### Batch 12: Sector-1 Same-Column `$2^k$`-Scale Left-Half Calculus, Vanishing Frobenius Defect, and Linearized Periodic Window Defect Law -/

/-- **Single-Term Collapse of `phiScale k (row t)` in Sector 1 (`phiScale_row_testBit_lhCenter_sector_one`)**:
    for all `t, k, p : Nat` with `t + p < 2^k` (including `p = 0`, the center column!), bit `t + p + 2^k` lies strictly below `2^(k+1)` while `(row t).testBit (t + p + 2^k) = lhCenter t (p + 2^k) = false`, so `(phiScale k (row t)).testBit (t + p + 2^k) = lhCenter t p`! -/
theorem phiScale_row_testBit_lhCenter_sector_one (t k p : Nat)
    (hp : t + p < twopow k) :
    (phiScale k (row t)).testBit (t + p + twopow k) = lhCenter t p := by
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
    ((row t) <<< (twopow k + twopow k))).testBit (t + p + twopow k) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (t + p + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (t + p + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
    show t + p + twopow k - twopow k = t + p by omega,
    show t + p + twopow k = t + (p + twopow k) by omega,
    ← lhCenter_eq_row_testBit_uncond t (p + twopow k),
    ← lhCenter_eq_row_testBit_uncond t p,
    lhCenter_gt_eq_false t (p + twopow k) (by omega),
    Bool.false_xor]

theorem phiScale_row_testBit_lhCenter_sector_one_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    wittBitBool (phiScale k (row t)) (t + p + twopow k) = lhCenter t p :=
  phiScale_row_testBit_lhCenter_sector_one t k p hp

/-- **Same-Column `$2^k$`-Scale Step of `lhCenter` Inside the `$2^k$`-Horizon (`lhCenter_scale_same_col_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k`, at the SAME spatial column `p` in the left half, `lhCenter (t + 2^k) p = lhCenter t p ⊕ (winWitt t (2^k)).testBit (t + p + 2^k)`! -/
theorem lhCenter_scale_same_col_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    lhCenter (t + twopow k) p =
      bxor (lhCenter t p)
        ((winWitt t (twopow k)).testBit (t + p + twopow k)) := by
  rw [lhCenter_eq_row_testBit_uncond (t + twopow k) p,
    show (t + twopow k) + p = t + p + twopow k by omega]
  have hsc := congrArg (fun n => n.testBit (t + p + twopow k)) (row_scale t k)
  rw [Nat.testBit_xor, phiScale_row_testBit_lhCenter_sector_one t k p hp] at hsc
  rw [hsc, bxor_eq_xor]

theorem lhCenter_scale_same_col_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    lhCenter (t + twopow k) p =
      bxor (lhCenter t p)
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow k)) :=
  lhCenter_scale_same_col_cone t k p hp

/-- **Same-Column `$2^k$`-Scale Pullback of `lhCenter` Inside the `$2^k$`-Horizon (`lhCenter_scale_inward_same_col_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k`, `lhCenter t p = lhCenter (t + 2^k) p ⊕ (winWitt t (2^k)).testBit (t + p + 2^k)`! -/
theorem lhCenter_scale_inward_same_col_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    lhCenter t p =
      bxor (lhCenter (t + twopow k) p)
        ((winWitt t (twopow k)).testBit (t + p + twopow k)) := by
  rw [lhCenter_scale_same_col_cone t k p hp]
  cases lhCenter t p <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow k) <;> rfl

theorem lhCenter_scale_inward_same_col_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    lhCenter t p =
      bxor (lhCenter (t + twopow k) p)
        (wittBitBool (winWitt t (twopow k)) (t + p + twopow k)) :=
  lhCenter_scale_inward_same_col_cone t k p hp

/-- **Exact Readout of Sector-1 `winWitt` as the Same-Column `$2^k$`-Time Jump of `lhCenter` (`winWitt_testBit_sector_one_lhCenter`)**:
    for all `t, k, p : Nat` with `t + p < 2^k`, `(winWitt t (2^k)).testBit (t + p + 2^k) = lhCenter (t + 2^k) p ⊕ lhCenter t p`! -/
theorem winWitt_testBit_sector_one_lhCenter (t k p : Nat)
    (hp : t + p < twopow k) :
    (winWitt t (twopow k)).testBit (t + p + twopow k) =
      bxor (lhCenter (t + twopow k) p) (lhCenter t p) := by
  rw [lhCenter_scale_same_col_cone t k p hp]
  cases lhCenter t p <;>
    cases (winWitt t (twopow k)).testBit (t + p + twopow k) <;> rfl

theorem winWitt_testBit_sector_one_lhCenter_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow k) =
      bxor (lhCenter (t + twopow k) p) (lhCenter t p) :=
  winWitt_testBit_sector_one_lhCenter t k p hp

/-- **Same-Column `$2^k$`-Scale Forward Step of `LhBandAgree` (`lhBandAgree_scale_same_col_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k`, `LhBandAgree t Q p0 L` and `WinWittAgree t k Q (t + p0 + 2^k) L` imply `LhBandAgree (t + 2^k) Q p0 L` at the SAME column `p0`! -/
theorem lhBandAgree_scale_same_col_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (h0 : LhBandAgree t Q p0 L)
    (hw : WinWittAgree t k Q (t + p0 + twopow k) L) :
    LhBandAgree (t + twopow k) Q p0 L := by
  intro i hi
  have hsQ := lhCenter_scale_same_col_cone (t + Q) k (p0 + i) (by omega)
  have hs0 := lhCenter_scale_same_col_cone t k (p0 + i) (by omega)
  have hb0 := h0 i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    hsQ, hs0, hb0,
    show (t + Q) + (p0 + i) + twopow k = (t + p0 + twopow k) + i + Q by omega,
    show t + (p0 + i) + twopow k = (t + p0 + twopow k) + i by omega,
    hwi]

/-- **Same-Column `$2^k$`-Scale Pullback of `LhBandAgree` (`lhBandAgree_scale_inward_same_col_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k`, `LhBandAgree (t + 2^k) Q p0 L` and `WinWittAgree t k Q (t + p0 + 2^k) L` imply `LhBandAgree t Q p0 L` at the SAME column `p0`! -/
theorem lhBandAgree_scale_inward_same_col_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q p0 L)
    (hw : WinWittAgree t k Q (t + p0 + twopow k) L) :
    LhBandAgree t Q p0 L := by
  intro i hi
  have hsQ := lhCenter_scale_inward_same_col_cone (t + Q) k (p0 + i) (by omega)
  have hs0 := lhCenter_scale_inward_same_col_cone t k (p0 + i) (by omega)
  have hbl := hlate i hi
  have hwi := hw i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hbl
  rw [hsQ, hs0, hbl,
    show (t + Q) + (p0 + i) + twopow k = (t + p0 + twopow k) + i + Q by omega,
    show t + (p0 + i) + twopow k = (t + p0 + twopow k) + i by omega,
    hwi]

/-- **Deriving Sector-1 `WinWittAgree` from Same-Column `LhBandAgree` at `t + 2^k` and `t` (`winWittAgree_sector_one_lhCenter`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k`, `LhBandAgree (t + 2^k) Q p0 L` and `LhBandAgree t Q p0 L` imply `WinWittAgree t k Q (t + p0 + 2^k) L`! -/
theorem winWittAgree_sector_one_lhCenter (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q p0 L)
    (h0 : LhBandAgree t Q p0 L) :
    WinWittAgree t k Q (t + p0 + twopow k) L := by
  intro i hi
  have hsQ := winWitt_testBit_sector_one_lhCenter (t + Q) k (p0 + i) (by omega)
  have hs0 := winWitt_testBit_sector_one_lhCenter t k (p0 + i) (by omega)
  have hbl := hlate i hi
  have hb0 := h0 i hi
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hbl
  rw [show (t + p0 + twopow k) + i + Q = (t + Q) + (p0 + i) + twopow k by omega,
    show (t + p0 + twopow k) + i = t + (p0 + i) + twopow k by omega,
    hsQ, hs0, hbl, hb0]

/-- **Refutation of Simultaneous Late Same-Column `LhBandAgree` and Sector-1 `WinWittAgree` (`not_lhBandAgree_late_and_winWittAgree_sector_one`)**:
    for all `t, k, Q, L : Nat` with `0 < Q`, `t + Q ≤ L`, and `t + Q + L < 2^k`, `LhBandAgree (t + 2^k) Q 0 L` (even though `L < 2^k` lies strictly inside the late light cone at `t + 2^k`!) and `WinWittAgree t k Q (t + 2^k) L` cannot both hold, because pulling back to time `t` reaches the left edge of the early light cone at `t + Q`! -/
theorem not_lhBandAgree_late_and_winWittAgree_sector_one (t k Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) (htk : t + Q + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q 0 L)
    (hw : WinWittAgree t k Q (t + twopow k) L) : False := by
  have hw0 : WinWittAgree t k Q (t + 0 + twopow k) L := by
    rwa [Nat.add_zero]
  have h0 := lhBandAgree_scale_inward_same_col_cone t k Q 0 L (by omega) hlate hw0
  exact not_lhBandAgree_of_lt_add t Q L hQ hL h0

/-- **Identical Vanishing of Sector-1 `frobDefect k (row t)` Across the Left Half (`frobDefect_row_testBit_lhCenter_sector_one_eq_false`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k` (including `p = 0`, the center column, for all `t + 1 < 2^k`!), both `rdiag ((t + p + 1) + 2^k) t` and `rdiag (t + p + 2^k) t` lie outside the light cone `2 * t` and vanish, so `(frobDefect k (row t)).testBit ((t + p + 1) + 2^k) = false`! -/
theorem frobDefect_row_testBit_lhCenter_sector_one_eq_false (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (frobDefect k (row t)).testBit ((t + p + 1) + twopow k) = false := by
  rw [frobDefect_row_testBit_sector_one t k (t + p) hp,
    show (t + p + 1) + twopow k = t + (p + 1 + twopow k) by omega,
    show (t + p) + twopow k = t + (p + twopow k) by omega,
    rdiag_add_eq_lhCenter_uncond t (p + 1 + twopow k),
    rdiag_add_eq_lhCenter_uncond t (p + twopow k),
    lhCenter_gt_eq_false t (p + 1 + twopow k) (by omega),
    lhCenter_gt_eq_false t (p + twopow k) (by omega),
    Bool.false_and, Bool.and_false]
  rfl

theorem frobDefect_row_testBit_lhCenter_sector_one_eq_false_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (frobDefect k (row t)) ((t + p + 1) + twopow k) = false :=
  frobDefect_row_testBit_lhCenter_sector_one_eq_false t k p hp

/-- **Single-Sector Collapse of Sector-1 `crossCarry` Across the Left Half (`crossCarry_row_scale_lhCenter_sector_one`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k`, `(crossCarry (phiScale k (row t)) (winWitt t (2^k))).testBit ((t + p + 1) + 2^k)` depends ONLY on `lhCenter t p`, `lhCenter t (p + 1)`, and Sector 1 of `winWitt t (2^k)`! -/
theorem crossCarry_row_scale_lhCenter_sector_one (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit
        ((t + p + 1) + twopow k) =
      bxor
        (lhCenter t (p + 1) &&
          (winWitt t (twopow k)).testBit (t + p + twopow k))
        ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) &&
          lhCenter t p) := by
  have hc := crossCarry_testBit_succ (phiScale k (row t)) (winWitt t (twopow k)) (t + p + twopow k)
  rw [show (t + p + twopow k) + 1 = (t + p + 1) + twopow k by omega] at hc
  rw [hc,
    show (t + p + 1) + twopow k = t + (p + 1) + twopow k by omega,
    phiScale_row_testBit_lhCenter_sector_one t k (p + 1) (by omega),
    phiScale_row_testBit_lhCenter_sector_one t k p (by omega)]

theorem crossCarry_row_scale_lhCenter_sector_one_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k)))
        ((t + p + 1) + twopow k) =
      bxor
        (lhCenter t (p + 1) &&
          wittBitBool (winWitt t (twopow k)) (t + p + twopow k))
        (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow k) &&
          lhCenter t p) :=
  crossCarry_row_scale_lhCenter_sector_one t k p hp

/-- **Single-Sector Window Step of Sector-1 `winWitt` Across the Left Half (`winWitt_step_sector_one_lhCenter`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k`, because `frobDefect = false` (`9.480`) and `phiScale k (row t) = lhCenter t p` (`9.472`), the universal window step `winWitt_step_frobDefect_testBit_succ` in Sector 1 collapses to a single-sector recurrence driven ONLY by `lhCenter t p`, `lhCenter t (p + 1)`, and `winWitt t (2^k)`! -/
theorem winWitt_step_sector_one_lhCenter (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p + 1) + twopow k) =
      bxor
        ((phi (winWitt t (twopow k))).testBit ((t + 1) + (p + 1) + twopow k))
        (bxor
          (lhCenter t (p + 1) &&
            (winWitt t (twopow k)).testBit (t + p + twopow k))
          ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) &&
            lhCenter t p)) := by
  have hs := winWitt_step_frobDefect_testBit_succ t k ((t + p + 1) + twopow k)
  rw [show ((t + p + 1) + twopow k) + 1 = (t + 1) + (p + 1) + twopow k by omega,
    crossCarry_row_scale_lhCenter_sector_one t k p hp,
    frobDefect_row_testBit_lhCenter_sector_one_eq_false t k p hp] at hs
  rw [hs]
  cases (phi (winWitt t (twopow k))).testBit ((t + 1) + (p + 1) + twopow k) <;>
    cases (bxor
      (lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow k))
      ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) && lhCenter t p)) <;> rfl

theorem winWitt_step_sector_one_lhCenter_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + (p + 1) + twopow k) =
      bxor
        (wittBitBool (phi (winWitt t (twopow k))) ((t + 1) + (p + 1) + twopow k))
        (bxor
          (lhCenter t (p + 1) &&
            wittBitBool (winWitt t (twopow k)) (t + p + twopow k))
          (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow k) &&
            lhCenter t p)) :=
  winWitt_step_sector_one_lhCenter t k p hp

/-- **Single-Sector Forward Step of Sector-1 `WinWittAgree` (`winWittAgree_step_sector_one_lhCenter`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L + 1 < 2^k`, `WinWittAgree` in Sector 1 steps forward from time `t` to `t + 1` using ONLY the single inner band `LhBandAgree t Q p0 (L + 1)`! -/
theorem winWittAgree_step_sector_one_lhCenter (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hb : LhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q (t + p0 + twopow k) (L + 2)) :
    WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow k) L := by
  intro i hi
  have hsQ := winWitt_step_sector_one_lhCenter (t + Q) k (p0 + i) (by omega)
  have hs0 := winWitt_step_sector_one_lhCenter t k (p0 + i) (by omega)
  have hb0 := hb i (by omega)
  have hb1 := hb (i + 1) (by omega)
  have hw0 := hw i (by omega)
  have hw1 := hw (i + 1) (by omega)
  have hw2 := hw (i + 2) (by omega)
  rw [show p0 + (i + 1) = (p0 + i) + 1 by omega] at hb1
  rw [show (t + p0 + twopow k) + i + Q = (t + Q) + (p0 + i) + twopow k by omega,
    show (t + p0 + twopow k) + i = t + (p0 + i) + twopow k by omega] at hw0
  rw [show (t + p0 + twopow k) + (i + 1) + Q = (t + Q) + ((p0 + i) + 1) + twopow k by omega,
    show (t + p0 + twopow k) + (i + 1) = t + ((p0 + i) + 1) + twopow k by omega] at hw1
  rw [show (t + p0 + twopow k) + (i + 2) + Q = ((t + Q) + (p0 + i) + twopow k) + 2 by omega,
    show (t + p0 + twopow k) + (i + 2) = (t + (p0 + i) + twopow k) + 2 by omega] at hw2
  have hphiQ : (phi (winWitt (t + Q) (twopow k))).testBit (((t + Q) + 1) + ((p0 + i) + 1) + twopow k) =
      bxor ((winWitt (t + Q) (twopow k)).testBit (((t + Q) + (p0 + i) + twopow k) + 2))
        ((winWitt (t + Q) (twopow k)).testBit ((t + Q) + ((p0 + i) + 1) + twopow k) ||
          (winWitt (t + Q) (twopow k)).testBit ((t + Q) + (p0 + i) + twopow k)) := by
    have hp0 := phi_testBit_add_two (winWitt (t + Q) (twopow k)) ((t + Q) + (p0 + i) + twopow k)
    rw [show (((t + Q) + 1) + ((p0 + i) + 1) + twopow k) =
        ((t + Q) + (p0 + i) + twopow k) + 2 by omega,
      hp0,
      show ((t + Q) + (p0 + i) + twopow k) + 1 = (t + Q) + ((p0 + i) + 1) + twopow k by omega,
      bxor_eq_xor]
  have hphi0 : (phi (winWitt t (twopow k))).testBit ((t + 1) + ((p0 + i) + 1) + twopow k) =
      bxor ((winWitt t (twopow k)).testBit ((t + (p0 + i) + twopow k) + 2))
        ((winWitt t (twopow k)).testBit (t + ((p0 + i) + 1) + twopow k) ||
          (winWitt t (twopow k)).testBit (t + (p0 + i) + twopow k)) := by
    have hp0 := phi_testBit_add_two (winWitt t (twopow k)) (t + (p0 + i) + twopow k)
    rw [show ((t + 1) + ((p0 + i) + 1) + twopow k) =
        (t + (p0 + i) + twopow k) + 2 by omega,
      hp0,
      show (t + (p0 + i) + twopow k) + 1 = t + ((p0 + i) + 1) + twopow k by omega,
      bxor_eq_xor]
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show ((t + 1) + (p0 + 1) + twopow k) + i + Q =
      ((t + Q) + 1) + ((p0 + i) + 1) + twopow k by omega,
    show ((t + 1) + (p0 + 1) + twopow k) + i =
      (t + 1) + ((p0 + i) + 1) + twopow k by omega,
    hsQ, hs0, hphiQ, hphi0, hb0, hb1, hw0, hw1, hw2]

/-- **Single-Sector Outward Step of Sector-1 `WinWittAgree` (`winWittAgree_outward_step_sector_one_lhCenter`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L + 1 < 2^k`, `LhBandAgree t Q p0 (L + 1)`, `WinWittAgree t k Q (t + p0 + 2^k) (L + 1)`, and `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^k) L` extend `WinWittAgree` at time `t` to width `L + 2`! -/
theorem winWittAgree_outward_step_sector_one_lhCenter (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hb : LhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q (t + p0 + twopow k) (L + 1))
    (hnext : WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow k) L) :
    WinWittAgree t k Q (t + p0 + twopow k) (L + 2) := by
  intro i hi
  by_cases hi1 : i ≤ L + 1
  · exact hw i hi1
  · have hi_eq : i = L + 2 := by omega
    subst hi_eq
    have hsQ := winWitt_step_sector_one_lhCenter (t + Q) k (p0 + L) (by omega)
    have hs0 := winWitt_step_sector_one_lhCenter t k (p0 + L) (by omega)
    have hb0 := hb L (by omega)
    have hb1 := hb (L + 1) (by omega)
    have hw0 := hw L (by omega)
    have hw1 := hw (L + 1) (by omega)
    have hwn := hnext L (Nat.le_refl L)
    rw [show p0 + (L + 1) = (p0 + L) + 1 by omega] at hb1
    rw [show (t + p0 + twopow k) + L + Q = (t + Q) + (p0 + L) + twopow k by omega,
      show (t + p0 + twopow k) + L = t + (p0 + L) + twopow k by omega] at hw0
    rw [show (t + p0 + twopow k) + (L + 1) + Q = (t + Q) + ((p0 + L) + 1) + twopow k by omega,
      show (t + p0 + twopow k) + (L + 1) = t + ((p0 + L) + 1) + twopow k by omega] at hw1
    rw [show (t + 1) + Q = (t + Q) + 1 by omega,
      show ((t + 1) + (p0 + 1) + twopow k) + L + Q =
        ((t + Q) + 1) + ((p0 + L) + 1) + twopow k by omega,
      show ((t + 1) + (p0 + 1) + twopow k) + L =
        (t + 1) + ((p0 + L) + 1) + twopow k by omega] at hwn
    have hphiQ : (phi (winWitt (t + Q) (twopow k))).testBit (((t + Q) + 1) + ((p0 + L) + 1) + twopow k) =
        bxor ((winWitt (t + Q) (twopow k)).testBit ((t + Q) + ((p0 + L) + 2) + twopow k))
          ((winWitt (t + Q) (twopow k)).testBit ((t + Q) + ((p0 + L) + 1) + twopow k) ||
            (winWitt (t + Q) (twopow k)).testBit ((t + Q) + (p0 + L) + twopow k)) := by
      have hp0 := phi_testBit_add_two (winWitt (t + Q) (twopow k)) ((t + Q) + (p0 + L) + twopow k)
      rw [show (((t + Q) + 1) + ((p0 + L) + 1) + twopow k) =
          ((t + Q) + (p0 + L) + twopow k) + 2 by omega,
        hp0,
        show ((t + Q) + (p0 + L) + twopow k) + 2 = (t + Q) + ((p0 + L) + 2) + twopow k by omega,
        show ((t + Q) + (p0 + L) + twopow k) + 1 = (t + Q) + ((p0 + L) + 1) + twopow k by omega,
        bxor_eq_xor]
    have hphi0 : (phi (winWitt t (twopow k))).testBit ((t + 1) + ((p0 + L) + 1) + twopow k) =
        bxor ((winWitt t (twopow k)).testBit (t + ((p0 + L) + 2) + twopow k))
          ((winWitt t (twopow k)).testBit (t + ((p0 + L) + 1) + twopow k) ||
            (winWitt t (twopow k)).testBit (t + (p0 + L) + twopow k)) := by
      have hp0 := phi_testBit_add_two (winWitt t (twopow k)) (t + (p0 + L) + twopow k)
      rw [show ((t + 1) + ((p0 + L) + 1) + twopow k) =
          (t + (p0 + L) + twopow k) + 2 by omega,
        hp0,
        show (t + (p0 + L) + twopow k) + 2 = t + ((p0 + L) + 2) + twopow k by omega,
        show (t + (p0 + L) + twopow k) + 1 = t + ((p0 + L) + 1) + twopow k by omega,
        bxor_eq_xor]
    rw [hsQ, hs0, hphiQ, hphi0, hb0, hb1, hw0, hw1] at hwn
    rw [show (t + p0 + twopow k) + (L + 2) + Q = (t + Q) + ((p0 + L) + 2) + twopow k by omega,
      show (t + p0 + twopow k) + (L + 2) = t + ((p0 + L) + 2) + twopow k by omega]
    revert hwn
    simp only [bxor_eq_xor]
    cases (winWitt (t + Q) (twopow k)).testBit ((t + Q) + ((p0 + L) + 2) + twopow k) <;>
      cases (winWitt t (twopow k)).testBit (t + ((p0 + L) + 2) + twopow k) <;>
      cases ((winWitt t (twopow k)).testBit (t + ((p0 + L) + 1) + twopow k) ||
        (winWitt t (twopow k)).testBit (t + (p0 + L) + twopow k)) <;>
      cases ((lhCenter t ((p0 + L) + 1) && (winWitt t (twopow k)).testBit (t + (p0 + L) + twopow k)) ^^
        ((winWitt t (twopow k)).testBit (t + ((p0 + L) + 1) + twopow k) && lhCenter t (p0 + L))) <;> decide

/-- **Automatic `$m * P$`-Invariance of the Sector-1 Center-Slot Window Bit Inside the `$2^k$`-Horizon (`periodic_winWitt_sector_one_zero_eq`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P < 2^k`, `(winWitt · (2^k)).testBit (· + 2^k)` equals `center (· + 2^k) ⊕ center ·` by `winWitt_testBit_sector_one_lhCenter` at `p = 0`, and therefore is automatically `m * P`-invariant! -/
theorem periodic_winWitt_sector_one_zero_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < twopow k) :
    (winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + twopow k) =
      (winWitt t (twopow k)).testBit (t + twopow k) := by
  have hQ := winWitt_testBit_sector_one_lhCenter (t + m * P) k 0 (by omega)
  have h0 := winWitt_testBit_sector_one_lhCenter t k 0 (by omega)
  rw [Nat.add_zero] at hQ h0
  have hc0 : lhCenter (t + m * P) 0 = lhCenter t 0 := by
    have hcol := periodic_lhColAgree_zero T P hP hper m t 0 ht 0 (Nat.le_refl 0)
    simpa using hcol
  have hcl : lhCenter ((t + m * P) + twopow k) 0 = lhCenter (t + twopow k) 0 := by
    have hcol := periodic_lhColAgree_zero T P hP hper m (t + twopow k) 0 (by omega) 0 (Nat.le_refl 0)
    rw [show (t + m * P) + twopow k = (t + twopow k) + m * P by omega]
    simpa using hcol
  rw [hQ, h0, hcl, hc0]

theorem periodic_winWitt_sector_one_zero_eq_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P < twopow k) :
    wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + twopow k) =
      wittBitBool (winWitt t (twopow k)) (t + twopow k) :=
  periodic_winWitt_sector_one_zero_eq T P hP hper m t k ht htk

/-- **Exact Linear Discrete Time-Derivative Law for the Sector-1 Column-`-2` Window Defect (`periodic_winWitt_sector_one_two_defect_eq`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P + 2 < 2^k`, combining `winWitt_testBit_sector_one_lhCenter` at `p = 1, 2` with `periodic_lhCenter_two_defect_eq` at `t` and `t + 2^k` proves that the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 2 + 2^k)` is the exact linear discrete time-derivative of the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 1 + 2^k)`! -/
theorem periodic_winWitt_sector_one_two_defect_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 2 < twopow k) :
    bxor
      ((winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 2 + twopow k))
      ((winWitt t (twopow k)).testBit (t + 2 + twopow k)) =
      bxor
        (bxor
          ((winWitt ((t + 1) + m * P) (twopow k)).testBit (((t + 1) + m * P) + 1 + twopow k))
          ((winWitt (t + 1) (twopow k)).testBit ((t + 1) + 1 + twopow k)))
        (bxor
          ((winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 1 + twopow k))
          ((winWitt t (twopow k)).testBit (t + 1 + twopow k))) := by
  have hw2Q := winWitt_testBit_sector_one_lhCenter (t + m * P) k 2 (by omega)
  have hw20 := winWitt_testBit_sector_one_lhCenter t k 2 (by omega)
  have hw1nQ := winWitt_testBit_sector_one_lhCenter ((t + 1) + m * P) k 1 (by omega)
  have hw1n0 := winWitt_testBit_sector_one_lhCenter (t + 1) k 1 (by omega)
  have hw1Q := winWitt_testBit_sector_one_lhCenter (t + m * P) k 1 (by omega)
  have hw10 := winWitt_testBit_sector_one_lhCenter t k 1 (by omega)
  have hd0 := periodic_lhCenter_two_defect_eq T P hP hper m t ht
  have hdl := periodic_lhCenter_two_defect_eq T P hP hper m (t + twopow k) (by omega)
  rw [show (t + m * P) + twopow k = (t + twopow k) + m * P by omega] at hw2Q hw1Q
  rw [show ((t + 1) + m * P) + twopow k = ((t + twopow k) + 1) + m * P by omega] at hw1nQ
  rw [show (t + 1) + twopow k = (t + twopow k) + 1 by omega] at hw1n0
  rw [hw2Q, hw20, hw1nQ, hw1n0, hw1Q, hw10]
  have hrearrange :
      bxor
        (bxor (lhCenter ((t + twopow k) + m * P) 2) (lhCenter (t + m * P) 2))
        (bxor (lhCenter (t + twopow k) 2) (lhCenter t 2)) =
      bxor
        (bxor (lhCenter ((t + twopow k) + m * P) 2) (lhCenter (t + twopow k) 2))
        (bxor (lhCenter (t + m * P) 2) (lhCenter t 2)) := by
    cases lhCenter ((t + twopow k) + m * P) 2 <;>
      cases lhCenter (t + m * P) 2 <;>
      cases lhCenter (t + twopow k) 2 <;>
      cases lhCenter t 2 <;> rfl
  rw [hrearrange, hdl, hd0]
  cases lhCenter (((t + twopow k) + 1) + m * P) 1 <;>
    cases lhCenter ((t + twopow k) + 1) 1 <;>
    cases lhCenter ((t + twopow k) + m * P) 1 <;>
    cases lhCenter (t + twopow k) 1 <;>
    cases lhCenter ((t + 1) + m * P) 1 <;>
    cases lhCenter (t + 1) 1 <;>
    cases lhCenter (t + m * P) 1 <;>
    cases lhCenter t 1 <;> rfl

theorem periodic_winWitt_sector_one_two_defect_eq_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 2 < twopow k) :
    bxor
      (wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + 2 + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + 2 + twopow k)) =
      bxor
        (bxor
          (wittBitBool (winWitt ((t + 1) + m * P) (twopow k)) (((t + 1) + m * P) + 1 + twopow k))
          (wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + 1 + twopow k)))
        (bxor
          (wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + 1 + twopow k))
          (wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k))) :=
  periodic_winWitt_sector_one_two_defect_eq T P hP hper m t k ht htk

/-! ### Batch 13: Same-Column `$2^k$`-Scale Right-Half Calculus, Inter-Cone Right Readout, and Symmetric Doubling of `RhBandAgree` & `WinWittAgree` -/

/-- **Finite-Horizon Right-Light-Cone Refutation of `RhBandAgree` (`not_rhBandAgree_of_lt_add`)**:
    for all `t, Q, L : Nat` with `0 < Q` and `t + Q ≤ L`, `RhBandAgree t Q 0 L` is impossible because `rhCenter (t + Q) (t + Q) = true` at the right light-cone edge of `t + Q` while `rhCenter t (t + Q) = false` outside the light cone of `t`! -/
theorem not_rhBandAgree_of_lt_add (t Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) :
    ¬ RhBandAgree t Q 0 L := by
  intro hb
  have hbi := hb (t + Q) hL
  rw [Nat.zero_add,
    rhCenter_self_eq_true (t + Q),
    rhCenter_gt_eq_false t (t + Q) (by omega)] at hbi
  exact Bool.noConfusion hbi

/-- **Single-Term Collapse of `phiScale k (row t)` at `(t + 2^k) - p` Inside the `$2^k$`-Horizon (`phiScale_row_testBit_rhCenter_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k` (with NO bound `p ≤ t` required, since for `p > t` bit `(t + 2^k) - p` crosses into the inter-cone zero gap where both sides equal `false`!), `(phiScale k (row t)).testBit ((t + 2^k) - p) = rhCenter t p`! -/
theorem phiScale_row_testBit_rhCenter_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    (phiScale k (row t)).testBit ((t + twopow k) - p) = rhCenter t p := by
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
    ((row t) <<< (twopow k + twopow k))).testBit ((t + twopow k) - p) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d2 : decide ((t + twopow k) - p ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  have hout : (row t).testBit ((t + twopow k) - p) = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t ((t + twopow k) - p) (by omega)
  by_cases hpt : p ≤ t
  · have d1 : decide ((t + twopow k) - p ≥ twopow k) = true := decide_eq_true (by omega)
    rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false, hout, Bool.false_xor,
      show (t + twopow k) - p - twopow k = t - p by omega,
      ← rhCenter_eq_row_testBit t p hpt]
  · have d1 : decide ((t + twopow k) - p ≥ twopow k) = false := decide_eq_false (by omega)
    rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false, hout,
      rhCenter_gt_eq_false t p (by omega)]

theorem phiScale_row_testBit_rhCenter_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    wittBitBool (phiScale k (row t)) ((t + twopow k) - p) = rhCenter t p :=
  phiScale_row_testBit_rhCenter_cone t k p hp

/-- **Same-Column `$2^k$`-Scale Step of `rhCenter` Inside the `$2^k$`-Horizon (`rhCenter_scale_same_col_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k` (no bound `p ≤ t` required!), at the SAME spatial column `p` in the right half, `rhCenter (t + 2^k) p = rhCenter t p ⊕ (winWitt t (2^k)).testBit ((t + 2^k) - p)`! -/
theorem rhCenter_scale_same_col_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    rhCenter (t + twopow k) p =
      bxor (rhCenter t p)
        ((winWitt t (twopow k)).testBit ((t + twopow k) - p)) := by
  rw [rhCenter_eq_row_testBit (t + twopow k) p (by omega)]
  have hsc := congrArg (fun n => n.testBit ((t + twopow k) - p)) (row_scale t k)
  rw [Nat.testBit_xor, phiScale_row_testBit_rhCenter_cone t k p hp] at hsc
  rw [hsc, bxor_eq_xor]

theorem rhCenter_scale_same_col_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    rhCenter (t + twopow k) p =
      bxor (rhCenter t p)
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p)) :=
  rhCenter_scale_same_col_cone t k p hp

/-- **Same-Column `$2^k$`-Scale Pullback of `rhCenter` Inside the `$2^k$`-Horizon (`rhCenter_scale_inward_same_col_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k` (no bound `p ≤ t` required!), `rhCenter t p = rhCenter (t + 2^k) p ⊕ (winWitt t (2^k)).testBit ((t + 2^k) - p)`! -/
theorem rhCenter_scale_inward_same_col_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    rhCenter t p =
      bxor (rhCenter (t + twopow k) p)
        ((winWitt t (twopow k)).testBit ((t + twopow k) - p)) := by
  rw [rhCenter_scale_same_col_cone t k p hp]
  cases rhCenter t p <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow k) - p) <;> rfl

theorem rhCenter_scale_inward_same_col_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    rhCenter t p =
      bxor (rhCenter (t + twopow k) p)
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p)) :=
  rhCenter_scale_inward_same_col_cone t k p hp

/-- **Exact Readout of `winWitt` at `(t + 2^k) - p` as the Same-Column `$2^k$`-Time Jump of `rhCenter` (`winWitt_testBit_rhCenter_same_col_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k` (no bound `p ≤ t` required!), `(winWitt t (2^k)).testBit ((t + 2^k) - p) = rhCenter (t + 2^k) p ⊕ rhCenter t p`! -/
theorem winWitt_testBit_rhCenter_same_col_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow k) - p) =
      bxor (rhCenter (t + twopow k) p) (rhCenter t p) := by
  rw [rhCenter_scale_same_col_cone t k p hp]
  cases rhCenter t p <;>
    cases (winWitt t (twopow k)).testBit ((t + twopow k) - p) <;> rfl

theorem winWitt_testBit_rhCenter_same_col_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p) =
      bxor (rhCenter (t + twopow k) p) (rhCenter t p) :=
  winWitt_testBit_rhCenter_same_col_cone t k p hp

/-- **Direct Readout of Late `rhCenter (t + 2^k) p` in the Inter-Cone Zero Gap (`winWitt_testBit_zero_gap_eq_rhCenter_late`)**:
    for all `t, k, p : Nat` with `t < p` and `t + p < 2^k`, `rhCenter t p = false`, so `(winWitt t (2^k)).testBit ((t + 2^k) - p) = rhCenter (t + 2^k) p` directly! -/
theorem winWitt_testBit_zero_gap_eq_rhCenter_late (t k p : Nat)
    (htp : t < p) (hp : t + p < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow k) - p) =
      rhCenter (t + twopow k) p := by
  rw [winWitt_testBit_rhCenter_same_col_cone t k p hp,
    rhCenter_gt_eq_false t p htp]
  cases rhCenter (t + twopow k) p <;> rfl

theorem winWitt_testBit_zero_gap_eq_rhCenter_late_prop (t k p : Nat)
    (htp : t < p) (hp : t + p < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p) =
      rhCenter (t + twopow k) p :=
  winWitt_testBit_zero_gap_eq_rhCenter_late t k p htp hp

/-- **Same-Column `$2^k$`-Scale Forward Step of `RhBandAgree` (`rhBandAgree_scale_same_col_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k` (no bound `p0 + L ≤ t` required!), `RhBandAgree t Q p0 L` and `WinWittAgree t k Q ((t + 2^k) - (p0 + L)) L` imply `RhBandAgree (t + 2^k) Q p0 L` at the SAME column `p0`! -/
theorem rhBandAgree_scale_same_col_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (h0 : RhBandAgree t Q p0 L)
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L)) L) :
    RhBandAgree (t + twopow k) Q p0 L := by
  intro i hi
  have hsQ := rhCenter_scale_same_col_cone (t + Q) k (p0 + i) (by omega)
  have hs0 := rhCenter_scale_same_col_cone t k (p0 + i) (by omega)
  have hb0 := h0 i hi
  have hwi := hw (L - i) (by omega)
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega,
    hsQ, hs0, hb0,
    show ((t + Q) + twopow k) - (p0 + i) = ((t + twopow k) - (p0 + L)) + (L - i) + Q by omega,
    show (t + twopow k) - (p0 + i) = ((t + twopow k) - (p0 + L)) + (L - i) by omega,
    hwi]

/-- **Same-Column `$2^k$`-Scale Pullback of `RhBandAgree` (`rhBandAgree_scale_inward_same_col_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k` (no bound `p0 + L ≤ t` required!), `RhBandAgree (t + 2^k) Q p0 L` and `WinWittAgree t k Q ((t + 2^k) - (p0 + L)) L` imply `RhBandAgree t Q p0 L` at the SAME column `p0`! -/
theorem rhBandAgree_scale_inward_same_col_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (hlate : RhBandAgree (t + twopow k) Q p0 L)
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L)) L) :
    RhBandAgree t Q p0 L := by
  intro i hi
  have hsQ := rhCenter_scale_inward_same_col_cone (t + Q) k (p0 + i) (by omega)
  have hs0 := rhCenter_scale_inward_same_col_cone t k (p0 + i) (by omega)
  have hbl := hlate i hi
  have hwi := hw (L - i) (by omega)
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hbl
  rw [hsQ, hs0, hbl,
    show ((t + Q) + twopow k) - (p0 + i) = ((t + twopow k) - (p0 + L)) + (L - i) + Q by omega,
    show (t + twopow k) - (p0 + i) = ((t + twopow k) - (p0 + L)) + (L - i) by omega,
    hwi]

/-- **Deriving `WinWittAgree` at `(t + 2^k) - (p0 + L)` from Same-Column `RhBandAgree` at `t + 2^k` and `t` (`winWittAgree_rhCenter_same_col_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k` (no bound `p0 + L ≤ t` required!), `RhBandAgree (t + 2^k) Q p0 L` and `RhBandAgree t Q p0 L` imply `WinWittAgree t k Q ((t + 2^k) - (p0 + L)) L`! -/
theorem winWittAgree_rhCenter_same_col_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (hlate : RhBandAgree (t + twopow k) Q p0 L)
    (h0 : RhBandAgree t Q p0 L) :
    WinWittAgree t k Q ((t + twopow k) - (p0 + L)) L := by
  intro i hi
  have hsQ := winWitt_testBit_rhCenter_same_col_cone (t + Q) k (p0 + (L - i)) (by omega)
  have hs0 := winWitt_testBit_rhCenter_same_col_cone t k (p0 + (L - i)) (by omega)
  have hbl := hlate (L - i) (by omega)
  have hb0 := h0 (L - i) (by omega)
  rw [show (t + twopow k) + Q = (t + Q) + twopow k by omega] at hbl
  rw [show ((t + twopow k) - (p0 + L)) + i + Q = ((t + Q) + twopow k) - (p0 + (L - i)) by omega,
    show ((t + twopow k) - (p0 + L)) + i = (t + twopow k) - (p0 + (L - i)) by omega,
    hsQ, hs0, hbl, hb0]

/-- **Refutation of Simultaneous Late Same-Column `RhBandAgree` and Right-Wing `WinWittAgree` (`not_rhBandAgree_late_and_winWittAgree_cone`)**:
    for all `t, k, Q, L : Nat` with `0 < Q`, `t + Q ≤ L`, and `t + Q + L < 2^k`, `RhBandAgree (t + 2^k) Q 0 L` and `WinWittAgree t k Q ((t + 2^k) - L) L` cannot both hold, since pulling back to time `t` violates `not_rhBandAgree_of_lt_add`! -/
theorem not_rhBandAgree_late_and_winWittAgree_cone (t k Q L : Nat)
    (hQ : 0 < Q) (hL : t + Q ≤ L) (htk : t + Q + L < twopow k)
    (hlate : RhBandAgree (t + twopow k) Q 0 L) :
    ¬ WinWittAgree t k Q ((t + twopow k) - L) L := by
  intro hw
  have hw0 : WinWittAgree t k Q ((t + twopow k) - (0 + L)) L := by
    rwa [Nat.zero_add]
  have h0 := rhBandAgree_scale_inward_same_col_cone t k Q 0 L (by omega) hlate hw0
  exact not_rhBandAgree_of_lt_add t Q L hQ hL h0

/-- **Extracting `LhBandAgree t Q 0 R` from Two-Sided Symmetric `RowAgree t Q (t - R) (2 * R)` (`lhBandAgree_of_rowAgree_symm`)**:
    for all `t, Q, R : Nat` with `R ≤ t`, symmetric row agreement `RowAgree t Q (t - R) (2 * R)` implies left-half band agreement `LhBandAgree t Q 0 R`! -/
theorem lhBandAgree_of_rowAgree_symm (t Q R : Nat)
    (hR : R ≤ t)
    (hrow : RowAgree t Q (t - R) (2 * R)) :
    LhBandAgree t Q 0 R := by
  intro i hi
  have hr := hrow (R + i) (by omega)
  rw [Nat.zero_add,
    lhCenter_eq_row_testBit_uncond (t + Q) i,
    lhCenter_eq_row_testBit_uncond t i,
    show (t + Q) + i = (t - R) + (R + i) + Q by omega,
    show t + i = (t - R) + (R + i) by omega]
  exact hr

/-- **Symmetric Doubling from `RhBandAgree` to `LhBandAgree` Across the Periodic Center (`periodic_lhBandAgree_zero_of_rhBandAgree_zero`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, R : Nat` with `T ≤ t` and `R ≤ t`, right-half band agreement `RhBandAgree t (m * P) 0 R` automatically doubles across the periodic center to left-half band agreement `LhBandAgree t (m * P) 0 R`! -/
theorem periodic_lhBandAgree_zero_of_rhBandAgree_zero
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t R : Nat) (ht : T ≤ t) (hR : R ≤ t)
    (hrh : RhBandAgree t (m * P) 0 R) :
    LhBandAgree t (m * P) 0 R := by
  have hrow_r := rowAgree_right_of_rhBandAgree t (m * P) 0 R (by omega) hrh
  rw [Nat.zero_add] at hrow_r
  have hrow_symm := periodic_rowAgree_symm_of_right T P hP hper m R t ht hR hrow_r
  exact lhBandAgree_of_rowAgree_symm t (m * P) R hR hrow_symm

/-- **Late-Time Symmetric Doubling from `RhBandAgree (t + 2^k)` to `LhBandAgree (t + 2^k)` Without `R ≤ t` (`periodic_lhBandAgree_late_of_rhBandAgree_late`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, R : Nat` with `T ≤ t` and `R ≤ 2^k` (no bound `R ≤ t` required, because `R ≤ 2^k ≤ t + 2^k`!), `RhBandAgree (t + 2^k) (m * P) 0 R` automatically implies `LhBandAgree (t + 2^k) (m * P) 0 R`! -/
theorem periodic_lhBandAgree_late_of_rhBandAgree_late
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k R : Nat) (ht : T ≤ t) (hR : R ≤ twopow k)
    (hrh : RhBandAgree (t + twopow k) (m * P) 0 R) :
    LhBandAgree (t + twopow k) (m * P) 0 R :=
  periodic_lhBandAgree_zero_of_rhBandAgree_zero T P hP hper m (t + twopow k) R (by omega) (by omega) hrh

/-- **Cross-Wing Refutation of Late `RhBandAgree (t + 2^k)` and Left Sector-1 `WinWittAgree` (`not_periodic_rhBandAgree_late_and_winWittAgree_sector_one`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, L : Nat` with `0 < m`, `T ≤ t`, `t + m * P ≤ L`, and `t + m * P + L < 2^k`, `RhBandAgree (t + 2^k) (m * P) 0 L` transfers across the periodic center at time `t + 2^k` to `LhBandAgree (t + 2^k) (m * P) 0 L` (`L ≤ 2^k`), which is incompatible with left Sector-1 `WinWittAgree t k (m * P) (t + 2^k) L`! -/
theorem not_periodic_rhBandAgree_late_and_winWittAgree_sector_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k L : Nat) (hm : 0 < m) (ht : T ≤ t) (hL : t + m * P ≤ L)
    (htk : t + m * P + L < twopow k)
    (hrh_late : RhBandAgree (t + twopow k) (m * P) 0 L) :
    ¬ WinWittAgree t k (m * P) (t + twopow k) L := by
  have hQ : 0 < m * P := Nat.mul_pos hm hP
  have hlh_late := periodic_lhBandAgree_late_of_rhBandAgree_late T P hP hper m t k L ht (by omega) hrh_late
  exact not_lhBandAgree_late_and_winWittAgree_sector_one t k (m * P) L hQ hL htk hlh_late

/-- **Symmetric Doubling of Sector-1 `WinWittAgree` Across the Periodic Center (`periodic_winWittAgree_sector_one_left_of_right`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k, R : Nat` with `T ≤ t`, `R ≤ t`, and `t + m * P + R < 2^k`, early right-half agreement `RhBandAgree t (m * P) 0 R` and right-wing window agreement `WinWittAgree t k (m * P) ((t + 2^k) - R) R` automatically imply left-wing Sector-1 window agreement `WinWittAgree t k (m * P) (t + 2^k) R`! -/
theorem periodic_winWittAgree_sector_one_left_of_right
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k R : Nat) (ht : T ≤ t) (hR : R ≤ t) (htk : t + m * P + R < twopow k)
    (hrh0 : RhBandAgree t (m * P) 0 R)
    (hw_right : WinWittAgree t k (m * P) ((t + twopow k) - R) R) :
    WinWittAgree t k (m * P) (t + twopow k) R := by
  have hw_r0 : WinWittAgree t k (m * P) ((t + twopow k) - (0 + R)) R := by
    rwa [Nat.zero_add]
  have hrh_late := rhBandAgree_scale_same_col_cone t k (m * P) 0 R (by omega) hrh0 hw_r0
  have hlh_late := periodic_lhBandAgree_late_of_rhBandAgree_late T P hP hper m t k R ht (by omega) hrh_late
  have hlh0 := periodic_lhBandAgree_zero_of_rhBandAgree_zero T P hP hper m t R ht hR hrh0
  have hw_left := winWittAgree_sector_one_lhCenter t k (m * P) 0 R (by omega) hlh_late hlh0
  rwa [Nat.add_zero] at hw_left

/-! ### Batch 14: Universal Inter-Cone & Sector-1 `frobDefect` Vanishing, Right-Half Window Step, and `Φ`-Coupled Sector-1 Window Defect Laws -/

/-- **Universal Vanishing of `frobDefect k (row t)` Above the Sector-0 Light Cone and Below Sector 2 (`frobDefect_row_testBit_gt_two_mul_eq_false`)**:
    for all `t, k, b : Nat` with `2 * t + 1 < b` and `b < 2^k + 2^k` (covering the inter-cone zero gap, the boundary `b = 2^k`, and the entire right, center, and left parts of Sector 1 without requiring `2 * t + 1 < 2^k`!), `(frobDefect k (row t)).testBit b = false`! -/
theorem frobDefect_row_testBit_gt_two_mul_eq_false (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k + twopow k) :
    (frobDefect k (row t)).testBit b = false := by
  have hu_b : (row t).testBit b = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t b (by omega)
  have hu_bm1 : (row t).testBit (b - 1) = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t (b - 1) (by omega)
  change (carry (phiScale k (row t)) ^^^ phiScale k (carry (row t))).testBit b = false
  simp only [Nat.testBit_xor]
  have hphi_b : (phiScale k (row t)).testBit b =
      (decide (b ≥ twopow k) && (row t).testBit (b - twopow k)) := by
    change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit b = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d2 : decide (b ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d2, Bool.false_and, Bool.xor_false, hu_b, Bool.false_xor]
  have hphi_bm1 : (phiScale k (row t)).testBit (b - 1) =
      (decide (b - 1 ≥ twopow k) && (row t).testBit (b - 1 - twopow k)) := by
    change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
      ((row t) <<< (twopow k + twopow k))).testBit (b - 1) = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d2 : decide (b - 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d2, Bool.false_and, Bool.xor_false, hu_bm1, Bool.false_xor]
  have hcarry_b : (carry (row t)).testBit b = false := by
    change ((row t) &&& ((row t) <<< 1)).testBit b = false
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
    rw [hu_b, Bool.false_and]
  have hlhs : (carry (phiScale k (row t))).testBit b =
      ((phiScale k (row t)).testBit b && (phiScale k (row t)).testBit (b - 1)) := by
    change ((phiScale k (row t)) &&& ((phiScale k (row t)) <<< 1)).testBit b = _
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
    have d0 : decide (b ≥ 1) = true := decide_eq_true (by omega)
    rw [d0, Bool.true_and]
  have hrhs : (phiScale k (carry (row t))).testBit b =
      (decide (b ≥ twopow k) && (carry (row t)).testBit (b - twopow k)) := by
    change (((carry (row t)) ^^^ ((carry (row t)) <<< twopow k)) ^^^
      ((carry (row t)) <<< (twopow k + twopow k))).testBit b = _
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have d2 : decide (b ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
    rw [d2, Bool.false_and, Bool.xor_false, hcarry_b, Bool.false_xor]
  rw [hlhs, hrhs, hphi_b, hphi_bm1]
  by_cases hbk : twopow k + 1 ≤ b
  · have d1 : decide (b ≥ twopow k) = true := decide_eq_true (by omega)
    have d1m : decide (b - 1 ≥ twopow k) = true := decide_eq_true (by omega)
    have hck : (carry (row t)).testBit (b - twopow k) =
        ((row t).testBit (b - twopow k) && (row t).testBit (b - 1 - twopow k)) := by
      change ((row t) &&& ((row t) <<< 1)).testBit (b - twopow k) = _
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft]
      have d0 : decide (b - twopow k ≥ 1) = true := decide_eq_true (by omega)
      rw [d0, Bool.true_and, show b - twopow k - 1 = b - 1 - twopow k by omega]
    rw [d1, d1m, Bool.true_and, Bool.true_and, Bool.true_and, hck, Bool.xor_self]
  · have d1m : decide (b - 1 ≥ twopow k) = false := decide_eq_false (by omega)
    have hck0 : (decide (b ≥ twopow k) && (carry (row t)).testBit (b - twopow k)) = false := by
      by_cases hbe : b ≥ twopow k
      · have hbeq : b - twopow k = 0 := by omega
        have hc0 : (carry (row t)).testBit 0 = false := by
          change ((row t) &&& ((row t) <<< 1)).testBit 0 = false
          simp
        rw [hbeq, hc0, Bool.and_false]
      · have df : decide (b ≥ twopow k) = false := decide_eq_false hbe
        rw [df, Bool.false_and]
    rw [d1m, Bool.false_and, Bool.and_false, hck0, Bool.xor_self]

theorem frobDefect_row_testBit_gt_two_mul_eq_false_prop (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k + twopow k) :
    wittBitBool (frobDefect k (row t)) b = false :=
  frobDefect_row_testBit_gt_two_mul_eq_false t k b hb0 hb1

/-- **Vanishing of `frobDefect k (row t)` Across the Right Half and Center of Sector 1 (`frobDefect_row_testBit_rhCenter_cone_eq_false`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k` (no bound `p ≤ t` required, and including `p = 0`, the center slot `t + 2^k`!), `(frobDefect k (row t)).testBit ((t + 2^k) - p) = false`! -/
theorem frobDefect_row_testBit_rhCenter_cone_eq_false (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (frobDefect k (row t)).testBit ((t + twopow k) - p) = false :=
  frobDefect_row_testBit_gt_two_mul_eq_false t k ((t + twopow k) - p) (by omega) (by omega)

theorem frobDefect_row_testBit_rhCenter_cone_eq_false_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (frobDefect k (row t)) ((t + twopow k) - p) = false :=
  frobDefect_row_testBit_rhCenter_cone_eq_false t k p hp

/-- **Single-Sector Collapse of Sector-1 `crossCarry` Across the Right Half and Center (`crossCarry_row_scale_rhCenter_cone`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k` (no bound `p ≤ t` required, and including `p = 0`!), `(crossCarry (phiScale k (row t)) (winWitt t (2^k))).testBit ((t + 2^k) - p)` depends ONLY on `rhCenter t p`, `rhCenter t (p + 1)`, and `winWitt t (2^k)`! -/
theorem crossCarry_row_scale_rhCenter_cone (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit
        ((t + twopow k) - p) =
      bxor
        (rhCenter t p &&
          (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)))
        ((winWitt t (twopow k)).testBit ((t + twopow k) - p) &&
          rhCenter t (p + 1)) := by
  have hc := crossCarry_testBit_succ (phiScale k (row t)) (winWitt t (twopow k))
    ((t + twopow k) - (p + 1))
  rw [show ((t + twopow k) - (p + 1)) + 1 = (t + twopow k) - p by omega] at hc
  rw [hc,
    phiScale_row_testBit_rhCenter_cone t k p (by omega),
    phiScale_row_testBit_rhCenter_cone t k (p + 1) (by omega)]

theorem crossCarry_row_scale_rhCenter_cone_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k)))
        ((t + twopow k) - p) =
      bxor
        (rhCenter t p &&
          wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 1)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p) &&
          rhCenter t (p + 1)) :=
  crossCarry_row_scale_rhCenter_cone t k p hp

/-- **Single-Sector Window Step of `winWitt` Across the Right Half and Center (`winWitt_step_rhCenter_cone`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k` (no bound `p ≤ t` required, and including `p = 0`!), because `frobDefect = false` (`9.503`) and `phiScale k (row t) = rhCenter t p` (`9.488`), the universal window step at `((t + 1) + 2^k) - p` collapses to a single-sector recurrence driven ONLY by `rhCenter t p`, `rhCenter t (p + 1)`, and `winWitt t (2^k)`! -/
theorem winWitt_step_rhCenter_cone (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit (((t + 1) + twopow k) - p) =
      bxor
        ((phi (winWitt t (twopow k))).testBit (((t + 1) + twopow k) - p))
        (bxor
          (rhCenter t p &&
            (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)))
          ((winWitt t (twopow k)).testBit ((t + twopow k) - p) &&
            rhCenter t (p + 1))) := by
  have hs := winWitt_step_frobDefect_testBit_succ t k ((t + twopow k) - p)
  rw [show ((t + twopow k) - p) + 1 = ((t + 1) + twopow k) - p by omega,
    crossCarry_row_scale_rhCenter_cone t k p hp,
    frobDefect_row_testBit_rhCenter_cone_eq_false t k p hp] at hs
  rw [hs]
  cases (phi (winWitt t (twopow k))).testBit (((t + 1) + twopow k) - p) <;>
    cases (bxor
      (rhCenter t p && (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)))
      ((winWitt t (twopow k)).testBit ((t + twopow k) - p) && rhCenter t (p + 1))) <;> rfl

theorem winWitt_step_rhCenter_cone_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) (((t + 1) + twopow k) - p) =
      bxor
        (wittBitBool (phi (winWitt t (twopow k))) (((t + 1) + twopow k) - p))
        (bxor
          (rhCenter t p &&
            wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 1)))
          (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p) &&
            rhCenter t (p + 1))) :=
  winWitt_step_rhCenter_cone t k p hp

/-- **Pure `Φ`-Evolution of `winWitt` in the Right Inter-Cone Zero Gap (`winWitt_step_zero_gap_eq_phi`)**:
    for all `t, k, p : Nat` with `t < p` and `t + p + 1 < 2^k`, both `rhCenter t p = false` and `rhCenter t (p + 1) = false`, so both `frobDefect` and `crossCarry` vanish and `winWitt` evolves by the pure Witt-row map `phi`! -/
theorem winWitt_step_zero_gap_eq_phi (t k p : Nat)
    (htp : t < p) (hp : t + p + 1 < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit (((t + 1) + twopow k) - p) =
      (phi (winWitt t (twopow k))).testBit (((t + 1) + twopow k) - p) := by
  rw [winWitt_step_rhCenter_cone t k p hp,
    rhCenter_gt_eq_false t p htp,
    rhCenter_gt_eq_false t (p + 1) (by omega),
    Bool.false_and, Bool.and_false]
  cases (phi (winWitt t (twopow k))).testBit (((t + 1) + twopow k) - p) <;> rfl

theorem winWitt_step_zero_gap_eq_phi_prop (t k p : Nat)
    (htp : t < p) (hp : t + p + 1 < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) (((t + 1) + twopow k) - p) =
      wittBitBool (phi (winWitt t (twopow k))) (((t + 1) + twopow k) - p) :=
  winWitt_step_zero_gap_eq_phi t k p htp hp

/-- **Pure `Φ`-Evolution of `winWitt` in the Left Outer Cone Gap (`winWitt_step_lhCenter_zero_gap_eq_phi`)**:
    for all `t, k, p : Nat` with `t < p` and `t + p + 1 < 2^k`, both `lhCenter t p = false` and `lhCenter t (p + 1) = false`, so both `frobDefect` and `crossCarry` vanish and `winWitt` at `(t + 1) + (p + 1) + 2^k` evolves by the pure Witt-row map `phi`! -/
theorem winWitt_step_lhCenter_zero_gap_eq_phi (t k p : Nat)
    (htp : t < p) (hp : t + p + 1 < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p + 1) + twopow k) =
      (phi (winWitt t (twopow k))).testBit ((t + 1) + (p + 1) + twopow k) := by
  rw [winWitt_step_sector_one_lhCenter t k p hp,
    lhCenter_gt_eq_false t p htp,
    lhCenter_gt_eq_false t (p + 1) (by omega),
    Bool.false_and, Bool.and_false]
  cases (phi (winWitt t (twopow k))).testBit ((t + 1) + (p + 1) + twopow k) <;> rfl

theorem winWitt_step_lhCenter_zero_gap_eq_phi_prop (t k p : Nat)
    (htp : t < p) (hp : t + p + 1 < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + (p + 1) + twopow k) =
      wittBitBool (phi (winWitt t (twopow k))) ((t + 1) + (p + 1) + twopow k) :=
  winWitt_step_lhCenter_zero_gap_eq_phi t k p htp hp

/-- **Single-Sector Forward Step of Right-Wing `WinWittAgree` (`winWittAgree_step_rhCenter_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L + 1 < 2^k` (no bound `p0 + L ≤ t` required, and including `p0 = 0`!), `WinWittAgree` on the right half of Sector 1 steps forward from time `t` to `t + 1` using ONLY `RhBandAgree t Q p0 (L + 1)`! -/
theorem winWittAgree_step_rhCenter_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hb : RhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 1)) (L + 2)) :
    WinWittAgree (t + 1) k Q (((t + 1) + twopow k) - (p0 + L)) L := by
  intro i hi
  have hsQ := winWitt_step_rhCenter_cone (t + Q) k (p0 + (L - i)) (by omega)
  have hs0 := winWitt_step_rhCenter_cone t k (p0 + (L - i)) (by omega)
  have hb0 := hb (L - i) (by omega)
  have hb1 := hb ((L - i) + 1) (by omega)
  have hw0 := hw i (by omega)
  have hw1 := hw (i + 1) (by omega)
  have hw2 := hw (i + 2) (by omega)
  rw [show p0 + ((L - i) + 1) = (p0 + (L - i)) + 1 by omega] at hb1
  rw [show ((t + twopow k) - (p0 + L + 1)) + i + Q =
      ((t + Q) + twopow k) - ((p0 + (L - i)) + 1) by omega,
    show ((t + twopow k) - (p0 + L + 1)) + i =
      (t + twopow k) - ((p0 + (L - i)) + 1) by omega] at hw0
  rw [show ((t + twopow k) - (p0 + L + 1)) + (i + 1) + Q =
      ((t + Q) + twopow k) - (p0 + (L - i)) by omega,
    show ((t + twopow k) - (p0 + L + 1)) + (i + 1) =
      (t + twopow k) - (p0 + (L - i)) by omega] at hw1
  rw [show ((t + twopow k) - (p0 + L + 1)) + (i + 2) + Q =
      (((t + Q) + twopow k) - ((p0 + (L - i)) + 1)) + 2 by omega,
    show ((t + twopow k) - (p0 + L + 1)) + (i + 2) =
      ((t + twopow k) - ((p0 + (L - i)) + 1)) + 2 by omega] at hw2
  have hphiQ : (phi (winWitt (t + Q) (twopow k))).testBit ((((t + Q) + 1) + twopow k) - (p0 + (L - i))) =
      bxor ((winWitt (t + Q) (twopow k)).testBit ((((t + Q) + twopow k) - ((p0 + (L - i)) + 1)) + 2))
        ((winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow k) - (p0 + (L - i))) ||
          (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow k) - ((p0 + (L - i)) + 1))) := by
    have hp0 := phi_testBit_add_two (winWitt (t + Q) (twopow k)) (((t + Q) + twopow k) - ((p0 + (L - i)) + 1))
    rw [show ((((t + Q) + 1) + twopow k) - (p0 + (L - i))) =
        (((t + Q) + twopow k) - ((p0 + (L - i)) + 1)) + 2 by omega,
      hp0,
      show (((t + Q) + twopow k) - ((p0 + (L - i)) + 1)) + 1 =
        ((t + Q) + twopow k) - (p0 + (L - i)) by omega,
      bxor_eq_xor]
  have hphi0 : (phi (winWitt t (twopow k))).testBit (((t + 1) + twopow k) - (p0 + (L - i))) =
      bxor ((winWitt t (twopow k)).testBit (((t + twopow k) - ((p0 + (L - i)) + 1)) + 2))
        ((winWitt t (twopow k)).testBit ((t + twopow k) - (p0 + (L - i))) ||
          (winWitt t (twopow k)).testBit ((t + twopow k) - ((p0 + (L - i)) + 1))) := by
    have hp0 := phi_testBit_add_two (winWitt t (twopow k)) ((t + twopow k) - ((p0 + (L - i)) + 1))
    rw [show (((t + 1) + twopow k) - (p0 + (L - i))) =
        ((t + twopow k) - ((p0 + (L - i)) + 1)) + 2 by omega,
      hp0,
      show ((t + twopow k) - ((p0 + (L - i)) + 1)) + 1 =
        (t + twopow k) - (p0 + (L - i)) by omega,
      bxor_eq_xor]
  rw [show (t + 1) + Q = (t + Q) + 1 by omega,
    show (((t + 1) + twopow k) - (p0 + L)) + i + Q =
      (((t + Q) + 1) + twopow k) - (p0 + (L - i)) by omega,
    show (((t + 1) + twopow k) - (p0 + L)) + i =
      ((t + 1) + twopow k) - (p0 + (L - i)) by omega,
    hsQ, hs0, hphiQ, hphi0, hb0, hb1, hw0, hw1, hw2]

/-- **Single-Sector Inward Extension of Right-Wing `WinWittAgree` Toward the Center (`winWittAgree_inward_step_rhCenter_cone`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L + 1 < 2^k`, `RhBandAgree t Q p0 (L + 1)`, `WinWittAgree t k Q ((t + 2^k) - (p0 + L + 1)) (L + 1)`, and `WinWittAgree (t + 1) k Q (((t + 1) + 2^k) - (p0 + L)) L` extend `WinWittAgree` at time `t` inward toward the center to width `L + 2`! -/
theorem winWittAgree_inward_step_rhCenter_cone (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hb : RhBandAgree t Q p0 (L + 1))
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 1)) (L + 1))
    (hnext : WinWittAgree (t + 1) k Q (((t + 1) + twopow k) - (p0 + L)) L) :
    WinWittAgree t k Q ((t + twopow k) - (p0 + L + 1)) (L + 2) := by
  intro i hi
  by_cases hi1 : i ≤ L + 1
  · exact hw i hi1
  · have hi_eq : i = L + 2 := by omega
    subst hi_eq
    have hsQ := winWitt_step_rhCenter_cone (t + Q) k p0 (by omega)
    have hs0 := winWitt_step_rhCenter_cone t k p0 (by omega)
    have hb0 := hb 0 (by omega)
    have hb1 := hb 1 (by omega)
    have hw0 := hw L (by omega)
    have hw1 := hw (L + 1) (by omega)
    have hwn := hnext L (Nat.le_refl L)
    rw [Nat.add_zero] at hb0
    rw [show ((t + twopow k) - (p0 + L + 1)) + L + Q = ((t + Q) + twopow k) - (p0 + 1) by omega,
      show ((t + twopow k) - (p0 + L + 1)) + L = (t + twopow k) - (p0 + 1) by omega] at hw0
    rw [show ((t + twopow k) - (p0 + L + 1)) + (L + 1) + Q = ((t + Q) + twopow k) - p0 by omega,
      show ((t + twopow k) - (p0 + L + 1)) + (L + 1) = (t + twopow k) - p0 by omega] at hw1
    rw [show (t + 1) + Q = (t + Q) + 1 by omega,
      show (((t + 1) + twopow k) - (p0 + L)) + L + Q = (((t + Q) + 1) + twopow k) - p0 by omega,
      show (((t + 1) + twopow k) - (p0 + L)) + L = ((t + 1) + twopow k) - p0 by omega] at hwn
    have hphiQ : (phi (winWitt (t + Q) (twopow k))).testBit ((((t + Q) + 1) + twopow k) - p0) =
        bxor ((winWitt (t + Q) (twopow k)).testBit ((((t + Q) + twopow k) - (p0 + 1)) + 2))
          ((winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow k) - p0) ||
            (winWitt (t + Q) (twopow k)).testBit (((t + Q) + twopow k) - (p0 + 1))) := by
      have hp0 := phi_testBit_add_two (winWitt (t + Q) (twopow k)) (((t + Q) + twopow k) - (p0 + 1))
      rw [show ((((t + Q) + 1) + twopow k) - p0) =
          (((t + Q) + twopow k) - (p0 + 1)) + 2 by omega,
        hp0,
        show (((t + Q) + twopow k) - (p0 + 1)) + 1 = ((t + Q) + twopow k) - p0 by omega,
        bxor_eq_xor]
    have hphi0 : (phi (winWitt t (twopow k))).testBit (((t + 1) + twopow k) - p0) =
        bxor ((winWitt t (twopow k)).testBit (((t + twopow k) - (p0 + 1)) + 2))
          ((winWitt t (twopow k)).testBit ((t + twopow k) - p0) ||
            (winWitt t (twopow k)).testBit ((t + twopow k) - (p0 + 1))) := by
      have hp0 := phi_testBit_add_two (winWitt t (twopow k)) ((t + twopow k) - (p0 + 1))
      rw [show (((t + 1) + twopow k) - p0) =
          ((t + twopow k) - (p0 + 1)) + 2 by omega,
        hp0,
        show ((t + twopow k) - (p0 + 1)) + 1 = (t + twopow k) - p0 by omega,
        bxor_eq_xor]
    rw [hsQ, hs0, hphiQ, hphi0, hb0, hb1, hw0, hw1] at hwn
    rw [show ((t + twopow k) - (p0 + L + 1)) + (L + 2) + Q =
        (((t + Q) + twopow k) - (p0 + 1)) + 2 by omega,
      show ((t + twopow k) - (p0 + L + 1)) + (L + 2) =
        ((t + twopow k) - (p0 + 1)) + 2 by omega]
    revert hwn
    simp only [bxor_eq_xor]
    cases (winWitt (t + Q) (twopow k)).testBit ((((t + Q) + twopow k) - (p0 + 1)) + 2) <;>
      cases (winWitt t (twopow k)).testBit (((t + twopow k) - (p0 + 1)) + 2) <;>
      cases ((winWitt t (twopow k)).testBit ((t + twopow k) - p0) ||
        (winWitt t (twopow k)).testBit ((t + twopow k) - (p0 + 1))) <;>
      cases ((rhCenter t p0 && (winWitt t (twopow k)).testBit ((t + twopow k) - (p0 + 1))) ^^
        ((winWitt t (twopow k)).testBit ((t + twopow k) - p0) && rhCenter t (p0 + 1))) <;> decide

/-- **Exact Center-Slot Step Law of Sector-1 `winWitt` (`winWitt_step_sector_one_center_slot`)**:
    for all `t, k : Nat` with `t + 1 < 2^k`, evaluating `winWitt_step_rhCenter_cone` at `p = 0` expresses the next center-slot window bit `(winWitt (t + 1) (2^k)).testBit ((t + 1) + 2^k)` directly from the left slot `t + 1 + 2^k`, center slot `t + 2^k`, and right slot `(t + 2^k) - 1` of `winWitt t (2^k)` together with `center t` and `rhCenter t 1`! -/
theorem winWitt_step_sector_one_center_slot (t k : Nat)
    (htk : t + 1 < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit ((t + 1) + twopow k) =
      bxor
        ((winWitt t (twopow k)).testBit (t + 1 + twopow k))
        (bxor
          ((winWitt t (twopow k)).testBit (t + twopow k) ||
            (winWitt t (twopow k)).testBit ((t + twopow k) - 1))
          (bxor
            (Rule30UOR.Core.center t &&
              (winWitt t (twopow k)).testBit ((t + twopow k) - 1))
            ((winWitt t (twopow k)).testBit (t + twopow k) &&
              rhCenter t 1))) := by
  have hs := winWitt_step_rhCenter_cone t k 0 (by omega)
  rw [Nat.sub_zero, Nat.sub_zero, Nat.zero_add, rhCenter_zero_eq_center t] at hs
  have hphi := phi_testBit_add_two (winWitt t (twopow k)) ((t + twopow k) - 1)
  rw [show ((t + twopow k) - 1) + 2 = (t + 1) + twopow k by omega,
    show ((t + twopow k) - 1) + 1 = t + twopow k by omega] at hphi
  rw [hs, hphi]
  rw [show (t + 1) + twopow k = t + 1 + twopow k by omega]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit (t + 1 + twopow k) <;>
    cases ((winWitt t (twopow k)).testBit (t + twopow k) ||
      (winWitt t (twopow k)).testBit ((t + twopow k) - 1)) <;>
    cases ((Rule30UOR.Core.center t && (winWitt t (twopow k)).testBit ((t + twopow k) - 1)) ^^
      ((winWitt t (twopow k)).testBit (t + twopow k) && rhCenter t 1)) <;> rfl

theorem winWitt_step_sector_one_center_slot_prop (t k : Nat)
    (htk : t + 1 < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + twopow k) =
      bxor
        (wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k))
        (bxor
          (wittBitBool (winWitt t (twopow k)) (t + twopow k) ||
            wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))
          (bxor
            (Rule30UOR.Core.center t &&
              wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))
            (wittBitBool (winWitt t (twopow k)) (t + twopow k) &&
              rhCenter t 1))) :=
  winWitt_step_sector_one_center_slot t k htk

/-- **`Φ`-Coupled Sector-1 Column-`-1` Window Defect Law — Late-Center Form (`periodic_winWitt_sector_one_one_defect_eq_late`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P + 1 < 2^k`, combining `winWitt_testBit_sector_one_lhCenter` (`p = 0, 1`), `winWitt_testBit_rhCenter_same_col_cone` (`p = 1`), and `periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect` at `t` and `t + 2^k` proves that the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 1 + 2^k)` equals `((winWitt t (2^k)).testBit (t + 2^k) && (rhCenter (t + m * P) 1 ⊕ rhCenter t 1)) ⊕ (!center (t + 2^k) && ((winWitt (t + m * P) (2^k)).testBit (((t + m * P) + 2^k) - 1) ⊕ (winWitt t (2^k)).testBit ((t + 2^k) - 1)))`! -/
theorem periodic_winWitt_sector_one_one_defect_eq_late
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k) :
    bxor
      ((winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 1 + twopow k))
      ((winWitt t (twopow k)).testBit (t + 1 + twopow k)) =
      bxor
        ((winWitt t (twopow k)).testBit (t + twopow k) &&
          bxor (rhCenter (t + m * P) 1) (rhCenter t 1))
        (!Rule30UOR.Core.center (t + twopow k) &&
          bxor
            ((winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1))
            ((winWitt t (twopow k)).testBit ((t + twopow k) - 1))) := by
  have hwlQ := winWitt_testBit_sector_one_lhCenter (t + m * P) k 1 (by omega)
  have hwl0 := winWitt_testBit_sector_one_lhCenter t k 1 (by omega)
  have hwrQ := winWitt_testBit_rhCenter_same_col_cone (t + m * P) k 1 (by omega)
  have hwr0 := winWitt_testBit_rhCenter_same_col_cone t k 1 (by omega)
  have hw0 := winWitt_testBit_sector_one_lhCenter t k 0 (by omega)
  rw [Nat.add_zero, lhCenter_zero_eq_center (t + twopow k), lhCenter_zero_eq_center t] at hw0
  have hd0 := periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect T P hP hper m t ht
  have hdl := periodic_lhCenter_one_defect_eq_not_center_and_rhCenter_one_defect T P hP hper m (t + twopow k) (by omega)
  rw [hwlQ, hwl0, hwrQ, hwr0, hw0,
    show (t + m * P) + twopow k = (t + twopow k) + m * P by omega]
  have hrearrange :
      bxor
        (bxor (lhCenter ((t + twopow k) + m * P) 1) (lhCenter (t + m * P) 1))
        (bxor (lhCenter (t + twopow k) 1) (lhCenter t 1)) =
      bxor
        (bxor (lhCenter ((t + twopow k) + m * P) 1) (lhCenter (t + twopow k) 1))
        (bxor (lhCenter (t + m * P) 1) (lhCenter t 1)) := by
    cases lhCenter ((t + twopow k) + m * P) 1 <;>
      cases lhCenter (t + m * P) 1 <;>
      cases lhCenter (t + twopow k) 1 <;>
      cases lhCenter t 1 <;> rfl
  rw [hrearrange, hdl, hd0]
  cases Rule30UOR.Core.center (t + twopow k) <;>
    cases Rule30UOR.Core.center t <;>
    cases rhCenter ((t + twopow k) + m * P) 1 <;>
    cases rhCenter (t + twopow k) 1 <;>
    cases rhCenter (t + m * P) 1 <;>
    cases rhCenter t 1 <;> rfl

theorem periodic_winWitt_sector_one_one_defect_eq_late_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k) :
    bxor
      (wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + 1 + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k)) =
      bxor
        (wittBitBool (winWitt t (twopow k)) (t + twopow k) &&
          bxor (rhCenter (t + m * P) 1) (rhCenter t 1))
        (!Rule30UOR.Core.center (t + twopow k) &&
          bxor
            (wittBitBool (winWitt (t + m * P) (twopow k)) (((t + m * P) + twopow k) - 1))
            (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))) :=
  periodic_winWitt_sector_one_one_defect_eq_late T P hP hper m t k ht htk

/-- **`Φ`-Coupled Sector-1 Column-`-1` Window Defect Law — Early-Center Form (`periodic_winWitt_sector_one_one_defect_eq_early`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P + 1 < 2^k`, the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 1 + 2^k)` also equals `((winWitt t (2^k)).testBit (t + 2^k) && (rhCenter ((t + 2^k) + m * P) 1 ⊕ rhCenter (t + 2^k) 1)) ⊕ (!center t && ((winWitt (t + m * P) (2^k)).testBit (((t + m * P) + 2^k) - 1) ⊕ (winWitt t (2^k)).testBit ((t + 2^k) - 1)))`! -/
theorem periodic_winWitt_sector_one_one_defect_eq_early
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k) :
    bxor
      ((winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 1 + twopow k))
      ((winWitt t (twopow k)).testBit (t + 1 + twopow k)) =
      bxor
        ((winWitt t (twopow k)).testBit (t + twopow k) &&
          bxor (rhCenter ((t + twopow k) + m * P) 1) (rhCenter (t + twopow k) 1))
        (!Rule30UOR.Core.center t &&
          bxor
            ((winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1))
            ((winWitt t (twopow k)).testBit ((t + twopow k) - 1))) := by
  rw [periodic_winWitt_sector_one_one_defect_eq_late T P hP hper m t k ht htk]
  have hwrQ := winWitt_testBit_rhCenter_same_col_cone (t + m * P) k 1 (by omega)
  have hwr0 := winWitt_testBit_rhCenter_same_col_cone t k 1 (by omega)
  have hw0 := winWitt_testBit_sector_one_lhCenter t k 0 (by omega)
  rw [Nat.add_zero, lhCenter_zero_eq_center (t + twopow k), lhCenter_zero_eq_center t] at hw0
  rw [hwrQ, hwr0, hw0,
    show (t + m * P) + twopow k = (t + twopow k) + m * P by omega]
  cases Rule30UOR.Core.center (t + twopow k) <;>
    cases Rule30UOR.Core.center t <;>
    cases rhCenter ((t + twopow k) + m * P) 1 <;>
    cases rhCenter (t + twopow k) 1 <;>
    cases rhCenter (t + m * P) 1 <;>
    cases rhCenter t 1 <;> rfl

theorem periodic_winWitt_sector_one_one_defect_eq_early_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k) :
    bxor
      (wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + 1 + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k)) =
      bxor
        (wittBitBool (winWitt t (twopow k)) (t + twopow k) &&
          bxor (rhCenter ((t + twopow k) + m * P) 1) (rhCenter (t + twopow k) 1))
        (!Rule30UOR.Core.center t &&
          bxor
            (wittBitBool (winWitt (t + m * P) (twopow k)) (((t + m * P) + twopow k) - 1))
            (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))) :=
  periodic_winWitt_sector_one_one_defect_eq_early T P hP hper m t k ht htk

/-- **Direct Gated Transfer Between Right and Left Column-`1` Window Slots When the Center Window Slot Vanishes (`periodic_winWitt_sector_one_one_defect_of_witt_zero_false`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t`, `t + m * P + 1 < 2^k`, and `(winWitt t (2^k)).testBit (t + 2^k) = false`, the `rhCenter · 1` term drops out completely and the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 1 + 2^k)` equals `!center t && ((winWitt (t + m * P) (2^k)).testBit (((t + m * P) + 2^k) - 1) ⊕ (winWitt t (2^k)).testBit ((t + 2^k) - 1))`! -/
theorem periodic_winWitt_sector_one_one_defect_of_witt_zero_false
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k)
    (hw0 : (winWitt t (twopow k)).testBit (t + twopow k) = false) :
    bxor
      ((winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 1 + twopow k))
      ((winWitt t (twopow k)).testBit (t + 1 + twopow k)) =
      (!Rule30UOR.Core.center t &&
        bxor
          ((winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1))
          ((winWitt t (twopow k)).testBit ((t + twopow k) - 1))) := by
  rw [periodic_winWitt_sector_one_one_defect_eq_early T P hP hper m t k ht htk,
    hw0, Bool.false_and]
  cases (!Rule30UOR.Core.center t &&
    bxor
      ((winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1))
      ((winWitt t (twopow k)).testBit ((t + twopow k) - 1))) <;> rfl

theorem periodic_winWitt_sector_one_one_defect_of_witt_zero_false_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k)
    (hw0 : wittBitBool (winWitt t (twopow k)) (t + twopow k) = false) :
    bxor
      (wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + 1 + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k)) =
      (!Rule30UOR.Core.center t &&
        bxor
          (wittBitBool (winWitt (t + m * P) (twopow k)) (((t + m * P) + twopow k) - 1))
          (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))) :=
  periodic_winWitt_sector_one_one_defect_of_witt_zero_false T P hP hper m t k ht htk hw0

/-- **Exact Identification of Left Column-`-1` Window Defect with Gated `rhCenter · 1` Defect Under Right-Slot Agreement (`periodic_winWitt_sector_one_one_defect_of_witt_right_eq`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P + 1 < 2^k`, if `(winWitt (t + m * P) (2^k)).testBit (((t + m * P) + 2^k) - 1) = (winWitt t (2^k)).testBit ((t + 2^k) - 1)`, then the `m * P`-defect of `(winWitt · (2^k)).testBit (· + 1 + 2^k)` equals `(winWitt t (2^k)).testBit (t + 2^k) && (rhCenter (t + m * P) 1 ⊕ rhCenter t 1)`! -/
theorem periodic_winWitt_sector_one_one_defect_of_witt_right_eq
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k)
    (hwr : (winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1) =
      (winWitt t (twopow k)).testBit ((t + twopow k) - 1)) :
    bxor
      ((winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 1 + twopow k))
      ((winWitt t (twopow k)).testBit (t + 1 + twopow k)) =
      ((winWitt t (twopow k)).testBit (t + twopow k) &&
        bxor (rhCenter (t + m * P) 1) (rhCenter t 1)) := by
  rw [periodic_winWitt_sector_one_one_defect_eq_late T P hP hper m t k ht htk, hwr]
  cases (winWitt t (twopow k)).testBit ((t + twopow k) - 1) <;>
    cases ((winWitt t (twopow k)).testBit (t + twopow k) &&
      bxor (rhCenter (t + m * P) 1) (rhCenter t 1)) <;>
    cases Rule30UOR.Core.center (t + twopow k) <;> rfl

theorem periodic_winWitt_sector_one_one_defect_of_witt_right_eq_prop
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k)
    (hwr : wittBitBool (winWitt (t + m * P) (twopow k)) (((t + m * P) + twopow k) - 1) =
      wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1)) :
    bxor
      (wittBitBool (winWitt (t + m * P) (twopow k)) ((t + m * P) + 1 + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k)) =
      (wittBitBool (winWitt t (twopow k)) (t + twopow k) &&
        bxor (rhCenter (t + m * P) 1) (rhCenter t 1)) :=
  periodic_winWitt_sector_one_one_defect_of_witt_right_eq T P hP hper m t k ht htk hwr

/-- **Symmetric Doubling of Sector-1 `WinWittAgree` at Width `1` Without `1 ≤ t` (`periodic_winWittAgree_sector_one_two_of_right_one`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P + 1 < 2^k` (no bound `1 ≤ t` required!), `rhCenter (t + m * P) 1 = rhCenter t 1` and `(winWitt (t + m * P) (2^k)).testBit (((t + m * P) + 2^k) - 1) = (winWitt t (2^k)).testBit ((t + 2^k) - 1)` imply `WinWittAgree t k (m * P) (t + 2^k) 1` across `[t + 2^k, t + 1 + 2^k]`! -/
theorem periodic_winWittAgree_sector_one_two_of_right_one
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 1 < twopow k)
    (hr1 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (hwr : (winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1) =
      (winWitt t (twopow k)).testBit ((t + twopow k) - 1)) :
    WinWittAgree t k (m * P) (t + twopow k) 1 := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [Nat.add_zero, show t + twopow k + m * P = (t + m * P) + twopow k by omega]
    exact periodic_winWitt_sector_one_zero_eq T P hP hper m t k ht (by omega)
  · have hi1 : i = 1 := by omega
    subst hi1
    have hd := periodic_winWitt_sector_one_one_defect_of_witt_right_eq T P hP hper m t k ht htk hwr
    rw [hr1] at hd
    rw [show (t + twopow k) + 1 + m * P = (t + m * P) + 1 + twopow k by omega,
      show (t + twopow k) + 1 = t + 1 + twopow k by omega]
    revert hd
    cases (winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 1 + twopow k) <;>
      cases (winWitt t (twopow k)).testBit (t + 1 + twopow k) <;>
      cases (winWitt t (twopow k)).testBit (t + twopow k) <;>
      cases rhCenter t 1 <;> decide

/-- **Extending Sector-1 `WinWittAgree` to Width `2` (`[t + 2^k, t + 2 + 2^k]`) from Two Steps of Right Column-`+1` Agreement (`periodic_winWittAgree_sector_one_three_of_right_one_step`)**:
    under `CenterPeriodic T P` (`0 < P`), for all `m, t, k : Nat` with `T ≤ t` and `t + m * P + 2 < 2^k` (no bound `2 ≤ t` required!), if `rhCenter · 1` and `(winWitt · (2^k)).testBit ((· + 2^k) - 1)` are `m * P`-invariant at `t` and `t + 1`, then `WinWittAgree t k (m * P) (t + 2^k) 2` holds across `[t + 2^k, t + 2 + 2^k]`! -/
theorem periodic_winWittAgree_sector_one_three_of_right_one_step
    (T P : Nat) (hP : 0 < P) (hper : Rule30UOR.Scale.CenterPeriodic T P)
    (m t k : Nat) (ht : T ≤ t) (htk : t + m * P + 2 < twopow k)
    (hr1 : rhCenter (t + m * P) 1 = rhCenter t 1)
    (hr1_next : rhCenter ((t + 1) + m * P) 1 = rhCenter (t + 1) 1)
    (hwr : (winWitt (t + m * P) (twopow k)).testBit (((t + m * P) + twopow k) - 1) =
      (winWitt t (twopow k)).testBit ((t + twopow k) - 1))
    (hwr_next : (winWitt ((t + 1) + m * P) (twopow k)).testBit ((((t + 1) + m * P) + twopow k) - 1) =
      (winWitt (t + 1) (twopow k)).testBit (((t + 1) + twopow k) - 1)) :
    WinWittAgree t k (m * P) (t + twopow k) 2 := by
  have hw1 := periodic_winWittAgree_sector_one_two_of_right_one T P hP hper m t k ht (by omega) hr1 hwr
  have hw1_next := periodic_winWittAgree_sector_one_two_of_right_one T P hP hper m (t + 1) k
    (by omega) (by omega) hr1_next hwr_next
  intro i hi
  by_cases hi1 : i ≤ 1
  · exact hw1 i hi1
  · have hi2 : i = 2 := by omega
    subst hi2
    have hbit1 := hw1 1 (Nat.le_refl 1)
    have hbit1_next := hw1_next 1 (Nat.le_refl 1)
    rw [show (t + twopow k) + 1 + m * P = (t + m * P) + 1 + twopow k by omega,
      show (t + twopow k) + 1 = t + 1 + twopow k by omega] at hbit1
    rw [show ((t + 1) + twopow k) + 1 + m * P = ((t + 1) + m * P) + 1 + twopow k by omega,
      show ((t + 1) + twopow k) + 1 = (t + 1) + 1 + twopow k by omega] at hbit1_next
    have hd2 := periodic_winWitt_sector_one_two_defect_eq T P hP hper m t k ht htk
    rw [hbit1, hbit1_next] at hd2
    rw [show (t + twopow k) + 2 + m * P = (t + m * P) + 2 + twopow k by omega,
      show (t + twopow k) + 2 = t + 2 + twopow k by omega]
    revert hd2
    cases (winWitt (t + m * P) (twopow k)).testBit ((t + m * P) + 2 + twopow k) <;>
      cases (winWitt t (twopow k)).testBit (t + 2 + twopow k) <;>
      cases (winWitt (t + 1) (twopow k)).testBit ((t + 1) + 1 + twopow k) <;>
      cases (winWitt t (twopow k)).testBit (t + 1 + twopow k) <;> decide

/-! ### Batch 15: Universal Sideways (Left-Permutive) Inversion of `winWitt`, Unconditional Zero-Gap Window Propagation, and Multi-Step Sector-1 Window Calculus -/

/-- **Universal Sideways (Left-Permutive) Inversion of `winWitt` (`winWitt_inward_step_frobDefect_testBit_succ`)**:
    for all `t, k, b : Nat` with `1 ≤ b`, because `(phi w).testBit (b + 1)` is linear in `w.testBit (b + 1)` while `(crossCarry (phiScale k (row t)) w).testBit b` and `(frobDefect k (row t)).testBit b` depend only on bits `≤ b`, the universal window step `winWitt_step_frobDefect_testBit_succ` inverts sideways to express `(winWitt t (2^k)).testBit (b + 1)` from `(winWitt (t + 1) (2^k)).testBit (b + 1)` and bits `b, b - 1` at time `t`! -/
theorem winWitt_inward_step_frobDefect_testBit_succ (t k b : Nat)
    (hb : 1 ≤ b) :
    (winWitt t (twopow k)).testBit (b + 1) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit (b + 1))
        (bxor
          ((winWitt t (twopow k)).testBit b ||
            (winWitt t (twopow k)).testBit (b - 1))
          (bxor
            ((crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit b)
            ((frobDefect k (row t)).testBit b))) := by
  have hs := winWitt_step_frobDefect_testBit_succ t k b
  have hphi := phi_testBit_add_two (winWitt t (twopow k)) (b - 1)
  rw [show (b - 1) + 2 = b + 1 by omega,
    show (b - 1) + 1 = b by omega] at hphi
  rw [hs, hphi]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit (b + 1) <;>
    cases ((winWitt t (twopow k)).testBit b ||
      (winWitt t (twopow k)).testBit (b - 1)) <;>
    cases ((crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit b) <;>
    cases ((frobDefect k (row t)).testBit b) <;> rfl

theorem winWitt_inward_step_frobDefect_testBit_succ_prop (t k b : Nat)
    (hb : 1 ≤ b) :
    wittBitBool (winWitt t (twopow k)) (b + 1) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) (b + 1))
        (bxor
          (wittBitBool (winWitt t (twopow k)) b ||
            wittBitBool (winWitt t (twopow k)) (b - 1))
          (bxor
            (wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k))) b)
            (wittBitBool (frobDefect k (row t)) b))) :=
  winWitt_inward_step_frobDefect_testBit_succ t k b hb

/-- **Sideways Inversion of `winWitt` Above the Sector-0 Light Cone (`winWitt_inward_step_gt_two_mul`)**:
    for all `t, k, b : Nat` with `2 * t + 1 < b` and `b < 2^k + 2^k`, `(frobDefect k (row t)).testBit b = false` (`9.502`), so `(winWitt t (2^k)).testBit (b + 1)` is determined purely by `(winWitt (t + 1) (2^k)).testBit (b + 1)`, `(winWitt t (2^k)).testBit b`, `(winWitt t (2^k)).testBit (b - 1)`, and `crossCarry` at bit `b`! -/
theorem winWitt_inward_step_gt_two_mul (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k + twopow k) :
    (winWitt t (twopow k)).testBit (b + 1) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit (b + 1))
        (bxor
          ((winWitt t (twopow k)).testBit b ||
            (winWitt t (twopow k)).testBit (b - 1))
          ((crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit b)) := by
  rw [winWitt_inward_step_frobDefect_testBit_succ t k b (by omega),
    frobDefect_row_testBit_gt_two_mul_eq_false t k b hb0 hb1]
  cases (winWitt (t + 1) (twopow k)).testBit (b + 1) <;>
    cases ((winWitt t (twopow k)).testBit b ||
      (winWitt t (twopow k)).testBit (b - 1)) <;>
    cases ((crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit b) <;> rfl

theorem winWitt_inward_step_gt_two_mul_prop (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k + twopow k) :
    wittBitBool (winWitt t (twopow k)) (b + 1) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) (b + 1))
        (bxor
          (wittBitBool (winWitt t (twopow k)) b ||
            wittBitBool (winWitt t (twopow k)) (b - 1))
          (wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k))) b)) :=
  winWitt_inward_step_gt_two_mul t k b hb0 hb1

/-- **Sideways Readout of the Left Column-`-1` Window Bit from Center and Right-Half Data (`winWitt_sector_one_one_from_center_and_right`)**:
    for all `t, k : Nat` with `t + 1 < 2^k`, inverting `winWitt_step_sector_one_center_slot` (`9.510`) expresses the left column-`-1` window bit `(winWitt t (2^k)).testBit (t + 1 + 2^k)` purely in terms of `(winWitt (t + 1) (2^k)).testBit ((t + 1) + 2^k)`, `(winWitt t (2^k)).testBit (t + 2^k)`, `(winWitt t (2^k)).testBit ((t + 2^k) - 1)`, `center t`, and `rhCenter t 1`! -/
theorem winWitt_sector_one_one_from_center_and_right (t k : Nat)
    (htk : t + 1 < twopow k) :
    (winWitt t (twopow k)).testBit (t + 1 + twopow k) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + 1) + twopow k))
        (bxor
          ((winWitt t (twopow k)).testBit (t + twopow k) ||
            (winWitt t (twopow k)).testBit ((t + twopow k) - 1))
          (bxor
            (Rule30UOR.Core.center t &&
              (winWitt t (twopow k)).testBit ((t + twopow k) - 1))
            ((winWitt t (twopow k)).testBit (t + twopow k) &&
              rhCenter t 1))) := by
  rw [winWitt_step_sector_one_center_slot t k htk]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit (t + 1 + twopow k) <;>
    cases ((winWitt t (twopow k)).testBit (t + twopow k) ||
      (winWitt t (twopow k)).testBit ((t + twopow k) - 1)) <;>
    cases ((Rule30UOR.Core.center t && (winWitt t (twopow k)).testBit ((t + twopow k) - 1)) ^^
      ((winWitt t (twopow k)).testBit (t + twopow k) && rhCenter t 1)) <;> rfl

theorem winWitt_sector_one_one_from_center_and_right_prop (t k : Nat)
    (htk : t + 1 < twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + 1 + twopow k) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + twopow k))
        (bxor
          (wittBitBool (winWitt t (twopow k)) (t + twopow k) ||
            wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))
          (bxor
            (Rule30UOR.Core.center t &&
              wittBitBool (winWitt t (twopow k)) ((t + twopow k) - 1))
            (wittBitBool (winWitt t (twopow k)) (t + twopow k) &&
              rhCenter t 1))) :=
  winWitt_sector_one_one_from_center_and_right t k htk

/-- **Sideways Outward Inversion of `winWitt` Across the Left Half of Sector 1 (`winWitt_inward_step_sector_one_lhCenter`)**:
    for all `t, k, p : Nat` with `t + p + 1 < 2^k`, solving `winWitt_step_sector_one_lhCenter` (`9.482`) for the outward bit `(winWitt t (2^k)).testBit (t + (p + 2) + 2^k)` expresses it in terms of `(winWitt (t + 1) (2^k)).testBit ((t + 1) + (p + 1) + 2^k)`, `winWitt t (2^k)` at `p, p + 1`, and `lhCenter t` at `p, p + 1`! -/
theorem winWitt_inward_step_sector_one_lhCenter (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    (winWitt t (twopow k)).testBit (t + (p + 2) + twopow k) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit ((t + 1) + (p + 1) + twopow k))
        (bxor
          ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) ||
            (winWitt t (twopow k)).testBit (t + p + twopow k))
          (bxor
            (lhCenter t (p + 1) &&
              (winWitt t (twopow k)).testBit (t + p + twopow k))
            ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) &&
              lhCenter t p))) := by
  have hs := winWitt_step_sector_one_lhCenter t k p hp
  have hphi := phi_testBit_add_two (winWitt t (twopow k)) (t + p + twopow k)
  rw [show (t + p + twopow k) + 2 = (t + 1) + (p + 1) + twopow k by omega,
    show (t + p + twopow k) + 1 = t + (p + 1) + twopow k by omega] at hphi
  rw [hs, hphi, show (t + 1) + (p + 1) + twopow k = t + (p + 2) + twopow k by omega]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit (t + (p + 2) + twopow k) <;>
    cases ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) ||
      (winWitt t (twopow k)).testBit (t + p + twopow k)) <;>
    cases ((lhCenter t (p + 1) && (winWitt t (twopow k)).testBit (t + p + twopow k)) ^^
      ((winWitt t (twopow k)).testBit (t + (p + 1) + twopow k) && lhCenter t p)) <;> rfl

theorem winWitt_inward_step_sector_one_lhCenter_prop (t k p : Nat)
    (hp : t + p + 1 < twopow k) :
    wittBitBool (winWitt t (twopow k)) (t + (p + 2) + twopow k) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) ((t + 1) + (p + 1) + twopow k))
        (bxor
          (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow k) ||
            wittBitBool (winWitt t (twopow k)) (t + p + twopow k))
          (bxor
            (lhCenter t (p + 1) &&
              wittBitBool (winWitt t (twopow k)) (t + p + twopow k))
            (wittBitBool (winWitt t (twopow k)) (t + (p + 1) + twopow k) &&
              lhCenter t p))) :=
  winWitt_inward_step_sector_one_lhCenter t k p hp

/-- **Sideways Inward Inversion of `winWitt` Across the Right Half of Sector 1 (`winWitt_inward_step_rhCenter_cone`)**:
    for all `t, k, p : Nat` with `t + p + 2 < 2^k` (no bound `p ≤ t` required!), solving `winWitt_step_rhCenter_cone` (`9.505`) at `p + 1` for the inward bit `(winWitt t (2^k)).testBit ((t + 2^k) - p)` expresses column `p` of the right-wing window from `(winWitt (t + 1) (2^k)).testBit (((t + 1) + 2^k) - (p + 1))` and columns `p + 1, p + 2` at time `t`! -/
theorem winWitt_inward_step_rhCenter_cone (t k p : Nat)
    (hp : t + p + 2 < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow k) - p) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit (((t + 1) + twopow k) - (p + 1)))
        (bxor
          ((winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)) ||
            (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 2)))
          (bxor
            (rhCenter t (p + 1) &&
              (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 2)))
            ((winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)) &&
              rhCenter t (p + 2)))) := by
  have hs := winWitt_step_rhCenter_cone t k (p + 1) (by omega)
  have hphi := phi_testBit_add_two (winWitt t (twopow k)) ((t + twopow k) - (p + 2))
  rw [show ((t + twopow k) - (p + 2)) + 2 = ((t + 1) + twopow k) - (p + 1) by omega,
    show ((t + twopow k) - (p + 2)) + 1 = (t + twopow k) - (p + 1) by omega] at hphi
  rw [hs, hphi,
    show (p + 1) + 1 = p + 2 by omega,
    show ((t + 1) + twopow k) - (p + 1) = (t + twopow k) - p by omega]
  simp only [bxor_eq_xor]
  cases (winWitt t (twopow k)).testBit ((t + twopow k) - p) <;>
    cases ((winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)) ||
      (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 2))) <;>
    cases ((rhCenter t (p + 1) && (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 2))) ^^
      ((winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)) && rhCenter t (p + 2))) <;> rfl

theorem winWitt_inward_step_rhCenter_cone_prop (t k p : Nat)
    (hp : t + p + 2 < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) (((t + 1) + twopow k) - (p + 1)))
        (bxor
          (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 1)) ||
            wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 2)))
          (bxor
            (rhCenter t (p + 1) &&
              wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 2)))
            (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 1)) &&
              rhCenter t (p + 2)))) :=
  winWitt_inward_step_rhCenter_cone t k p hp

/-- **Pure-`Φ` Sideways Inward Inversion of `winWitt` in the Right Inter-Cone Zero Gap (`winWitt_inward_step_zero_gap`)**:
    for all `t, k, p : Nat` with `t ≤ p` and `t + p + 2 < 2^k` (including `p = t`, right at the Sector-1 light-cone boundary `b = 2^k`!), both `rhCenter t (p + 1) = false` and `rhCenter t (p + 2) = false`, so `(winWitt t (2^k)).testBit ((t + 2^k) - p)` equals `(winWitt (t + 1) (2^k)).testBit (((t + 1) + 2^k) - (p + 1)) ⊕ ((winWitt t (2^k)).testBit ((t + 2^k) - (p + 1)) || (winWitt t (2^k)).testBit ((t + 2^k) - (p + 2)))`! -/
theorem winWitt_inward_step_zero_gap (t k p : Nat)
    (htp : t ≤ p) (hp : t + p + 2 < twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow k) - p) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit (((t + 1) + twopow k) - (p + 1)))
        ((winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)) ||
          (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 2))) := by
  rw [winWitt_inward_step_rhCenter_cone t k p hp,
    rhCenter_gt_eq_false t (p + 1) (by omega),
    rhCenter_gt_eq_false t (p + 2) (by omega),
    Bool.false_and, Bool.and_false]
  cases (winWitt (t + 1) (twopow k)).testBit (((t + 1) + twopow k) - (p + 1)) <;>
    cases ((winWitt t (twopow k)).testBit ((t + twopow k) - (p + 1)) ||
      (winWitt t (twopow k)).testBit ((t + twopow k) - (p + 2))) <;> rfl

theorem winWitt_inward_step_zero_gap_prop (t k p : Nat)
    (htp : t ≤ p) (hp : t + p + 2 < twopow k) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) (((t + 1) + twopow k) - (p + 1)))
        (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 1)) ||
          wittBitBool (winWitt t (twopow k)) ((t + twopow k) - (p + 2))) :=
  winWitt_inward_step_zero_gap t k p htp hp

/-- **Unconditional Forward Step of `WinWittAgree` in the Right Inter-Cone Zero Gap (`winWittAgree_step_zero_gap`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0` and `t + Q + p0 + L + 1 < 2^k`, `WinWittAgree t k Q ((t + 2^k) - (p0 + L + 1)) (L + 2)` steps forward to `WinWittAgree (t + 1) k Q (((t + 1) + 2^k) - (p0 + L)) L` with ZERO row or band hypotheses at time `t`! -/
theorem winWittAgree_step_zero_gap (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 1)) (L + 2)) :
    WinWittAgree (t + 1) k Q (((t + 1) + twopow k) - (p0 + L)) L :=
  winWittAgree_step_rhCenter_cone t k Q p0 L hp
    (rhBandAgree_outside_cone t Q p0 (L + 1) hp0) hw

/-- **Unconditional Inward Extension of `WinWittAgree` in the Right Inter-Cone Zero Gap (`winWittAgree_inward_step_zero_gap`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0` and `t + Q + p0 + L + 1 < 2^k`, `WinWittAgree t k Q ((t + 2^k) - (p0 + L + 1)) (L + 1)` and `WinWittAgree (t + 1) k Q (((t + 1) + 2^k) - (p0 + L)) L` extend `WinWittAgree` at time `t` inward to width `L + 2` with ZERO row or band hypotheses at time `t`! -/
theorem winWittAgree_inward_step_zero_gap (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 1)) (L + 1))
    (hnext : WinWittAgree (t + 1) k Q (((t + 1) + twopow k) - (p0 + L)) L) :
    WinWittAgree t k Q ((t + twopow k) - (p0 + L + 1)) (L + 2) :=
  winWittAgree_inward_step_rhCenter_cone t k Q p0 L hp
    (rhBandAgree_outside_cone t Q p0 (L + 1) hp0) hw hnext

/-- **Unconditional Forward Step of `WinWittAgree` in the Left Outer Cone Gap (`winWittAgree_step_lhCenter_zero_gap`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0` and `t + Q + p0 + L + 1 < 2^k`, `WinWittAgree t k Q (t + p0 + 2^k) (L + 2)` steps forward to `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^k) L` with ZERO row or band hypotheses at time `t`! -/
theorem winWittAgree_step_lhCenter_zero_gap (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hw : WinWittAgree t k Q (t + p0 + twopow k) (L + 2)) :
    WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow k) L :=
  winWittAgree_step_sector_one_lhCenter t k Q p0 L hp
    (lhBandAgree_outside_cone t Q p0 (L + 1) hp0) hw

/-- **Unconditional Outward Extension of `WinWittAgree` in the Left Outer Cone Gap (`winWittAgree_outward_step_lhCenter_zero_gap`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q < p0` and `t + Q + p0 + L + 1 < 2^k`, `WinWittAgree t k Q (t + p0 + 2^k) (L + 1)` and `WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + 2^k) L` extend `WinWittAgree` at time `t` outward to width `L + 2` with ZERO row or band hypotheses at time `t`! -/
theorem winWittAgree_outward_step_lhCenter_zero_gap (t k Q p0 L : Nat)
    (hp0 : t + Q < p0)
    (hp : t + Q + p0 + L + 1 < twopow k)
    (hw : WinWittAgree t k Q (t + p0 + twopow k) (L + 1))
    (hnext : WinWittAgree (t + 1) k Q ((t + 1) + (p0 + 1) + twopow k) L) :
    WinWittAgree t k Q (t + p0 + twopow k) (L + 2) :=
  winWittAgree_outward_step_sector_one_lhCenter t k Q p0 L hp
    (lhBandAgree_outside_cone t Q p0 (L + 1) hp0) hw hnext

/-- **Multi-Step Forward Propagation of Right-Wing `WinWittAgree` Across the Right Half (`winWittAgree_steps_rhCenter_cone`)**:
    for all `t, k, Q, p0, L, s : Nat` with `t + Q + p0 + L + 2 * s < 2^k`, `RhBandAgree t Q p0 (L + 2 * s)` and `WinWittAgree t k Q ((t + 2^k) - (p0 + L + 2 * s)) (L + 2 * s)` propagate forward across `s` steps to `WinWittAgree (t + s) k Q (((t + s) + 2^k) - ((p0 + s) + L)) L`! -/
theorem winWittAgree_steps_rhCenter_cone (t k Q p0 L s : Nat)
    (hp : t + Q + p0 + L + 2 * s < twopow k)
    (hb : RhBandAgree t Q p0 (L + 2 * s))
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 2 * s)) (L + 2 * s)) :
    WinWittAgree (t + s) k Q (((t + s) + twopow k) - ((p0 + s) + L)) L := by
  induction s generalizing t p0 L with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    rw [Nat.mul_zero, Nat.add_zero] at hw
    exact hw
  | succ s ih =>
    have hb1 : RhBandAgree (t + 1) Q (p0 + 1) (L + 2 * s) := by
      apply rhBandAgree_step t Q p0 (L + 2 * s)
      rwa [show (L + 2 * s) + 2 = L + 2 * (s + 1) by omega]
    have hb_sub : RhBandAgree t Q (p0 + 1) ((L + 2 * s) + 1) :=
      rhBandAgree_mono t Q p0 (L + 2 * (s + 1)) (p0 + 1) ((L + 2 * s) + 1) (by omega) (by omega) hb
    have hw_sub : WinWittAgree t k Q ((t + twopow k) - ((p0 + 1) + (L + 2 * s) + 1)) ((L + 2 * s) + 2) := by
      rwa [show (p0 + 1) + (L + 2 * s) + 1 = p0 + L + 2 * (s + 1) by omega,
        show (L + 2 * s) + 2 = L + 2 * (s + 1) by omega]
    have hw1 := winWittAgree_step_rhCenter_cone t k Q (p0 + 1) (L + 2 * s) (by omega) hb_sub hw_sub
    rw [show (p0 + 1) + (L + 2 * s) = (p0 + 1) + L + 2 * s by omega] at hw1
    have hih := ih (t + 1) (p0 + 1) L (by omega) hb1 hw1
    rwa [show (t + 1) + s = t + (s + 1) by omega,
      show (p0 + 1) + s = p0 + (s + 1) by omega] at hih

/-- **Multi-Step Propagation of Late `RhBandAgree ((t + s) + 2^k)` from Early `RhBandAgree` and `WinWittAgree` (`rhBandAgree_late_steps_cone`)**:
    for all `t, k, Q, p0, L, s : Nat` with `t + Q + p0 + L + 2 * s < 2^k`, `RhBandAgree t Q p0 (L + 2 * s)` and `WinWittAgree t k Q ((t + 2^k) - (p0 + L + 2 * s)) (L + 2 * s)` at time `t` imply late band agreement `RhBandAgree ((t + s) + 2^k) Q (p0 + s) L` at every shifted time `(t + s) + 2^k`! -/
theorem rhBandAgree_late_steps_cone (t k Q p0 L s : Nat)
    (hp : t + Q + p0 + L + 2 * s < twopow k)
    (hb : RhBandAgree t Q p0 (L + 2 * s))
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 2 * s)) (L + 2 * s)) :
    RhBandAgree ((t + s) + twopow k) Q (p0 + s) L := by
  have hbs := rhBandAgree_steps t Q p0 L s hb
  have hws := winWittAgree_steps_rhCenter_cone t k Q p0 L s hp hb hw
  exact rhBandAgree_scale_same_col_cone (t + s) k Q (p0 + s) L (by omega) hbs hws

/-- **Multi-Step Unconditional Forward Propagation of `WinWittAgree` in the Right Inter-Cone Zero Gap (`winWittAgree_steps_zero_gap`)**:
    for all `t, k, Q, p0, L, s : Nat` with `t + Q < p0` and `t + Q + p0 + L + 2 * s < 2^k`, `WinWittAgree t k Q ((t + 2^k) - (p0 + L + 2 * s)) (L + 2 * s)` propagates forward across `s` steps to `WinWittAgree (t + s) k Q (((t + s) + 2^k) - ((p0 + s) + L)) L` with ZERO row or band hypotheses! -/
theorem winWittAgree_steps_zero_gap (t k Q p0 L s : Nat)
    (hp0 : t + Q < p0)
    (hp : t + Q + p0 + L + 2 * s < twopow k)
    (hw : WinWittAgree t k Q ((t + twopow k) - (p0 + L + 2 * s)) (L + 2 * s)) :
    WinWittAgree (t + s) k Q (((t + s) + twopow k) - ((p0 + s) + L)) L :=
  winWittAgree_steps_rhCenter_cone t k Q p0 L s hp
    (rhBandAgree_outside_cone t Q p0 (L + 2 * s) hp0) hw

/-- **Multi-Step Forward Propagation of Sector-1 `WinWittAgree` Across the Left Half (`winWittAgree_steps_sector_one_lhCenter`)**:
    for all `t, k, Q, p0, L, s : Nat` with `t + Q + p0 + L + 2 * s < 2^k`, `LhBandAgree t Q p0 (L + 2 * s)` and `WinWittAgree t k Q (t + p0 + 2^k) (L + 2 * s)` propagate forward across `s` steps to `WinWittAgree (t + s) k Q ((t + s) + (p0 + s) + 2^k) L`! -/
theorem winWittAgree_steps_sector_one_lhCenter (t k Q p0 L s : Nat)
    (hp : t + Q + p0 + L + 2 * s < twopow k)
    (hb : LhBandAgree t Q p0 (L + 2 * s))
    (hw : WinWittAgree t k Q (t + p0 + twopow k) (L + 2 * s)) :
    WinWittAgree (t + s) k Q ((t + s) + (p0 + s) + twopow k) L := by
  induction s generalizing t p0 L with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    rw [Nat.mul_zero, Nat.add_zero] at hw
    exact hw
  | succ s ih =>
    have hb1 : LhBandAgree (t + 1) Q (p0 + 1) (L + 2 * s) := by
      apply lhBandAgree_step t Q p0 (L + 2 * s)
      rwa [show (L + 2 * s) + 2 = L + 2 * (s + 1) by omega]
    have hb_sub : LhBandAgree t Q p0 ((L + 2 * s) + 1) :=
      lhBandAgree_mono t Q p0 (L + 2 * (s + 1)) p0 ((L + 2 * s) + 1) (by omega) (by omega) hb
    have hw_sub : WinWittAgree t k Q (t + p0 + twopow k) ((L + 2 * s) + 2) := by
      rwa [show (L + 2 * s) + 2 = L + 2 * (s + 1) by omega]
    have hw1 := winWittAgree_step_sector_one_lhCenter t k Q p0 (L + 2 * s) (by omega) hb_sub hw_sub
    have hih := ih (t + 1) (p0 + 1) L (by omega) hb1 hw1
    rwa [show (t + 1) + s = t + (s + 1) by omega,
      show (p0 + 1) + s = p0 + (s + 1) by omega] at hih

/-- **Multi-Step Propagation of Late `LhBandAgree ((t + s) + 2^k)` from Early `LhBandAgree` and `WinWittAgree` (`lhBandAgree_late_steps_sector_one`)**:
    for all `t, k, Q, p0, L, s : Nat` with `t + Q + p0 + L + 2 * s < 2^k`, `LhBandAgree t Q p0 (L + 2 * s)` and `WinWittAgree t k Q (t + p0 + 2^k) (L + 2 * s)` at time `t` imply late band agreement `LhBandAgree ((t + s) + 2^k) Q (p0 + s) L` at every shifted time `(t + s) + 2^k`! -/
theorem lhBandAgree_late_steps_sector_one (t k Q p0 L s : Nat)
    (hp : t + Q + p0 + L + 2 * s < twopow k)
    (hb : LhBandAgree t Q p0 (L + 2 * s))
    (hw : WinWittAgree t k Q (t + p0 + twopow k) (L + 2 * s)) :
    LhBandAgree ((t + s) + twopow k) Q (p0 + s) L := by
  have hbs := lhBandAgree_steps t Q p0 L s hb
  have hws := winWittAgree_steps_sector_one_lhCenter t k Q p0 L s hp hb hw
  exact lhBandAgree_scale_same_col_cone (t + s) k Q (p0 + s) L (by omega) hbs hws

/-! ### Batch 16: Raw Inter-Cone Pure-`Φ` Window Evolution, Non-Overlapping 3-Sector Copy Laws of `phiScale`, and Early-Free Cross-Sector Window Duality -/

/-- **Vanishing of `phiScale k (row t)` Across the Raw Inter-Cone Gap (`phiScale_row_testBit_inter_cone_gap_eq_false`)**:
    for all `t, k, b : Nat` with `2 * t < b` and `b < 2^k`, bit `b` lies strictly above the Sector-0 light cone `2 * t` and strictly below the Sector-1 shift `2^k`, so `(phiScale k (row t)).testBit b = false`! -/
theorem phiScale_row_testBit_inter_cone_gap_eq_false (t k b : Nat)
    (hb0 : 2 * t < b) (hb1 : b < twopow k) :
    (phiScale k (row t)).testBit b = false := by
  have hu : (row t).testBit b = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t b hb0
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
    ((row t) <<< (twopow k + twopow k))).testBit b = false
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (b ≥ twopow k) = false := decide_eq_false (by omega)
  have d2 : decide (b ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [d1, d2, Bool.false_and, Bool.false_and, hu]
  rfl

theorem phiScale_row_testBit_inter_cone_gap_eq_false_prop (t k b : Nat)
    (hb0 : 2 * t < b) (hb1 : b < twopow k) :
    wittBitBool (phiScale k (row t)) b = false :=
  phiScale_row_testBit_inter_cone_gap_eq_false t k b hb0 hb1

/-- **Direct Readout of Late `row (t + 2^k)` Across the Raw Inter-Cone Gap (`winWitt_testBit_inter_cone_gap_eq_row_late`)**:
    for all `t, k, b : Nat` with `2 * t < b` and `b < 2^k`, because `(phiScale k (row t)).testBit b = false`, `(winWitt t (2^k)).testBit b` equals `(row (t + 2^k)).testBit b` directly! -/
theorem winWitt_testBit_inter_cone_gap_eq_row_late (t k b : Nat)
    (hb0 : 2 * t < b) (hb1 : b < twopow k) :
    (winWitt t (twopow k)).testBit b = (row (t + twopow k)).testBit b := by
  have hsc := congrArg (fun n => n.testBit b) (row_scale t k)
  rw [Nat.testBit_xor,
    phiScale_row_testBit_inter_cone_gap_eq_false t k b hb0 hb1,
    Bool.false_xor] at hsc
  exact hsc.symm

theorem winWitt_testBit_inter_cone_gap_eq_row_late_prop (t k b : Nat)
    (hb0 : 2 * t < b) (hb1 : b < twopow k) :
    wittBitBool (winWitt t (twopow k)) b =
      wittBitBool (row (t + twopow k)) b :=
  winWitt_testBit_inter_cone_gap_eq_row_late t k b hb0 hb1

/-- **Vanishing of `crossCarry` Across the Raw Inter-Cone Gap (`crossCarry_row_scale_inter_cone_gap_eq_false`)**:
    for all `t, k, b : Nat` with `2 * t + 1 < b` and `b < 2^k`, both `b` and `b - 1` lie in the inter-cone gap `(2 * t, 2^k)` where `phiScale k (row t)` vanishes, so `(crossCarry (phiScale k (row t)) (winWitt t (2^k))).testBit b = false`! -/
theorem crossCarry_row_scale_inter_cone_gap_eq_false (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k) :
    (crossCarry (phiScale k (row t)) (winWitt t (twopow k))).testBit b = false := by
  have hc := crossCarry_testBit_succ (phiScale k (row t)) (winWitt t (twopow k)) (b - 1)
  rw [show (b - 1) + 1 = b by omega] at hc
  rw [hc,
    phiScale_row_testBit_inter_cone_gap_eq_false t k b (by omega) hb1,
    phiScale_row_testBit_inter_cone_gap_eq_false t k (b - 1) (by omega) (by omega),
    Bool.false_and, Bool.and_false]
  rfl

theorem crossCarry_row_scale_inter_cone_gap_eq_false_prop (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k) :
    wittBitBool (crossCarry (phiScale k (row t)) (winWitt t (twopow k))) b = false :=
  crossCarry_row_scale_inter_cone_gap_eq_false t k b hb0 hb1

/-- **Pure-`Φ` Forward Step of `winWitt` Across the Raw Inter-Cone Gap (`winWitt_step_inter_cone_gap_eq_phi`)**:
    for all `t, k, b : Nat` with `2 * t + 1 < b` and `b < 2^k` (including `b = 2^k - 1`, where `b + 1 = 2^k` is the exact Sector-1 boundary bit!), both `crossCarry` and `frobDefect` vanish at bit `b`, so `(winWitt (t + 1) (2^k)).testBit (b + 1) = (phi (winWitt t (2^k))).testBit (b + 1)`! -/
theorem winWitt_step_inter_cone_gap_eq_phi (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k) :
    (winWitt (t + 1) (twopow k)).testBit (b + 1) =
      (phi (winWitt t (twopow k))).testBit (b + 1) := by
  rw [winWitt_step_frobDefect_testBit_succ t k b,
    crossCarry_row_scale_inter_cone_gap_eq_false t k b hb0 hb1,
    frobDefect_row_testBit_gt_two_mul_eq_false t k b hb0 (by omega)]
  cases (phi (winWitt t (twopow k))).testBit (b + 1) <;> rfl

theorem winWitt_step_inter_cone_gap_eq_phi_prop (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k) :
    wittBitBool (winWitt (t + 1) (twopow k)) (b + 1) =
      wittBitBool (phi (winWitt t (twopow k))) (b + 1) :=
  winWitt_step_inter_cone_gap_eq_phi t k b hb0 hb1

/-- **Pure-`Φ` Sideways Inversion of `winWitt` Across the Raw Inter-Cone Gap (`winWitt_inward_step_inter_cone_gap`)**:
    for all `t, k, b : Nat` with `2 * t + 1 < b` and `b < 2^k`, `(winWitt t (2^k)).testBit (b + 1)` equals `(winWitt (t + 1) (2^k)).testBit (b + 1) ⊕ ((winWitt t (2^k)).testBit b || (winWitt t (2^k)).testBit (b - 1))`! -/
theorem winWitt_inward_step_inter_cone_gap (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k) :
    (winWitt t (twopow k)).testBit (b + 1) =
      bxor
        ((winWitt (t + 1) (twopow k)).testBit (b + 1))
        ((winWitt t (twopow k)).testBit b ||
          (winWitt t (twopow k)).testBit (b - 1)) := by
  rw [winWitt_inward_step_gt_two_mul t k b hb0 (by omega),
    crossCarry_row_scale_inter_cone_gap_eq_false t k b hb0 hb1]
  cases (winWitt (t + 1) (twopow k)).testBit (b + 1) <;>
    cases ((winWitt t (twopow k)).testBit b ||
      (winWitt t (twopow k)).testBit (b - 1)) <;> rfl

theorem winWitt_inward_step_inter_cone_gap_prop (t k b : Nat)
    (hb0 : 2 * t + 1 < b) (hb1 : b < twopow k) :
    wittBitBool (winWitt t (twopow k)) (b + 1) =
      bxor
        (wittBitBool (winWitt (t + 1) (twopow k)) (b + 1))
        (wittBitBool (winWitt t (twopow k)) b ||
          wittBitBool (winWitt t (twopow k)) (b - 1)) :=
  winWitt_inward_step_inter_cone_gap t k b hb0 hb1

/-- **Non-Overlapping Sector-1 Copy Law of `phiScale k (row t)` (`phiScale_row_testBit_sector_one_eq_row`)**:
    for all `t, k, d : Nat` with `2 * t < 2^k` and `d < 2^k`, Sector 1 of `phiScale k (row t)` is an exact bit-for-bit shifted copy of `row t`: `(phiScale k (row t)).testBit (d + 2^k) = (row t).testBit d`! -/
theorem phiScale_row_testBit_sector_one_eq_row (t k d : Nat)
    (htk : 2 * t < twopow k) (hd : d < twopow k) :
    (phiScale k (row t)).testBit (d + twopow k) = (row t).testBit d := by
  have hu : (row t).testBit (d + twopow k) = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t (d + twopow k) (by omega)
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
    ((row t) <<< (twopow k + twopow k))).testBit (d + twopow k) = (row t).testBit d
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (d + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (d + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [d1, d2, Bool.true_and, Bool.false_and,
    hu,
    show (d + twopow k) - twopow k = d by omega]
  cases (row t).testBit d <;> rfl

theorem phiScale_row_testBit_sector_one_eq_row_prop (t k d : Nat)
    (htk : 2 * t < twopow k) (hd : d < twopow k) :
    wittBitBool (phiScale k (row t)) (d + twopow k) =
      wittBitBool (row t) d :=
  phiScale_row_testBit_sector_one_eq_row t k d htk hd

/-- **Non-Overlapping Sector-2 Copy Law of `phiScale k (row t)` (`phiScale_row_testBit_sector_two_eq_row`)**:
    for all `t, k, d : Nat` with `2 * t < 2^k` (for ALL `d : Nat`, with no bound `d < 2^k` required!), Sector 2 of `phiScale k (row t)` is an exact bit-for-bit shifted copy of `row t`: `(phiScale k (row t)).testBit (d + 2^(k+1)) = (row t).testBit d`! -/
theorem phiScale_row_testBit_sector_two_eq_row (t k d : Nat)
    (htk : 2 * t < twopow k) :
    (phiScale k (row t)).testBit (d + twopow (k + 1)) = (row t).testBit d := by
  have hstep_k : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hu2 : (row t).testBit (d + twopow (k + 1)) = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t (d + twopow (k + 1)) (by omega)
  have hu1 : (row t).testBit (d + twopow k) = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t (d + twopow k) (by omega)
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^
    ((row t) <<< (twopow k + twopow k))).testBit (d + twopow (k + 1)) = (row t).testBit d
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (d + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (d + twopow (k + 1) ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [d1, d2, Bool.true_and, Bool.true_and,
    hu2,
    show (d + twopow (k + 1)) - twopow k = d + twopow k by omega,
    hu1,
    show (d + twopow (k + 1)) - (twopow k + twopow k) = d by omega]
  cases (row t).testBit d <;> rfl

theorem phiScale_row_testBit_sector_two_eq_row_prop (t k d : Nat)
    (htk : 2 * t < twopow k) :
    wittBitBool (phiScale k (row t)) (d + twopow (k + 1)) =
      wittBitBool (row t) d :=
  phiScale_row_testBit_sector_two_eq_row t k d htk

/-- **Non-Overlapping Sector-1 Bit Readout of `winWitt t (2^k)` (`winWitt_testBit_sector_one_eq_row_xor`)**:
    for all `t, k, d : Nat` with `2 * t < 2^k` and `d < 2^k`, `(winWitt t (2^k)).testBit (d + 2^k) = (row (t + 2^k)).testBit (d + 2^k) ⊕ (row t).testBit d`! -/
theorem winWitt_testBit_sector_one_eq_row_xor (t k d : Nat)
    (htk : 2 * t < twopow k) (hd : d < twopow k) :
    (winWitt t (twopow k)).testBit (d + twopow k) =
      bxor ((row (t + twopow k)).testBit (d + twopow k)) ((row t).testBit d) := by
  have hsc := congrArg (fun n => n.testBit (d + twopow k)) (row_scale t k)
  rw [Nat.testBit_xor,
    phiScale_row_testBit_sector_one_eq_row t k d htk hd] at hsc
  rw [hsc]
  simp only [bxor_eq_xor]
  cases (row t).testBit d <;>
    cases (winWitt t (twopow k)).testBit (d + twopow k) <;> rfl

theorem winWitt_testBit_sector_one_eq_row_xor_prop (t k d : Nat)
    (htk : 2 * t < twopow k) (hd : d < twopow k) :
    wittBitBool (winWitt t (twopow k)) (d + twopow k) =
      bxor (wittBitBool (row (t + twopow k)) (d + twopow k))
        (wittBitBool (row t) d) :=
  winWitt_testBit_sector_one_eq_row_xor t k d htk hd

/-- **Non-Overlapping Sector-2 Bit Readout of `winWitt t (2^k)` (`winWitt_testBit_sector_two_eq_row_xor`)**:
    for all `t, k, d : Nat` with `2 * t < 2^k` (for ALL `d : Nat`), `(winWitt t (2^k)).testBit (d + 2^(k+1)) = (row (t + 2^k)).testBit (d + 2^(k+1)) ⊕ (row t).testBit d`! -/
theorem winWitt_testBit_sector_two_eq_row_xor (t k d : Nat)
    (htk : 2 * t < twopow k) :
    (winWitt t (twopow k)).testBit (d + twopow (k + 1)) =
      bxor ((row (t + twopow k)).testBit (d + twopow (k + 1))) ((row t).testBit d) := by
  have hsc := congrArg (fun n => n.testBit (d + twopow (k + 1))) (row_scale t k)
  rw [Nat.testBit_xor,
    phiScale_row_testBit_sector_two_eq_row t k d htk] at hsc
  rw [hsc]
  simp only [bxor_eq_xor]
  cases (row t).testBit d <;>
    cases (winWitt t (twopow k)).testBit (d + twopow (k + 1)) <;> rfl

theorem winWitt_testBit_sector_two_eq_row_xor_prop (t k d : Nat)
    (htk : 2 * t < twopow k) :
    wittBitBool (winWitt t (twopow k)) (d + twopow (k + 1)) =
      bxor (wittBitBool (row (t + twopow k)) (d + twopow (k + 1)))
        (wittBitBool (row t) d) :=
  winWitt_testBit_sector_two_eq_row_xor t k d htk

/-- **Early-Free Right-to-Left Cross-Sector Window Duality (`winWitt_sector_one_xor_sector_two_rhCenter_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k`, the common early term `rhCenter t p` in `winWitt_testBit_rhCenter_same_col_cone` (`9.491`) and `winWitt_testBit_scale_cross_cone` (`9.458`) cancels identically under XOR, equating `(winWitt t (2^k)).testBit ((t + 2^k) - p) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - p)` directly to the late-only pair `rhCenter (t + 2^k) p ⊕ lhCenter (t + 2^k) (2^k - p)`! -/
theorem winWitt_sector_one_xor_sector_two_rhCenter_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow k) - p))
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - p)) =
      bxor
        (rhCenter (t + twopow k) p)
        (lhCenter (t + twopow k) (twopow k - p)) := by
  rw [winWitt_testBit_rhCenter_same_col_cone t k p hp,
    winWitt_testBit_scale_cross_cone t k p hp]
  cases rhCenter (t + twopow k) p <;>
    cases lhCenter (t + twopow k) (twopow k - p) <;>
    cases rhCenter t p <;> rfl

theorem winWitt_sector_one_xor_sector_two_rhCenter_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - p))
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - p)) =
      bxor
        (rhCenter (t + twopow k) p)
        (lhCenter (t + twopow k) (twopow k - p)) :=
  winWitt_sector_one_xor_sector_two_rhCenter_cone t k p hp

/-- **Early-Free Left-to-Left Cross-Sector Window Duality (`winWitt_sector_one_xor_sector_two_lhCenter_cone`)**:
    for all `t, k, p : Nat` with `t + p < 2^k`, the common early term `lhCenter t p` in `winWitt_testBit_sector_one_lhCenter` (`9.475`) and `winWitt_testBit_outer_left_strip` (`9.434`) cancels identically under XOR, equating `(winWitt t (2^k)).testBit (t + p + 2^k) ⊕ (winWitt t (2^k)).testBit (t + p + 2^(k+1))` directly to the late-only pair `lhCenter (t + 2^k) p ⊕ lhCenter (t + 2^k) (p + 2^k)`! -/
theorem winWitt_sector_one_xor_sector_two_lhCenter_cone (t k p : Nat)
    (hp : t + p < twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit (t + p + twopow k))
      ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) =
      bxor
        (lhCenter (t + twopow k) p)
        (lhCenter (t + twopow k) (p + twopow k)) := by
  rw [winWitt_testBit_sector_one_lhCenter t k p hp,
    winWitt_testBit_outer_left_strip t k p (by omega)]
  cases lhCenter (t + twopow k) p <;>
    cases lhCenter (t + twopow k) (p + twopow k) <;>
    cases lhCenter t p <;> rfl

theorem winWitt_sector_one_xor_sector_two_lhCenter_cone_prop (t k p : Nat)
    (hp : t + p < twopow k) :
    bxor
      (wittBitBool (winWitt t (twopow k)) (t + p + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) =
      bxor
        (lhCenter (t + twopow k) p)
        (lhCenter (t + twopow k) (p + twopow k)) :=
  winWitt_sector_one_xor_sector_two_lhCenter_cone t k p hp

/-- **Early-Free `$2^k$`-Spatial Shift of Late `LhBandAgree (t + 2^k)` via Cross-Sector `WinWittAgree` (`lhBandAgree_late_shift_of_winWittAgree_sectors`)**:
    for all `t, k, Q, p0, L : Nat` with `t + Q + p0 + L < 2^k`, `LhBandAgree (t + 2^k) Q p0 L`, `WinWittAgree t k Q (t + p0 + 2^k) L`, and `WinWittAgree t k Q (t + p0 + 2^(k+1)) L` imply `LhBandAgree (t + 2^k) Q (p0 + 2^k) L` with ZERO band hypotheses at time `t`! -/
theorem lhBandAgree_late_shift_of_winWittAgree_sectors (t k Q p0 L : Nat)
    (hp : t + Q + p0 + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q p0 L)
    (hw1 : WinWittAgree t k Q (t + p0 + twopow k) L)
    (hw2 : WinWittAgree t k Q (t + p0 + twopow (k + 1)) L) :
    LhBandAgree (t + twopow k) Q (p0 + twopow k) L := by
  have h0 := lhBandAgree_scale_inward_same_col_cone t k Q p0 L hp hlate hw1
  exact lhBandAgree_scale_step_outer_strip t k Q p0 L (by omega) h0 hw2

/-- **Early-Free Cross-Center Transfer from Late `LhBandAgree (t + 2^k)` to Late `RhBandAgree (t + 2^k)` via Cross-Sector `WinWittAgree` (`rhBandAgree_late_of_lhBandAgree_late_and_winWittAgree_sectors`)**:
    for all `t, k, Q, L : Nat` with `t + Q + L < 2^k`, `LhBandAgree (t + 2^k) Q (2^k - L) L`, `WinWittAgree t k Q ((t + 2^k) - L) L`, and `WinWittAgree t k Q ((t + 2^(k+1)) - L) L` imply `RhBandAgree (t + 2^k) Q 0 L` with ZERO band hypotheses at time `t`! -/
theorem rhBandAgree_late_of_lhBandAgree_late_and_winWittAgree_sectors (t k Q L : Nat)
    (hp : t + Q + L < twopow k)
    (hlate : LhBandAgree (t + twopow k) Q (twopow k - L) L)
    (hw1 : WinWittAgree t k Q ((t + twopow k) - L) L)
    (hw2 : WinWittAgree t k Q ((t + twopow (k + 1)) - L) L) :
    RhBandAgree (t + twopow k) Q 0 L := by
  have h0 := rhBandAgree_of_lhBandAgree_and_winWittAgree_cross_cone t k Q L hp hlate hw2
  have hw1_0 : WinWittAgree t k Q ((t + twopow k) - (0 + L)) L := by
    rwa [Nat.zero_add]
  exact rhBandAgree_scale_same_col_cone t k Q 0 L (by omega) h0 hw1_0

/-- **Exact Sector-1 Boundary Bit Readout `(winWitt t (2^k)).testBit (2^k) = !rhCenter (t + 2^k) t` (`winWitt_testBit_twopow_eq_not_rhCenter_late`)**:
    for all `t, k : Nat` with `2 * t < 2^k`, evaluating `winWitt_testBit_rhCenter_same_col_cone` at the right light-cone boundary `p = t` (`(t + 2^k) - t = 2^k`, `rhCenter t t = true`) proves that bit `2^k` of `winWitt t (2^k)` is the exact negation of `rhCenter (t + 2^k) t`! -/
theorem winWitt_testBit_twopow_eq_not_rhCenter_late (t k : Nat)
    (htk : 2 * t < twopow k) :
    (winWitt t (twopow k)).testBit (twopow k) =
      !rhCenter (t + twopow k) t := by
  have hw := winWitt_testBit_rhCenter_same_col_cone t k t (by omega)
  rw [show (t + twopow k) - t = twopow k by omega,
    rhCenter_self_eq_true t] at hw
  rw [hw]
  cases rhCenter (t + twopow k) t <;> rfl

theorem winWitt_testBit_twopow_eq_not_rhCenter_late_prop (t k : Nat)
    (htk : 2 * t < twopow k) :
    wittBitBool (winWitt t (twopow k)) (twopow k) =
      !rhCenter (t + twopow k) t :=
  winWitt_testBit_twopow_eq_not_rhCenter_late t k htk

/-- **Pure-`Φ` Recurrence of Late `rhCenter (t + 2^k) t` Along the Sector-1 Boundary (`rhCenter_late_self_from_zero_gap_step`)**:
    for all `t, k : Nat` with `2 * t + 2 < 2^k`, combining `winWitt_inward_step_zero_gap` at `p = t` (`9.522`), `winWitt_testBit_twopow_eq_not_rhCenter_late` (`9.545`), and `winWitt_testBit_zero_gap_eq_rhCenter_late` (`9.492`) at `p = t + 1, t + 2` expresses `rhCenter (t + 2^k) t` directly from `rhCenter ((t + 1) + 2^k) (t + 1)` and `rhCenter (t + 2^k) (t + 1) || rhCenter (t + 2^k) (t + 2)`! -/
theorem rhCenter_late_self_from_zero_gap_step (t k : Nat)
    (htk : 2 * t + 2 < twopow k) :
    rhCenter (t + twopow k) t =
      bxor
        (rhCenter ((t + 1) + twopow k) (t + 1))
        (rhCenter (t + twopow k) (t + 1) ||
          rhCenter (t + twopow k) (t + 2)) := by
  have hs := winWitt_inward_step_zero_gap t k t (Nat.le_refl t) (by omega)
  have hw0 := winWitt_testBit_twopow_eq_not_rhCenter_late t k (by omega)
  have hw1 := winWitt_testBit_twopow_eq_not_rhCenter_late (t + 1) k (by omega)
  have hg1 := winWitt_testBit_zero_gap_eq_rhCenter_late t k (t + 1) (by omega) (by omega)
  have hg2 := winWitt_testBit_zero_gap_eq_rhCenter_late t k (t + 2) (by omega) (by omega)
  rw [show (t + twopow k) - t = twopow k by omega,
    show ((t + 1) + twopow k) - (t + 1) = twopow k by omega] at hs
  rw [hw0, hw1, hg1, hg2] at hs
  revert hs
  simp only [bxor_eq_xor]
  cases rhCenter (t + twopow k) t <;>
    cases rhCenter ((t + 1) + twopow k) (t + 1) <;>
    cases (rhCenter (t + twopow k) (t + 1) || rhCenter (t + twopow k) (t + 2)) <;> decide

/-! ### Batch 17: Scale-Independent Left-Diagonal Coordinates at `t + 2^k`, Zero-State Center Cross-Sector Readout, and Zero-Diagonal Window Mirrors -/

/-- **Scale-Independent Left-Diagonal Coordinate of `lhCenter (t + 2^k) (p + 2^k)` (`lhCenter_late_shift_eq_ldiag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, the late shifted left-half cell `lhCenter (t + 2^k) (p + 2^k)` lies on left diagonal `t - p` (independent of `k`!): `lhCenter (t + 2^k) (p + 2^k) = ldiag (t - p) (t + 2^k)`! -/
theorem lhCenter_late_shift_eq_ldiag (t k p : Nat) (hp : p ≤ t) :
    lhCenter (t + twopow k) (p + twopow k) =
      ldiag (t - p) (t + twopow k) := by
  rw [lhCenter_eq_ldiag (t + twopow k) (p + twopow k) (by omega),
    show (t + twopow k) - (p + twopow k) = t - p by omega]

/-- **Scale-Independent Left-Diagonal Coordinate of `lhCenter (t + 2^k) (2^k - r)` (`lhCenter_late_cross_eq_ldiag`)**:
    for all `t, k, r : Nat` with `r ≤ 2^k`, the late cross-center cell `lhCenter (t + 2^k) (2^k - r)` lies on left diagonal `t + r` (independent of `k`!): `lhCenter (t + 2^k) (2^k - r) = ldiag (t + r) (t + 2^k)`! -/
theorem lhCenter_late_cross_eq_ldiag (t k r : Nat) (hr : r ≤ twopow k) :
    lhCenter (t + twopow k) (twopow k - r) =
      ldiag (t + r) (t + twopow k) := by
  rw [lhCenter_eq_ldiag (t + twopow k) (twopow k - r) (by omega),
    show (t + twopow k) - (twopow k - r) = t + r by omega]

/-- **Direct Settled Readout of `zcenter t` at `lhCenter (t + 2^k) (2^k)` (`lhCenter_late_twopow_eq_zcenter`)**:
    for all `t, k : Nat` with `t ≤ k` and `settle t ≤ t + 2^k` (`SettledAt t k`), the late cell `lhCenter (t + 2^k) (2^k)` equals the zero-state center `zcenter t`! -/
theorem lhCenter_late_twopow_eq_zcenter (t k : Nat)
    (hk : t ≤ k) (hset : settle t ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k) = zcenter t := by
  have h0 := lhCenter_late_shift_eq_ldiag t k 0 (Nat.zero_le t)
  rw [Nat.zero_add, Nat.sub_zero] at h0
  rw [h0, ldiag_settled_eq_zcenter t k hk hset]

theorem lhCenter_late_twopow_eq_zcenter_prop (t k : Nat)
    (hk : t ≤ k) (hset : SettledAt t k) :
    ZCenterEq t (lhCenter (t + twopow k) (twopow k)) :=
  (lhCenter_late_twopow_eq_zcenter t k hk hset).symm

/-- **Settled Sector-2 Center-Slot Window Readout of `zcenter t` (`winWitt_testBit_sector_two_center_slot_zcenter`)**:
    for all `t, k : Nat` with `t ≤ k` and `settle t ≤ t + 2^k` (`SettledAt t k`), `zcenter t = (winWitt t (2^k)).testBit (t + 2^(k+1)) ⊕ center t`! -/
theorem winWitt_testBit_sector_two_center_slot_zcenter (t k : Nat)
    (hk : t ≤ k) (hset : settle t ≤ t + twopow k) :
    zcenter t =
      bxor
        ((winWitt t (twopow k)).testBit (t + twopow (k + 1)))
        (Rule30UOR.Core.center t) := by
  have htk : t < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hw := winWitt_testBit_outer_left_strip t k 0 (by omega)
  rw [Nat.add_zero, Nat.zero_add,
    lhCenter_late_twopow_eq_zcenter t k hk hset,
    lhCenter_zero_eq_center t] at hw
  rw [hw]
  cases zcenter t <;> cases Rule30UOR.Core.center t <;> rfl

theorem winWitt_testBit_sector_two_center_slot_zcenter_prop (t k : Nat)
    (hk : t ≤ k) (hset : SettledAt t k) :
    ZCenterEq t
      (bxor
        (wittBitBool (winWitt t (twopow k)) (t + twopow (k + 1)))
        (Rule30UOR.Core.center t)) :=
  winWitt_testBit_sector_two_center_slot_zcenter t k hk hset

/-- **Early-Free Cross-Sector Window Readout of `zcenter t` (`winWitt_sector_one_xor_sector_two_center_slot_zcenter`)**:
    for all `t, k : Nat` with `t ≤ k` and `settle t ≤ t + 2^k` (`SettledAt t k`), evaluating `winWitt_sector_one_xor_sector_two_lhCenter_cone` at `p = 0` expresses `zcenter t` purely in terms of the late center `center (t + 2^k)` and the Sector-1 and Sector-2 center-slot bits of `winWitt t (2^k)`! -/
theorem winWitt_sector_one_xor_sector_two_center_slot_zcenter (t k : Nat)
    (hk : t ≤ k) (hset : settle t ≤ t + twopow k) :
    zcenter t =
      bxor
        (Rule30UOR.Core.center (t + twopow k))
        (bxor
          ((winWitt t (twopow k)).testBit (t + twopow k))
          ((winWitt t (twopow k)).testBit (t + twopow (k + 1)))) := by
  have htk : t < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hd := winWitt_sector_one_xor_sector_two_lhCenter_cone t k 0 (by omega)
  rw [Nat.add_zero, Nat.zero_add,
    lhCenter_zero_eq_center (t + twopow k),
    lhCenter_late_twopow_eq_zcenter t k hk hset] at hd
  revert hd
  simp only [bxor_eq_xor]
  cases zcenter t <;>
    cases Rule30UOR.Core.center (t + twopow k) <;>
    cases ((winWitt t (twopow k)).testBit (t + twopow k) ^^
      (winWitt t (twopow k)).testBit (t + twopow (k + 1))) <;> decide

theorem winWitt_sector_one_xor_sector_two_center_slot_zcenter_prop (t k : Nat)
    (hk : t ≤ k) (hset : SettledAt t k) :
    ZCenterEq t
      (bxor
        (Rule30UOR.Core.center (t + twopow k))
        (bxor
          (wittBitBool (winWitt t (twopow k)) (t + twopow k))
          (wittBitBool (winWitt t (twopow k)) (t + twopow (k + 1))))) :=
  winWitt_sector_one_xor_sector_two_center_slot_zcenter t k hk hset

/-- **Exact Late Left-Half Vanishing Along Any Zero Diagonal (`lhCenter_late_shift_of_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `t - p ≤ k`, `IsZeroDiag (t - p)`, and `settle (t - p) ≤ t + 2^k` (`SettledBy (t - p) (t + 2^k)`), the late shifted cell `lhCenter (t + 2^k) (p + 2^k)` vanishes identically! -/
theorem lhCenter_late_shift_of_zero_diag (t k p : Nat)
    (hp : p ≤ t) (hk : t - p ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle (t - p) ≤ t + twopow k) :
    lhCenter (t + twopow k) (p + twopow k) = false := by
  rw [lhCenter_late_shift_eq_ldiag t k p hp,
    ldiag_settled_eq_E (t - p) t k hk hset,
    hz t]

theorem lhCenter_late_shift_of_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (hk : t - p ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy (t - p) (t + twopow k)) :
    lhCenter (t + twopow k) (p + twopow k) = false :=
  lhCenter_late_shift_of_zero_diag t k p hp hk hz hset

/-- **Exact Late Cross-Center Vanishing Along Any Zero Diagonal (`lhCenter_late_cross_of_zero_diag`)**:
    for all `t, k, r : Nat` with `t + r ≤ k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k` (`SettledBy (t + r) (t + 2^k)`), the late cross-center cell `lhCenter (t + 2^k) (2^k - r)` vanishes identically! -/
theorem lhCenter_late_cross_of_zero_diag (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    lhCenter (t + twopow k) (twopow k - r) = false := by
  have hrk : r ≤ twopow k := by
    have := twopow_gt_self k
    omega
  rw [lhCenter_late_cross_eq_ldiag t k r hrk,
    ldiag_settled_eq_E (t + r) t k hk hset,
    hz t]

theorem lhCenter_late_cross_of_zero_diag_prop (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    lhCenter (t + twopow k) (twopow k - r) = false :=
  lhCenter_late_cross_of_zero_diag t k r hk hz hset

/-- **Direct Readout of Early `lhCenter t p` from Sector-2 `winWitt` Along a Zero Diagonal (`winWitt_testBit_outer_left_strip_of_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `t - p ≤ k`, `IsZeroDiag (t - p)`, and `settle (t - p) ≤ t + 2^k`, because `lhCenter (t + 2^k) (p + 2^k) = false`, the Sector-2 window bit `(winWitt t (2^k)).testBit (t + p + 2^(k+1))` equals `lhCenter t p` directly (even before diagonal `t - p` has settled at time `t`!)! -/
theorem winWitt_testBit_outer_left_strip_of_zero_diag (t k p : Nat)
    (hp : p ≤ t) (hk : t - p ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle (t - p) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit (t + p + twopow (k + 1)) =
      lhCenter t p := by
  have hlt : t < p + twopow k := by
    have := twopow_gt_self k
    omega
  rw [winWitt_testBit_outer_left_strip t k p hlt,
    lhCenter_late_shift_of_zero_diag t k p hp hk hz hset]
  cases lhCenter t p <;> rfl

theorem winWitt_testBit_outer_left_strip_of_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (hk : t - p ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy (t - p) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1)) =
      lhCenter t p :=
  winWitt_testBit_outer_left_strip_of_zero_diag t k p hp hk hz hset

/-- **Direct Readout of Early `rhCenter t r` from Sector-2 `winWitt` Along a Zero Diagonal (`winWitt_testBit_scale_cross_of_zero_diag`)**:
    for all `t, k, r : Nat` with `t + r ≤ k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k`, because `lhCenter (t + 2^k) (2^k - r) = false`, the Sector-2 cross-center window bit `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r)` equals `rhCenter t r` directly! -/
theorem winWitt_testBit_scale_cross_of_zero_diag (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) =
      rhCenter t r := by
  have hlt : t + r < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  rw [winWitt_testBit_scale_cross_cone t k r hlt,
    lhCenter_late_cross_of_zero_diag t k r hk hz hset]
  cases rhCenter t r <;> rfl

theorem winWitt_testBit_scale_cross_of_zero_diag_prop (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) =
      rhCenter t r :=
  winWitt_testBit_scale_cross_of_zero_diag t k r hk hz hset

/-- **Exact Vanishing of Sector-2 Cross-Center `winWitt` in the Inter-Cone Zero Gap Along a Zero Diagonal (`winWitt_testBit_scale_cross_zero_gap_of_zero_diag`)**:
    for all `t, k, r : Nat` with `t < r`, `t + r ≤ k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k`, both `lhCenter (t + 2^k) (2^k - r) = false` and `rhCenter t r = false`, so `(winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = false`! -/
theorem winWitt_testBit_scale_cross_zero_gap_of_zero_diag (t k r : Nat)
    (htr : t < r) (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    (winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r) = false := by
  rw [winWitt_testBit_scale_cross_of_zero_diag t k r hk hz hset,
    rhCenter_gt_eq_false t r htr]

theorem winWitt_testBit_scale_cross_zero_gap_of_zero_diag_prop (t k r : Nat)
    (htr : t < r) (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r) = false :=
  winWitt_testBit_scale_cross_zero_gap_of_zero_diag t k r htr hk hz hset

/-- **Direct Cross-Sector Window Readout of Late `lhCenter (t + 2^k) p` Along a Zero Diagonal (`winWitt_sector_one_xor_sector_two_lhCenter_of_zero_diag`)**:
    for all `t, k, p : Nat` with `p ≤ t`, `t + p < 2^k`, `t - p ≤ k`, `IsZeroDiag (t - p)`, and `settle (t - p) ≤ t + 2^k`, `(winWitt t (2^k)).testBit (t + p + 2^k) ⊕ (winWitt t (2^k)).testBit (t + p + 2^(k+1)) = lhCenter (t + 2^k) p` directly! -/
theorem winWitt_sector_one_xor_sector_two_lhCenter_of_zero_diag (t k p : Nat)
    (hp : p ≤ t) (htp : t + p < twopow k) (hk : t - p ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : settle (t - p) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit (t + p + twopow k))
      ((winWitt t (twopow k)).testBit (t + p + twopow (k + 1))) =
      lhCenter (t + twopow k) p := by
  rw [winWitt_sector_one_xor_sector_two_lhCenter_cone t k p htp,
    lhCenter_late_shift_of_zero_diag t k p hp hk hz hset]
  cases lhCenter (t + twopow k) p <;> rfl

theorem winWitt_sector_one_xor_sector_two_lhCenter_of_zero_diag_prop (t k p : Nat)
    (hp : p ≤ t) (htp : t + p < twopow k) (hk : t - p ≤ k)
    (hz : IsZeroDiag (t - p))
    (hset : SettledBy (t - p) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) (t + p + twopow k))
      (wittBitBool (winWitt t (twopow k)) (t + p + twopow (k + 1))) =
      lhCenter (t + twopow k) p :=
  winWitt_sector_one_xor_sector_two_lhCenter_of_zero_diag t k p hp htp hk hz hset

/-- **Direct Cross-Sector Window Readout of Late `rhCenter (t + 2^k) r` Along a Zero Diagonal (`winWitt_sector_one_xor_sector_two_rhCenter_of_zero_diag`)**:
    for all `t, k, r : Nat` with `t + r ≤ k`, `IsZeroDiag (t + r)`, and `settle (t + r) ≤ t + 2^k`, `(winWitt t (2^k)).testBit ((t + 2^k) - r) ⊕ (winWitt t (2^k)).testBit ((t + 2^(k+1)) - r) = rhCenter (t + 2^k) r` directly! -/
theorem winWitt_sector_one_xor_sector_two_rhCenter_of_zero_diag (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : settle (t + r) ≤ t + twopow k) :
    bxor
      ((winWitt t (twopow k)).testBit ((t + twopow k) - r))
      ((winWitt t (twopow k)).testBit ((t + twopow (k + 1)) - r)) =
      rhCenter (t + twopow k) r := by
  have hlt : t + r < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  rw [winWitt_sector_one_xor_sector_two_rhCenter_cone t k r hlt,
    lhCenter_late_cross_of_zero_diag t k r hk hz hset]
  cases rhCenter (t + twopow k) r <;> rfl

theorem winWitt_sector_one_xor_sector_two_rhCenter_of_zero_diag_prop (t k r : Nat)
    (hk : t + r ≤ k)
    (hz : IsZeroDiag (t + r))
    (hset : SettledBy (t + r) (t + twopow k)) :
    bxor
      (wittBitBool (winWitt t (twopow k)) ((t + twopow k) - r))
      (wittBitBool (winWitt t (twopow k)) ((t + twopow (k + 1)) - r)) =
      rhCenter (t + twopow k) r :=
  winWitt_sector_one_xor_sector_two_rhCenter_of_zero_diag t k r hk hz hset

/-- **Exact Vanishing of `lhCenter (z + 2^k) (2^k)` at Any Zero Diagonal `z` (`lhCenter_late_twopow_of_zero_diag`)**:
    for all `z, k : Nat` with `z ≤ k`, `IsZeroDiag z`, and `settle z ≤ z + 2^k` (`SettledAt z k`), `lhCenter (z + 2^k) (2^k) = false`! -/
theorem lhCenter_late_twopow_of_zero_diag (z k : Nat)
    (hk : z ≤ k) (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    lhCenter (z + twopow k) (twopow k) = false := by
  rw [lhCenter_late_twopow_eq_zcenter z k hk hset,
    zcenter_of_zero_diag z hz]

theorem lhCenter_late_twopow_of_zero_diag_prop (z k : Nat)
    (hk : z ≤ k) (hz : IsZeroDiag z) (hset : SettledAt z k) :
    lhCenter (z + twopow k) (twopow k) = false :=
  lhCenter_late_twopow_of_zero_diag z k hk hz hset

/-- **Direct Sector-2 Window Readout of `center z` at Any Zero Diagonal `z` (`winWitt_testBit_sector_two_center_slot_of_zero_diag`)**:
    for all `z, k : Nat` with `z ≤ k`, `IsZeroDiag z`, and `settle z ≤ z + 2^k` (`SettledAt z k`), `(winWitt z (2^k)).testBit (z + 2^(k+1)) = center z` directly! -/
theorem winWitt_testBit_sector_two_center_slot_of_zero_diag (z k : Nat)
    (hk : z ≤ k) (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    (winWitt z (twopow k)).testBit (z + twopow (k + 1)) =
      Rule30UOR.Core.center z := by
  have h := winWitt_testBit_sector_two_center_slot_zcenter z k hk hset
  rw [zcenter_of_zero_diag z hz] at h
  revert h
  simp only [bxor_eq_xor]
  cases (winWitt z (twopow k)).testBit (z + twopow (k + 1)) <;>
    cases Rule30UOR.Core.center z <;> decide

theorem winWitt_testBit_sector_two_center_slot_of_zero_diag_prop (z k : Nat)
    (hk : z ≤ k) (hz : IsZeroDiag z) (hset : SettledAt z k) :
    wittBitBool (winWitt z (twopow k)) (z + twopow (k + 1)) =
      Rule30UOR.Core.center z :=
  winWitt_testBit_sector_two_center_slot_of_zero_diag z k hk hz hset

/-- **Direct Cross-Sector Window Readout of Late `center (z + 2^k)` at Any Zero Diagonal `z` (`winWitt_sector_one_xor_sector_two_center_slot_of_zero_diag`)**:
    for all `z, k : Nat` with `z ≤ k`, `IsZeroDiag z`, and `settle z ≤ z + 2^k` (`SettledAt z k`), `(winWitt z (2^k)).testBit (z + 2^k) ⊕ (winWitt z (2^k)).testBit (z + 2^(k+1)) = center (z + 2^k)` directly! -/
theorem winWitt_sector_one_xor_sector_two_center_slot_of_zero_diag (z k : Nat)
    (hk : z ≤ k) (hz : IsZeroDiag z) (hset : settle z ≤ z + twopow k) :
    bxor
      ((winWitt z (twopow k)).testBit (z + twopow k))
      ((winWitt z (twopow k)).testBit (z + twopow (k + 1))) =
      Rule30UOR.Core.center (z + twopow k) := by
  have h := winWitt_sector_one_xor_sector_two_center_slot_zcenter z k hk hset
  rw [zcenter_of_zero_diag z hz] at h
  revert h
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center (z + twopow k) <;>
    cases ((winWitt z (twopow k)).testBit (z + twopow k) ^^
      (winWitt z (twopow k)).testBit (z + twopow (k + 1))) <;> decide

theorem winWitt_sector_one_xor_sector_two_center_slot_of_zero_diag_prop (z k : Nat)
    (hk : z ≤ k) (hz : IsZeroDiag z) (hset : SettledAt z k) :
    bxor
      (wittBitBool (winWitt z (twopow k)) (z + twopow k))
      (wittBitBool (winWitt z (twopow k)) (z + twopow (k + 1))) =
      Rule30UOR.Core.center (z + twopow k) :=
  winWitt_sector_one_xor_sector_two_center_slot_of_zero_diag z k hk hz hset

end Rule30UOR.Interfaces
