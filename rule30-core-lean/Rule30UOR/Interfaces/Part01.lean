module

public import Rule30UOR.Core
public import Rule30UOR.Kit
public import Rule30UOR.Intent
public import Rule30UOR.CompilePoints
public import Rule30UOR.Right
public import Rule30UOR.Fixed
public import Rule30UOR.Scale
public import Ruliology.CellularAutomata.Rule30RightPeriods

/-!
# `Rule30UOR.Interfaces`, part 1

* Preamble
* `F₄`
* Bit lemmas
* The step through the interfaces
* Bridging Witt rows (`row`, `rowCenter`, `bit`) to the right system (`rdiag`, `rcenter`)
* Witt dyadic scale and Rule-150 / Rule-60 cone duality
* The two places at time `d + 2^k`
* Cancellation of masked column-1 parity in the dyadic coboundary
* Ostrowski–Archimedean support of `winWitt`
* General two-place readouts and compile-point coboundary oscillation
* Prop-valued paper interfaces for settled two-place and coboundary laws
* Repeat scales under a periodic center
* Right-period threshold `J(k)` and 2-adic leading bit of `winWitt`
* Bilinear cross-carry polarization and base-time evolution of `winWitt`
* Cyclotomic (`Φ₃`, `1 + x`) interfaces and nonlinear cone evolution of `winWitt`
* Paper-facing `bit` (`wittbit`) wrappers for `winWitt` ray and threshold theorems
* Sigmatics Triality Sector Decomposition (`Z_3 × Z_{2^k}`) and D-Transform Coupling
* Exact Rule 30 Evolution of `phiScale` and Wronskian Cross-Carry Localization
* 2-Adic Threshold Spacetime Geometry and Archimedean Sector-2 Settling Laws
-/

@[expose] public section

namespace Rule30UOR.Interfaces
open Rule30UOR.Core (phi carry phiLinear)

theorem phi_def (y : Nat) : phi y = y ^^^ ((y <<< 1) ||| (y <<< 2)) := rfl

theorem carry_def (y : Nat) : carry y = y &&& (y <<< 1) := rfl

/-! ### `F₄` -/

def add4 (u v : Bool × Bool) : Bool × Bool := (xor u.1 v.1, xor u.2 v.2)

/-- Multiplication by `ω`: `ω (a + b ω) = b + (a + b) ω`. -/
def mulω (u : Bool × Bool) : Bool × Bool := (u.2, xor u.1 u.2)

/-- The value of a row at `ω`: `Σ bitᵢ ωⁱ`. -/
def val (n : Nat) : Bool × Bool :=
  if h : n = 0 then (false, false)
  else add4 (n % 2 == 1, false) (mulω (val (n / 2)))
decreasing_by omega

/-- The value of a row at `1`: the parity of its black cells. -/
def par (n : Nat) : Bool :=
  if h : n = 0 then false else xor (n % 2 == 1) (par (n / 2))
decreasing_by omega

/-! ### Bit lemmas -/

theorem mod_two_eq (n : Nat) : (n % 2 == 1) = n.testBit 0 := by
  rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

theorem div_two_testBit (n i : Nat) : (n / 2).testBit i = n.testBit (i + 1) := by
  have e : n / 2 = n >>> 1 := by rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [e, Nat.testBit_shiftRight, Nat.add_comm]

theorem eq_zero_iff_testBit (n : Nat) : n = 0 ↔ ∀ i, n.testBit i = false := by
  constructor
  · intro h i; subst h; simp
  · intro h; exact Nat.eq_of_testBit_eq (fun i => by rw [h i]; simp)

/-- `val` and `par` read only bits: equal bits give equal values. -/
theorem val_congr : ∀ m n : Nat, (∀ i, m.testBit i = n.testBit i) → val m = val n := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n h
    have hmn : m = n := Nat.eq_of_testBit_eq h
    rw [hmn]

theorem val_eq (n : Nat) : val n = add4 (n.testBit 0, false) (mulω (val (n / 2))) := by
  by_cases h : n = 0
  · subst h; simp [val, add4, mulω]
  · rw [val, dif_neg h, mod_two_eq]

theorem par_eq (n : Nat) : par n = xor (n.testBit 0) (par (n / 2)) := by
  by_cases h : n = 0
  · subst h; simp [par]
  · rw [par, dif_neg h, mod_two_eq]

theorem add4_zero (v : Bool × Bool) : add4 (false, false) v = v := by
  obtain ⟨a, b⟩ := v; cases a <;> cases b <;> rfl

theorem val_zero : val 0 = (false, false) := by rw [val]; rfl

theorem par_zero : par 0 = false := by rw [par]; rfl

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 :=
  Nat.eq_of_testBit_eq (fun i => by simp only [div_two_testBit, Nat.testBit_xor])

theorem val_xor : ∀ a b : Nat, val (a ^^^ b) = add4 (val a) (val b) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b
    by_cases ha : a = 0
    · subst ha; rw [Nat.zero_xor, val_zero, add4_zero]
    · rw [val_eq (a ^^^ b), val_eq a, val_eq b, xor_div_two, ih (a / 2) (by omega), Nat.testBit_xor]
      simp only [add4, mulω]
      cases a.testBit 0 <;> cases b.testBit 0 <;> cases (val (a / 2)).1 <;> cases (val (a / 2)).2 <;>
        cases (val (b / 2)).1 <;> cases (val (b / 2)).2 <;> rfl

theorem par_xor : ∀ a b : Nat, par (a ^^^ b) = xor (par a) (par b) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b
    by_cases ha : a = 0
    · subst ha; rw [Nat.zero_xor, par_zero]; cases par b <;> rfl
    · rw [par_eq (a ^^^ b), par_eq a, par_eq b, xor_div_two, ih (a / 2) (by omega), Nat.testBit_xor]
      cases a.testBit 0 <;> cases b.testBit 0 <;> cases par (a / 2) <;> cases par (b / 2) <;> rfl

theorem two_mul_div_two (n : Nat) : (n <<< 1) / 2 = n := by
  rw [Nat.shiftLeft_eq]; omega

theorem shl_testBit_zero (n : Nat) : (n <<< 1).testBit 0 = false := by
  rw [Nat.testBit_shiftLeft]; simp

theorem val_shl (n : Nat) : val (n <<< 1) = mulω (val n) := by
  rw [val_eq, shl_testBit_zero, two_mul_div_two]
  simp only [add4, mulω]; cases (val n).1 <;> cases (val n).2 <;> rfl

theorem par_shl (n : Nat) : par (n <<< 1) = par n := by
  rw [par_eq, shl_testBit_zero, two_mul_div_two]; cases par n <;> rfl

/-! ### The step through the interfaces -/

theorem shl_two (n : Nat) : n <<< 2 = (n <<< 1) <<< 1 := by
  simp only [Nat.shiftLeft_eq]; rw [Nat.pow_succ, Nat.pow_one, Nat.mul_assoc]

/-- Rule 30 = linear part (multiplication by `Φ₃`) ⊕ carry. -/
theorem phi_split (y : Nat) :
    phi y = y ^^^ (y <<< 1) ^^^ (y <<< 2) ^^^ (carry y <<< 1) :=
  Rule30UOR.Core.phi_split y

/-- **The `Φ₃` interface.** The linear part vanishes at `ω`; the row's value is the carry's. -/
theorem val_phi (y : Nat) : val (phi y) = mulω (val (carry y)) := by
  rw [phi_split, val_xor, val_xor, val_xor, shl_two, val_shl, val_shl, val_shl, val_shl]
  simp only [add4, mulω]
  cases (val y).1 <;> cases (val y).2 <;> cases (val (carry y)).1 <;> cases (val (carry y)).2 <;> rfl

/-- **The `1 + x` interface.** The linear part is the identity at `1`; the parity changes by the
carry's. -/
theorem par_phi (y : Nat) : par (phi y) = xor (par y) (par (carry y)) := by
  rw [phi_split, par_xor, par_xor, par_xor, shl_two, par_shl, par_shl, par_shl, par_shl]
  cases par y <;> cases par (carry y) <;> rfl



open Rule30UOR.Core (phi carry phiLinear row rowCenter bit rdiag rcenter bxor)

/-- The two coordinates of the value at `ω`. -/
def valA (n : Nat) : Bool := (val n).1
def valB (n : Nat) : Bool := (val n).2

theorem valA_phi (y : Nat) : valA (phi y) = valB (carry y) := by
  unfold valA valB; rw [val_phi]; rfl

theorem valB_phi (y : Nat) : valB (phi y) = xor (valA (carry y)) (valB (carry y)) := by
  unfold valA valB; rw [val_phi]; rfl

theorem par_phi_bxor (y : Nat) : par (phi y) = Rule30UOR.Core.bxor (par y) (par (carry y)) := by
  rw [par_phi]; cases par y <;> cases par (carry y) <;> rfl

theorem valB_phi_bxor (y : Nat) : valB (phi y) = Rule30UOR.Core.bxor (valA (carry y)) (valB (carry y)) := by
  rw [valB_phi]; cases valA (carry y) <;> cases valB (carry y) <;> rfl

/-! ### Bridging Witt rows (`row`, `rowCenter`, `bit`) to the right system (`rdiag`, `rcenter`) -/

theorem phi_testBit_zero (y : Nat) : (phi y).testBit 0 = y.testBit 0 := by
  change (y ^^^ ((y <<< 1) ||| (y <<< 2))).testBit 0 = y.testBit 0
  simp

theorem phi_testBit_one (y : Nat) : (phi y).testBit 1 = xor (y.testBit 1) (y.testBit 0) := by
  change (y ^^^ ((y <<< 1) ||| (y <<< 2))).testBit 1 = xor (y.testBit 1) (y.testBit 0)
  simp [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]

theorem phi_testBit_add_two (y k : Nat) :
    (phi y).testBit (k + 2) = xor (y.testBit (k + 2)) (y.testBit (k + 1) || y.testBit k) := by
  change (y ^^^ ((y <<< 1) ||| (y <<< 2))).testBit (k + 2) =
    xor (y.testBit (k + 2)) (y.testBit (k + 1) || y.testBit k)
  simp [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]

theorem rdiag_zero_all : ∀ t : Nat, rdiag 0 t = true
  | 0 => rfl
  | _ + 1 => rfl

theorem bxor_eq_xor (a b : Bool) : bxor a b = xor a b := by
  cases a <;> cases b <;> rfl

/-- Bit `j` of the Witt integer `row t` is depth `j` of the right-diagonal system `rdiag j t`. -/
theorem row_testBit : ∀ (t j : Nat), (row t).testBit j = rdiag j t
  | 0, 0 => by decide
  | 0, k + 1 => by
    show (1 : Nat).testBit (k + 1) = false
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ≤ 2 ^ (k + 1) := by
      rw [Nat.pow_succ]
      have := Nat.one_le_two_pow (n := k)
      omega
    have hdiv : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv]
    decide
  | t + 1, 0 => by
    show (phi (row t)).testBit 0 = rdiag 0 (t + 1)
    rw [phi_testBit_zero, row_testBit t 0, rdiag_zero_all t, rdiag_zero_all (t + 1)]
  | t + 1, 1 => by
    show (phi (row t)).testBit 1 = !rdiag 1 t
    rw [phi_testBit_one, row_testBit t 1, row_testBit t 0, rdiag_zero_all t]
    cases rdiag 1 t <;> rfl
  | t + 1, k + 2 => by
    show (phi (row t)).testBit (k + 2) = bxor (rdiag (k + 2) t) (rdiag (k + 1) t || rdiag k t)
    rw [phi_testBit_add_two, row_testBit t (k + 2), row_testBit t (k + 1), row_testBit t k, bxor_eq_xor]

/-- `bit n k` is `1` when `n.testBit k` is `true` and `0` when `false`. -/
theorem bit_eq_if_testBit (n k : Nat) : bit n k = if n.testBit k then 1 else 0 := by
  change (n >>> k) % 2 = if n.testBit k then 1 else 0
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1 (n / 2 ^ k), Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> rw [h] <;> rfl

/-- Convert a `Bool` to its `0`/`1` `Nat` bit value. -/
def bton (b : Bool) : Nat := if b then 1 else 0

/-- The LexLean `bit` extraction on `row t` reads `rdiag j t` as `0`/`1`. -/
theorem bit_row_eq_rdiag (t j : Nat) : bit (row t) j = if rdiag j t then 1 else 0 := by
  rw [bit_eq_if_testBit, row_testBit]

/-- Paper-facing form: bit `j` of `row t` is `bton (rdiag j t)`. -/
theorem bit_row_bton (t j : Nat) : bit (row t) j = bton (rdiag j t) :=
  bit_row_eq_rdiag t j

/-- The LexLean `rowCenter t` reads `rcenter t` as `0`/`1`. -/
theorem rowCenter_eq_rcenter (t : Nat) : rowCenter t = if rcenter t then 1 else 0 :=
  bit_row_eq_rdiag t t

/-- Paper-facing form: `rowCenter t` is `bton (rcenter t)`. -/
theorem rowCenter_bton (t : Nat) : rowCenter t = bton (rcenter t) :=
  rowCenter_eq_rcenter t

/-- The core's center column equals the right-system center readout. -/
theorem core_center_eq_rcenter (t : Nat) : Rule30UOR.Core.center t = rcenter t := by
  rw [Rule30UOR.Scale.center_eq_kit, Rule30UOR.Right.center_eq_rcenter]

/-- Bit `t` of the Witt integer `row t` is the center cell `center t`. -/
theorem row_testBit_center (t : Nat) : (row t).testBit t = Rule30UOR.Core.center t := by
  rw [row_testBit, core_center_eq_rcenter]; rfl

/-- `rowCenter t` is the `0`/`1` bit encoding of `center t`. -/
theorem rowCenter_eq_center (t : Nat) : rowCenter t = bton (Rule30UOR.Core.center t) := by
  rw [rowCenter_bton, core_center_eq_rcenter]

theorem bton_inj {a b : Bool} (h : bton a = bton b) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- The Witt center bit sequence repeats with period `P` from `T`. -/
def RowCenterPeriodic (T P : Nat) : Prop := ∀ t, T ≤ t → rowCenter (t + P) = rowCenter t

/-- No positive period exists for the Witt center bit sequence. -/
def NoRowCenterPeriod : Prop := ∀ T P, 0 < P → ¬ RowCenterPeriodic T P

theorem rowCenterPeriodic_iff_centerPeriodic (T P : Nat) :
    RowCenterPeriodic T P ↔ Rule30UOR.Scale.CenterPeriodic T P := by
  constructor
  · intro h t ht
    have h1 := h t ht
    rw [rowCenter_eq_center, rowCenter_eq_center] at h1
    exact bton_inj h1
  · intro h t ht
    rw [rowCenter_eq_center, rowCenter_eq_center, h t ht]

theorem problem1_iff_noRowCenterPeriod :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 ↔ NoRowCenterPeriod := by
  rw [Rule30UOR.Scale.problem1_iff]
  constructor
  · intro h T P hP hrc
    exact h T P hP ((rowCenterPeriodic_iff_centerPeriodic T P).1 hrc)
  · intro h T P hP hc
    exact h T P hP ((rowCenterPeriodic_iff_centerPeriodic T P).2 hc)

theorem problem1_of_noRowCenterPeriod (h : NoRowCenterPeriod) :
    Ruliology.CellularAutomata.Rule30Prize.Problem1 :=
  problem1_iff_noRowCenterPeriod.2 h

theorem noRowCenterPeriod_of_problem1 (h : Ruliology.CellularAutomata.Rule30Prize.Problem1) :
    NoRowCenterPeriod :=
  problem1_iff_noRowCenterPeriod.1 h

/-- Above depth `2 * t`, the right-diagonal system is white (left of the left light-cone edge). -/
theorem rdiag_gt_two_mul : ∀ (t j : Nat), 2 * t < j → rdiag j t = false
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | t + 1, 0, h => by omega
  | t + 1, 1, h => by omega
  | t + 1, k + 2, h => by
    show bxor (rdiag (k + 2) t) (rdiag (k + 1) t || rdiag k t) = false
    rw [rdiag_gt_two_mul t (k + 2) (by omega), rdiag_gt_two_mul t (k + 1) (by omega),
      rdiag_gt_two_mul t k (by omega)]
    rfl

/-- At depth `2 * t`, the right-diagonal system hits the left light-cone edge and is black. -/
theorem rdiag_left_edge : ∀ (t : Nat), rdiag (2 * t) t = true
  | 0 => rfl
  | t + 1 => by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega]
    show bxor (rdiag (2 * t + 2) t) (rdiag (2 * t + 1) t || rdiag (2 * t) t) = true
    rw [rdiag_gt_two_mul t (2 * t + 2) (by omega), rdiag_gt_two_mul t (2 * t + 1) (by omega),
      rdiag_left_edge t]
    rfl

/-- The leading bit of `row t` is at index `2 * t` (the left light-cone edge). -/
theorem bit_row_left_edge (t : Nat) : bit (row t) (2 * t) = 1 := by
  rw [bit_row_eq_rdiag, rdiag_left_edge]; rfl

/-- All bits of `row t` above index `2 * t` are `0`. -/
theorem bit_row_gt_two_mul (t j : Nat) (h : 2 * t < j) : bit (row t) j = 0 := by
  rw [bit_row_eq_rdiag, rdiag_gt_two_mul t j h]; rfl

/-- Bit `k + 1` of the Witt carry `carry (row t)` is the conjunction of adjacent right diagonals. -/
theorem carry_row_testBit_succ (t k : Nat) :
    (carry (row t)).testBit (k + 1) = (rdiag (k + 1) t && rdiag k t) := by
  change ((row t) &&& ((row t) <<< 1)).testBit (k + 1) = (rdiag (k + 1) t && rdiag k t)
  simp [Nat.testBit_and, Nat.testBit_shiftLeft, row_testBit]

/-- Along the single-seed orbit, the `Φ₃` valuation of row `t + 1` is `ω` times the valuation of row `t`'s carry. -/
theorem val_row_succ (t : Nat) : val (row (t + 1)) = mulω (val (carry (row t))) :=
  val_phi (row t)

/-- Along the single-seed orbit, the first `F₄` coordinate of row `t + 1` is the second coordinate of row `t`'s carry. -/
theorem valA_row_succ (t : Nat) : valA (row (t + 1)) = valB (carry (row t)) :=
  valA_phi (row t)

/-- Along the single-seed orbit, the second `F₄` coordinate of row `t + 1` is the XOR of the coordinates of row `t`'s carry. -/
theorem valB_row_succ_bxor (t : Nat) :
    valB (row (t + 1)) = bxor (valA (carry (row t))) (valB (carry (row t))) :=
  valB_phi_bxor (row t)

/-- Along the single-seed orbit, the row parity changes by the parity of the row's carry. -/
theorem par_row_succ_bxor (t : Nat) :
    par (row (t + 1)) = bxor (par (row t)) (par (carry (row t))) :=
  par_phi_bxor (row t)

/-! ### Witt dyadic scale and Rule-150 / Rule-60 cone duality -/

open Rule30UOR.Core (phiLinearPow phiScale winWitt wittResponse twopow twopow_succ)

theorem phiLinear_xor (a b : Nat) : phiLinear (a ^^^ b) = phiLinear a ^^^ phiLinear b :=
  Nat.eq_of_testBit_eq fun i => by
    change (((a ^^^ b) ^^^ ((a ^^^ b) <<< 1)) ^^^ ((a ^^^ b) <<< 2)).testBit i =
      (((a ^^^ (a <<< 1)) ^^^ (a <<< 2)) ^^^ ((b ^^^ (b <<< 1)) ^^^ (b <<< 2))).testBit i
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    cases decide (i ≥ 1) <;> cases decide (i ≥ 2) <;>
      cases a.testBit i <;> cases b.testBit i <;>
      cases a.testBit (i - 1) <;> cases b.testBit (i - 1) <;>
      cases a.testBit (i - 2) <;> cases b.testBit (i - 2) <;> rfl

theorem phiLinearPow_add : ∀ (m n y : Nat), phiLinearPow (m + n) y = phiLinearPow m (phiLinearPow n y)
  | 0, _, _ => by simp [phiLinearPow]
  | m + 1, n, y => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    show phiLinear (phiLinearPow (m + n) y) = phiLinear (phiLinearPow m (phiLinearPow n y))
    rw [phiLinearPow_add m n y]

theorem phiLinearPow_xor : ∀ (n a b : Nat), phiLinearPow n (a ^^^ b) = phiLinearPow n a ^^^ phiLinearPow n b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    show phiLinear (phiLinearPow n (a ^^^ b)) = phiLinear (phiLinearPow n a) ^^^ phiLinear (phiLinearPow n b)
    rw [phiLinearPow_xor n a b, phiLinear_xor]

theorem phiScale_scale (k y : Nat) : phiScale k (phiScale k y) = phiScale (k + 1) y :=
  Nat.eq_of_testBit_eq fun i => by
    let L := twopow k
    change (((y ^^^ (y <<< L) ^^^ (y <<< (L + L))) ^^^
        ((y ^^^ (y <<< L) ^^^ (y <<< (L + L))) <<< L)) ^^^
        ((y ^^^ (y <<< L) ^^^ (y <<< (L + L))) <<< (L + L))).testBit i =
      ((y ^^^ (y <<< (L + L))) ^^^ (y <<< ((L + L) + (L + L)))).testBit i
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases h4 : i ≥ (L + L) + (L + L)
    · have h3 : i - (L + L) ≥ L + L := by omega
      have h2 : i - (L + L) ≥ L := by omega
      have h1 : i - L ≥ L + L := by omega
      have h0 : i - L ≥ L := by omega
      have ha : i ≥ L + L := by omega
      have hb : i ≥ L := by omega
      simp only [decide_eq_true h4, decide_eq_true h3, decide_eq_true h2, decide_eq_true h1,
        decide_eq_true h0, decide_eq_true ha, decide_eq_true hb, Bool.true_and,
        show i - L - L = i - (L + L) by omega,
        show i - L - (L + L) = i - (L + L) - L by omega,
        show i - (L + L) - (L + L) = i - ((L + L) + (L + L)) by omega]
      cases y.testBit i <;> cases y.testBit (i - L) <;> cases y.testBit (i - (L + L)) <;>
        cases y.testBit (i - (L + L) - L) <;> cases y.testBit (i - ((L + L) + (L + L))) <;> rfl
    · by_cases h3 : i ≥ L + (L + L)
      · have h3' : ¬ (i - (L + L) ≥ L + L) := by omega
        have h2 : i - (L + L) ≥ L := by omega
        have h1 : i - L ≥ L + L := by omega
        have h0 : i - L ≥ L := by omega
        have ha : i ≥ L + L := by omega
        have hb : i ≥ L := by omega
        simp only [decide_eq_false h4, decide_eq_false h3', decide_eq_true h2, decide_eq_true h1,
          decide_eq_true h0, decide_eq_true ha, decide_eq_true hb, Bool.true_and, Bool.false_and,
          show i - L - L = i - (L + L) by omega,
          show i - L - (L + L) = i - (L + L) - L by omega]
        cases y.testBit i <;> cases y.testBit (i - L) <;> cases y.testBit (i - (L + L)) <;>
          cases y.testBit (i - (L + L) - L) <;> rfl
      · by_cases ha : i ≥ L + L
        · have h2 : ¬ (i - (L + L) ≥ L) := by omega
          have h3' : ¬ (i - (L + L) ≥ L + L) := by omega
          have h1 : ¬ (i - L ≥ L + L) := by omega
          have h0 : i - L ≥ L := by omega
          have hb : i ≥ L := by omega
          simp only [decide_eq_false h4, decide_eq_false h3', decide_eq_false h2, decide_eq_false h1,
            decide_eq_true h0, decide_eq_true ha, decide_eq_true hb, Bool.true_and, Bool.false_and,
            show i - L - L = i - (L + L) by omega]
          cases y.testBit i <;> cases y.testBit (i - L) <;> cases y.testBit (i - (L + L)) <;> rfl
        · by_cases hb : i ≥ L
          · have h0 : ¬ (i - L ≥ L) := by omega
            have h1 : ¬ (i - L ≥ L + L) := by omega
            simp only [decide_eq_false h4, decide_eq_false ha, decide_eq_false h0, decide_eq_false h1,
              decide_eq_true hb, Bool.true_and, Bool.false_and]
            cases y.testBit i <;> cases y.testBit (i - L) <;> rfl
          · simp only [decide_eq_false h4, decide_eq_false ha, decide_eq_false hb, Bool.false_and]
            cases y.testBit i <;> rfl

/-- **Freshman's Dream for `Φ₃(x) = 1 + x + x²`**: iterating `phiLinear` `2^k` times gives `phiScale k`. -/
theorem phiLinear_freshman : ∀ (k y : Nat), phiLinearPow (twopow k) y = phiScale k y
  | 0, _ => rfl
  | k + 1, y => by
    rw [twopow_succ, phiLinearPow_add, phiLinear_freshman k y, phiLinear_freshman k (phiScale k y),
      phiScale_scale]

/-- **Witt Duhamel on `Nat` rows**: `row (t0 + n)` splits into `Φ₃^n(row t0)` XOR `winWitt t0 n`. -/
theorem row_duhamel (t0 : Nat) : ∀ n : Nat, row (t0 + n) = (phiLinearPow n (row t0)) ^^^ (winWitt t0 n)
  | 0 => by
    show row t0 = (row t0) ^^^ 0
    exact (Nat.xor_zero (row t0)).symm
  | n + 1 => by
    rw [show t0 + (n + 1) = (t0 + n) + 1 by omega]
    show phi (row (t0 + n)) = (phiLinear (phiLinearPow n (row t0))) ^^^
      ((phiLinear (winWitt t0 n)) ^^^ ((carry (row (t0 + n))) <<< 1))
    have hs : phi (row (t0 + n)) = (phiLinear (row (t0 + n))) ^^^ ((carry (row (t0 + n))) <<< 1) :=
      phi_split (row (t0 + n))
    rw [hs, row_duhamel t0 n, phiLinear_xor, Nat.xor_assoc]

/-- **Witt dyadic scale identity on `Nat` rows.** -/
theorem row_scale (t0 k : Nat) :
    row (t0 + twopow k) = (phiScale k (row t0)) ^^^ (winWitt t0 (twopow k)) := by
  rw [row_duhamel, phiLinear_freshman]

/-- Boolean readout of the Witt window response at the center bit `t + 2^k`. -/
def wittRespBool (t k : Nat) : Bool := (winWitt t (twopow k)).testBit (t + twopow k)

theorem wittResponse_bton (t k : Nat) : wittResponse t k = bton (wittRespBool t k) := by
  unfold wittResponse wittRespBool bton
  exact bit_eq_if_testBit (winWitt t (twopow k)) (t + twopow k)

/-- Inside the light cone (`t < 2^k`), both outer wings of `phiScale k (row t)` vanish at bit `t + 2^k`. -/
theorem phiScale_row_testBit_cone (t k : Nat) (hk : t < twopow k) :
    (phiScale k (row t)).testBit (t + twopow k) = Rule30UOR.Core.center t := by
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^ ((row t) <<< (twopow k + twopow k))).testBit (t + twopow k) =
    Rule30UOR.Core.center t
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have hw1 : (row t).testBit (t + twopow k) = false := by
    rw [row_testBit]
    exact rdiag_gt_two_mul t (t + twopow k) (by omega)
  have hm : decide (t + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have hw2 : decide (t + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [hw1, hm, hw2, Bool.true_and, Bool.false_and, Bool.false_xor, Bool.xor_false,
    show t + twopow k - twopow k = t by omega, row_testBit_center]

/-- **Witt dyadic scale identity at the center inside the cone (`t < 2^k`).** -/
theorem center_witt_scale_cone (t k : Nat) (hk : t < twopow k) :
    Rule30UOR.Core.center (t + twopow k) = bxor (Rule30UOR.Core.center t) (wittRespBool t k) := by
  rw [← row_testBit_center (t + twopow k), row_scale, Nat.testBit_xor,
    phiScale_row_testBit_cone t k hk, bxor_eq_xor]
  rfl

/-- **Cone duality**: for `t < 2^k`, the symmetric Witt (Rule-150) window response at the center equals the one-sided Rule-60 window response. -/
theorem wittRespBool_eq_response_cone (t k : Nat) (hk : t < twopow k) :
    wittRespBool t k = Rule30UOR.Scale.response t k := by
  have h1 := center_witt_scale_cone t k hk
  have h2 := Rule30UOR.Scale.scale_center t k
  have hw : Rule30UOR.Core.cell t (-(twopow k : Int)) = false :=
    Rule30UOR.Scale.cell_left_white t (-(twopow k : Int)) (by omega)
  rw [hw] at h2
  unfold Rule30UOR.Scale.response
  rw [bxor_eq_xor] at h1
  rw [h1] at h2
  revert h2
  cases Rule30UOR.Core.center t <;> cases wittRespBool t k <;> cases Rule30UOR.Core.window60 t (twopow k) 0 <;> simp

/-- Under a periodic center, inside the cone (`T ≤ t < 2^k`), the Witt window response equals the center difference at lag `2^k mod P`. -/
theorem periodic_witt_cone (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k t : Nat) (ht : T ≤ t) (hk : t < twopow k) :
    wittRespBool t k = bxor (Rule30UOR.Core.center (t + Rule30UOR.Scale.lag P k)) (Rule30UOR.Core.center t) := by
  rw [wittRespBool_eq_response_cone t k hk]
  exact Rule30UOR.Scale.periodic_scale_cone_paper T P hP h k t ht hk

/-- Depth `t + m` of the right system at time `t` is `cell t (-m)`. -/
theorem rdiag_add_eq_cell_neg (t m : Nat) :
    rdiag (t + m) t = Rule30UOR.Core.cell t (-(m : Int)) := by
  rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Scale.cell_eq_kit]
  unfold Ruliology.CellularAutomata.Rule30Diagonals.R
  exact congrArg (Ruliology.CellularAutomata.Rule30Jen.cell t) (by omega)

/-- Outside the cone (`2^k ≤ t`), `phiScale k (row t)` at bit `t + 2^k` reads the three cells at `-2^k`, `0`, and `+2^k`. -/
theorem phiScale_row_testBit_ge (t k : Nat) (hk : twopow k ≤ t) :
    (phiScale k (row t)).testBit (t + twopow k) =
      xor (xor (Rule30UOR.Core.cell t (-(twopow k : Int))) (Rule30UOR.Core.center t))
        (rdiag (t - twopow k) t) := by
  change (((row t) ^^^ ((row t) <<< twopow k)) ^^^ ((row t) <<< (twopow k + twopow k))).testBit (t + twopow k) = _
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have hm1 : decide (t + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have hm2 : decide (t + twopow k ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [hm1, hm2, Bool.true_and, Bool.true_and,
    show t + twopow k - twopow k = t by omega,
    show t + twopow k - (twopow k + twopow k) = t - twopow k by omega,
    row_testBit t (t + twopow k), rdiag_add_eq_cell_neg t (twopow k),
    row_testBit_center t, row_testBit t (t - twopow k)]

/-- **Outside-the-cone duality (`2^k ≤ t`)**: the XOR of the Witt (Rule-150) and Rule-60 dyadic window responses at the center is the right-diagonal cell `rdiag (t - 2^k) t`. -/
theorem wittRespBool_xor_response_ge (t k : Nat) (hk : twopow k ≤ t) :
    bxor (wittRespBool t k) (Rule30UOR.Scale.response t k) = rdiag (t - twopow k) t := by
  have h1 : Rule30UOR.Core.center (t + twopow k) =
      xor ((phiScale k (row t)).testBit (t + twopow k)) (wittRespBool t k) := by
    rw [← row_testBit_center (t + twopow k), row_scale, Nat.testBit_xor]
    rfl
  rw [phiScale_row_testBit_ge t k hk] at h1
  have h2 := Rule30UOR.Scale.scale_center t k
  unfold Rule30UOR.Scale.response
  rw [bxor_eq_xor]
  rw [h2] at h1
  revert h1
  cases Rule30UOR.Core.center t <;> cases Rule30UOR.Core.cell t (-(twopow k : Int)) <;>
    cases Rule30UOR.Core.window60 t (twopow k) 0 <;> cases rdiag (t - twopow k) t <;>
    cases wittRespBool t k <;> simp

theorem twopow_eq_pow : ∀ k : Nat, twopow k = 2 ^ k
  | 0 => rfl
  | k + 1 => by rw [twopow_succ, twopow_eq_pow k, Nat.pow_succ]; omega

theorem rdiag_periodic_mul (j : Nat) : ∀ m t : Nat, rdiag j (t + m * 2 ^ j) = rdiag j t
  | 0, t => by simp
  | m + 1, t => by
    rw [show t + (m + 1) * 2 ^ j = (t + m * 2 ^ j) + 2 ^ j by rw [Nat.succ_mul]; omega,
      Rule30UOR.Right.rdiag_periodic, rdiag_periodic_mul j m t]

/-- **Early center from late dyadic responses**: for every time `d` and every scale `k ≥ d`, the center bit `center d` equals the XOR of the Witt (Rule-150) and Rule-60 window responses at late time `d + 2^k`. -/
theorem center_from_late_responses (d k : Nat) (hk : d ≤ k) :
    Rule30UOR.Core.center d =
      bxor (wittRespBool (d + twopow k) k) (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hle : twopow k ≤ d + twopow k := by omega
  rw [wittRespBool_xor_response_ge (d + twopow k) k hle,
    show d + twopow k - twopow k = d by omega, twopow_eq_pow k]
  have hpow : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
    rw [← Nat.pow_add, show k - d + d = k by omega]
  rw [hpow, rdiag_periodic_mul d (2 ^ (k - d)) d, core_center_eq_rcenter]
  rfl

/-! ### The two places at time `d + 2^k` -/

open Rule30UOR.Core (ldiag)
open Rule30UOR.Intent (settle E)

/-- At time `d + m`, position `-m` is depth `d` of the left-diagonal system `ldiag d (d + m)`. -/
theorem ldiag_eq_cell_neg (d m : Nat) :
    ldiag d (d + m) = Rule30UOR.Core.cell (d + m) (-(m : Int)) := by
  rw [Rule30UOR.Kit.ldiag_eq_D, Rule30UOR.Scale.cell_eq_kit]
  unfold Ruliology.CellularAutomata.Rule30Diagonals.D
  exact congrArg (Ruliology.CellularAutomata.Rule30Jen.cell (d + m)) (by omega)

/-- **The two-place Witt scale identity**: at time `d + 2^k` (`d ≤ k`), the left wing of `Φ₃^(2^k)` reads `ldiag d (d + 2^k)` (the Archimedean / left place) and the right wing reads `center d = rdiag d d` (the 2-adic / right place). -/
theorem two_places_witt_scale (d k : Nat) (hk : d ≤ k) :
    bxor (Rule30UOR.Core.center d) (ldiag d (d + twopow k)) =
      bxor (bxor (Rule30UOR.Core.center ((d + twopow k) + twopow k))
        (Rule30UOR.Core.center (d + twopow k)))
        (wittRespBool (d + twopow k) k) := by
  have hc := center_from_late_responses d k hk
  have hs := Rule30UOR.Scale.scale_center (d + twopow k) k
  rw [← ldiag_eq_cell_neg d (twopow k)] at hs
  unfold Rule30UOR.Scale.response at hc
  rw [bxor_eq_xor] at hc
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, hc, hs]
  cases Rule30UOR.Core.center (d + twopow k) <;>
    cases ldiag d (d + twopow k) <;>
    cases Rule30UOR.Core.window60 (d + twopow k) (twopow k) 0 <;>
    cases wittRespBool (d + twopow k) k <;> rfl

/-- The zero-state's center readout `E d d`. -/
noncomputable def zcenter (d : Nat) : Bool := E d d

/-- Once `d + 2^k` has passed `settle d` (`settle d ≤ d + 2^k`), at every scale `k ≥ d` the left wing `ldiag d (d + 2^k)` equals the zero-state center `zcenter d = E d d`. Crucially, this requires only `settle d ≤ d + 2^k` (which holds for every `d` and all sufficiently large `k`), not `settle d ≤ d`. -/
theorem ldiag_settled_eq_zcenter (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    ldiag d (d + twopow k) = zcenter d := by
  unfold zcenter
  rw [Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D d (d + twopow k) hset, twopow_eq_pow k]
  have hpow : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
    rw [← Nat.pow_add, show k - d + d = k by omega]
  rw [hpow]
  exact Rule30UOR.ZeroDiagonals.E_per_mul d (2 ^ (k - d)) d

/-- **The settled two-place identity**: for every `d ≤ k` with `settle d ≤ d + 2^k`, the center damage `bxor (center d) (zcenter d)` at time `d` equals the Witt scale increment at late time `d + 2^k`. -/
theorem two_places_settled (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    bxor (Rule30UOR.Core.center d) (zcenter d) =
      bxor (bxor (Rule30UOR.Core.center ((d + twopow k) + twopow k))
        (Rule30UOR.Core.center (d + twopow k)))
        (wittRespBool (d + twopow k) k) := by
  rw [← ldiag_settled_eq_zcenter d k hk hset]
  exact two_places_witt_scale d k hk

/-- **Zero-state center from late Rule-60 scale**: for every `d ≤ k` with `settle d ≤ d + 2^k`, the zero-state center `zcenter d` equals the Rule-60 scale increment at late time `d + 2^k`. -/
theorem zcenter_from_late_scale (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    zcenter d =
      bxor (bxor (Rule30UOR.Core.center ((d + twopow k) + twopow k))
        (Rule30UOR.Core.center (d + twopow k)))
        (Rule30UOR.Scale.response (d + twopow k) k) := by
  rw [← ldiag_settled_eq_zcenter d k hk hset]
  have hs := Rule30UOR.Scale.scale_center (d + twopow k) k
  rw [← ldiag_eq_cell_neg d (twopow k)] at hs
  unfold Rule30UOR.Scale.response
  rw [bxor_eq_xor, bxor_eq_xor, hs]
  cases Rule30UOR.Core.center (d + twopow k) <;>
    cases ldiag d (d + twopow k) <;>
    cases Rule30UOR.Core.window60 (d + twopow k) (twopow k) 0 <;> rfl

/-- Under a periodic center (`CenterPeriodic T P`), for `d ≤ k`, `settle d ≤ d + 2^k`, and `T ≤ d + 2^k`, the center damage at `d` is fixed by the Witt response and the center lag at `d + 2^k`. -/
theorem two_places_periodic (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) (ht : T ≤ d + twopow k) :
    bxor (Rule30UOR.Core.center d) (zcenter d) =
      bxor (bxor (Rule30UOR.Core.center ((d + twopow k) + Rule30UOR.Scale.lag P k))
        (Rule30UOR.Core.center (d + twopow k)))
        (wittRespBool (d + twopow k) k) := by
  rw [two_places_settled d k hk hset,
    Rule30UOR.Scale.center_mod hP h (d + twopow k) (twopow k) ht]
  rfl

/-- Every scale `k` satisfies `k < 2^k`. -/
theorem twopow_gt_self : ∀ k : Nat, k < twopow k
  | 0 => by decide
  | k + 1 => by
    have ih := twopow_gt_self k
    rw [Rule30UOR.Core.twopow_succ]
    omega

/-- **Dyadic coboundary of the Rule-60 response**: for `d ≤ k`, stepping `d → d + 2^k → d + 2^(k+1)` versus `d → d + 2^(k+1)` shows that the coboundary defect `response d (k+1) ⊕ response d k ⊕ response (d + 2^k) k` is the left wing `ldiag d (d + 2^k)`. -/
theorem ldiag_eq_response_coboundary (d k : Nat) (hk : d ≤ k) :
    ldiag d (d + twopow k) =
      bxor (bxor (Rule30UOR.Scale.response d (k + 1)) (Rule30UOR.Scale.response d k))
        (Rule30UOR.Scale.response (d + twopow k) k) := by
  have hd_k : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hd_k1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hc1 := center_witt_scale_cone d k hd_k
  rw [wittRespBool_eq_response_cone d k hd_k] at hc1
  have hc2 := center_witt_scale_cone d (k + 1) hd_k1
  rw [wittRespBool_eq_response_cone d (k + 1) hd_k1] at hc2
  have hs := Rule30UOR.Scale.scale_center (d + twopow k) k
  rw [← ldiag_eq_cell_neg d (twopow k)] at hs
  have hstep : (d + twopow k) + twopow k = d + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep, hc2, hc1] at hs
  unfold Rule30UOR.Scale.response at *
  rw [bxor_eq_xor, bxor_eq_xor] at hs
  rw [bxor_eq_xor, bxor_eq_xor]
  revert hs
  cases Rule30UOR.Core.center d <;>
    cases Rule30UOR.Core.window60 d (twopow (k + 1)) 0 <;>
    cases Rule30UOR.Core.window60 d (twopow k) 0 <;>
    cases ldiag d (d + twopow k) <;>
    cases Rule30UOR.Core.window60 (d + twopow k) (twopow k) 0 <;> decide

/-- **Zero-state center as the Rule-60 dyadic coboundary**: for `d ≤ k` and `settle d ≤ d + 2^k`, `zcenter d` is the dyadic coboundary defect of `response` across the triangle `d → d + 2^k → d + 2^(k+1)`. -/
theorem zcenter_eq_response_coboundary (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    zcenter d =
      bxor (bxor (Rule30UOR.Scale.response d (k + 1)) (Rule30UOR.Scale.response d k))
        (Rule30UOR.Scale.response (d + twopow k) k) := by
  rw [← ldiag_settled_eq_zcenter d k hk hset]
  exact ldiag_eq_response_coboundary d k hk

/-- **The two-place Witt dyadic coboundary**: for every `d ≤ k`, `bxor (center d) (ldiag d (d + 2^k))` is the dyadic coboundary defect of `wittRespBool` across the triangle `d → d + 2^k → d + 2^(k+1)`. -/
theorem two_places_eq_witt_coboundary (d k : Nat) (hk : d ≤ k) :
    bxor (Rule30UOR.Core.center d) (ldiag d (d + twopow k)) =
      bxor (bxor (wittRespBool d (k + 1)) (wittRespBool d k))
        (wittRespBool (d + twopow k) k) := by
  have hd_k : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hd_k1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hc1 := center_witt_scale_cone d k hd_k
  have hc2 := center_witt_scale_cone d (k + 1) hd_k1
  have h2p := two_places_witt_scale d k hk
  have hstep : (d + twopow k) + twopow k = d + twopow (k + 1) := by
    rw [Rule30UOR.Core.twopow_succ]; omega
  rw [hstep, hc2, hc1] at h2p
  rw [h2p]
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Core.center d <;>
    cases wittRespBool d (k + 1) <;>
    cases wittRespBool d k <;>
    cases wittRespBool (d + twopow k) k <;> rfl

/-- **Center damage as the Witt (Rule-150) dyadic coboundary**: for `d ≤ k` and `settle d ≤ d + 2^k`, the center damage `bxor (center d) (zcenter d)` is the dyadic coboundary defect of `wittRespBool` across the triangle `d → d + 2^k → d + 2^(k+1)`. -/
theorem damage_eq_witt_coboundary (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    bxor (Rule30UOR.Core.center d) (zcenter d) =
      bxor (bxor (wittRespBool d (k + 1)) (wittRespBool d k))
        (wittRespBool (d + twopow k) k) := by
  rw [← ldiag_settled_eq_zcenter d k hk hset]
  exact two_places_eq_witt_coboundary d k hk

/-! ### Cancellation of masked column-1 parity in the dyadic coboundary -/

/-- The 1D running sum `maskcount` is additive over concatenated time intervals. -/
theorem maskcount_add (t0 m : Nat) : ∀ n : Nat,
    Rule30UOR.Scale.maskcount t0 (m + n) =
      xor (Rule30UOR.Scale.maskcount t0 m) (Rule30UOR.Scale.maskcount (t0 + m) n)
  | 0 => by
    show Rule30UOR.Scale.maskcount t0 m = xor (Rule30UOR.Scale.maskcount t0 m) false
    cases Rule30UOR.Scale.maskcount t0 m <;> rfl
  | n + 1 => by
    rw [show m + (n + 1) = (m + n) + 1 by omega]
    show xor (Rule30UOR.Scale.maskcount t0 (m + n)) (Rule30UOR.Core.carry60 (t0 + (m + n)) 0) =
      xor (Rule30UOR.Scale.maskcount t0 m)
        (xor (Rule30UOR.Scale.maskcount (t0 + m) n) (Rule30UOR.Core.carry60 (t0 + m + n) 0))
    rw [maskcount_add t0 m n, show t0 + (m + n) = t0 + m + n by omega]
    cases Rule30UOR.Scale.maskcount t0 m <;>
      cases Rule30UOR.Scale.maskcount (t0 + m) n <;>
      cases Rule30UOR.Core.carry60 (t0 + m + n) 0 <;> rfl

/-- **Exact vanishing of the `maskparity` dyadic coboundary**: across `d → d + 2^k → d + 2^(k+1)`, the masked column-1 parity is a 1D cochain whose coboundary vanishes identically. -/
theorem maskparity_coboundary (d k : Nat) :
    bxor (bxor (Rule30UOR.Scale.maskparity d (k + 1)) (Rule30UOR.Scale.maskparity d k))
      (Rule30UOR.Scale.maskparity (d + twopow k) k) = false := by
  unfold Rule30UOR.Scale.maskparity
  rw [Rule30UOR.Core.twopow_succ, maskcount_add d (twopow k) (twopow k), bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.maskcount d (twopow k) <;>
    cases Rule30UOR.Scale.maskcount (d + twopow k) (twopow k) <;> rfl

/-- **Left-diagonal readout as the pure left-half response coboundary**: because `maskparity` cancels out of the dyadic coboundary, `ldiag d (d + 2^k)` depends only on the left-half carry responses `leftresponse`. -/
theorem ldiag_eq_leftresponse_coboundary (d k : Nat) (hk : d ≤ k) :
    ldiag d (d + twopow k) =
      bxor (bxor (Rule30UOR.Scale.leftresponse d (k + 1)) (Rule30UOR.Scale.leftresponse d k))
        (Rule30UOR.Scale.leftresponse (d + twopow k) k) := by
  rw [ldiag_eq_response_coboundary d k hk,
    Rule30UOR.Scale.split_paper d (k + 1),
    Rule30UOR.Scale.split_paper d k,
    Rule30UOR.Scale.split_paper (d + twopow k) k]
  have hm := maskparity_coboundary d k
  revert hm
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse d (k + 1) <;>
    cases Rule30UOR.Scale.leftresponse d k <;>
    cases Rule30UOR.Scale.leftresponse (d + twopow k) k <;>
    cases Rule30UOR.Scale.maskparity d (k + 1) <;>
    cases Rule30UOR.Scale.maskparity d k <;>
    cases Rule30UOR.Scale.maskparity (d + twopow k) k <;> decide

/-- **Zero-state center as the pure left-half response coboundary**: for `d ≤ k` and `settle d ≤ d + 2^k`, `zcenter d` is given purely by the dyadic coboundary of `leftresponse`. -/
theorem zcenter_eq_leftresponse_coboundary (d k : Nat) (hk : d ≤ k) (hset : settle d ≤ d + twopow k) :
    zcenter d =
      bxor (bxor (Rule30UOR.Scale.leftresponse d (k + 1)) (Rule30UOR.Scale.leftresponse d k))
        (Rule30UOR.Scale.leftresponse (d + twopow k) k) := by
  rw [← ldiag_settled_eq_zcenter d k hk hset]
  exact ldiag_eq_leftresponse_coboundary d k hk

/-! ### Ostrowski–Archimedean support of `winWitt` -/

/-- **Ray 0 (Right-diagonal ray) of the Witt window response**: for every `t0` and every `j < 2^k`, bit `j` of `winWitt t0 (2^k)` is the `2^k`-step shift difference `bxor (rdiag j (t0 + 2^k)) (rdiag j t0)` along right diagonal `j`. -/
theorem winWitt_testBit_lt_twopow (t0 k j : Nat) (hj : j < twopow k) :
    (winWitt t0 (twopow k)).testBit j = bxor (rdiag j (t0 + twopow k)) (rdiag j t0) := by
  have hr := congrArg (fun n => n.testBit j) (row_scale t0 k)
  change (row (t0 + twopow k)).testBit j =
    ((((row t0) ^^^ ((row t0) <<< twopow k)) ^^^ ((row t0) <<< (twopow k + twopow k))) ^^^
      (winWitt t0 (twopow k))).testBit j at hr
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft] at hr
  have hm1 : decide (j ≥ twopow k) = false := decide_eq_false (by omega)
  have hm2 : decide (j ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [hm1, hm2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false,
    row_testBit (t0 + twopow k) j, row_testBit t0 j] at hr
  rw [bxor_eq_xor]
  revert hr
  cases rdiag j (t0 + twopow k) <;>
    cases rdiag j t0 <;>
    cases (winWitt t0 (twopow k)).testBit j <;> decide

/-- **2-adic zero gap of `winWitt` from right-diagonal periodicity**: for every `t0` and every `j < 2^k` whose right diagonal `j` has period `2^k` (`Per j (2^k)`), bit `j` of `winWitt t0 (2^k)` is `false`. -/
theorem winWitt_testBit_of_per (t0 k j : Nat) (hj : j < twopow k)
    (hper : Ruliology.CellularAutomata.Rule30RightPeriods.Per j (2 ^ k)) :
    (winWitt t0 (twopow k)).testBit j = false := by
  rw [winWitt_testBit_lt_twopow t0 k j hj]
  have hp : rdiag j (t0 + twopow k) = rdiag j t0 := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact hper t0
  rw [hp, bxor_eq_xor, Bool.xor_self]

/-- **Universal 2-adic leading bit of `winWitt` at the right-doubling threshold `J + 1`**: if right diagonal `J` has period `2^k` and `J + 1` does not (`J + 1 < 2^k`), then bit `J + 1` of `winWitt t0 (2^k)` is `true` for **every** `t0 : Nat`. -/
theorem winWitt_testBit_antiperiod (t0 k J : Nat) (hJlt : J + 1 < twopow k)
    (hJ : Ruliology.CellularAutomata.Rule30RightPeriods.Per J (2 ^ k))
    (hJ1 : ¬ Ruliology.CellularAutomata.Rule30RightPeriods.Per (J + 1) (2 ^ k)) :
    (winWitt t0 (twopow k)).testBit (J + 1) = true := by
  rw [winWitt_testBit_lt_twopow t0 k (J + 1) hJlt]
  have ha : rdiag (J + 1) (t0 + twopow k) = !rdiag (J + 1) t0 := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact Rule30UOR.KitConstructive.antiperiod hJ hJ1 t0
  rw [ha, bxor_eq_xor]
  cases rdiag (J + 1) t0 <;> rfl

/-- **2-adic valuation of the Witt window response**: for every `t0` and every `j ≤ k`, bit `j` of `winWitt t0 (2^k)` is `false` (`2^(k+1) ∣ winWitt t0 (2^k)` for `j ≤ k`). -/
theorem winWitt_testBit_low (t0 k j : Nat) (hj : j ≤ k) :
    (winWitt t0 (twopow k)).testBit j = false := by
  have hlt1 : j < twopow k := Nat.lt_of_le_of_lt hj (twopow_gt_self k)
  rw [winWitt_testBit_lt_twopow t0 k j hlt1]
  have hrd : rdiag j (t0 + twopow k) = rdiag j t0 := by
    rw [twopow_eq_pow k, show 2 ^ k = 2 ^ (k - j) * 2 ^ j by
      rw [← Nat.pow_add, show k - j + j = k by omega]]
    exact rdiag_periodic_mul j (2 ^ (k - j)) t0
  rw [hrd, bxor_eq_xor, Bool.xor_self]

/-- **Archimedean degree of the Witt window response**: for every `t0` and every `j > 2 * (t0 + 2^k)`, bit `j` of `winWitt t0 (2^k)` is `false`. -/
theorem winWitt_testBit_gt_two_mul (t0 k j : Nat) (hj : 2 * (t0 + twopow k) < j) :
    (winWitt t0 (twopow k)).testBit j = false := by
  have hr := congrArg (fun n => n.testBit j) (row_scale t0 k)
  change (row (t0 + twopow k)).testBit j =
    ((((row t0) ^^^ ((row t0) <<< twopow k)) ^^^ ((row t0) <<< (twopow k + twopow k))) ^^^
      (winWitt t0 (twopow k))).testBit j at hr
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft] at hr
  have hm1 : decide (j ≥ twopow k) = true := decide_eq_true (by omega)
  have hm2 : decide (j ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
  rw [hm1, hm2, Bool.true_and, Bool.true_and,
    row_testBit (t0 + twopow k) j,
    row_testBit t0 j,
    row_testBit t0 (j - twopow k),
    row_testBit t0 (j - (twopow k + twopow k)),
    rdiag_gt_two_mul (t0 + twopow k) j hj,
    rdiag_gt_two_mul t0 j (by omega),
    rdiag_gt_two_mul t0 (j - twopow k) (by omega),
    rdiag_gt_two_mul t0 (j - (twopow k + twopow k)) (by omega)] at hr
  simpa using hr.symm

/-- **Ray 1 (Vertical-column ray) of the Witt window response**: for every `t0`, `k`, and `i < 2^k` with `2 * t0 < i + 2^k`, bit `i + 2^k` of `winWitt t0 (2^k)` is the `2^k`-step vertical shift difference `bxor (rdiag (i + 2^k) (t0 + 2^k)) (rdiag i t0)` along column `t0 - i`. -/
theorem winWitt_testBit_middle_ray (t0 k i : Nat) (hi : i < twopow k) (hcone : 2 * t0 < i + twopow k) :
    (winWitt t0 (twopow k)).testBit (i + twopow k) =
      bxor (rdiag (i + twopow k) (t0 + twopow k)) (rdiag i t0) := by
  have hr := congrArg (fun n => n.testBit (i + twopow k)) (row_scale t0 k)
  change (row (t0 + twopow k)).testBit (i + twopow k) =
    ((((row t0) ^^^ ((row t0) <<< twopow k)) ^^^ ((row t0) <<< (twopow k + twopow k))) ^^^
      (winWitt t0 (twopow k))).testBit (i + twopow k) at hr
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft] at hr
  have hm1 : decide (i + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have hm2 : decide (i + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [hm1, hm2, Bool.true_and, Bool.false_and, Bool.xor_false,
    show i + twopow k - twopow k = i by omega,
    row_testBit (t0 + twopow k) (i + twopow k),
    row_testBit t0 (i + twopow k),
    row_testBit t0 i,
    rdiag_gt_two_mul t0 (i + twopow k) hcone] at hr
  rw [bxor_eq_xor]
  revert hr
  cases rdiag (i + twopow k) (t0 + twopow k) <;>
    cases rdiag i t0 <;>
    cases (winWitt t0 (twopow k)).testBit (i + twopow k) <;> decide

/-- **Ray 2 (Left-diagonal ray) of the Witt window response**: for every depth `d`, offset `m`, and scale `k` with `d + m < 2^k`, bit `d + 2m + 2^(k+1)` of `winWitt (d + m) (2^k)` is the `2^k`-step shift difference `bxor (ldiag d (d + m)) (ldiag d ((d + m) + 2^k))` along left diagonal `d`. -/
theorem winWitt_testBit_left_ray (d m k : Nat) (hdm : d + m < twopow k) :
    (winWitt (d + m) (twopow k)).testBit (d + 2 * m + twopow (k + 1)) =
      bxor (ldiag d (d + m)) (ldiag d ((d + m) + twopow k)) := by
  have hr := congrArg (fun n => n.testBit (d + 2 * m + twopow (k + 1))) (row_scale (d + m) k)
  change (row ((d + m) + twopow k)).testBit (d + 2 * m + twopow (k + 1)) =
    ((((row (d + m)) ^^^ ((row (d + m)) <<< twopow k)) ^^^
      ((row (d + m)) <<< (twopow k + twopow k))) ^^^
      (winWitt (d + m) (twopow k))).testBit (d + 2 * m + twopow (k + 1)) at hr
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft] at hr
  have hstep : twopow (k + 1) = twopow k + twopow k := Rule30UOR.Core.twopow_succ k
  have hm1 : decide (d + 2 * m + twopow (k + 1) ≥ twopow k) = true := decide_eq_true (by omega)
  have hm2 : decide (d + 2 * m + twopow (k + 1) ≥ twopow k + twopow k) = true :=
    decide_eq_true (by omega)
  have hld_late : rdiag (d + 2 * m + twopow (k + 1)) ((d + m) + twopow k) =
      ldiag d ((d + m) + twopow k) := by
    rw [show d + 2 * m + twopow (k + 1) = ((d + m) + twopow k) + (m + twopow k) by omega,
      rdiag_add_eq_cell_neg ((d + m) + twopow k) (m + twopow k),
      show (d + m) + twopow k = d + (m + twopow k) by omega,
      ← ldiag_eq_cell_neg d (m + twopow k)]
  have hld_early : rdiag (d + 2 * m) (d + m) = ldiag d (d + m) := by
    rw [show d + 2 * m = (d + m) + m by omega,
      rdiag_add_eq_cell_neg (d + m) m,
      ← ldiag_eq_cell_neg d m]
  rw [hm1, hm2, Bool.true_and, Bool.true_and,
    show d + 2 * m + twopow (k + 1) - (twopow k + twopow k) = d + 2 * m by omega,
    show d + 2 * m + twopow (k + 1) - twopow k = d + 2 * m + twopow k by omega,
    row_testBit ((d + m) + twopow k) (d + 2 * m + twopow (k + 1)),
    row_testBit (d + m) (d + 2 * m + twopow (k + 1)),
    row_testBit (d + m) (d + 2 * m + twopow k),
    row_testBit (d + m) (d + 2 * m),
    rdiag_gt_two_mul (d + m) (d + 2 * m + twopow (k + 1)) (by omega),
    rdiag_gt_two_mul (d + m) (d + 2 * m + twopow k) (by omega),
    hld_late, hld_early] at hr
  rw [bxor_eq_xor]
  revert hr
  cases ldiag d ((d + m) + twopow k) <;>
    cases ldiag d (d + m) <;>
    cases (winWitt (d + m) (twopow k)).testBit (d + 2 * m + twopow (k + 1)) <;> decide

/-- **Archimedean wing of the Witt window response**: for `d ≤ k`, bit `d + 2^(k+1)` of `winWitt d (2^k)` equals `bxor (center d) (ldiag d (d + 2^k))`. -/
theorem winWitt_testBit_archimedean (d k : Nat) (hk : d ≤ k) :
    (winWitt d (twopow k)).testBit (d + twopow (k + 1)) =
      bxor (Rule30UOR.Core.center d) (ldiag d (d + twopow k)) := by
  have hd_k : d + 0 < twopow k := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self k)
  have h := winWitt_testBit_left_ray d 0 k hd_k
  simp only [Nat.add_zero, Nat.mul_zero] at h
  have hc : ldiag d d = Rule30UOR.Core.center d := by
    have h0 := ldiag_eq_cell_neg d 0
    simp only [Nat.add_zero] at h0
    exact h0
  rw [hc] at h
  exact h

/-! ### General two-place readouts and compile-point coboundary oscillation -/

open Rule30UOR.ZeroDiagonals (IsZeroDiag)
open Rule30UOR.CompilePoints (IsBlackDiag DoublesAt black_after_zero_diag antiperiodic_of_doubles)

/-- **General settled left-diagonal readout**: for every depth `d`, time `s`, and scale `k ≥ d` with `settle d ≤ s + 2^k`, `ldiag d (s + 2^k)` equals the zero-state value `E d s`. -/
theorem ldiag_settled_eq_E (d s k : Nat) (hk : d ≤ k) (hset : settle d ≤ s + twopow k) :
    ldiag d (s + twopow k) = E d s := by
  rw [Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D d (s + twopow k) hset, twopow_eq_pow k]
  have hpow : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
    rw [← Nat.pow_add, show k - d + d = k by omega]
  rw [hpow]
  exact Rule30UOR.ZeroDiagonals.E_per_mul d (2 ^ (k - d)) s

/-- **Archimedean damage-band readout of `winWitt`**: for `d ≤ k`, `d + m < 2^k`, and `settle d ≤ (d + m) + 2^k`, bit `d + 2m + 2^(k+1)` of `winWitt (d + m) (2^k)` equals the left-diagonal damage `bxor (ldiag d (d + m)) (E d (d + m))`. -/
theorem winWitt_testBit_left_damage (d m k : Nat) (hk : d ≤ k) (hdm : d + m < twopow k)
    (hset : settle d ≤ (d + m) + twopow k) :
    (winWitt (d + m) (twopow k)).testBit (d + 2 * m + twopow (k + 1)) =
      bxor (ldiag d (d + m)) (E d (d + m)) := by
  rw [winWitt_testBit_left_ray d m k hdm, ldiag_settled_eq_E d (d + m) k hk hset]

/-- **Archimedean zero gap of `winWitt` on settled left diagonals**: once left diagonal `d` has settled by time `d + m` (`settle d ≤ d + m`), for every scale `k ≥ d` with `d + m < 2^k`, bit `d + 2m + 2^(k+1)` of `winWitt (d + m) (2^k)` is `false`. -/
theorem winWitt_testBit_left_settled_zero (d m k : Nat) (hk : d ≤ k) (hdm : d + m < twopow k)
    (hset : settle d ≤ d + m) :
    (winWitt (d + m) (twopow k)).testBit (d + 2 * m + twopow (k + 1)) = false := by
  rw [winWitt_testBit_left_damage d m k hk hdm (by omega),
    Rule30UOR.Kit.ldiag_eq_D, ← Rule30UOR.Intent.E_eq_D d (d + m) hset,
    bxor_eq_xor, Bool.xor_self]

/-- **General right-diagonal scale invariance**: for every depth `d`, time `s`, and scale `k ≥ d`, `rdiag d (s + 2^k) = rdiag d s` from time `0`. -/
theorem rdiag_scale_eq (d s k : Nat) (hk : d ≤ k) :
    rdiag d (s + twopow k) = rdiag d s := by
  rw [twopow_eq_pow k]
  have hpow : 2 ^ k = 2 ^ (k - d) * 2 ^ d := by
    rw [← Nat.pow_add, show k - d + d = k by omega]
  rw [hpow]
  exact rdiag_periodic_mul d (2 ^ (k - d)) s

/-- **Real-orbit antiperiodicity at a doubling zero diagonal**: if `z` is a zero diagonal where period `P` doubles, then for every `k ≥ z + 1` and `s` with `settle (z + 1) ≤ s + 2^k`, shifting time by `P` flips `ldiag (z + 1)` at scale `k`. -/
theorem ldiag_antiperiodic_of_doubles (P z s k : Nat) (hz : IsZeroDiag z) (hd : DoublesAt P z)
    (hk : z + 1 ≤ k) (hset : settle (z + 1) ≤ s + twopow k) :
    ldiag (z + 1) ((s + P) + twopow k) = !ldiag (z + 1) (s + twopow k) := by
  have hsetP : settle (z + 1) ≤ (s + P) + twopow k := by omega
  rw [ldiag_settled_eq_E (z + 1) (s + P) k hk hsetP,
    ldiag_settled_eq_E (z + 1) s k hk hset]
  exact antiperiodic_of_doubles P z hz hd s

/-- At any zero diagonal `z`, the zero-state center `zcenter z` is `false`. -/
theorem zcenter_of_zero_diag (z : Nat) (hz : IsZeroDiag z) : zcenter z = false :=
  hz z

/-- Two diagonals past any zero diagonal `z`, the zero-state center `zcenter (z + 2)` is `true`. -/
theorem zcenter_after_zero_diag (z : Nat) (hz : IsZeroDiag z) : zcenter (z + 2) = true :=
  black_after_zero_diag z hz (z + 2)

/-- **Unbounded oscillation of `zcenter`**: for every `N`, there is a zero diagonal `z ≥ N` where `zcenter z = false` and `zcenter (z + 2) = true`. -/
theorem zcenter_oscillates (N : Nat) : ∃ z, N ≤ z ∧ zcenter z = false ∧ zcenter (z + 2) = true := by
  obtain ⟨z, hzN, hz⟩ := Rule30UOR.ZeroDiagonals.zero_diagonals_unbounded N
  exact ⟨z, hzN, zcenter_of_zero_diag z hz, zcenter_after_zero_diag z hz⟩

/-- **At a zero diagonal `z`, the settled `leftresponse` dyadic coboundary vanishes**: for `z ≤ k` and `settle z ≤ z + 2^k`, the coboundary defect of `leftresponse` at `z` is `false`. -/
theorem leftresponse_coboundary_at_zero_diag (z k : Nat) (hz : IsZeroDiag z)
    (hk : z ≤ k) (hset : settle z ≤ z + twopow k) :
    bxor (bxor (Rule30UOR.Scale.leftresponse z (k + 1)) (Rule30UOR.Scale.leftresponse z k))
      (Rule30UOR.Scale.leftresponse (z + twopow k) k) = false := by
  rw [← zcenter_eq_leftresponse_coboundary z k hk hset, zcenter_of_zero_diag z hz]

/-- **Two steps past a zero diagonal `z`, the settled `leftresponse` dyadic coboundary is `true`**: for `z + 2 ≤ k` and `settle (z + 2) ≤ (z + 2) + 2^k`, the coboundary defect of `leftresponse` at `z + 2` is `true`. -/
theorem leftresponse_coboundary_after_zero_diag (z k : Nat) (hz : IsZeroDiag z)
    (hk : z + 2 ≤ k) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor (bxor (Rule30UOR.Scale.leftresponse (z + 2) (k + 1)) (Rule30UOR.Scale.leftresponse (z + 2) k))
      (Rule30UOR.Scale.leftresponse ((z + 2) + twopow k) k) = true := by
  rw [← zcenter_eq_leftresponse_coboundary (z + 2) k hk hset, zcenter_after_zero_diag z hz]

/-- **At a zero diagonal `z`, the settled Witt coboundary reads `center z` directly**: for `z ≤ k` and `settle z ≤ z + 2^k`, the dyadic coboundary of `wittRespBool` at `z` equals `center z`. -/
theorem witt_coboundary_at_zero_diag (z k : Nat) (hz : IsZeroDiag z)
    (hk : z ≤ k) (hset : settle z ≤ z + twopow k) :
    bxor (bxor (wittRespBool z (k + 1)) (wittRespBool z k))
      (wittRespBool (z + twopow k) k) = Rule30UOR.Core.center z := by
  have h := damage_eq_witt_coboundary z k hk hset
  rw [zcenter_of_zero_diag z hz] at h
  rw [← h, bxor_eq_xor, Bool.xor_false]

/-- **Two steps past a zero diagonal `z`, the settled Witt coboundary reads `!center (z + 2)`**: for `z + 2 ≤ k` and `settle (z + 2) ≤ (z + 2) + 2^k`, the dyadic coboundary of `wittRespBool` at `z + 2` equals `!center (z + 2)`. -/
theorem witt_coboundary_after_zero_diag (z k : Nat) (hz : IsZeroDiag z)
    (hk : z + 2 ≤ k) (hset : settle (z + 2) ≤ (z + 2) + twopow k) :
    bxor (bxor (wittRespBool (z + 2) (k + 1)) (wittRespBool (z + 2) k))
      (wittRespBool ((z + 2) + twopow k) k) = !Rule30UOR.Core.center (z + 2) := by
  have h := damage_eq_witt_coboundary (z + 2) k hk hset
  rw [zcenter_after_zero_diag z hz] at h
  rw [← h, bxor_eq_xor]
  cases Rule30UOR.Core.center (z + 2) <;> rfl

/-! ### Prop-valued paper interfaces for settled two-place and coboundary laws -/

/-- Scale `k` is past the settling time of depth `d` at time `d + 2^k`. -/
def SettledAt (d k : Nat) : Prop := settle d ≤ d + twopow k

/-- The zero-state center `zcenter d` equals `b`. -/
def ZCenterEq (d : Nat) (b : Bool) : Prop := zcenter d = b

/-- The center damage `bxor (center d) (zcenter d)` at time `d` equals `b`. -/
def DamageEq (d : Nat) (b : Bool) : Prop := bxor (Rule30UOR.Core.center d) (zcenter d) = b

theorem two_places_settled_prop (d k : Nat) (hk : d ≤ k) (hset : SettledAt d k) :
    DamageEq d (bxor (bxor (Rule30UOR.Core.center ((d + twopow k) + twopow k))
      (Rule30UOR.Core.center (d + twopow k))) (wittRespBool (d + twopow k) k)) :=
  two_places_settled d k hk hset

theorem zcenter_leftresponse_coboundary_prop (d k : Nat) (hk : d ≤ k) (hset : SettledAt d k) :
    ZCenterEq d (bxor (bxor (Rule30UOR.Scale.leftresponse d (k + 1))
      (Rule30UOR.Scale.leftresponse d k))
      (Rule30UOR.Scale.leftresponse (d + twopow k) k)) :=
  zcenter_eq_leftresponse_coboundary d k hk hset

theorem damage_witt_coboundary_prop (d k : Nat) (hk : d ≤ k) (hset : SettledAt d k) :
    DamageEq d (bxor (bxor (wittRespBool d (k + 1)) (wittRespBool d k))
      (wittRespBool (d + twopow k) k)) :=
  damage_eq_witt_coboundary d k hk hset

theorem zcenter_zero_prop (z : Nat) (hz : IsZeroDiag z) : ZCenterEq z false :=
  zcenter_of_zero_diag z hz

theorem zcenter_after_zero_prop (z : Nat) (hz : IsZeroDiag z) : ZCenterEq (z + 2) true :=
  zcenter_after_zero_diag z hz

theorem zcenter_oscillates_prop (N : Nat) :
    ∃ z, (N ≤ z ∧ ZCenterEq z false) ∧ ZCenterEq (z + 2) true := by
  obtain ⟨z, hzN, hz0, hz2⟩ := zcenter_oscillates N
  exact ⟨z, ⟨hzN, hz0⟩, hz2⟩

/-! ### Repeat scales under a periodic center -/

/-- Under a periodic center (`CenterPeriodic T P`), at any two scales `k1, k2` with the same dyadic lag `2^k1 mod P = 2^k2 mod P`, the cone responses `response t k1` and `response t k2` are equal for all `T ≤ t < min(2^k1, 2^k2)`. -/
theorem periodic_response_eq_of_lag_eq (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k1 k2 t : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ t) (hk1 : t < twopow k1) (hk2 : t < twopow k2) :
    Rule30UOR.Scale.response t k1 = Rule30UOR.Scale.response t k2 := by
  rw [Rule30UOR.Scale.periodic_scale_cone_paper T P hP h k1 t ht hk1,
    Rule30UOR.Scale.periodic_scale_cone_paper T P hP h k2 t ht hk2, hlag]

/-- Under a periodic center (`CenterPeriodic T P`), at any two scales `k1, k2` with `lag P k1 = lag P k2`, the Witt cone responses `wittRespBool t k1` and `wittRespBool t k2` are equal for all `T ≤ t < min(2^k1, 2^k2)`. -/
theorem periodic_witt_eq_of_lag_eq (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k1 k2 t : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ t) (hk1 : t < twopow k1) (hk2 : t < twopow k2) :
    wittRespBool t k1 = wittRespBool t k2 := by
  rw [wittRespBool_eq_response_cone t k1 hk1, wittRespBool_eq_response_cone t k2 hk2]
  exact periodic_response_eq_of_lag_eq T P hP h k1 k2 t hlag ht hk1 hk2

/-- **Left–right parity lock at repeat scales**: under `CenterPeriodic T P`, whenever `lag P k1 = lag P k2` and `T ≤ t < min(2^k1, 2^k2)`, the difference of the left-half responses equals the difference of the column-1 masked parities. -/
theorem periodic_left_eq_mask_of_lag_eq (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (k1 k2 t : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ t) (hk1 : t < twopow k1) (hk2 : t < twopow k2) :
    bxor (Rule30UOR.Scale.leftresponse t k1) (Rule30UOR.Scale.leftresponse t k2) =
      bxor (Rule30UOR.Scale.maskparity t k1) (Rule30UOR.Scale.maskparity t k2) := by
  have heq := periodic_response_eq_of_lag_eq T P hP h k1 k2 t hlag ht hk1 hk2
  rw [Rule30UOR.Scale.split_paper t k1, Rule30UOR.Scale.split_paper t k2] at heq
  revert heq
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse t k1 <;>
    cases Rule30UOR.Scale.leftresponse t k2 <;>
    cases Rule30UOR.Scale.maskparity t k1 <;>
    cases Rule30UOR.Scale.maskparity t k2 <;> decide

/-- Under `CenterPeriodic T P`, whenever `lag P (k + 1) = lag P k` (e.g., for `P ∣ 2^k`), the cone terms of the dyadic coboundary cancel for all `T ≤ d ≤ k`, so `zcenter d = response (d + 2^k) k` and `bxor (center d) (zcenter d) = wittRespBool (d + 2^k) k`. -/
theorem periodic_coboundary_collapse (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k : Nat) (hlag : Rule30UOR.Scale.lag P (k + 1) = Rule30UOR.Scale.lag P k)
    (ht : T ≤ d) (hk : d ≤ k) (hset : SettledAt d k) :
    zcenter d = Rule30UOR.Scale.response (d + twopow k) k ∧
      bxor (Rule30UOR.Core.center d) (zcenter d) = wittRespBool (d + twopow k) k := by
  have hd_k : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hd_k1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hr := periodic_response_eq_of_lag_eq T P hP h (k + 1) k d hlag ht hd_k1 hd_k
  have hw := periodic_witt_eq_of_lag_eq T P hP h (k + 1) k d hlag ht hd_k1 hd_k
  have hz := zcenter_eq_response_coboundary d k hk hset
  have hdam := damage_eq_witt_coboundary d k hk hset
  rw [hr] at hz
  rw [hw] at hdam
  refine ⟨?_, ?_⟩
  · rw [hz, bxor_eq_xor, bxor_eq_xor]
    cases Rule30UOR.Scale.response d k <;> cases Rule30UOR.Scale.response (d + twopow k) k <;> rfl
  · rw [hdam, bxor_eq_xor, bxor_eq_xor]
    cases wittRespBool d k <;> cases wittRespBool (d + twopow k) k <;> rfl

/-- Equality of dyadic lags at `k1` and `k2` propagates to `k1 + 1` and `k2 + 1`. -/
theorem lag_succ_eq_of_lag_eq (P k1 k2 : Nat)
    (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2) :
    Rule30UOR.Scale.lag P (k1 + 1) = Rule30UOR.Scale.lag P (k2 + 1) := by
  unfold Rule30UOR.Scale.lag at *
  rw [Rule30UOR.Core.twopow_succ, Rule30UOR.Core.twopow_succ,
    Nat.add_mod, hlag, ← Nat.add_mod]

/-- **Outside-the-cone scale invariance of `response` at repeat lags**: under `CenterPeriodic T P` (for any `P > 0`), if `lag P k1 = lag P k2`, then at any depth `d ≤ min(k1, k2)` with `T ≤ d` and `SettledAt d k1`, `SettledAt d k2`, the late Rule-60 responses `response (d + 2^k1) k1` and `response (d + 2^k2) k2` are equal. -/
theorem periodic_late_response_eq_of_lag_eq (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d) (hk1 : d ≤ k1) (hk2 : d ≤ k2)
    (hset1 : SettledAt d k1) (hset2 : SettledAt d k2) :
    Rule30UOR.Scale.response (d + twopow k1) k1 = Rule30UOR.Scale.response (d + twopow k2) k2 := by
  have hd_k1 : d < twopow k1 := Nat.lt_of_le_of_lt hk1 (twopow_gt_self k1)
  have hd_k2 : d < twopow k2 := Nat.lt_of_le_of_lt hk2 (twopow_gt_self k2)
  have hd_k1s : d < twopow (k1 + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k1 + 1))
  have hd_k2s : d < twopow (k2 + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k2 + 1))
  have hr0 := periodic_response_eq_of_lag_eq T P hP h k1 k2 d hlag ht hd_k1 hd_k2
  have hr1 := periodic_response_eq_of_lag_eq T P hP h (k1 + 1) (k2 + 1) d
    (lag_succ_eq_of_lag_eq P k1 k2 hlag) ht hd_k1s hd_k2s
  have hz1 := zcenter_eq_response_coboundary d k1 hk1 hset1
  have hz2 := zcenter_eq_response_coboundary d k2 hk2 hset2
  rw [hz1, hr0, hr1] at hz2
  revert hz2
  rw [bxor_eq_xor, bxor_eq_xor]
  cases Rule30UOR.Scale.response d (k2 + 1) <;>
    cases Rule30UOR.Scale.response d k2 <;>
    cases Rule30UOR.Scale.response (d + twopow k1) k1 <;>
    cases Rule30UOR.Scale.response (d + twopow k2) k2 <;> decide

/-- **Outside-the-cone scale invariance of `wittRespBool` at repeat lags**: under `CenterPeriodic T P` (for any `P > 0`), if `lag P k1 = lag P k2`, then at any depth `d ≤ min(k1, k2)` with `T ≤ d` and `SettledAt d k1`, `SettledAt d k2`, the late Witt responses `wittRespBool (d + 2^k1) k1` and `wittRespBool (d + 2^k2) k2` are equal. -/
theorem periodic_late_witt_eq_of_lag_eq (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d) (hk1 : d ≤ k1) (hk2 : d ≤ k2)
    (hset1 : SettledAt d k1) (hset2 : SettledAt d k2) :
    wittRespBool (d + twopow k1) k1 = wittRespBool (d + twopow k2) k2 := by
  have hd_k1 : d < twopow k1 := Nat.lt_of_le_of_lt hk1 (twopow_gt_self k1)
  have hd_k2 : d < twopow k2 := Nat.lt_of_le_of_lt hk2 (twopow_gt_self k2)
  have hd_k1s : d < twopow (k1 + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k1 + 1))
  have hd_k2s : d < twopow (k2 + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k2 + 1))
  have hw0 := periodic_witt_eq_of_lag_eq T P hP h k1 k2 d hlag ht hd_k1 hd_k2
  have hw1 := periodic_witt_eq_of_lag_eq T P hP h (k1 + 1) (k2 + 1) d
    (lag_succ_eq_of_lag_eq P k1 k2 hlag) ht hd_k1s hd_k2s
  have hd1 := damage_eq_witt_coboundary d k1 hk1 hset1
  have hd2 := damage_eq_witt_coboundary d k2 hk2 hset2
  rw [hd1, hw0, hw1] at hd2
  revert hd2
  rw [bxor_eq_xor, bxor_eq_xor]
  cases wittRespBool d (k2 + 1) <;>
    cases wittRespBool d k2 <;>
    cases wittRespBool (d + twopow k1) k1 <;>
    cases wittRespBool (d + twopow k2) k2 <;> decide

/-- **Outside-the-cone left–right parity lock at repeat lags**: under `CenterPeriodic T P`, if `lag P k1 = lag P k2`, `T ≤ d ≤ min(k1, k2)`, and `SettledAt d k1`, `SettledAt d k2`, the difference of the late left-half responses at `d + 2^k1` and `d + 2^k2` equals the difference of the late column-1 masked parities. -/
theorem periodic_late_left_eq_mask_of_lag_eq (T P : Nat) (hP : 0 < P) (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d) (hk1 : d ≤ k1) (hk2 : d ≤ k2)
    (hset1 : SettledAt d k1) (hset2 : SettledAt d k2) :
    bxor (Rule30UOR.Scale.leftresponse (d + twopow k1) k1)
      (Rule30UOR.Scale.leftresponse (d + twopow k2) k2) =
    bxor (Rule30UOR.Scale.maskparity (d + twopow k1) k1)
      (Rule30UOR.Scale.maskparity (d + twopow k2) k2) := by
  have heq := periodic_late_response_eq_of_lag_eq T P hP h d k1 k2 hlag ht hk1 hk2 hset1 hset2
  rw [Rule30UOR.Scale.split_paper (d + twopow k1) k1,
    Rule30UOR.Scale.split_paper (d + twopow k2) k2] at heq
  revert heq
  rw [bxor_eq_xor]
  cases Rule30UOR.Scale.leftresponse (d + twopow k1) k1 <;>
    cases Rule30UOR.Scale.leftresponse (d + twopow k2) k2 <;>
    cases Rule30UOR.Scale.maskparity (d + twopow k1) k1 <;>
    cases Rule30UOR.Scale.maskparity (d + twopow k2) k2 <;> decide

/-! ### Right-period threshold `J(k)` and 2-adic leading bit of `winWitt` -/

/-- `J` is the last right diagonal of period `2^k`: `Per J (2^k)` holds and `Per (J + 1) (2^k)` fails. -/
def IsRightThreshold (k J : Nat) : Prop :=
  Ruliology.CellularAutomata.Rule30RightPeriods.Per J (2 ^ k) ∧
    ¬ Ruliology.CellularAutomata.Rule30RightPeriods.Per (J + 1) (2 ^ k)

/-- For every scale `k`, there exists a unique right-period threshold `J` with `k ≤ J ≤ 2^(k+1) - 2`. -/
theorem exists_right_threshold (k : Nat) :
    ∃ J, k ≤ J ∧ J ≤ 2 ^ (k + 1) - 2 ∧ IsRightThreshold k J := by
  obtain ⟨J, hJ, hJ1, hk⟩ := Rule30UOR.KitConstructive.exists_last k
  exact ⟨J, hk, Rule30UOR.KitConstructive.per_bound hJ, hJ, hJ1⟩

/-- Every bit `j ≤ J` (with `j < 2^k`) below the right-period threshold `J` of scale `k` vanishes in `winWitt t0 (2^k)` for all `t0`. -/
theorem winWitt_zero_gap_of_threshold (t0 k J j : Nat) (hJ : IsRightThreshold k J)
    (hjJ : j ≤ J) (hj : j < twopow k) :
    (winWitt t0 (twopow k)).testBit j = false :=
  winWitt_testBit_of_per t0 k j hj
    (Rule30UOR.KitConstructive.per_mono_le hjJ hJ.1)

/-- At `J + 1` (when `J + 1 < 2^k`), the bit of `winWitt t0 (2^k)` is universally `true` for every `t0 : Nat`. -/
theorem winWitt_leading_bit_of_threshold (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) :
    (winWitt t0 (twopow k)).testBit (J + 1) = true :=
  winWitt_testBit_antiperiod t0 k J hJlt hJ.1 hJ.2

/-- If `2^k ≤ t` and right diagonal `t` has period `2^k`, then `center t = false` (contrapositive of `Rule30RightPeriods.center_black_lt`). -/
theorem center_false_of_ge_of_per (t k : Nat) (ht : twopow k ≤ t)
    (hper : Ruliology.CellularAutomata.Rule30RightPeriods.Per t (2 ^ k)) :
    Rule30UOR.Core.center t = false := by
  cases hc : Rule30UOR.Core.center t with
  | false => rfl
  | true =>
    rw [Rule30UOR.Scale.center_eq_kit] at hc
    have hlt := Ruliology.CellularAutomata.Rule30RightPeriods.center_black_lt hc hper
    rw [← twopow_eq_pow k] at hlt
    omega

/-- Any black center cell `center t = true` at time `t ≥ 2^k` strictly bounds the right-period threshold `J < t`. -/
theorem threshold_lt_of_center_true (t k J : Nat) (hJ : IsRightThreshold k J)
    (ht : twopow k ≤ t) (hc : Rule30UOR.Core.center t = true) :
    J < t := by
  apply Nat.lt_of_not_le
  intro hle
  have hper := Rule30UOR.KitConstructive.per_mono_le hle hJ.1
  have hfalse := center_false_of_ge_of_per t k ht hper
  rw [hc] at hfalse
  contradiction

/-- Whenever `center (2^k - 1) = false`, the right-period threshold satisfies `J + 1 < 2^k`, so `(winWitt t0 (2^k)).testBit (J + 1) = true` for every `t0 : Nat`. -/
theorem threshold_succ_lt_twopow_of_center_pred_false (k J : Nat) (hJ : IsRightThreshold k J)
    (hc : Rule30UOR.Core.center (twopow k - 1) = false) :
    J + 1 < twopow k := by
  have hp := Nat.two_pow_pos k
  rw [← twopow_eq_pow k] at hp
  apply Nat.lt_of_not_le
  intro hle
  have hper : Ruliology.CellularAutomata.Rule30RightPeriods.Per (2 ^ k - 1) (2 ^ k) := by
    apply Rule30UOR.KitConstructive.per_mono_le _ hJ.1
    rw [← twopow_eq_pow k]
    omega
  have hlast := Rule30UOR.KitConstructive.last_one (2 ^ k - 1) k hper
  have hcent : Rule30UOR.Core.center (twopow k - 1) = true := by
    rw [core_center_eq_rcenter]
    show rdiag (twopow k - 1) (twopow k - 1) = true
    rw [Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact hlast
  rw [hc] at hcent
  contradiction

/-! ### Bilinear cross-carry polarization and base-time evolution of `winWitt` -/

/-- The bilinear cross-carry (adjacent 2x2 determinant over `F₂`) of two Witt row integers `a, b`. -/
def crossCarry (a b : Nat) : Nat :=
  (a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))

/-- **Quadratic polarization of `carry`**: `carry (a ^^^ b) = (carry a ^^^ carry b) ^^^ crossCarry a b`. -/
theorem carry_xor (a b : Nat) :
    carry (a ^^^ b) = (carry a ^^^ carry b) ^^^ crossCarry a b := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((a ^^^ b) &&& ((a ^^^ b) <<< 1)).testBit i =
    ((((a &&& (a <<< 1)) ^^^ (b &&& (b <<< 1))) ^^^
      ((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))))).testBit i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  cases decide (i ≥ 1) <;>
    cases a.testBit i <;>
    cases b.testBit i <;>
    cases a.testBit (i - 1) <;>
    cases b.testBit (i - 1) <;> rfl

/-- **Nonlinear superposition law of `phi`**: the failure of `phi` to be `F₂`-linear on `a ^^^ b` is `crossCarry a b <<< 1`. -/
theorem phi_xor (a b : Nat) :
    phi (a ^^^ b) = (phi a ^^^ phi b) ^^^ (crossCarry a b <<< 1) := by
  have hsab : phi (a ^^^ b) = phiLinear (a ^^^ b) ^^^ (carry (a ^^^ b) <<< 1) :=
    Rule30UOR.Core.phi_split (a ^^^ b)
  have hsa : phi a = phiLinear a ^^^ (carry a <<< 1) := Rule30UOR.Core.phi_split a
  have hsb : phi b = phiLinear b ^^^ (carry b <<< 1) := Rule30UOR.Core.phi_split b
  rw [hsab, hsa, hsb, phiLinear_xor, carry_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases (phiLinear a).testBit i <;>
    cases (phiLinear b).testBit i <;>
    cases decide (i ≥ 1) <;>
    cases (carry a).testBit (i - 1) <;>
    cases (carry b).testBit (i - 1) <;>
    cases (crossCarry a b).testBit (i - 1) <;> rfl

/-- `phiScale k` is `F₂`-linear with respect to bitwise XOR. -/
theorem phiScale_xor (k a b : Nat) :
    phiScale k (a ^^^ b) = phiScale k a ^^^ phiScale k b := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (((a ^^^ b) ^^^ ((a ^^^ b) <<< twopow k)) ^^^
      ((a ^^^ b) <<< (twopow k + twopow k))).testBit i =
    ((((a ^^^ (a <<< twopow k)) ^^^ (a <<< (twopow k + twopow k))) ^^^
      ((b ^^^ (b <<< twopow k)) ^^^ (b <<< (twopow k + twopow k))))).testBit i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases a.testBit i <;>
    cases b.testBit i <;>
    cases decide (i ≥ twopow k) <;>
    cases a.testBit (i - twopow k) <;>
    cases b.testBit (i - twopow k) <;>
    cases decide (i ≥ twopow k + twopow k) <;>
    cases a.testBit (i - (twopow k + twopow k)) <;>
    cases b.testBit (i - (twopow k + twopow k)) <;> rfl

/-- `phiScale k` commutes with arbitrary left shifts `<<< s`. -/
theorem phiScale_shl (k y s : Nat) :
    phiScale k (y <<< s) = (phiScale k y) <<< s := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (((y <<< s) ^^^ ((y <<< s) <<< twopow k)) ^^^
      ((y <<< s) <<< (twopow k + twopow k))).testBit i =
    ((((y ^^^ (y <<< twopow k)) ^^^ (y <<< (twopow k + twopow k))) <<< s)).testBit i
  simp only [Nat.testBit_xor, ← Nat.shiftLeft_add]
  rw [show s + twopow k = twopow k + s by omega,
    show s + (twopow k + twopow k) = (twopow k + twopow k) + s by omega,
    Nat.shiftLeft_add, Nat.shiftLeft_add]
  simp only [Nat.testBit_shiftLeft, Nat.testBit_xor]
  cases decide (i ≥ s) <;> simp

/-- `phiScale k` commutes with `phiLinear`. -/
theorem phiScale_phiLinear (k y : Nat) :
    phiScale k (phiLinear y) = phiLinear (phiScale k y) := by
  change phiScale k ((y ^^^ (y <<< 1)) ^^^ (y <<< 2)) =
    ((phiScale k y) ^^^ ((phiScale k y) <<< 1)) ^^^ ((phiScale k y) <<< 2)
  rw [phiScale_xor, phiScale_xor, phiScale_shl k y 1, phiScale_shl k y 2]

/-- **Base-time step of the Witt window response**: advancing the base time `t0 ↦ t0 + 1` at fixed scale `2^k` applies `phiLinear` to `winWitt t0 (2^k)` and injects the boundary carry defect `(carry (row (t0 + 2^k)) ^^^ phiScale k (carry (row t0))) <<< 1`. -/
theorem winWitt_base_step (t0 k : Nat) :
    winWitt (t0 + 1) (twopow k) =
      phiLinear (winWitt t0 (twopow k)) ^^^
        ((carry (row (t0 + twopow k)) ^^^ phiScale k (carry (row t0))) <<< 1) := by
  have hs0 : phiLinear (row (t0 + twopow k)) =
      phiLinear (phiScale k (row t0)) ^^^ phiLinear (winWitt t0 (twopow k)) := by
    rw [row_scale t0 k, phiLinear_xor]
  have hs1 := row_scale (t0 + 1) k
  have hstep_late : row ((t0 + 1) + twopow k) =
      (phiLinear (phiScale k (row t0)) ^^^ phiLinear (winWitt t0 (twopow k))) ^^^
        (carry (row (t0 + twopow k)) <<< 1) := by
    rw [← hs0, show (t0 + 1) + twopow k = (t0 + twopow k) + 1 by omega]
    change phi (row (t0 + twopow k)) = _
    exact Rule30UOR.Core.phi_split (row (t0 + twopow k))
  have hphi0 : phi (row t0) = phiLinear (row t0) ^^^ (carry (row t0) <<< 1) :=
    Rule30UOR.Core.phi_split (row t0)
  have hstep_early : phiScale k (row (t0 + 1)) =
      phiLinear (phiScale k (row t0)) ^^^ ((phiScale k (carry (row t0))) <<< 1) := by
    change phiScale k (phi (row t0)) = _
    rw [hphi0, phiScale_xor, phiScale_phiLinear, phiScale_shl]
  rw [hstep_late, hstep_early] at hs1
  apply Nat.eq_of_testBit_eq
  intro i
  have hbit := congrArg (fun n => n.testBit i) hs1
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft] at hbit ⊢
  revert hbit
  cases (phiLinear (phiScale k (row t0))).testBit i <;>
    cases (phiLinear (winWitt t0 (twopow k))).testBit i <;>
    cases (winWitt (t0 + 1) (twopow k)).testBit i <;>
    cases decide (i ≥ 1) <;>
    cases (carry (row (t0 + twopow k))).testBit (i - 1) <;>
    cases (phiScale k (carry (row t0))).testBit (i - 1) <;> decide

/-! ### Cyclotomic (`Φ₃`, `1 + x`) interfaces and nonlinear cone evolution of `winWitt` -/

/-- `phiLinear y` vanishes identically at the `Φ₃` root `ω` in `F₄`. -/
theorem val_phiLinear (y : Nat) : val (phiLinear y) = (false, false) := by
  change val ((y ^^^ (y <<< 1)) ^^^ (y <<< 2)) = (false, false)
  rw [val_xor, val_xor, shl_two, val_shl, val_shl, val_shl]
  simp only [add4, mulω]
  cases (val y).1 <;> cases (val y).2 <;> rfl

/-- Every positive power `phiLinearPow (n + 1) y` vanishes at `ω` in `F₄`. -/
theorem val_phiLinearPow_succ (n y : Nat) :
    val (Rule30UOR.Core.phiLinearPow (n + 1) y) = (false, false) := by
  rw [Rule30UOR.Core.phiLinearPow_step]
  exact val_phiLinear (Rule30UOR.Core.phiLinearPow n y)

/-- `phiScale k y` (multiplication by `Φ₃(x)^(2^k)`) vanishes at `ω` in `F₄` for every scale `k`. -/
theorem val_phiScale (k y : Nat) : val (phiScale k y) = (false, false) := by
  rw [← phiLinear_freshman k y]
  have hp : 0 < twopow k := by
    rw [twopow_eq_pow k]
    exact Nat.two_pow_pos k
  obtain ⟨n, hn⟩ : ∃ n, twopow k = n + 1 := ⟨twopow k - 1, by omega⟩
  rw [hn]
  exact val_phiLinearPow_succ n y

/-- **The `Φ₃` interface on `winWitt`**: at every base time `t0` and scale `k`, the `F₄`-value of `winWitt t0 (2^k)` equals the `F₄`-value of `row (t0 + 2^k)`. -/
theorem val_winWitt (t0 k : Nat) :
    val (winWitt t0 (twopow k)) = val (row (t0 + twopow k)) := by
  rw [row_scale t0 k, val_xor, val_phiScale, add4_zero]

/-- Paper-facing first `F₄` coordinate of `val_winWitt`. -/
theorem valA_winWitt (t0 k : Nat) :
    valA (winWitt t0 (twopow k)) = valA (row (t0 + twopow k)) := by
  unfold valA; rw [val_winWitt]

/-- Paper-facing second `F₄` coordinate of `val_winWitt`. -/
theorem valB_winWitt (t0 k : Nat) :
    valB (winWitt t0 (twopow k)) = valB (row (t0 + twopow k)) := by
  unfold valB; rw [val_winWitt]

/-- Shifting by any `s : Nat` preserves row parity `par`. -/
theorem par_shl_iter (y : Nat) : ∀ s : Nat, par (y <<< s) = par y
  | 0 => rfl
  | s + 1 => by
    have hshl : y <<< (s + 1) = (y <<< s) <<< 1 := by
      rw [← Nat.shiftLeft_add]
    rw [hshl, par_shl, par_shl_iter y s]

/-- `phiScale k y` preserves row parity `par` for every scale `k`. -/
theorem par_phiScale (k y : Nat) : par (phiScale k y) = par y := by
  change par (((y ^^^ (y <<< twopow k)) ^^^ (y <<< (twopow k + twopow k)))) = par y
  rw [par_xor, par_xor, par_shl_iter, par_shl_iter]
  cases par y <;> rfl

/-- **The `1 + x` interface on `winWitt`**: at every base time `t0` and scale `k`, the parity of `winWitt t0 (2^k)` equals the parity change `bxor (par (row (t0 + 2^k))) (par (row t0))`. -/
theorem par_winWitt (t0 k : Nat) :
    par (winWitt t0 (twopow k)) = bxor (par (row (t0 + twopow k))) (par (row t0)) := by
  have hp := congrArg par (row_scale t0 k)
  rw [par_xor, par_phiScale] at hp
  rw [bxor_eq_xor]
  revert hp
  cases par (row (t0 + twopow k)) <;>
    cases par (row t0) <;>
    cases par (winWitt t0 (twopow k)) <;> decide

/-- Inside the light cone (`2 * t0 + 1 < 2^k`), the three shifted copies of `row t0` in `phiScale k (row t0)` have disjoint supports even after a 1-bit shift, so `carry` commutes with `phiScale k` on `row t0`. -/
theorem carry_phiScale_row_cone (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    carry (phiScale k (row t0)) = phiScale k (carry (row t0)) := by
  have hzero : ∀ m, 2 * t0 < m → (row t0).testBit m = false := by
    intro m hm
    rw [row_testBit]
    exact rdiag_gt_two_mul t0 m hm
  apply Nat.eq_of_testBit_eq
  intro i
  change ((phiScale k (row t0)) &&& ((phiScale k (row t0)) <<< 1)).testBit i =
    (((carry (row t0)) ^^^ ((carry (row t0)) <<< twopow k)) ^^^
      ((carry (row t0)) <<< (twopow k + twopow k))).testBit i
  change ((((row t0) ^^^ ((row t0) <<< twopow k)) ^^^ ((row t0) <<< (twopow k + twopow k))) &&&
      ((((row t0) ^^^ ((row t0) <<< twopow k)) ^^^ ((row t0) <<< (twopow k + twopow k))) <<< 1)).testBit i =
    ((((row t0) &&& ((row t0) <<< 1)) ^^^ (((row t0) &&& ((row t0) <<< 1)) <<< twopow k)) ^^^
      (((row t0) &&& ((row t0) <<< 1)) <<< (twopow k + twopow k))).testBit i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
  by_cases hi0 : i = 0
  · subst hi0; simp
  · have hi1 : decide (i ≥ 1) = true := decide_eq_true (by omega)
    rw [hi1, Bool.true_and]
    by_cases h1 : i < twopow k
    · have d1 : decide (i ≥ twopow k) = false := decide_eq_false (by omega)
      have d2 : decide (i ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
      have d3 : decide (i - 1 ≥ twopow k) = false := decide_eq_false (by omega)
      have d4 : decide (i - 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
      rw [d1, d2, d3, d4]
      simp
    · by_cases h1eq : i = twopow k
      · subst h1eq
        have d1 : decide (twopow k ≥ twopow k) = true := decide_eq_true (by omega)
        have d2 : decide (twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
        have d3 : decide (twopow k - 1 ≥ twopow k) = false := decide_eq_false (by omega)
        have d4 : decide (twopow k - 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
        have d5 : decide (twopow k - twopow k ≥ 1) = false := decide_eq_false (by omega)
        rw [d1, d2, d3, d4, d5, hzero (twopow k) (by omega), hzero (twopow k - 1) (by omega)]
        simp
      · by_cases h2 : i < twopow k + twopow k
        · have d1 : decide (i ≥ twopow k) = true := decide_eq_true (by omega)
          have d2 : decide (i ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
          have d3 : decide (i - 1 ≥ twopow k) = true := decide_eq_true (by omega)
          have d4 : decide (i - 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
          have d5 : decide (i - twopow k ≥ 1) = true := decide_eq_true (by omega)
          rw [d1, d2, d3, d4, d5,
            hzero i (by omega), hzero (i - 1) (by omega),
            show i - 1 - twopow k = i - twopow k - 1 by omega]
          simp
        · by_cases h2eq : i = twopow k + twopow k
          · have d1 : decide (i ≥ twopow k) = true := decide_eq_true (by omega)
            have d2 : decide (i ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
            have d3 : decide (i - 1 ≥ twopow k) = true := decide_eq_true (by omega)
            have d4 : decide (i - 1 ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
            have d5 : decide (i - twopow k ≥ 1) = true := decide_eq_true (by omega)
            have d6 : decide (i - (twopow k + twopow k) ≥ 1) = false := decide_eq_false (by omega)
            rw [d1, d2, d3, d4, d5, d6,
              hzero i (by omega), hzero (i - 1) (by omega),
              hzero (i - twopow k) (by omega), hzero (i - 1 - twopow k) (by omega),
              hzero (i - twopow k - 1) (by omega)]
            simp
          · have d1 : decide (i ≥ twopow k) = true := decide_eq_true (by omega)
            have d2 : decide (i ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
            have d3 : decide (i - 1 ≥ twopow k) = true := decide_eq_true (by omega)
            have d4 : decide (i - 1 ≥ twopow k + twopow k) = true := decide_eq_true (by omega)
            have d5 : decide (i - twopow k ≥ 1) = true := decide_eq_true (by omega)
            have d6 : decide (i - (twopow k + twopow k) ≥ 1) = true := decide_eq_true (by omega)
            rw [d1, d2, d3, d4, d5, d6,
              hzero i (by omega), hzero (i - 1) (by omega),
              hzero (i - twopow k) (by omega), hzero (i - 1 - twopow k) (by omega),
              hzero (i - twopow k - 1) (by omega),
              show i - 1 - (twopow k + twopow k) = i - (twopow k + twopow k) - 1 by omega]
            simp

/-- **Nonlinear Rule 30 evolution of `winWitt` inside the light cone (`2 * t0 + 1 < 2^k`)**: advancing `t0 ↦ t0 + 1` applies the full nonlinear Rule 30 step `phi` to `winWitt t0 (2^k)`, perturbed only by the bilinear cross-carry `crossCarry (phiScale k (row t0)) (winWitt t0 (2^k)) <<< 1`. -/
theorem winWitt_cone_step (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    winWitt (t0 + 1) (twopow k) =
      phi (winWitt t0 (twopow k)) ^^^
        (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) <<< 1) := by
  have hb := winWitt_base_step t0 k
  have hc : carry (row (t0 + twopow k)) =
      (phiScale k (carry (row t0)) ^^^ carry (winWitt t0 (twopow k))) ^^^
        crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) := by
    rw [row_scale t0 k, carry_xor, carry_phiScale_row_cone t0 k hcone]
  have hp : phi (winWitt t0 (twopow k)) =
      phiLinear (winWitt t0 (twopow k)) ^^^ (carry (winWitt t0 (twopow k)) <<< 1) :=
    Rule30UOR.Core.phi_split (winWitt t0 (twopow k))
  rw [hb, hc, hp]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  cases (phiLinear (winWitt t0 (twopow k))).testBit i <;>
    cases decide (i ≥ 1) <;>
    cases (phiScale k (carry (row t0))).testBit (i - 1) <;>
    cases (carry (winWitt t0 (twopow k))).testBit (i - 1) <;>
    cases (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (i - 1) <;> rfl

/-! ### Paper-facing `bit` (`wittbit`) wrappers for `winWitt` ray and threshold theorems -/

theorem bit_eq_bton_testBit (n k : Nat) : bit n k = bton (n.testBit k) :=
  bit_eq_if_testBit n k

theorem bit_winWitt_lt_twopow (t0 k j : Nat) (hj : j < twopow k) :
    bit (winWitt t0 (twopow k)) j = bton (bxor (rdiag j (t0 + twopow k)) (rdiag j t0)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_lt_twopow t0 k j hj]

theorem bit_winWitt_low (t0 k j : Nat) (hj : j ≤ k) :
    bit (winWitt t0 (twopow k)) j = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_low t0 k j hj]; rfl

theorem bit_winWitt_middle_ray (t0 k i : Nat) (hi : i < twopow k) (hcone : 2 * t0 < i + twopow k) :
    bit (winWitt t0 (twopow k)) (i + twopow k) =
      bton (bxor (rdiag (i + twopow k) (t0 + twopow k)) (rdiag i t0)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_middle_ray t0 k i hi hcone]

theorem bit_winWitt_left_ray (d m k : Nat) (hdm : d + m < twopow k) :
    bit (winWitt (d + m) (twopow k)) (d + 2 * m + twopow (k + 1)) =
      bton (bxor (ldiag d (d + m)) (ldiag d ((d + m) + twopow k))) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_left_ray d m k hdm]

theorem bit_winWitt_archimedean (d k : Nat) (hk : d ≤ k) :
    bit (winWitt d (twopow k)) (d + twopow (k + 1)) =
      bton (bxor (Rule30UOR.Core.center d) (ldiag d (d + twopow k))) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_archimedean d k hk]

theorem bit_winWitt_gt_two_mul (t0 k j : Nat) (hj : 2 * (t0 + twopow k) < j) :
    bit (winWitt t0 (twopow k)) j = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_gt_two_mul t0 k j hj]; rfl

theorem bit_winWitt_zero_gap_of_threshold (t0 k J j : Nat) (hJ : IsRightThreshold k J)
    (hjJ : j ≤ J) (hj : j < twopow k) :
    bit (winWitt t0 (twopow k)) j = 0 := by
  rw [bit_eq_if_testBit, winWitt_zero_gap_of_threshold t0 k J j hJ hjJ hj]; rfl

theorem bit_winWitt_leading_bit_of_threshold (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) :
    bit (winWitt t0 (twopow k)) (J + 1) = 1 := by
  rw [bit_eq_if_testBit, winWitt_leading_bit_of_threshold t0 k J hJ hJlt]; rfl

/-- Left diagonal `d` has settled into its zero-state period by time `s`. -/
def SettledBy (d s : Nat) : Prop := settle d ≤ s

theorem bit_winWitt_left_settled_zero (d m k : Nat) (hk : d ≤ k) (hdm : d + m < twopow k)
    (hset : SettledBy d (d + m)) :
    bit (winWitt (d + m) (twopow k)) (d + 2 * m + twopow (k + 1)) = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_left_settled_zero d m k hk hdm hset]; rfl

theorem exists_right_threshold_prop (k : Nat) :
    ∃ J, (k ≤ J ∧ J + 2 ≤ twopow (k + 1)) ∧ IsRightThreshold k J := by
  obtain ⟨J, hk, hb, hJ⟩ := exists_right_threshold k
  have hp := Nat.two_pow_pos (k + 1)
  have hb' : J + 2 ≤ twopow (k + 1) := by
    rw [twopow_eq_pow (k + 1)]
    omega
  exact ⟨J, ⟨hk, hb'⟩, hJ⟩

/-! ### Sigmatics Triality Sector Decomposition (`Z_3 × Z_{2^k}`) and D-Transform Coupling -/

/-- The Sigmatics-style mixed-radix ray-sector coordinate `d * 2^k + r` (`d ∈ {0,1,2}`, `r < 2^k`), decomposing the support of `Φ₃(x)^(2^k) = 1 + x^(2^k) + x^(2^(k+1))` into three triality sectors of stride `2^k`. -/
def trialityAddr (k d r : Nat) : Nat := d * twopow k + r

theorem trialityAddr_zero (k r : Nat) : trialityAddr k 0 r = r := by
  unfold trialityAddr; simp

theorem trialityAddr_one (k r : Nat) : trialityAddr k 1 r = r + twopow k := by
  unfold trialityAddr; omega

theorem trialityAddr_two (k r : Nat) : trialityAddr k 2 r = r + twopow (k + 1) := by
  unfold trialityAddr
  rw [Rule30UOR.Core.twopow_succ]
  omega

/-- Inside the light cone (`2 * t0 < 2^k`), every bit index `j ≥ 3 * 2^k` lies strictly outside the three triality sectors `d ∈ {0,1,2}` and vanishes in `winWitt t0 (2^k)`. -/
theorem winWitt_testBit_triality_outside (t0 k j : Nat) (hcone : 2 * t0 < twopow k)
    (hj : 3 * twopow k ≤ j) :
    (winWitt t0 (twopow k)).testBit j = false :=
  winWitt_testBit_gt_two_mul t0 k j (by omega)

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_triality_outside`. -/
theorem bit_winWitt_triality_outside (t0 k j : Nat) (hcone : 2 * t0 < twopow k)
    (hj : 3 * twopow k ≤ j) :
    bit (winWitt t0 (twopow k)) j = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_triality_outside t0 k j hcone hj]; rfl

/-- Inside the light cone (`2 * t0 < 2^k`), **every** slot `r < 2^k` of Triality Sector 1 (`j = r + 2^k`) satisfies the middle-ray condition unconditionally. -/
theorem winWitt_testBit_sector_one_cone (t0 k r : Nat) (hcone : 2 * t0 < twopow k) (hr : r < twopow k) :
    (winWitt t0 (twopow k)).testBit (r + twopow k) =
      bxor (rdiag (r + twopow k) (t0 + twopow k)) (rdiag r t0) :=
  winWitt_testBit_middle_ray t0 k r hr (by omega)

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_cone`. -/
theorem bit_winWitt_sector_one_cone (t0 k r : Nat) (hcone : 2 * t0 < twopow k) (hr : r < twopow k) :
    bit (winWitt t0 (twopow k)) (r + twopow k) =
      bton (bxor (rdiag (r + twopow k) (t0 + twopow k)) (rdiag r t0)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_cone t0 k r hcone hr]

/-- **Sigmatics Triality D-Coupling between Sector 0 and Sector 1**: at any slot `r < 2^k` with `2 * t0 < r + 2^k`, XORing Sector 0 (`j = r`) and Sector 1 (`j = r + 2^k`) of `winWitt t0 (2^k)` cancels the early-time state `rdiag r t0` identically, leaving the pure late-time spatial difference `bxor (rdiag r (t0 + 2^k)) (rdiag (r + 2^k) (t0 + 2^k))`. -/
theorem winWitt_testBit_sector_zero_xor_one (t0 k r : Nat) (hr : r < twopow k)
    (hcone : 2 * t0 < r + twopow k) :
    bxor ((winWitt t0 (twopow k)).testBit r) ((winWitt t0 (twopow k)).testBit (r + twopow k)) =
      bxor (rdiag r (t0 + twopow k)) (rdiag (r + twopow k) (t0 + twopow k)) := by
  rw [winWitt_testBit_lt_twopow t0 k r hr, winWitt_testBit_middle_ray t0 k r hr hcone]
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases rdiag r (t0 + twopow k) <;>
    cases rdiag (r + twopow k) (t0 + twopow k) <;>
    cases rdiag r t0 <;> rfl

/-- **Center-Slot Readout in Sector 1 (`r = t0 < 2^k`)**: at slot `r = t0`, Sector 1 (`j = t0 + 2^k`) of `winWitt t0 (2^k)` is the exact center-column difference `bxor (center (t0 + 2^k)) (center t0)`. -/
theorem winWitt_testBit_center_slot (t0 k : Nat) (ht0 : t0 < twopow k) :
    (winWitt t0 (twopow k)).testBit (t0 + twopow k) =
      bxor (Rule30UOR.Core.center (t0 + twopow k)) (Rule30UOR.Core.center t0) := by
  rw [winWitt_testBit_middle_ray t0 k t0 ht0 (by omega),
    core_center_eq_rcenter (t0 + twopow k), core_center_eq_rcenter t0]
  rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_center_slot`. -/
theorem bit_winWitt_center_slot (t0 k : Nat) (ht0 : t0 < twopow k) :
    bit (winWitt t0 (twopow k)) (t0 + twopow k) =
      bton (bxor (Rule30UOR.Core.center (t0 + twopow k)) (Rule30UOR.Core.center t0)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_center_slot t0 k ht0]

/-- **Threshold-Center Resonance (`t0 = J + 1 < 2^k`)**: at the right-period threshold time `t0 = J + 1`, bit `J + 1` in Sector 0 is universally `true`, forcing `rdiag (J + 1) ((J + 1) + 2^k) = !center (J + 1)` and locking the center response `wittRespBool (J + 1) k` to the negation of `bxor (center ((J + 1) + 2^k)) (rdiag (J + 1) ((J + 1) + 2^k))`. -/
theorem threshold_center_resonance (k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) :
    rdiag (J + 1) ((J + 1) + twopow k) = !Rule30UOR.Core.center (J + 1) ∧
      wittRespBool (J + 1) k =
        !bxor (Rule30UOR.Core.center ((J + 1) + twopow k))
          (rdiag (J + 1) ((J + 1) + twopow k)) := by
  have h0 := winWitt_leading_bit_of_threshold (J + 1) k J hJ hJlt
  have hray0 := winWitt_testBit_lt_twopow (J + 1) k (J + 1) hJlt
  have hray1 := winWitt_testBit_middle_ray (J + 1) k (J + 1) hJlt (by omega)
  rw [core_center_eq_rcenter (J + 1), core_center_eq_rcenter ((J + 1) + twopow k)]
  unfold rcenter wittRespBool
  rw [h0] at hray0
  rw [hray1]
  revert hray0
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases rdiag (J + 1) ((J + 1) + twopow k) <;>
    cases rdiag (J + 1) (J + 1) <;>
    cases rdiag ((J + 1) + twopow k) ((J + 1) + twopow k) <;> decide

theorem threshold_center_antiperiod (k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) :
    rdiag (J + 1) ((J + 1) + twopow k) = !Rule30UOR.Core.center (J + 1) :=
  (threshold_center_resonance k J hJ hJlt).1

theorem threshold_center_witt_response (k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) :
    wittRespBool (J + 1) k =
      !bxor (Rule30UOR.Core.center ((J + 1) + twopow k))
        (rdiag (J + 1) ((J + 1) + twopow k)) :=
  (threshold_center_resonance k J hJ hJlt).2

/-- **Sector 1 Late-Slice Reduction Below the Threshold (`r ≤ J`)**: for every slot `r ≤ J` (`r < 2^k`, `2 * t0 < r + 2^k`), Sector 0 vanishes (`rdiag r (t0 + 2^k) = rdiag r t0`), so Sector 1 (`j = r + 2^k`) reduces to the pure late-time spatial difference `bxor (rdiag (r + 2^k) (t0 + 2^k)) (rdiag r (t0 + 2^k))`. -/
theorem winWitt_testBit_sector_one_below_threshold (t0 k J r : Nat) (hJ : IsRightThreshold k J)
    (hrJ : r ≤ J) (hr : r < twopow k) (hcone : 2 * t0 < r + twopow k) :
    (winWitt t0 (twopow k)).testBit (r + twopow k) =
      bxor (rdiag (r + twopow k) (t0 + twopow k)) (rdiag r (t0 + twopow k)) := by
  have h0 := winWitt_zero_gap_of_threshold t0 k J r hJ hrJ hr
  have hxor := winWitt_testBit_sector_zero_xor_one t0 k r hr hcone
  rw [h0] at hxor
  revert hxor
  rw [bxor_eq_xor, bxor_eq_xor]
  cases (winWitt t0 (twopow k)).testBit (r + twopow k) <;>
    cases rdiag r (t0 + twopow k) <;>
    cases rdiag (r + twopow k) (t0 + twopow k) <;> decide

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_below_threshold`. -/
theorem bit_winWitt_sector_one_below_threshold (t0 k J r : Nat) (hJ : IsRightThreshold k J)
    (hrJ : r ≤ J) (hr : r < twopow k) (hcone : 2 * t0 < r + twopow k) :
    bit (winWitt t0 (twopow k)) (r + twopow k) =
      bton (bxor (rdiag (r + twopow k) (t0 + twopow k)) (rdiag r (t0 + twopow k))) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_below_threshold t0 k J r hJ hrJ hr hcone]

/-- **Sector 1 Late-Slice Inversion at the Threshold (`r = J + 1`)**: at the right-period threshold slot `r = J + 1 < 2^k` (`2 * t0 < J + 1 + 2^k`), Sector 0 is universally `true`, so Sector 1 (`j = J + 1 + 2^k`) is the negation of the late-time spatial difference `!bxor (rdiag (J + 1 + 2^k) (t0 + 2^k)) (rdiag (J + 1) (t0 + 2^k))`. -/
theorem winWitt_testBit_sector_one_at_threshold (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) (hcone : 2 * t0 < (J + 1) + twopow k) :
    (winWitt t0 (twopow k)).testBit ((J + 1) + twopow k) =
      !bxor (rdiag ((J + 1) + twopow k) (t0 + twopow k)) (rdiag (J + 1) (t0 + twopow k)) := by
  have h1 := winWitt_leading_bit_of_threshold t0 k J hJ hJlt
  have hxor := winWitt_testBit_sector_zero_xor_one t0 k (J + 1) hJlt hcone
  rw [h1] at hxor
  revert hxor
  rw [bxor_eq_xor, bxor_eq_xor]
  cases (winWitt t0 (twopow k)).testBit ((J + 1) + twopow k) <;>
    cases rdiag (J + 1) (t0 + twopow k) <;>
    cases rdiag ((J + 1) + twopow k) (t0 + twopow k) <;> decide

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_at_threshold`. -/
theorem bit_winWitt_sector_one_at_threshold (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (hJlt : J + 1 < twopow k) (hcone : 2 * t0 < (J + 1) + twopow k) :
    bit (winWitt t0 (twopow k)) ((J + 1) + twopow k) =
      bton (!bxor (rdiag ((J + 1) + twopow k) (t0 + twopow k)) (rdiag (J + 1) (t0 + twopow k))) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_at_threshold t0 k J hJ hJlt hcone]

/-! ### Exact Rule 30 Evolution of `phiScale` and Wronskian Cross-Carry Localization -/

/-- **Exact Rule 30 Evolution of `phiScale k (row t0)` inside the Cone (`2 * t0 + 1 < 2^k`)**: because the three shifted copies of `row t0` have disjoint supports separated by at least two white cells, `phiScale k` commutes with the full nonlinear Rule 30 operator `phi` on `row t0`. -/
theorem phiScale_row_cone_step (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    phiScale k (row (t0 + 1)) = phi (phiScale k (row t0)) := by
  have h0 : row (t0 + 1) = phiLinear (row t0) ^^^ (carry (row t0) <<< 1) :=
    Rule30UOR.Core.phi_split (row t0)
  have h1 : phi (phiScale k (row t0)) =
      phiLinear (phiScale k (row t0)) ^^^ (carry (phiScale k (row t0)) <<< 1) :=
    Rule30UOR.Core.phi_split (phiScale k (row t0))
  rw [h0, h1, phiScale_xor, phiScale_phiLinear, phiScale_shl, carry_phiScale_row_cone t0 k hcone]

/-- In Sector 0 (`r < 2^k`), `phiScale k (row t0)` reads `rdiag r t0`. -/
theorem phiScale_row_testBit_sector_zero (t0 k r : Nat) (hr : r < twopow k) :
    (phiScale k (row t0)).testBit r = rdiag r t0 := by
  change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^ ((row t0) <<< (twopow k + twopow k))).testBit r =
    rdiag r t0
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (r ≥ twopow k) = false := decide_eq_false (by omega)
  have d2 : decide (r ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [d1, d2, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false, row_testBit]

/-- In Sector 0 (`2 * t0 < r < 2^k`), `phiScale k (row t0)` vanishes outside the light cone of `row t0`. -/
theorem phiScale_row_testBit_sector_zero_gap (t0 k r : Nat) (hgt : 2 * t0 < r) (hr : r < twopow k) :
    (phiScale k (row t0)).testBit r = false := by
  rw [phiScale_row_testBit_sector_zero t0 k r hr]
  exact rdiag_gt_two_mul t0 r hgt

/-- In Sector 1 (`r < 2^k` with `2 * t0 < r + 2^k`), `phiScale k (row t0)` at bit `r + 2^k` reads `rdiag r t0`. -/
theorem phiScale_row_testBit_sector_one (t0 k r : Nat) (hr : r < twopow k)
    (hcone : 2 * t0 < r + twopow k) :
    (phiScale k (row t0)).testBit (r + twopow k) = rdiag r t0 := by
  change (((row t0) ^^^ ((row t0) <<< twopow k)) ^^^
      ((row t0) <<< (twopow k + twopow k))).testBit (r + twopow k) = rdiag r t0
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have d1 : decide (r + twopow k ≥ twopow k) = true := decide_eq_true (by omega)
  have d2 : decide (r + twopow k ≥ twopow k + twopow k) = false := decide_eq_false (by omega)
  rw [d1, d2, Bool.true_and, Bool.false_and, Bool.xor_false,
    show r + twopow k - twopow k = r by omega,
    row_testBit t0 (r + twopow k), row_testBit t0 r,
    rdiag_gt_two_mul t0 (r + twopow k) hcone, Bool.false_xor]

/-- In Sector 1 (`2 * t0 < r < 2^k`), `phiScale k (row t0)` vanishes at bit `r + 2^k`. -/
theorem phiScale_row_testBit_sector_one_gap (t0 k r : Nat) (hgt : 2 * t0 < r) (hr : r < twopow k) :
    (phiScale k (row t0)).testBit (r + twopow k) = false := by
  rw [phiScale_row_testBit_sector_one t0 k r hr (by omega)]
  exact rdiag_gt_two_mul t0 r hgt

/-- Local vanishing of `(crossCarry a b <<< 1).testBit j` when `a` vanishes at `j - 1` and `j - 2`. -/
theorem crossCarry_shl_testBit_of_left_zero (a b j : Nat)
    (ha1 : a.testBit (j - 1) = false) (ha2 : a.testBit (j - 2) = false) :
    (crossCarry a b <<< 1).testBit j = false := by
  by_cases hj1 : j ≥ 1
  · by_cases hj2 : j ≥ 2
    · change (((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))) <<< 1).testBit j = false
      simp only [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_and]
      have d1 : decide (j ≥ 1) = true := decide_eq_true hj1
      have d2 : decide (j - 1 ≥ 1) = true := decide_eq_true (by omega)
      rw [d1, d2, Bool.true_and, Bool.true_and,
        show j - 1 - 1 = j - 2 by omega, ha1, ha2]
      simp
    · have hj_eq : j = 1 := by omega
      subst hj_eq
      change (((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))) <<< 1).testBit 1 = false
      simp
  · have hj_eq : j = 0 := by omega
    subst hj_eq
    change (((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))) <<< 1).testBit 0 = false
    simp

/-- Local vanishing of `(crossCarry a b <<< 1).testBit j` when `b` vanishes at `j - 1` and `j - 2`. -/
theorem crossCarry_shl_testBit_of_right_zero (a b j : Nat)
    (hb1 : b.testBit (j - 1) = false) (hb2 : b.testBit (j - 2) = false) :
    (crossCarry a b <<< 1).testBit j = false := by
  by_cases hj1 : j ≥ 1
  · by_cases hj2 : j ≥ 2
    · change (((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))) <<< 1).testBit j = false
      simp only [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_and]
      have d1 : decide (j ≥ 1) = true := decide_eq_true hj1
      have d2 : decide (j - 1 ≥ 1) = true := decide_eq_true (by omega)
      rw [d1, d2, Bool.true_and, Bool.true_and,
        show j - 1 - 1 = j - 2 by omega, hb1, hb2]
      simp
    · have hj_eq : j = 1 := by omega
      subst hj_eq
      change (((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))) <<< 1).testBit 1 = false
      simp
  · have hj_eq : j = 0 := by omega
    subst hj_eq
    change (((a &&& (b <<< 1)) ^^^ (b &&& (a <<< 1))) <<< 1).testBit 0 = false
    simp

/-- **Unperturbed Rule 30 Evolution of `winWitt` below the 2-Adic Threshold (`j ≤ J + 1`)**: because `winWitt t0 (2^k)` vanishes on `[0, J]`, `crossCarry` vanishes on `[0, J + 1]`, so `(winWitt (t0 + 1) (2^k)).testBit j = (phi (winWitt t0 (2^k))).testBit j` for all `j ≤ J + 1` (`j ≤ 2^k`). -/
theorem winWitt_cone_step_unperturbed_below_threshold (t0 k J j : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hJ : IsRightThreshold k J)
    (hjJ : j ≤ J + 1) (hj : j ≤ twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit j = (phi (winWitt t0 (twopow k))).testBit j := by
  have hstep := congrArg (fun n => n.testBit j) (winWitt_cone_step t0 k hcone)
  rw [Nat.testBit_xor] at hstep
  have hcc : (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) <<< 1).testBit j = false := by
    by_cases hj1 : j ≥ 1
    · apply crossCarry_shl_testBit_of_right_zero
      · exact winWitt_zero_gap_of_threshold t0 k J (j - 1) hJ (by omega) (by omega)
      · exact winWitt_zero_gap_of_threshold t0 k J (j - 2) hJ (by omega) (by omega)
    · have hj0 : j = 0 := by omega
      subst hj0
      simp
  rw [hcc, Bool.xor_false] at hstep
  exact hstep

/-- **Unperturbed Rule 30 Evolution of `winWitt` in the Sector-0 Gap (`2 * t0 + 2 < j ≤ 2^k`)**: above the light cone of `row t0` in Sector 0, `phiScale k (row t0)` vanishes, so `winWitt` evolves by the exact unperturbed Rule 30 step `phi`. -/
theorem winWitt_cone_step_unperturbed_sector_zero_gap (t0 k j : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hgt : 2 * t0 + 2 < j) (hj : j ≤ twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit j = (phi (winWitt t0 (twopow k))).testBit j := by
  have hstep := congrArg (fun n => n.testBit j) (winWitt_cone_step t0 k hcone)
  rw [Nat.testBit_xor] at hstep
  have hcc : (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) <<< 1).testBit j = false := by
    apply crossCarry_shl_testBit_of_left_zero
    · exact phiScale_row_testBit_sector_zero_gap t0 k (j - 1) (by omega) (by omega)
    · exact phiScale_row_testBit_sector_zero_gap t0 k (j - 2) (by omega) (by omega)
  rw [hcc, Bool.xor_false] at hstep
  exact hstep

/-- **Complete Unperturbed Sector-0 Rule 30 Evolution before Collision (`2 * t0 < J`)**: while the light cone `2 * t0` of `row t0` is strictly below the 2-adic threshold `J`, the two zero-cross-carry regions (`j ≤ J + 1` and `2 * t0 + 2 < j ≤ 2^k`) overlap to cover all of `[0, 2^k]`, so `winWitt` evolves by the exact unperturbed Rule 30 step `phi` on every bit `j ≤ 2^k`. -/
theorem winWitt_cone_step_unperturbed_sector_zero (t0 k J j : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 < J) (hj : j ≤ twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit j = (phi (winWitt t0 (twopow k))).testBit j := by
  by_cases hjJ : j ≤ J + 1
  · exact winWitt_cone_step_unperturbed_below_threshold t0 k J j hcone hJ hjJ hj
  · exact winWitt_cone_step_unperturbed_sector_zero_gap t0 k j hcone (by omega) hj

/-- **Unperturbed Rule 30 Evolution of `winWitt` in the Sector-1 Gap (`2 * t0 + 2 < r ≤ 2^k`)**: above the shifted light cone of `row t0` in Sector 1, `phiScale k (row t0)` vanishes, so `winWitt` evolves by the exact unperturbed Rule 30 step `phi` at `j = r + 2^k`. -/
theorem winWitt_cone_step_unperturbed_sector_one_gap (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hgt : 2 * t0 + 2 < r) (hr : r ≤ twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit (r + twopow k) =
      (phi (winWitt t0 (twopow k))).testBit (r + twopow k) := by
  have hstep := congrArg (fun n => n.testBit (r + twopow k)) (winWitt_cone_step t0 k hcone)
  rw [Nat.testBit_xor] at hstep
  have hcc : (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k)) <<< 1).testBit (r + twopow k) = false := by
    apply crossCarry_shl_testBit_of_left_zero
    · rw [show r + twopow k - 1 = (r - 1) + twopow k by omega]
      exact phiScale_row_testBit_sector_one_gap t0 k (r - 1) (by omega) (by omega)
    · rw [show r + twopow k - 2 = (r - 2) + twopow k by omega]
      exact phiScale_row_testBit_sector_one_gap t0 k (r - 2) (by omega) (by omega)
  rw [hcc, Bool.xor_false] at hstep
  exact hstep

/-- **Exact Wronskian Collision at the Threshold (`J = 2 * t0`)**: when the left edge `2 * t0` of `row t0` meets the 2-adic threshold `J = 2 * t0` (`J + 1 < 2^k`), the 2x2 bit matrix of `phiScale k (row t0)` and `winWitt t0 (2^k)` at `(J, J + 1)` is the identity matrix `[[1, 0], [0, 1]]`, so `crossCarry` evaluates to `true` at bit `J + 1` and flips bit `J + 2` of `winWitt (t0 + 1) (2^k)` relative to `phi (winWitt t0 (2^k))`. -/
theorem crossCarry_collision_at_threshold (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJt : J = 2 * t0) (hJlt : J + 1 < twopow k) :
    (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (J + 1) = true ∧
      (winWitt (t0 + 1) (twopow k)).testBit (J + 2) =
        !(phi (winWitt t0 (twopow k))).testBit (J + 2) := by
  have hcone : 2 * t0 + 1 < twopow k := by omega
  have ha0 : (phiScale k (row t0)).testBit J = true := by
    rw [phiScale_row_testBit_sector_zero t0 k J (by omega), hJt]
    exact rdiag_left_edge t0
  have ha1 : (phiScale k (row t0)).testBit (J + 1) = false := by
    exact phiScale_row_testBit_sector_zero_gap t0 k (J + 1) (by omega) hJlt
  have hb0 : (winWitt t0 (twopow k)).testBit J = false :=
    winWitt_zero_gap_of_threshold t0 k J J hJ (by omega) (by omega)
  have hb1 : (winWitt t0 (twopow k)).testBit (J + 1) = true :=
    winWitt_leading_bit_of_threshold t0 k J hJ hJlt
  have hcc : (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (J + 1) = true := by
    change (((phiScale k (row t0) &&& (winWitt t0 (twopow k) <<< 1)) ^^^
      (winWitt t0 (twopow k) &&& (phiScale k (row t0) <<< 1)))).testBit (J + 1) = true
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
    have d1 : decide (J + 1 ≥ 1) = true := decide_eq_true (by omega)
    rw [d1, Bool.true_and, Bool.true_and, show J + 1 - 1 = J by omega, ha0, ha1, hb0, hb1]
    rfl
  refine ⟨hcc, ?_⟩
  have hstep := congrArg (fun n => n.testBit (J + 2)) (winWitt_cone_step t0 k hcone)
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft] at hstep
  have d2 : decide (J + 2 ≥ 1) = true := decide_eq_true (by omega)
  rw [d2, Bool.true_and, show J + 2 - 1 = J + 1 by omega, hcc] at hstep
  rw [hstep]
  cases (phi (winWitt t0 (twopow k))).testBit (J + 2) <;> rfl

theorem winWitt_collision_flip_at_threshold (t0 k J : Nat)
    (hJ : IsRightThreshold k J) (hJt : J = 2 * t0) (hJlt : J + 1 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit (J + 2) =
      !(phi (winWitt t0 (twopow k))).testBit (J + 2) :=
  (crossCarry_collision_at_threshold t0 k J hJ hJt hJlt).2

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_cone_step_unperturbed_sector_zero`. -/
theorem bit_winWitt_cone_step_unperturbed_sector_zero (t0 k J j : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 < J) (hj : j ≤ twopow k) :
    bit (winWitt (t0 + 1) (twopow k)) j = bit (phi (winWitt t0 (twopow k))) j := by
  rw [bit_eq_if_testBit, bit_eq_if_testBit,
    winWitt_cone_step_unperturbed_sector_zero t0 k J j hcone hJ htJ hj]

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_cone_step_unperturbed_sector_one_gap`. -/
theorem bit_winWitt_cone_step_unperturbed_sector_one_gap (t0 k r : Nat)
    (hcone : 2 * t0 + 1 < twopow k) (hgt : 2 * t0 + 2 < r) (hr : r ≤ twopow k) :
    bit (winWitt (t0 + 1) (twopow k)) (r + twopow k) =
      bit (phi (winWitt t0 (twopow k))) (r + twopow k) := by
  rw [bit_eq_if_testBit, bit_eq_if_testBit,
    winWitt_cone_step_unperturbed_sector_one_gap t0 k r hcone hgt hr]

/-- **Archimedean Left-Diagonal Readout in the Sector-1 Gap (`1 ≤ m`, `2 * t0 + m < 2^k`)**: above the shifted light cone `2 * t0 + 2^k` in Sector 1, `phiScale k (row t0)` vanishes, so bit `2 * t0 + m + 2^k` of `winWitt t0 (2^k)` directly reads the late left diagonal `ldiag (2^k - m) (t0 + 2^k)` without any early-time term. -/
theorem winWitt_testBit_sector_one_gap_ldiag (t0 k m : Nat)
    (hm : 1 ≤ m) (hcone : 2 * t0 + m < twopow k) :
    (winWitt t0 (twopow k)).testBit (2 * t0 + m + twopow k) =
      ldiag (twopow k - m) (t0 + twopow k) := by
  rw [winWitt_testBit_middle_ray t0 k (2 * t0 + m) hcone (by omega),
    rdiag_gt_two_mul t0 (2 * t0 + m) (by omega),
    bxor_eq_xor, Bool.xor_false,
    show 2 * t0 + m + twopow k = (t0 + twopow k) + (t0 + m) by omega,
    rdiag_add_eq_cell_neg (t0 + twopow k) (t0 + m),
    show t0 + twopow k = (twopow k - m) + (t0 + m) by omega,
    ← ldiag_eq_cell_neg (twopow k - m) (t0 + m)]

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_gap_ldiag`. -/
theorem bit_winWitt_sector_one_gap_ldiag (t0 k m : Nat)
    (hm : 1 ≤ m) (hcone : 2 * t0 + m < twopow k) :
    bit (winWitt t0 (twopow k)) (2 * t0 + m + twopow k) =
      bton (ldiag (twopow k - m) (t0 + twopow k)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_gap_ldiag t0 k m hm hcone]

/-- **Sector-1 Shifted Light-Cone Edge (`2 * t0 < 2^k`)**: at the shifted left-cone boundary `2 * t0 + 2^k`, `rdiag (2 * t0) t0 = true` flips the late left diagonal `ldiag (2^k) (t0 + 2^k)`. -/
theorem winWitt_testBit_sector_one_cone_edge (t0 k : Nat) (hcone : 2 * t0 < twopow k) :
    (winWitt t0 (twopow k)).testBit (2 * t0 + twopow k) =
      !ldiag (twopow k) (t0 + twopow k) := by
  rw [winWitt_testBit_middle_ray t0 k (2 * t0) hcone (by omega),
    rdiag_left_edge t0,
    show 2 * t0 + twopow k = (t0 + twopow k) + t0 by omega,
    rdiag_add_eq_cell_neg (t0 + twopow k) t0,
    show t0 + twopow k = twopow k + t0 by omega,
    ← ldiag_eq_cell_neg (twopow k) t0,
    bxor_eq_xor]
  cases ldiag (twopow k) (twopow k + t0) <;> rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_cone_edge`. -/
theorem bit_winWitt_sector_one_cone_edge (t0 k : Nat) (hcone : 2 * t0 < twopow k) :
    bit (winWitt t0 (twopow k)) (2 * t0 + twopow k) =
      bton (!ldiag (twopow k) (t0 + twopow k)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_cone_edge t0 k hcone]

/-- **Exact Cross-Carry Injection of `ldiag (2^k - 1)` at the Sector-1 Cone Edge (`2 * t0 + 1 < 2^k`)**: at bit `2 * t0 + 1 + 2^k`, `phiScale k (row t0)` transitions from `true` (at `2 * t0 + 2^k`) to `false` (at `2 * t0 + 1 + 2^k`), so the bilinear cross-carry with `winWitt t0 (2^k)` evaluates to `ldiag (2^k - 1) (t0 + 2^k)` and injects it into bit `2 * t0 + 2 + 2^k` of `winWitt (t0 + 1) (2^k)`. -/
theorem crossCarry_sector_one_cone_edge (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (2 * t0 + 1 + twopow k) =
      ldiag (twopow k - 1) (t0 + twopow k) ∧
    (winWitt (t0 + 1) (twopow k)).testBit (2 * t0 + 2 + twopow k) =
      bxor ((phi (winWitt t0 (twopow k))).testBit (2 * t0 + 2 + twopow k))
        (ldiag (twopow k - 1) (t0 + twopow k)) := by
  have ha0 : (phiScale k (row t0)).testBit (2 * t0 + twopow k) = true := by
    rw [phiScale_row_testBit_sector_one t0 k (2 * t0) (by omega) (by omega)]
    exact rdiag_left_edge t0
  have ha1 : (phiScale k (row t0)).testBit (2 * t0 + 1 + twopow k) = false :=
    phiScale_row_testBit_sector_one_gap t0 k (2 * t0 + 1) (by omega) hcone
  have hb1 : (winWitt t0 (twopow k)).testBit (2 * t0 + 1 + twopow k) =
      ldiag (twopow k - 1) (t0 + twopow k) :=
    winWitt_testBit_sector_one_gap_ldiag t0 k 1 (by omega) hcone
  have hcc : (crossCarry (phiScale k (row t0)) (winWitt t0 (twopow k))).testBit (2 * t0 + 1 + twopow k) =
      ldiag (twopow k - 1) (t0 + twopow k) := by
    change (((phiScale k (row t0) &&& (winWitt t0 (twopow k) <<< 1)) ^^^
      (winWitt t0 (twopow k) &&& (phiScale k (row t0) <<< 1)))).testBit (2 * t0 + 1 + twopow k) =
      ldiag (twopow k - 1) (t0 + twopow k)
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
    have d1 : decide (2 * t0 + 1 + twopow k ≥ 1) = true := decide_eq_true (by omega)
    rw [d1, Bool.true_and, Bool.true_and,
      show 2 * t0 + 1 + twopow k - 1 = 2 * t0 + twopow k by omega,
      ha0, ha1, hb1]
    cases (winWitt t0 (twopow k)).testBit (2 * t0 + twopow k) <;>
      cases ldiag (twopow k - 1) (t0 + twopow k) <;> rfl
  refine ⟨hcc, ?_⟩
  have hstep := congrArg (fun n => n.testBit (2 * t0 + 2 + twopow k)) (winWitt_cone_step t0 k hcone)
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft] at hstep
  have d2 : decide (2 * t0 + 2 + twopow k ≥ 1) = true := decide_eq_true (by omega)
  rw [d2, Bool.true_and,
    show 2 * t0 + 2 + twopow k - 1 = 2 * t0 + 1 + twopow k by omega,
    hcc, ← bxor_eq_xor] at hstep
  exact hstep

theorem winWitt_cone_step_sector_one_edge (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit (2 * t0 + 2 + twopow k) =
      bxor ((phi (winWitt t0 (twopow k))).testBit (2 * t0 + 2 + twopow k))
        (ldiag (twopow k - 1) (t0 + twopow k)) :=
  (crossCarry_sector_one_cone_edge t0 k hcone).2

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_cone_step_sector_one_edge`. -/
theorem bit_winWitt_cone_step_sector_one_edge (t0 k : Nat) (hcone : 2 * t0 + 1 < twopow k) :
    bit (winWitt (t0 + 1) (twopow k)) (2 * t0 + 2 + twopow k) =
      bton (bxor ((phi (winWitt t0 (twopow k))).testBit (2 * t0 + 2 + twopow k))
        (ldiag (twopow k - 1) (t0 + twopow k))) := by
  rw [bit_eq_bton_testBit, winWitt_cone_step_sector_one_edge t0 k hcone]

/-- **Fundamental Two-Place Diagonal Shear (`D_d(d + s) = R_{d + 2s}(d + s)`)**: at time `d + s`, left diagonal `d` coincides with right diagonal `d + 2 * s`. -/
theorem ldiag_eq_rdiag (d s : Nat) :
    ldiag d (d + s) = rdiag (d + 2 * s) (d + s) := by
  rw [ldiag_eq_cell_neg d s,
    show d + 2 * s = (d + s) + s by omega,
    rdiag_add_eq_cell_neg (d + s) s]

/-- **Right-Period Transport of Left Diagonals below the Threshold (`d + 2 * s ≤ J`)**: whenever `d + 2 * s ≤ J` (`d + 2 * s < 2^k`), the value of left diagonal `d` at early time `d + s` reappears in the right system at late time `d + s + 2^k` along right diagonal `d + 2 * s`. -/
theorem rdiag_threshold_sub_eq_ldiag (d s k J : Nat) (hJ : IsRightThreshold k J)
    (hdsJ : d + 2 * s ≤ J) (hdsk : d + 2 * s < twopow k) :
    rdiag (d + 2 * s) ((d + s) + twopow k) = ldiag d (d + s) := by
  have h0 := winWitt_zero_gap_of_threshold (d + s) k J (d + 2 * s) hJ hdsJ hdsk
  have hray0 := winWitt_testBit_lt_twopow (d + s) k (d + 2 * s) hdsk
  rw [h0, ← ldiag_eq_rdiag d s, bxor_eq_xor] at hray0
  revert hray0
  cases rdiag (d + 2 * s) ((d + s) + twopow k) <;>
    cases ldiag d (d + s) <;> decide

/-- **Right-Period Antiperiodic Transport of Left Diagonals at the Threshold (`d + 2 * s = J + 1`)**: whenever `d + 2 * s = J + 1 < 2^k`, the value of right diagonal `J + 1` at late time `d + s + 2^k` is the exact negation of left diagonal `d` at early time `d + s`. -/
theorem rdiag_threshold_succ_eq_not_ldiag (d s k J : Nat) (hJ : IsRightThreshold k J)
    (hdsJ : d + 2 * s = J + 1) (hJlt : J + 1 < twopow k) :
    rdiag (J + 1) ((d + s) + twopow k) = !ldiag d (d + s) := by
  have h1 := winWitt_leading_bit_of_threshold (d + s) k J hJ hJlt
  have hray0 := winWitt_testBit_lt_twopow (d + s) k (J + 1) hJlt
  have hld : ldiag d (d + s) = rdiag (J + 1) (d + s) := by
    rw [← hdsJ]
    exact ldiag_eq_rdiag d s
  rw [h1, ← hld, bxor_eq_xor] at hray0
  revert hray0
  cases rdiag (J + 1) ((d + s) + twopow k) <;>
    cases ldiag d (d + s) <;> decide

/-- **Unified Triality Sector 0 Readout at Slot `r = d + 2 * s < 2^k` (`t0 = d + s`)**: bit `d + 2 * s` of `winWitt (d + s) (2^k)` compares `rdiag (d + 2 * s) (d + s + 2^k)` with the early left diagonal `ldiag d (d + s)`. -/
theorem winWitt_testBit_sector_zero_ldiag (d s k : Nat) (hds : d + 2 * s < twopow k) :
    (winWitt (d + s) (twopow k)).testBit (d + 2 * s) =
      bxor (rdiag (d + 2 * s) ((d + s) + twopow k)) (ldiag d (d + s)) := by
  rw [winWitt_testBit_lt_twopow (d + s) k (d + 2 * s) hds, ldiag_eq_rdiag d s]

/-- **Unified Triality Sector 1 Readout at Slot `r = d + 2 * s < 2^k` (`t0 = d + s`)**: bit `d + 2 * s + 2^k` of `winWitt (d + s) (2^k)` compares the late shifted left diagonal `ldiag (d + 2^k) (d + s + 2^k)` with the early left diagonal `ldiag d (d + s)` (both on column `-s`). -/
theorem winWitt_testBit_sector_one_ldiag (d s k : Nat) (hds : d + 2 * s < twopow k) :
    (winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k) =
      bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d (d + s)) := by
  rw [winWitt_testBit_middle_ray (d + s) k (d + 2 * s) hds (by omega),
    ← ldiag_eq_rdiag d s,
    show d + 2 * s + twopow k = (d + twopow k) + 2 * s by omega,
    show (d + s) + twopow k = (d + twopow k) + s by omega,
    ← ldiag_eq_rdiag (d + twopow k) s]

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_ldiag`. -/
theorem bit_winWitt_sector_one_ldiag (d s k : Nat) (hds : d + 2 * s < twopow k) :
    bit (winWitt (d + s) (twopow k)) (d + 2 * s + twopow k) =
      bton (bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d (d + s))) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_ldiag d s k hds]

/-- **Sigmatics Triality D-Coupling between Sector 1 and Sector 2 (`r = d + 2 * s < 2^k`)**: XORing Sector 1 (`r + 2^k`) and Sector 2 (`r + 2^(k+1)`) of `winWitt (d + s) (2^k)` cancels the early state `ldiag d (d + s)` identically, leaving the pure late-time left-diagonal difference `bxor (ldiag (d + 2^k) (d + s + 2^k)) (ldiag d (d + s + 2^k))`. -/
theorem winWitt_testBit_sector_one_xor_two (d s k : Nat) (hds : d + 2 * s < twopow k) :
    bxor ((winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k))
      ((winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow (k + 1))) =
      bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)) := by
  rw [winWitt_testBit_sector_one_ldiag d s k hds,
    winWitt_testBit_left_ray d s k (by omega)]
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases ldiag (d + twopow k) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;>
    cases ldiag d (d + s) <;> rfl

/-- **Sigmatics Triality D-Coupling between Sector 0 and Sector 2 (`r = d + 2 * s < 2^k`)**: XORing Sector 0 (`r`) and Sector 2 (`r + 2^(k+1)`) of `winWitt (d + s) (2^k)` cancels the early state `ldiag d (d + s)` identically, leaving the pure late-time two-place difference `bxor (rdiag (d + 2 * s) (d + s + 2^k)) (ldiag d (d + s + 2^k))`. -/
theorem winWitt_testBit_sector_zero_xor_two (d s k : Nat) (hds : d + 2 * s < twopow k) :
    bxor ((winWitt (d + s) (twopow k)).testBit (d + 2 * s))
      ((winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow (k + 1))) =
      bxor (rdiag (d + 2 * s) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)) := by
  rw [winWitt_testBit_sector_zero_ldiag d s k hds,
    winWitt_testBit_left_ray d s k (by omega)]
  rw [bxor_eq_xor, bxor_eq_xor, bxor_eq_xor, bxor_eq_xor]
  cases rdiag (d + 2 * s) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;>
    cases ldiag d (d + s) <;> rfl

/-- Left diagonal `0` is identically `true` at all times `t`. -/
theorem ldiag_zero_eq_true (t : Nat) : ldiag 0 t = true := by
  rw [Rule30UOR.Kit.ldiag_eq_D]
  exact Ruliology.CellularAutomata.Rule30Diagonals.D_zero t

/-- Left diagonal `1` is identically `true` at all times `1 + m`. -/
theorem ldiag_one_eq_true (m : Nat) : ldiag 1 (1 + m) = true := by
  rw [Rule30UOR.Kit.ldiag_eq_D, show 1 + m = m + 1 by omega]
  exact Ruliology.CellularAutomata.Rule30Diagonals.D_one m

/-- **Universal Vanishing of the Top Light-Cone Edge `2 * t0 + 2^(k+1)` in `winWitt`**: because `ldiag 0` is identically `true`, the top light-cone edge of `row (t0 + 2^k)` and the top shifted edge of `phiScale k (row t0)` cancel identically at bit `2 * t0 + 2^(k+1)` for all `t0 < 2^k`. -/
theorem winWitt_testBit_top_edge_zero (t0 k : Nat) (ht0 : t0 < twopow k) :
    (winWitt t0 (twopow k)).testBit (2 * t0 + twopow (k + 1)) = false := by
  have h := winWitt_testBit_left_ray 0 t0 k (by omega)
  simp only [Nat.zero_add] at h
  rw [h, ldiag_zero_eq_true t0, ldiag_zero_eq_true (t0 + twopow k)]
  rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_top_edge_zero`. -/
theorem bit_winWitt_top_edge_zero (t0 k : Nat) (ht0 : t0 < twopow k) :
    bit (winWitt t0 (twopow k)) (2 * t0 + twopow (k + 1)) = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_top_edge_zero t0 k ht0]; rfl

/-- **Universal Vanishing of the Second Light-Cone Edge `1 + 2 * m + 2^(k+1)` in `winWitt`**: because `ldiag 1 (1 + m) = true` for all `m`, bit `1 + 2 * m + 2^(k+1)` of `winWitt (1 + m) (2^k)` vanishes for all `1 + m < 2^k`. -/
theorem winWitt_testBit_second_edge_zero (m k : Nat) (hm : 1 + m < twopow k) :
    (winWitt (1 + m) (twopow k)).testBit (1 + 2 * m + twopow (k + 1)) = false := by
  rw [winWitt_testBit_left_ray 1 m k hm,
    ldiag_one_eq_true m,
    show (1 + m) + twopow k = 1 + (m + twopow k) by omega,
    ldiag_one_eq_true (m + twopow k)]
  rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_second_edge_zero`. -/
theorem bit_winWitt_second_edge_zero (m k : Nat) (hm : 1 + m < twopow k) :
    bit (winWitt (1 + m) (twopow k)) (1 + 2 * m + twopow (k + 1)) = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_second_edge_zero m k hm]; rfl

/-! ### 2-Adic Threshold Spacetime Geometry and Archimedean Sector-2 Settling Laws -/

/-- **Late White Window below the 2-Adic Threshold (`2 * t0 < j ≤ J`)**: every right diagonal `j` between the early cone edge `2 * t0` and the threshold `J` vanishes at the late time `t0 + 2^k`. -/
theorem rdiag_threshold_late_false_window (t0 k J j : Nat) (hJ : IsRightThreshold k J)
    (hgt : 2 * t0 < j) (hjJ : j ≤ J) :
    rdiag j (t0 + twopow k) = false := by
  have hper := Rule30UOR.KitConstructive.per_mono_le hjJ hJ.1
  have heq : rdiag j (t0 + twopow k) = rdiag j t0 := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact hper t0
  rw [heq]
  exact rdiag_gt_two_mul t0 j hgt

/-- **Universal Late Black Plateau at `J + 1` before Cone Arrival (`2 * t0 ≤ J`)**: for every `t0` with `2 * t0 ≤ J`, right diagonal `J + 1` is identically `true` at the late time `t0 + 2^k`. -/
theorem rdiag_threshold_late_true_plateau (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 ≤ J) :
    rdiag (J + 1) (t0 + twopow k) = true := by
  have ha : rdiag (J + 1) (t0 + twopow k) = !rdiag (J + 1) t0 := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact Rule30UOR.KitConstructive.antiperiod hJ.1 hJ.2 t0
  rw [ha, rdiag_gt_two_mul t0 (J + 1) (by omega)]
  rfl

/-- **Odd-Threshold Plateau Termination at Cone Arrival (`2 * t0 = J + 1`)**: when `J` is odd and the early left-cone edge hits `J + 1 = 2 * t0`, the late right diagonal `rdiag (J + 1) (t0 + 2^k)` turns `false`. -/
theorem rdiag_threshold_late_false_odd_hit (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 = J + 1) :
    rdiag (J + 1) (t0 + twopow k) = false := by
  have ha : rdiag (J + 1) (t0 + twopow k) = !rdiag (J + 1) t0 := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact Rule30UOR.KitConstructive.antiperiod hJ.1 hJ.2 t0
  have h1 : rdiag (J + 1) t0 = true := by
    rw [← htJ]
    exact rdiag_left_edge t0
  rw [ha, h1]
  rfl

/-- **Even-Threshold Plateau Termination at Cone Arrival (`2 * t0 = J`)**: when `J = 2 * t0` is even, at the next step `t0 + 1` (where the second left diagonal `ldiag 1` hits `J + 1 = 1 + 2 * t0`), the late right diagonal `rdiag (J + 1) ((t0 + 1) + 2^k)` turns `false`. -/
theorem rdiag_threshold_late_false_even_hit (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 = J) :
    rdiag (J + 1) ((t0 + 1) + twopow k) = false := by
  have ha : rdiag (J + 1) ((t0 + 1) + twopow k) = !rdiag (J + 1) (t0 + 1) := by
    rw [Rule30UOR.Right.rdiag_eq_R, Rule30UOR.Right.rdiag_eq_R, twopow_eq_pow k]
    exact Rule30UOR.KitConstructive.antiperiod hJ.1 hJ.2 (t0 + 1)
  have h1 : rdiag (J + 1) (t0 + 1) = true := by
    rw [show J + 1 = 1 + 2 * t0 by omega, show t0 + 1 = 1 + t0 by omega,
      ← ldiag_eq_rdiag 1 t0]
    exact ldiag_one_eq_true t0
  rw [ha, h1]
  rfl

/-- **Strict Period-2 Alternation of `rdiag (J + 2)` along the Late Threshold Plateau (`2 * t0 ≤ J`)**: because `rdiag (J + 1) (t0 + 2^k) = true` for all `2 * t0 ≤ J`, the next right diagonal `rdiag (J + 2)` flips at every step `t0 + 2^k ↦ (t0 + 1) + 2^k`. -/
theorem rdiag_threshold_plus_two_step_neg (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 ≤ J) :
    rdiag (J + 2) ((t0 + 1) + twopow k) = !rdiag (J + 2) (t0 + twopow k) := by
  rw [show (t0 + 1) + twopow k = (t0 + twopow k) + 1 by omega,
    Rule30UOR.Core.rdiag_step J (t0 + twopow k),
    rdiag_threshold_late_true_plateau t0 k J hJ htJ,
    Bool.true_or, bxor_eq_xor]
  cases rdiag (J + 2) (t0 + twopow k) <;> rfl

/-- **Strict Alternation of Bit `J + 2` of `winWitt` before Cone Collision (`2 * t0 < J`)**: for `2 * t0 < J` and `J + 2 < 2^k`, bit `J + 2` of `winWitt t0 (2^k)` flips at every step `t0 ↦ t0 + 1`. -/
theorem winWitt_testBit_threshold_plus_two_step_neg (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 < J) (hJlt : J + 2 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit (J + 2) =
      !(winWitt t0 (twopow k)).testBit (J + 2) := by
  rw [winWitt_testBit_lt_twopow (t0 + 1) k (J + 2) hJlt,
    winWitt_testBit_lt_twopow t0 k (J + 2) hJlt,
    rdiag_gt_two_mul (t0 + 1) (J + 2) (by omega),
    rdiag_gt_two_mul t0 (J + 2) (by omega),
    rdiag_threshold_plus_two_step_neg t0 k J hJ (by omega),
    bxor_eq_xor, bxor_eq_xor]
  cases rdiag (J + 2) (t0 + twopow k) <;> rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_threshold_plus_two_step_neg`. -/
theorem bit_winWitt_threshold_plus_two_step_neg (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 < J) (hJlt : J + 2 < twopow k) :
    bit (winWitt (t0 + 1) (twopow k)) (J + 2) =
      bton (!(winWitt t0 (twopow k)).testBit (J + 2)) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_threshold_plus_two_step_neg t0 k J hJ htJ hJlt]

/-- **Collision Freeze of Bit `J + 2` of `winWitt` at `2 * t0 = J`**: at the exact Wronskian collision `2 * t0 = J` (`J + 2 < 2^k`), the arrival of the early left-cone edge `rdiag (2 * (t0 + 1)) (t0 + 1) = true` cancels the late alternation of `rdiag (J + 2)`, so bit `J + 2` of `winWitt` freezes (`winWitt (t0 + 1) = winWitt t0` at bit `J + 2`). -/
theorem winWitt_testBit_threshold_plus_two_collision_freeze (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 = J) (hJlt : J + 2 < twopow k) :
    (winWitt (t0 + 1) (twopow k)).testBit (J + 2) =
      (winWitt t0 (twopow k)).testBit (J + 2) := by
  have hearly1 : rdiag (J + 2) (t0 + 1) = true := by
    rw [show J + 2 = 2 * (t0 + 1) by omega]
    exact rdiag_left_edge (t0 + 1)
  rw [winWitt_testBit_lt_twopow (t0 + 1) k (J + 2) hJlt,
    winWitt_testBit_lt_twopow t0 k (J + 2) hJlt,
    hearly1,
    rdiag_gt_two_mul t0 (J + 2) (by omega),
    rdiag_threshold_plus_two_step_neg t0 k J hJ (by omega),
    bxor_eq_xor, bxor_eq_xor]
  cases rdiag (J + 2) (t0 + twopow k) <;> rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_threshold_plus_two_collision_freeze`. -/
theorem bit_winWitt_threshold_plus_two_collision_freeze (t0 k J : Nat) (hJ : IsRightThreshold k J)
    (htJ : 2 * t0 = J) (hJlt : J + 2 < twopow k) :
    bit (winWitt (t0 + 1) (twopow k)) (J + 2) =
      bit (winWitt t0 (twopow k)) (J + 2) := by
  rw [bit_eq_bton_testBit, bit_eq_bton_testBit,
    winWitt_testBit_threshold_plus_two_collision_freeze t0 k J hJ htJ hJlt]

/-- Left diagonal `2` is identically `false` at all times `2 + m` (the universal zero diagonal at depth `2`). -/
theorem ldiag_two_eq_false (m : Nat) : ldiag 2 (2 + m) = false := by
  rw [show 2 + m = (1 + m) + 1 by omega,
    Rule30UOR.Core.ldiag_step 0 (1 + m),
    ldiag_zero_eq_true (1 + m),
    ldiag_one_eq_true m]
  rfl

/-- **Universal Vanishing of the Third Light-Cone Edge `2 + 2 * m + 2^(k+1)` in `winWitt`**: because `ldiag 2 (2 + m) = false` for all `m`, bit `2 + 2 * m + 2^(k+1)` of `winWitt (2 + m) (2^k)` vanishes for all `2 + m < 2^k`. -/
theorem winWitt_testBit_third_edge_zero (m k : Nat) (hm : 2 + m < twopow k) :
    (winWitt (2 + m) (twopow k)).testBit (2 + 2 * m + twopow (k + 1)) = false := by
  rw [winWitt_testBit_left_ray 2 m k hm,
    ldiag_two_eq_false m,
    show (2 + m) + twopow k = 2 + (m + twopow k) by omega,
    ldiag_two_eq_false (m + twopow k)]
  rfl

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_third_edge_zero`. -/
theorem bit_winWitt_third_edge_zero (m k : Nat) (hm : 2 + m < twopow k) :
    bit (winWitt (2 + m) (twopow k)) (2 + 2 * m + twopow (k + 1)) = 0 := by
  rw [bit_eq_if_testBit, winWitt_testBit_third_edge_zero m k hm]; rfl

/-- Left diagonal `3` strictly alternates (`!ldiag 3 (2 + m)`) for all `m` behind the zero diagonal at depth `2`. -/
theorem ldiag_three_step_neg (m : Nat) : ldiag 3 (3 + m) = !ldiag 3 (2 + m) := by
  rw [show 3 + m = (2 + m) + 1 by omega,
    Rule30UOR.Core.ldiag_step 1 (2 + m),
    show 2 + m = 1 + (1 + m) by omega,
    ldiag_one_eq_true (1 + m),
    show 1 + (1 + m) = 2 + m by omega,
    ldiag_two_eq_false m,
    Bool.false_or, bxor_eq_xor]
  cases ldiag 3 (2 + m) <;> rfl

/-- **Sector 1 Late-Slice Reduction on Settled Left Diagonals (`SettledBy d (d + s)`)**: once left diagonal `d ≤ k` has settled by time `d + s` (`d + 2 * s < 2^k`), Sector 2 vanishes (`ldiag d (d + s + 2^k) = ldiag d (d + s)`), so Sector 1 (`d + 2 * s + 2^k`) reduces to the pure late-time left-diagonal difference `bxor (ldiag (d + 2^k) (d + s + 2^k)) (ldiag d (d + s + 2^k))`. -/
theorem winWitt_testBit_sector_one_settled (d s k : Nat) (hk : d ≤ k)
    (hds : d + 2 * s < twopow k) (hset : SettledBy d (d + s)) :
    (winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k) =
      bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k)) := by
  have h2 := winWitt_testBit_left_settled_zero d s k hk (by omega) hset
  have hxor := winWitt_testBit_sector_one_xor_two d s k hds
  rw [h2] at hxor
  revert hxor
  rw [bxor_eq_xor, bxor_eq_xor]
  cases (winWitt (d + s) (twopow k)).testBit (d + 2 * s + twopow k) <;>
    cases ldiag (d + twopow k) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;> decide

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_one_settled`. -/
theorem bit_winWitt_sector_one_settled (d s k : Nat) (hk : d ≤ k)
    (hds : d + 2 * s < twopow k) (hset : SettledBy d (d + s)) :
    bit (winWitt (d + s) (twopow k)) (d + 2 * s + twopow k) =
      bton (bxor (ldiag (d + twopow k) ((d + s) + twopow k)) (ldiag d ((d + s) + twopow k))) := by
  rw [bit_eq_bton_testBit, winWitt_testBit_sector_one_settled d s k hk hds hset]

/-- **Two-Place Late Diagonal Agreement below Both Thresholds**: whenever slot `r = d + 2 * s < 2^k` lies below the 2-adic right-period threshold (`d + 2 * s ≤ J`) AND left diagonal `d ≤ k` has settled by `d + s` (`SettledBy d (d + s)`), both Sector 0 and Sector 2 vanish, forcing `rdiag (d + 2 * s) (d + s + 2^k) = ldiag d (d + s + 2^k)`. -/
theorem rdiag_eq_ldiag_of_settled_below_threshold (d s k J : Nat) (hJ : IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s ≤ J) (hds : d + 2 * s < twopow k)
    (hset : SettledBy d (d + s)) :
    rdiag (d + 2 * s) ((d + s) + twopow k) = ldiag d ((d + s) + twopow k) := by
  have h0 := winWitt_zero_gap_of_threshold (d + s) k J (d + 2 * s) hJ hdJ hds
  have h2 := winWitt_testBit_left_settled_zero d s k hk (by omega) hset
  have hxor := winWitt_testBit_sector_zero_xor_two d s k hds
  rw [h0, h2] at hxor
  revert hxor
  rw [bxor_eq_xor, bxor_eq_xor]
  cases rdiag (d + 2 * s) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;> decide

/-- **Two-Place Late Diagonal Antiperiodicity at the 2-Adic Threshold on Settled Left Diagonals**: when `d + 2 * s = J + 1 < 2^k` and `SettledBy d (d + s)` (`d ≤ k`), Sector 0 is `true` while Sector 2 is `false`, forcing `rdiag (J + 1) (d + s + 2^k) = !ldiag d (d + s + 2^k)`. -/
theorem rdiag_eq_not_ldiag_of_settled_at_threshold (d s k J : Nat) (hJ : IsRightThreshold k J)
    (hk : d ≤ k) (hdJ : d + 2 * s = J + 1) (hJlt : J + 1 < twopow k)
    (hset : SettledBy d (d + s)) :
    rdiag (J + 1) ((d + s) + twopow k) = !ldiag d ((d + s) + twopow k) := by
  have hds : d + 2 * s < twopow k := by omega
  have h0 : (winWitt (d + s) (twopow k)).testBit (d + 2 * s) = true := by
    rw [hdJ]
    exact winWitt_leading_bit_of_threshold (d + s) k J hJ hJlt
  have h2 := winWitt_testBit_left_settled_zero d s k hk (by omega) hset
  have hxor := winWitt_testBit_sector_zero_xor_two d s k hds
  rw [h0, h2, hdJ] at hxor
  revert hxor
  rw [bxor_eq_xor, bxor_eq_xor]
  cases rdiag (J + 1) ((d + s) + twopow k) <;>
    cases ldiag d ((d + s) + twopow k) <;> decide

/-- **Universal Scale Invariance of Triality Sector 2 in the Archimedean Damage Band**: for any two scales `k1, k2 ≥ d` such that `(d + s) + 2^k1` and `(d + s) + 2^k2` have passed `settle d`, bit `d + 2 * s + 2^(k+1)` of `winWitt (d + s) (2^k)` takes the exact same value at `k1` and `k2`. -/
theorem winWitt_testBit_sector_two_scale_eq (d s k1 k2 : Nat)
    (hk1 : d ≤ k1) (hk2 : d ≤ k2)
    (hds1 : d + s < twopow k1) (hds2 : d + s < twopow k2)
    (hset1 : SettledBy d ((d + s) + twopow k1))
    (hset2 : SettledBy d ((d + s) + twopow k2)) :
    (winWitt (d + s) (twopow k1)).testBit (d + 2 * s + twopow (k1 + 1)) =
      (winWitt (d + s) (twopow k2)).testBit (d + 2 * s + twopow (k2 + 1)) := by
  rw [winWitt_testBit_left_damage d s k1 hk1 hds1 hset1,
    winWitt_testBit_left_damage d s k2 hk2 hds2 hset2]

/-- Paper-facing `bit` (`wittbit`) wrapper for `winWitt_testBit_sector_two_scale_eq`. -/
theorem bit_winWitt_sector_two_scale_eq (d s k1 k2 : Nat)
    (hk1 : d ≤ k1) (hk2 : d ≤ k2)
    (hds1 : d + s < twopow k1) (hds2 : d + s < twopow k2)
    (hset1 : SettledBy d ((d + s) + twopow k1))
    (hset2 : SettledBy d ((d + s) + twopow k2)) :
    bit (winWitt (d + s) (twopow k1)) (d + 2 * s + twopow (k1 + 1)) =
      bit (winWitt (d + s) (twopow k2)) (d + 2 * s + twopow (k2 + 1)) := by
  rw [bit_eq_bton_testBit, bit_eq_bton_testBit,
    winWitt_testBit_sector_two_scale_eq d s k1 k2 hk1 hk2 hds1 hds2 hset1 hset2]

/-- **Center-Slot Triality Sector 1 ⊕ Sector 2 Cross-Scale Identity (`s = 0`, `r = d ≤ k`)**: at `t0 = d`, XORing Sector 1 (`d + 2^k`) and Sector 2 (`d + 2^(k+1)`) of `winWitt d (2^k)` equals the cross-scale Witt difference `bxor (wittRespBool d (k + 1)) (wittRespBool (d + 2^k) k)`. -/
theorem winWitt_testBit_center_sector_one_xor_two_witt (d k : Nat) (hk : d ≤ k) :
    bxor ((winWitt d (twopow k)).testBit (d + twopow k))
      ((winWitt d (twopow k)).testBit (d + twopow (k + 1))) =
      bxor (wittRespBool d (k + 1)) (wittRespBool (d + twopow k) k) := by
  have hdk : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hdk1 : d < twopow (k + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k + 1))
  have hs1 : (winWitt d (twopow k)).testBit (d + twopow k) = wittRespBool d k := rfl
  have hs2 := winWitt_testBit_archimedean d k hk
  have htp := two_places_witt_scale d k hk
  have hc0 := center_witt_scale_cone d k hdk
  have hc1 := center_witt_scale_cone d (k + 1) hdk1
  rw [Rule30UOR.Core.twopow_succ, ← Nat.add_assoc] at hc1
  rw [hs1, hs2, htp]
  revert hc0 hc1
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center d <;>
    cases Rule30UOR.Core.center (d + twopow k) <;>
    cases Rule30UOR.Core.center ((d + twopow k) + twopow k) <;>
    cases wittRespBool d k <;>
    cases wittRespBool d (k + 1) <;>
    cases wittRespBool (d + twopow k) k <;> decide

/-- **Cross-Scale Witt Identity for the Late Two-Place Difference (`d ≤ k`)**: for every `d ≤ k` (without any settling assumption), the difference `bxor (center (d + 2^k)) (ldiag d (d + 2^k))` between the late center and the late left diagonal equals the cross-scale Witt difference `bxor (wittRespBool d (k + 1)) (wittRespBool (d + 2^k) k)`. -/
theorem center_late_xor_ldiag_eq_witt_cross_scale (d k : Nat) (hk : d ≤ k) :
    bxor (Rule30UOR.Core.center (d + twopow k)) (ldiag d (d + twopow k)) =
      bxor (wittRespBool d (k + 1)) (wittRespBool (d + twopow k) k) := by
  have hdk : d < twopow k := Nat.lt_of_le_of_lt hk (twopow_gt_self k)
  have hxor := winWitt_testBit_sector_one_xor_two d 0 k (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at hxor
  have hcent : ldiag (d + twopow k) (d + twopow k) = Rule30UOR.Core.center (d + twopow k) := by
    have h0 := ldiag_eq_cell_neg (d + twopow k) 0
    simp only [Nat.add_zero] at h0
    exact h0
  rw [hcent] at hxor
  rw [← hxor]
  exact winWitt_testBit_center_sector_one_xor_two_witt d k hk

/-- **Unsettled Repeat-Lag Lock between Left Diagonals and Late Witt Responses**: under `CenterPeriodic T P`, for any two repeat scales `lag P k1 = lag P k2` and any `T ≤ d ≤ min(k1, k2)` (without any settling assumption), the left-diagonal difference `bxor (ldiag d (d + 2^k1)) (ldiag d (d + 2^k2))` equals the late Witt response difference `bxor (wittRespBool (d + 2^k1) k1) (wittRespBool (d + 2^k2) k2)`. -/
theorem periodic_ldiag_xor_eq_late_witt_xor_of_lag_eq (T P : Nat) (hP : 0 < P)
    (h : Rule30UOR.Scale.CenterPeriodic T P)
    (d k1 k2 : Nat) (hlag : Rule30UOR.Scale.lag P k1 = Rule30UOR.Scale.lag P k2)
    (ht : T ≤ d) (hk1 : d ≤ k1) (hk2 : d ≤ k2) :
    bxor (ldiag d (d + twopow k1)) (ldiag d (d + twopow k2)) =
      bxor (wittRespBool (d + twopow k1) k1) (wittRespBool (d + twopow k2) k2) := by
  have hd_k1s : d < twopow (k1 + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k1 + 1))
  have hd_k2s : d < twopow (k2 + 1) := Nat.lt_of_le_of_lt (by omega) (twopow_gt_self (k2 + 1))
  have hw1 := periodic_witt_eq_of_lag_eq T P hP h (k1 + 1) (k2 + 1) d
    (lag_succ_eq_of_lag_eq P k1 k2 hlag) ht hd_k1s hd_k2s
  have hc1 := Rule30UOR.Scale.center_mod hP h d (twopow k1) ht
  have hc2 := Rule30UOR.Scale.center_mod hP h d (twopow k2) ht
  have hceq : Rule30UOR.Core.center (d + twopow k1) = Rule30UOR.Core.center (d + twopow k2) := by
    rw [hc1, hc2]; unfold Rule30UOR.Scale.lag at hlag; rw [hlag]
  have hx1 := center_late_xor_ldiag_eq_witt_cross_scale d k1 hk1
  have hx2 := center_late_xor_ldiag_eq_witt_cross_scale d k2 hk2
  rw [hceq, hw1] at hx1
  revert hx1 hx2
  simp only [bxor_eq_xor]
  cases Rule30UOR.Core.center (d + twopow k2) <;>
    cases ldiag d (d + twopow k1) <;>
    cases ldiag d (d + twopow k2) <;>
    cases wittRespBool d (k2 + 1) <;>
    cases wittRespBool (d + twopow k1) k1 <;>
    cases wittRespBool (d + twopow k2) k2 <;> decide

end Rule30UOR.Interfaces
