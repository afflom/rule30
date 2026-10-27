module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
public import Ruliology.CellularAutomata.Rule30Ether

/-!
# Rule 30, period 2: the coupled question `CQ01` and the ether as an infinite witness

`Q01` (`Rule30ZeroBoundary.Q01`) only uses the left half. An eventual period `2` also constrains
the right half: with the center black at the even steps, column `1` at every white step is the
complement of column `-1` (`Rule30PeriodTwo.p1_odd`), and the right half evolves as the half driven
by the alternating column (`Rule30Ether.drv`).

* `CQ01`: **the coupled question** (open). No pair of a finitely supported ZBL start `L` and a
  finitely supported right half `R` such that, with column `0` alternating black at the even steps,
  `R` evolves as the driven right half, column `-1` of `L` is black at every black step, and at
  every white step column `-1` of `L` is the complement of column `1` of `R`.
* `CQ01_of_Q01`: `Q01` implies `CQ01`. `no_eventual_period_two_of_CQ01`: `CQ01` excludes an
  eventually 2-periodic center column, for every transient.

**The ether.** The 7×4 ether of `Rule30Ether` is the orbit of `c7` from the two-sided barrier
(`c7_eq_ether`, up to a spatial shift of `4`). Read from its alternating column B4:
* `etherLeft_zbl`: its left half is a ZBL orbit (B3 is black wherever B4 is: `B4_imp_B3`);
* `ether_col1_black`, `ether_free_bits`: column `-1` is black at the black steps and the free bits
  alternate `0, 1, 0, 1, …`; `etherLeft_eq_Theta`: the ether's left half is the constrained start
  `Theta` of the alternating free bits;
* `etherRight_drv`, `ether_coupled_witness`: its right half is the right half driven by the
  alternating column, and the free bits are the complement of column `1` at the white steps.
So the ether satisfies every condition of `CQ01` except finite support: as for `Q01` (whose
infinite witness is the stripe, `Rule30ZeroBoundary.zrow_stripe`), finite support is essential.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoCoupled

open Rule30Jen Rule30Prize Rule30ZeroBoundary
open Rule30Ether (ether ether_rule ether_congr drv drv_col0 drv_init cell_eq_drv)

/-! ### The coupled question -/

/-- The alternating column, black at the even steps. -/
def altCol (t : Nat) : Bool := t % 2 == 0

/-- **`CQ01`** (open): no finitely supported ZBL start `L` and finitely supported right half `R`
such that, with column `0` alternating black at the even steps, column `-1` of `L` is black at the
black steps and is the complement of column `1` of the driven right half at the white steps. -/
def CQ01 : Prop :=
  ¬ ∃ L R : Nat → Bool, FinSupp L ∧ FinSupp R ∧ (∀ s, zrow L (2 * s) 1 = true) ∧
    ∀ s, zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1

/-- `Q01` implies `CQ01`. -/
theorem CQ01_of_Q01 (hQ : Q01) : CQ01 := by
  rintro ⟨L, R, hL, -, hX, -⟩
  exact hQ L hL hX

/-- **`CQ01` excludes an eventually 2-periodic center column**, for every transient. (The constant
case is excluded by `Rule30Prize.center_not_eventually_constant`, through
`Rule30PeriodTwo.normalize`.) -/
theorem no_eventual_period_two_of_CQ01 (hC : CQ01) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hT0⟩
  obtain ⟨T, hT⟩ := Rule30PeriodTwo.normalize hT0
  have hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
    intro t ht
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
    · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
      rw [(hT j).2]; cases cell (T + 2 * j) 0 <;> rfl
    · show (cell (T + 2 * j + 1) 0 && cell (T + 2 * j + 1 + 1) 0) = false
      rw [(hT j).2]; rfl
  have hz := left_half_is_zbl hw
  have hdrv : (fun t => cell (T + t) 0) = altCol := by
    funext t
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = 2 * j ∨ t = 2 * j + 1 := ⟨t / 2, by omega⟩
    · rw [(hT j).1]; unfold altCol; simp
    · rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega, (hT j).2]; unfold altCol
      simp [show (2 * j + 1) % 2 = 1 by omega]
  refine hC ⟨leftRow T, fun p => cell T (p : Int), ⟨T, leftRow_fin T⟩,
    ⟨T, fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)⟩, fun s => ?_, fun s => ?_⟩
  · rw [hz (2 * s) 1 (Nat.le_refl 1)]
    exact Rule30PeriodTwo.m1_even hT s
  · rw [hz (2 * s + 1) 1 (Nat.le_refl 1), ← hdrv, ← cell_eq_drv T (2 * s + 1) 1]
    show cell (T + 2 * s + 1) (-1) = !cell (T + 2 * s + 1) 1
    rw [Rule30PeriodTwo.p1_odd hT s]
    cases cell (T + 2 * s + 1) (-1) <;> rfl

/-! ### The ether as an infinite witness -/

open Rule30ZeroBoundaryBarriers (c7 evol_c7_shift evol_c7_period_mul)

theorem c7_ether_check : ∀ a : Nat, a < 7 → ∀ b : Nat, b < 4 →
    Rule30Realization.evol c7 b ((a : Int) + 4) = ether a b := by decide

/-- **`c7` is the ether** up to a spatial shift of `4`: column `j + 4` of the orbit of `c7` is ether
column `j`, at every time. -/
theorem c7_eq_ether (j t : Nat) : Rule30Realization.evol c7 t ((j : Int) + 4) = ether j t := by
  have hj : (j : Int) + 4 = ((j % 7 : Nat) : Int) + 4 + 7 * ((j / 7 : Nat) : Int) := by omega
  have ht : t = t % 4 + 4 * (t / 4) := by omega
  rw [hj, evol_c7_shift, ht, evol_c7_period_mul,
    ether_congr (j' := j % 7) (φ' := t % 4) (by omega) (by omega)]
  exact c7_ether_check _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))

/-- Kernel check on the ether columns: B3 is black wherever B4 is; B4 alternates; B3 is the
complement of B5 at the even phases. -/
theorem ether_check : (∀ φ, φ < 4 → ether 3 φ = true → ether 2 φ = true) ∧
    (∀ φ, φ < 4 → ether 3 φ = (φ % 2 == 1)) ∧
    (∀ φ, φ < 4 → φ % 2 = 0 → ether 2 φ = !ether 4 φ) ∧
    (∀ φ, φ < 4 → φ % 2 = 0 → ether 2 φ = (φ == 0)) := by decide

theorem ether_mod (j φ : Nat) : ether j φ = ether j (φ % 4) := ether_congr rfl (by omega)

/-- B3 is black wherever B4 is black. -/
theorem B4_imp_B3 (φ : Nat) (h : ether 3 φ = true) : ether 2 φ = true := by
  rw [ether_mod] at h ⊢
  exact ether_check.1 _ (Nat.mod_lt _ (by decide)) h

/-- The alternating column is B4, one phase later. -/
theorem altCol_eq_B4 (t : Nat) : altCol t = ether 3 (t + 1) := by
  rw [ether_mod, ether_check.2.1 _ (Nat.mod_lt _ (by decide))]
  unfold altCol
  rw [show (t + 1) % 4 % 2 = (t + 1) % 2 by omega]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [h, show (t + 1) % 2 = 1 by omega]; rfl
  · rw [h, show (t + 1) % 2 = 0 by omega]; rfl

/-- The left half of the ether, read leftwards from B4 as a ZBL start at phase `φ`: depth `k ≥ 1`
is ether column `3 - k (mod 7)`. -/
def etherLeft (φ : Nat) (k : Nat) : Bool := if k = 0 then false else ether (3 + 6 * k) φ

/-- **The ether's left half is a ZBL orbit**: replacing B4 by a white wall does not change it. -/
theorem etherLeft_zbl (φ : Nat) : ∀ t k, zrow (etherLeft φ) t k = etherLeft (φ + t) k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ j =>
      rw [zrow_succ, ih, ih, ih]
      show _ = ether (3 + 6 * (j + 1)) (φ + (t + 1))
      rw [show φ + (t + 1) = (φ + t) + 1 by omega, ether_rule]
      have e1 : etherLeft (φ + t) (j + 2) = ether (3 + 6 * (j + 1) + 6) (φ + t) := by
        show ether (3 + 6 * (j + 2)) (φ + t) = _
        exact ether_congr (by omega) rfl
      have e2 : etherLeft (φ + t) (j + 1) = ether (3 + 6 * (j + 1)) (φ + t) := rfl
      rw [e1, e2]
      unfold rule
      congr 1
      cases j with
      | zero =>
        have h3 : ether (3 + 6 * (0 + 1) + 1) (φ + t) = ether 3 (φ + t) := ether_congr (by omega) rfl
        have h2 : ether (3 + 6 * (0 + 1)) (φ + t) = ether 2 (φ + t) := ether_congr (by omega) rfl
        rw [h3, h2, show etherLeft (φ + t) 0 = false from rfl]
        cases hb : ether 3 (φ + t)
        · rfl
        · rw [B4_imp_B3 _ hb]; rfl
      | succ i =>
        have e3 : etherLeft (φ + t) (i + 1) = ether (3 + 6 * (i + 1 + 1) + 1) (φ + t) := by
          show ether (3 + 6 * (i + 1)) (φ + t) = _
          exact ether_congr (by omega) rfl
        rw [e3]

/-- Column `-1` of the ether's left half is black at the black steps. -/
theorem ether_col1_black (s : Nat) : zrow (etherLeft 1) (2 * s) 1 = true := by
  rw [etherLeft_zbl]
  show ether (3 + 6 * 1) (1 + 2 * s) = true
  rw [ether_congr (j' := 2) (φ' := 1 + 2 * s) (by omega) rfl]
  apply B4_imp_B3
  rw [show 1 + 2 * s = 2 * s + 1 by omega, ← altCol_eq_B4]
  unfold altCol; simp

/-- The free bits of the ether's left half alternate `0, 1, 0, 1, …`. -/
theorem ether_free_bits (s : Nat) : zrow (etherLeft 1) (2 * s + 1) 1 = (s % 2 == 1) := by
  rw [etherLeft_zbl]
  show ether (3 + 6 * 1) (1 + (2 * s + 1)) = _
  rw [ether_congr (j' := 2) (φ' := (2 * s + 2) % 4) (by omega) (by omega),
    ether_check.2.2.2 _ (Nat.mod_lt _ (by decide)) (by omega)]
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · rw [show (2 * s + 2) % 4 = 2 by omega, h]; rfl
  · rw [show (2 * s + 2) % 4 = 0 by omega, h]; rfl

/-- The ether's left half is the constrained start with alternating free bits. -/
theorem etherLeft_eq_Theta : zrow (etherLeft 1) 0 = Theta (fun s => s % 2 == 1) :=
  Theta_unique ether_col1_black ether_free_bits

/-- The right half of the ether at phase `φ`: column `p` is ether column `3 + p`. -/
def etherRight (φ : Nat) (p : Nat) : Bool := ether (3 + p) φ

/-- **The ether's right half is the right half driven by the alternating column.** -/
theorem etherRight_drv : ∀ t p, drv altCol (etherRight 1) t p = ether (3 + p) (1 + t) := by
  intro t
  induction t with
  | zero =>
    intro p
    cases p with
    | zero => rw [drv_col0, altCol_eq_B4]
    | succ q => rw [drv_init _ _ _ (by omega)]; rfl
  | succ t ih =>
    intro p
    cases p with
    | zero => rw [drv_col0, altCol_eq_B4, show t + 1 + 1 = 1 + (t + 1) by omega]
    | succ q =>
      show rule (drv altCol (etherRight 1) t q) (drv altCol (etherRight 1) t (q + 1))
        (drv altCol (etherRight 1) t (q + 2)) = _
      rw [ih, ih, ih, show 1 + (t + 1) = (1 + t) + 1 by omega, ether_rule,
        ether_congr (j := 3 + q) (j' := 3 + (q + 1) + 6) (φ := 1 + t) (φ' := 1 + t) (by omega) rfl,
        ether_congr (j := 3 + (q + 2)) (j' := 3 + (q + 1) + 1) (φ := 1 + t) (φ' := 1 + t) (by omega) rfl]

/-- **The ether is an infinite coupled witness.** Its left half `etherLeft 1` and right half
`etherRight 1` (driven by the alternating column, black at the even steps) satisfy every condition
of `CQ01` except finite support. -/
theorem ether_coupled_witness :
    (∀ s, zrow (etherLeft 1) (2 * s) 1 = true) ∧
    (∀ s, zrow (etherLeft 1) (2 * s + 1) 1 = !drv altCol (etherRight 1) (2 * s + 1) 1) := by
  refine ⟨ether_col1_black, fun s => ?_⟩
  rw [etherLeft_zbl, etherRight_drv]
  show ether (3 + 6 * 1) (1 + (2 * s + 1)) = !ether (3 + 1) (1 + (2 * s + 1))
  rw [ether_congr (j' := 2) (φ' := (2 * s + 2) % 4) (by omega) (by omega),
    ether_congr (j := 3 + 1) (j' := 4) (φ' := (2 * s + 2) % 4) (by omega) (by omega)]
  exact ether_check.2.2.1 _ (Nat.mod_lt _ (by decide)) (by omega)

end Rule30PeriodTwoCoupled
end Ruliology.CellularAutomata
