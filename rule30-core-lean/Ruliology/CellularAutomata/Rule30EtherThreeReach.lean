module

public import Ruliology.CellularAutomata.Rule30EtherThreeTrap

/-!
# Rule 30, least period 3: the `001` trap is reached

A sanity anchor for `Rule30EtherThreeTrap`: the trap `t001` is not vacuous. The empty right half,
driven by `001^∞` from phase `0`, is in the trap at time `1270` (`t001_reached`), i.e. it satisfies
the conclusion of `AbsorptionT t001` for this one start (`absorbed_empty`).

* `stepN`, `rowN`: the driven right half of a finitely supported start as bit masks
  (bit `i` = column `i + 1`); `rowN_eq_drv` identifies it with `Rule30Ether.drv`.
* `t001_reached`: kernel computation of `1270` steps, then a lookup in the trap.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThree

open Rule30Jen Rule30StripCertificates Rule30Ether

/-- One step of a finitely supported right half as a bit mask, with column `0` equal to `c`. -/
def stepN (c : Bool) (r : Nat) : Nat :=
  (c.toNat ||| (r <<< 1)) ^^^ (((c.toNat ||| (r <<< 1)) >>> 1) ||| ((c.toNat ||| (r <<< 1)) >>> 2))

/-- The driven right half as bit masks. -/
def rowN (c : Nat → Bool) (x0 : Nat) : Nat → Nat
  | 0 => x0
  | t + 1 => stepN (c t) (rowN c x0 t)

theorem testBit_full (c : Bool) (r j : Nat) :
    (c.toNat ||| (r <<< 1)).testBit j = if j = 0 then c else r.testBit (j - 1) := by
  rw [Nat.testBit_or, testBit_toNat, Nat.testBit_shiftLeft]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj, show j ≥ 1 by omega]

theorem testBit_stepN (c : Bool) (r i : Nat) :
    (stepN c r).testBit i =
      rule (if i = 0 then c else r.testBit (i - 1)) (r.testBit i) (r.testBit (i + 1)) := by
  unfold stepN
  generalize hF : c.toNat ||| (r <<< 1) = F
  have hF' : ∀ j, F.testBit j = if j = 0 then c else r.testBit (j - 1) := by
    intro j; rw [← hF]; exact testBit_full c r j
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    hF' i, hF' (1 + i), hF' (2 + i), ite_eq_right (show ¬ (1 + i = 0) by omega),
    ite_eq_right (show ¬ (2 + i = 0) by omega),
    show 1 + i - 1 = i by omega, show 2 + i - 1 = i + 1 by omega]
  rfl

theorem rowN_eq_drv (c : Nat → Bool) (x0 : Nat) :
    ∀ t i, (rowN c x0 t).testBit i = drv c (fun p => x0.testBit (p - 1)) t (i + 1) := by
  intro t
  induction t with
  | zero => intro i; rw [drv_init _ _ _ (by omega)]; rfl
  | succ t ih =>
    intro i
    show (stepN (c t) (rowN c x0 t)).testBit i =
      rule (drv c _ t i) (drv c _ t (i + 1)) (drv c _ t (i + 2))
    rw [testBit_stepN, ih i, ih (i + 1)]
    congr 1
    by_cases hi : i = 0
    · subst hi; rw [ite_eq_left rfl, drv_col0]
    · rw [ite_eq_right hi, ih (i - 1), show i - 1 + 1 = i by omega]

theorem rowN_empty_eq :
    t001.st 597 = rowN (fun t => wordAt3 w001 (t + 0)) 0 1270 % 2 ^ 47 := by decide +kernel

/-- **The `001` trap is reached**: the empty right half driven by `001^∞` (phase `0`) is trap state
`597` of `t001` at time `1270`, with the label of the right phase. -/
theorem t001_reached : ∃ i, i < t001.n ∧ (1270 + 0) % 3 = t001.lab i % 3 ∧
    EncF (drv (fun t => wordAt3 w001 (t + 0)) (fun _ => false)) t001.b 1270 0 (t001.st i) := by
  refine ⟨597, by decide, by decide, PTrap.st_lt t001 597, fun k hk => ?_⟩
  have hx : (fun p : Nat => (0 : Nat).testBit (p - 1)) = fun _ => false := by
    funext p; exact Nat.zero_testBit _
  have hb : t001.b = 47 := rfl
  rw [hb] at hk
  rw [rowN_empty_eq, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
    rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]

/-- The empty right half at phase `0` satisfies the conclusion of `AbsorptionT t001`. -/
theorem absorbed_empty : ∃ t1 i, i < t001.n ∧ (t1 + 0) % 3 = t001.lab i % 3 ∧
    EncF (drv (fun t => wordAt3 t001.w (t + 0)) (fun _ => false)) t001.b t1 0 (t001.st i) :=
  ⟨1270, t001_reached⟩

end Rule30EtherThree
end Ruliology.CellularAutomata
