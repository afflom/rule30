module

/-!
# The white end: the finite relaxation and its kernel checks

Data for `Rule30WhiteEnd`. The eight cells right of a column, with an arbitrary cell beyond them at
every step, evolve as a nondeterministic system on `256` states (`stp`); a set of states is a
`256`-bit number (`img`, `Wp`, `mac`, `reach`). For `q = 10, …, 25`, `checkQ q` says that three
periods of the word `1 0^q` reach a set of states that one more period maps into itself, and that on
it the first cell of the strip takes a single value at every tick of the period. For
`q = 22, …, 25`, `repOK q` gives `W^26 = W^22` on the sets that occur, for the white-step relation
`W`. Each is decided by the kernel (`decide +kernel`), one declaration per `q`; `control_q9` shows
that the check fails at `q = 9`, so it is not vacuous.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Ruliology.CellularAutomata.Rule30WhiteEnd

/-! ## The finite relaxation on eight cells -/

/-- One step of the eight cells: state bit `j` is cell `c + 1 + j`, `w` the column's bit, `u` the cell beyond. -/
def stp (w s u : Nat) : Nat := ((((s <<< 1) ||| w) &&& 255) ^^^ (s ||| ((s >>> 1) ||| (u <<< 7)))) &&& 255

def imgAux (w S n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun k ih acc => ih (if S.testBit k then acc ||| (1 <<< stp w k 0) ||| (1 <<< stp w k 1) else acc)) n

theorem imgAux_succ (w S n acc : Nat) : imgAux w S (n + 1) acc =
    imgAux w S n (if S.testBit n then acc ||| (1 <<< stp w n 0) ||| (1 <<< stp w n 1) else acc) := rfl

/-- The image of the set `S` (a 256-bit number) under one step with column bit `w` and every outside bit. -/
def img (w S : Nat) : Nat := imgAux w S 256 0

/-- `Wp j S`: `j` white steps. -/
def Wp : Nat → Nat → Nat
  | 0, S => S
  | j + 1, S => img 0 (Wp j S)

/-- One period of the word `1 0^q`: a black step, then `q` white steps. -/
def mac (q S : Nat) : Nat := Wp q (img 1 S)

def reach (q : Nat) : Nat → Nat
  | 0 => 2 ^ 256 - 1
  | n + 1 => mac q (reach q n)

/-- Every state in `S` has cell `c + 1` equal to `b`. -/
def bit0Const (S : Nat) (b : Bool) : Bool := (List.range 256).all fun s => !(S.testBit s) || (s.testBit 0 == b)

def ticksAux : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | r + 1, j, X => bit0Const X (decide (2 ≤ j)) && ticksAux r (j + 1) (img 0 X)

/-- Cell `c + 1` at the `q` ticks after the black one: `0, 0`, then `1`. -/
def ticksOK (q S : Nat) : Bool := ticksAux q 0 (img 1 S)

def checkQ (q : Nat) : Bool :=
  mac q (reach q 3) == reach q 3 && bit0Const (reach q 3) true && ticksOK q (reach q 3)

def repOK (q : Nat) : Bool :=
  (List.range 4).all (fun n => Wp 26 (img 1 (reach q n)) == Wp 22 (img 1 (reach q n))) && ticksOK 26 (reach q 3)

-- The finite facts, one kernel check per word length (with Elab.async off, memory stays near one check's).
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check10 : checkQ 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11 : checkQ 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check12 : checkQ 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13 : checkQ 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check14 : checkQ 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check15 : checkQ 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check16 : checkQ 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17 : checkQ 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check18 : checkQ 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19 : checkQ 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check20 : checkQ 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check21 : checkQ 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check22 : checkQ 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23 : checkQ 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check24 : checkQ 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check25 : checkQ 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep22 : repOK 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep23 : repOK 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep24 : repOK 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep25 : repOK 25 = true := by decide +kernel

/-- The checks for `q = 10, …, 25`. -/
theorem checks : ∀ q : Nat, 10 ≤ q → q ≤ 25 → checkQ q = true
  | 10, _, _ => check10
  | 11, _, _ => check11
  | 12, _, _ => check12
  | 13, _, _ => check13
  | 14, _, _ => check14
  | 15, _, _ => check15
  | 16, _, _ => check16
  | 17, _, _ => check17
  | 18, _, _ => check18
  | 19, _, _ => check19
  | 20, _, _ => check20
  | 21, _, _ => check21
  | 22, _, _ => check22
  | 23, _, _ => check23
  | 24, _, _ => check24
  | 25, _, _ => check25
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _ | 9, h, _ => absurd h (by decide)
  | n + 26, _, h => absurd h (by omega)

/-- The periodicity checks for `q = 22, …, 25`. -/
theorem reps : ∀ q : Nat, 22 ≤ q → q ≤ 25 → repOK q = true
  | 22, _, _ => rep22
  | 23, _, _ => rep23
  | 24, _, _ => rep24
  | 25, _, _ => rep25
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _ | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _ | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ => absurd h (by decide)
  | n + 26, _, h => absurd h (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Control: the check is not vacuous; it fails at `q = 9`, where width 8 does not determine cell `c + 1`. -/
theorem control_q9 : checkQ 9 = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem stp_bits : ∀ s < 256, ∀ w u : Bool, ∀ j < 8,
    (stp w.toNat s u.toNat).testBit j =
      xor (if j = 0 then w else s.testBit (j - 1)) (s.testBit j || if j = 7 then u else s.testBit (j + 1)) := by
  decide

theorem stp_lt (w s u : Nat) : stp w s u < 256 := by
  unfold stp; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end Ruliology.CellularAutomata.Rule30WhiteEnd
