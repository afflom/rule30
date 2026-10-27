module

public import Ruliology.CellularAutomata.BusyBeaverLifetimes

/-!
# Rule 30: only 24 of the 32 possible 3×2 blocks occur

Wolfram, *Oh My Gosh, It's Covered in Rule 30s!* (2017), section "A British Train Station":
<https://writings.stephenwolfram.com/2017/06/oh-my-gosh-its-covered-in-rule-30s/>

"If one looks at 3×2 blocks of cells, only 24 of the 32 possible ones ever occur." A 3×2 block is
three adjacent cells and the same three cells one step later. The bottom middle cell is
determined by the top row, so 32 blocks are possible a priori (`consistent_count`).

* `blockAt_allowed`: in every rule 30 evolution, from any configuration of the infinite line, every
  block is one of the 24 `allowed` ones (`allowed_count`). Rule 30 is `l xor (c || r)`. If the top
  right cell is black, the cell below it is `c xor 1`, the opposite of the top middle cell. So the
  8 blocks with a black top right cell and equal top-middle and bottom-right cells never occur.
  These 8 answer the post's puzzle for people waiting for trains: which blocks are missing.
* `occurs_iff`: a block occurs at some position of some configuration exactly when it is allowed.
* `occurs_single_cell`: all 24 allowed blocks occur in the classic evolution from a single black
  cell, by step 21.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Blocks

open BusyBeaverLifetimes

/-- Rule 30: `left xor (center || right)`. -/
def rule (a b c : Bool) : Bool := xor a (b || c)

/-- One step of rule 30 on a configuration of the infinite line. -/
def step (x : Int → Bool) : Int → Bool := fun p => rule (x (p - 1)) (x p) (x (p + 1))

/-- A 3×2 block: the top row `a b c` and the bottom row `d e f` one step later. -/
structure Block where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  deriving DecidableEq

/-- The block of `x` centered at `p`. -/
def blockAt (x : Int → Bool) (p : Int) : Block :=
  ⟨x (p - 1), x p, x (p + 1), step x (p - 1), step x p, step x (p + 1)⟩

/-- The bottom middle cell follows the rule from the top row. -/
def Block.consistent (k : Block) : Bool := k.e == rule k.a k.b k.c

/-- Consistent, and if the top right cell is black, the bottom right cell is the opposite of the
top middle cell. -/
def Block.allowed (k : Block) : Bool := k.consistent && (!k.c || k.f == !k.b)

/-- All 64 blocks. -/
def allBlocks : List Block :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c =>
  [false, true].flatMap fun d => [false, true].flatMap fun e => [false, true].map fun f =>
    ⟨a, b, c, d, e, f⟩

theorem mem_allBlocks (k : Block) : k ∈ allBlocks := by
  obtain ⟨a, b, c, d, e, f⟩ := k
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem consistent_count : (allBlocks.filter Block.consistent).length = 32 := by decide

theorem allowed_count : (allBlocks.filter Block.allowed).length = 24 := by decide

/-- **Only allowed blocks occur**, in every evolution. -/
theorem blockAt_allowed (x : Int → Bool) (p : Int) : (blockAt x p).allowed = true := by
  simp only [blockAt, step, Block.allowed, Block.consistent]
  rw [show p + 1 - 1 = p by omega]
  generalize x (p - 1) = a
  generalize x p = b
  generalize x (p + 1) = c
  generalize x (p + 1 + 1) = g
  cases a <;> cases b <;> cases c <;> cases g <;> rfl

/-- A configuration showing the block `⟨a, b, c, d, e, f⟩` at position `0`. -/
def witnessConfig (a b c d f : Bool) : Int → Bool := fun q =>
  if q = -2 then xor d (a || b) else if q = -1 then a else if q = 0 then b else if q = 1 then c
  else if q = 2 then xor f b else false

theorem blockAt_witnessConfig : ∀ k : Block, k.allowed = true →
    blockAt (witnessConfig k.a k.b k.c k.d k.f) 0 = k := by
  intro k hk
  obtain ⟨a, b, c, d, e, f⟩ := k
  revert hk
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

/-- **Exactly the allowed blocks occur.** -/
theorem occurs_iff (k : Block) : (∃ x p, blockAt x p = k) ↔ k.allowed = true := by
  constructor
  · rintro ⟨x, p, rfl⟩
    exact blockAt_allowed x p
  · intro hk
    exact ⟨_, 0, blockAt_witnessConfig k hk⟩

/-! ### The evolution from a single black cell -/

/-- One step of rule 30 on a bit-plane: new bit `j` is the rule applied to old bits `j - 2`,
`j - 1` and `j` (see `TwoColor.Rep`). -/
def F (A : Nat) : Nat := (A <<< 2) ^^^ ((A <<< 1) ||| A)

theorem index_one (g : Nat → Bool) : TwoColor.index 1 g =
    (if g 0 then 4 else 0) + (if g 1 then 2 else 0) + (if g 2 then 1 else 0) := by
  unfold TwoColor.index
  rw [show List.range (2 * 1 + 1) = [0, 1, 2] from rfl]
  simp only [List.foldl]
  cases g 0 <;> cases g 1 <;> cases g 2 <;> rfl

theorem stepCorrect : TwoColor.StepCorrect 30 1 F := by
  intro A j
  rw [index_one]
  simp only [F, Nat.testBit_xor, Nat.testBit_or, Nat.shiftLeft_zero,
    show 2 * 1 - 0 = 2 from rfl, show 2 * 1 - 1 = 1 from rfl, show 2 * 1 - 2 = 0 from rfl]
  generalize (A <<< 2).testBit j = x
  generalize (A <<< 1).testBit j = y
  generalize A.testBit j = z
  cases x <;> cases y <;> cases z <;> decide

/-- The planes of the evolution from a single cell. -/
def plane : Nat → Nat
  | 0 => 2
  | t + 1 => F (plane t)

theorem rep_plane : ∀ t, TwoColor.Rep 30 1 t (plane t)
  | 0 => TwoColor.rep_init 30 1
  | t + 1 => TwoColor.rep_step (F := F) (by decide) stepCorrect (rep_plane t)

/-- The evolution from a single black cell, read off the planes. -/
theorem cell_eq (t : Nat) (q : Int) (hq : -(t : Int) - 1 ≤ q) :
    TwoColor.cell 30 1 t q = (plane t).testBit (q + t + 1).toNat := by
  have := rep_plane t ((q + t + 1).toNat)
  rw [show (((q + t + 1).toNat : Nat) : Int) - ((1 * t : Nat) : Int) - ((1 : Nat) : Int) = q by
    push_cast; omega] at this
  exact this

/-- The single-cell evolution steps by rule 30. -/
theorem cell_succ (t : Nat) : TwoColor.cell 30 1 (t + 1) = step (TwoColor.cell 30 1 t) := by
  funext p
  show (30 : Nat).testBit (TwoColor.index 1 fun i => TwoColor.cell 30 1 t (p - (1 : Nat) + i)) = _
  rw [index_one]
  simp only [step, rule]
  rw [show p - ((1 : Nat) : Int) + ((1 : Nat) : Int) = p by omega,
    show p - ((1 : Nat) : Int) + ((2 : Nat) : Int) = p + 1 by omega,
    show p - ((1 : Nat) : Int) = p - 1 by omega, show p - 1 + ((0 : Nat) : Int) = p - 1 by omega]
  generalize TwoColor.cell 30 1 t (p - 1) = x
  generalize TwoColor.cell 30 1 t p = y
  generalize TwoColor.cell 30 1 t (p + 1) = z
  cases x <;> cases y <;> cases z <;> decide

/-- The block at time `t`, position `p`, read off the planes. -/
def blockOfPlanes (t : Nat) (p : Int) : Block :=
  ⟨(plane t).testBit (p + t).toNat, (plane t).testBit (p + t + 1).toNat,
    (plane t).testBit (p + t + 2).toNat, (plane (t + 1)).testBit (p + t + 1).toNat,
    (plane (t + 1)).testBit (p + t + 2).toNat, (plane (t + 1)).testBit (p + t + 3).toNat⟩

theorem blockAt_cell (t : Nat) (p : Int) (hp : -(t : Int) ≤ p) :
    blockAt (TwoColor.cell 30 1 t) p = blockOfPlanes t p := by
  simp only [blockAt, ← cell_succ, blockOfPlanes]
  rw [cell_eq t _ (by omega), cell_eq t _ (by omega), cell_eq t _ (by omega),
    cell_eq (t + 1) _ (by omega), cell_eq (t + 1) _ (by omega), cell_eq (t + 1) _ (by omega)]
  congr 2 <;> congr 1 <;> push_cast <;> omega

/-- Where each allowed block first occurs in the evolution from a single cell. -/
def witnesses : List (Block × Nat × Int) := [
  (⟨false, true, false, true, true, true⟩, 0, 0),
  (⟨false, true, true, true, true, false⟩, 1, -1),
  (⟨true, true, true, true, false, false⟩, 1, 0),
  (⟨true, true, false, false, false, true⟩, 1, 1),
  (⟨true, true, false, true, false, true⟩, 2, -1),
  (⟨true, false, false, false, true, true⟩, 2, 0),
  (⟨false, false, true, true, true, true⟩, 2, 1),
  (⟨true, true, false, true, false, false⟩, 3, -2),
  (⟨true, false, true, false, false, true⟩, 3, -1),
  (⟨false, true, true, false, true, false⟩, 3, 0),
  (⟨true, true, true, false, false, false⟩, 3, 2),
  (⟨true, false, false, true, true, false⟩, 4, 1),
  (⟨false, false, false, true, false, true⟩, 4, 2),
  (⟨false, false, true, false, true, true⟩, 4, 3),
  (⟨true, true, false, false, false, false⟩, 5, 1),
  (⟨false, false, false, true, false, false⟩, 6, 0),
  (⟨false, false, false, false, false, true⟩, 6, 1),
  (⟨true, false, false, true, true, true⟩, 6, 4),
  (⟨true, false, false, false, true, false⟩, 8, 3),
  (⟨false, false, false, false, false, false⟩, 8, 5),
  (⟨false, true, false, true, true, false⟩, 10, -1),
  (⟨true, false, true, true, false, true⟩, 10, 0),
  (⟨false, true, false, false, true, true⟩, 11, 1),
  (⟨false, true, false, false, true, false⟩, 21, 13)]

theorem witnesses_ok : witnesses.all (fun w => decide (-(w.2.1 : Int) ≤ w.2.2) &&
    blockOfPlanes w.2.1 w.2.2 == w.1) = true := by decide +kernel

theorem witnesses_cover : allBlocks.all (fun k => !k.allowed || witnesses.any (·.1 == k)) = true := by
  decide

/-- **All 24 allowed blocks occur** in the evolution of rule 30 from a single black cell, by
step 21. -/
theorem occurs_single_cell (k : Block) (hk : k.allowed = true) :
    ∃ t p, t ≤ 21 ∧ blockAt (TwoColor.cell 30 1 t) p = k := by
  have hc := List.all_eq_true.1 witnesses_cover k (mem_allBlocks k)
  simp only [hk, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at hc
  obtain ⟨w, hw, rfl⟩ := hc
  have hok := List.all_eq_true.1 witnesses_ok w hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  have ht : w.2.1 ≤ 21 := by
    have : ∀ w ∈ witnesses, w.2.1 ≤ 21 := by decide
    exact this w hw
  exact ⟨w.2.1, w.2.2, ht, by rw [blockAt_cell _ _ hok.1, hok.2]⟩

end Rule30Blocks
end Ruliology.CellularAutomata
