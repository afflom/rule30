module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-!
# Rule 30: light cones and the block tree

The locality facts behind space-efficient evaluation of the center column.

* `evol_window`: the cell at position `p` and time `t` depends only on the initial cells in
  `[p - t, p + t]`.
* `block_step`: cut the rows into space blocks of width `b` (`block`) and the time axis into steps
  of `b`. Block `j` at time `(k + 1) b` is a fixed function, `blockStep b`, of the blocks `j - 1`,
  `j` and `j + 1` at time `k b`.
* `center_eq_root`: so the center cell at time `m b` is the first entry of the node `(m, 0)` of a
  dependency graph of height `m` and fan-in `3`, whose nodes are `b`-bit blocks and whose sources
  are blocks of the initial row.

This is the shape that R. Williams's block-respecting simulation ("Simulating Time with Square-Root
Space", STOC 2025) passes to the tree evaluation algorithm of J. Cook and I. Mertz (STOC 2024).
Tree evaluation needs about `(h + v) log v` bits for height `h` and node size `v`; here `h = n / b`
and `v = b`, so `b ≈ √n` gives the center cell at time `n` in about `√n · log n` bits of memory. Neither algorithm is formalized here. Nothing in this module is specific to rule 30
beyond its radius `1`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LightCone

open Rule30Realization (evol)
open Rule30ZeroBoundaryBarriers (evol_local evol_restart evol_shift_all)

/-- **The light cone.** The cell at position `p` and time `t` depends only on the initial cells in
`[p - t, p + t]`. -/
theorem evol_window {x x' : Int → Bool} {t : Nat} {p : Int}
    (h : ∀ q, p - t ≤ q → q ≤ p + t → x' q = x q) : evol x' t p = evol x t p :=
  evol_local h t p (by omega) (by omega)

/-- Space block `j` of width `b`: the cells `j b, …, j b + b - 1` of the row `x`. -/
def block (b : Nat) (x : Int → Bool) (j : Int) : List Bool :=
  (List.range b).map fun i : Nat => x (j * b + (i : Int))

/-- The row made of three blocks: `l` on `[-b, 0)`, `m` on `[0, b)` and `r` on `[b, 2 b)`, white
elsewhere. -/
def assemble (b : Nat) (l m r : List Bool) (p : Int) : Bool :=
  if p < -(b : Int) then false
  else if p < 0 then l.getD (p + b).toNat false
  else if p < b then m.getD p.toNat false
  else if p < 2 * b then r.getD (p - b).toNat false
  else false

/-- One time block: the middle block after `b` steps from three adjacent blocks. -/
def blockStep (b : Nat) (l m r : List Bool) : List Bool := block b (evol (assemble b l m r) b) 0

theorem getD_block (b : Nat) (x : Int → Bool) (j : Int) {i : Nat} (hi : i < b) :
    (block b x j).getD i false = x (j * b + i) := by
  simp [block, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- `assemble` reproduces the row around block `j`, translated to block `0`. -/
theorem assemble_blocks (b : Nat) (y : Int → Bool) (j : Int) (q : Int) (h1 : -(b : Int) ≤ q)
    (h2 : q ≤ 2 * b - 1) :
    assemble b (block b y (j - 1)) (block b y j) (block b y (j + 1)) q = y (q + j * b) := by
  unfold assemble
  rw [ite_eq_right (by omega)]
  by_cases hq0 : q < 0
  · rw [ite_eq_left hq0, getD_block b y _ (by omega)]
    congr 1
    rw [Int.toNat_of_nonneg (by omega), Int.sub_mul]
    omega
  · rw [ite_eq_right hq0]
    by_cases hqb : q < b
    · rw [ite_eq_left hqb, getD_block b y _ (by omega), Int.toNat_of_nonneg (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hqb, ite_eq_left (by omega), getD_block b y _ (by omega)]
      congr 1
      rw [Int.toNat_of_nonneg (by omega), Int.add_mul]
      omega

/-- **Each node of the block tree has three parents**: block `j` at time `(k + 1) b` is
`blockStep b` of the blocks `j - 1`, `j`, `j + 1` at time `k b`. -/
theorem block_step (b : Nat) (x : Int → Bool) (k : Nat) (j : Int) :
    block b (fun p => evol x ((k + 1) * b) p) j =
      blockStep b (block b (fun p => evol x (k * b) p) (j - 1))
        (block b (fun p => evol x (k * b) p) j) (block b (fun p => evol x (k * b) p) (j + 1)) := by
  let y : Int → Bool := fun p => evol x (k * b) p
  have key : ∀ i : Nat, i < b →
      evol (assemble b (block b y (j - 1)) (block b y j) (block b y (j + 1))) b (0 * b + i) =
        evol x ((k + 1) * b) (j * b + i) := by
    intro i hi
    have hz := evol_local (x := fun q => y (q + j * b))
      (x' := assemble b (block b y (j - 1)) (block b y j) (block b y (j + 1)))
      (a := -(b : Int)) (b := 2 * b - 1)
      (fun q h1 h2 => assemble_blocks b y j q h1 h2) b (0 * b + i) (by omega) (by omega)
    have hs := evol_shift_all (x := y) (x' := fun q => y (q + j * b)) (d := -(j * b))
      (fun p => by show y (p + -(j * b) + j * b) = y p; congr 1; omega) b (j * b + i)
    rw [show (j * b + (i : Int)) + -(j * b) = 0 * b + i by omega] at hs
    have hr : evol y b (j * b + i) = evol x ((k + 1) * b) (j * b + i) := by
      rw [show (k + 1) * b = k * b + b by rw [Nat.succ_mul]]
      exact evol_restart x (k * b) b (j * b + i)
    exact hz.trans (hs.trans hr)
  unfold blockStep
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact (key i hi).symm

/-- **The center cell is the root of the block tree**: at time `m b` it is the first entry of
block `0`. -/
theorem center_eq_root (b m : Nat) (hb : 0 < b) (x : Int → Bool) :
    evol x (m * b) 0 = (block b (fun p => evol x (m * b) p) 0).getD 0 false := by
  rw [getD_block b _ 0 hb]
  simp

end Rule30LightCone
end Ruliology.CellularAutomata
