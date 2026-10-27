module

/-!
# Busy-beaver lifetimes of cellular automata

Wolfram, *Why Does Biological Evolution Work? A Minimal Model for Biological Evolution and Other
Adaptive Processes* (2024), section "Computation Theoretic Perspectives and Busy Beavers":
<https://writings.stephenwolfram.com/2024/05/why-does-biological-evolution-work-a-minimal-model-for-biological-evolution-and-other-adaptive-processes/>

The section describes "a cellular automaton analog of the so-called busy beaver problem". It
summarizes the longest lifetimes found ("all for single-cell initial conditions") in a table.
The essay itself says these are only "lower bounds on the actual maximum lifetime". We certify
the exhibited lifetimes. In each case the pattern started from a single cell of color `1` is
nonzero at every step `t < T` and identically zero at step `T`.

| rule | colors `k` | radius `r` | lifetime `T` | theorem |
|---|---|---|---|---|
| 450504084 | 2 | 2 | 308 | `lifetime450504084` |
| 977937844 (mirror image of 450504084) | 2 | 2 | 308 | `lifetime977937844` |
| 2455381412 (left-right symmetric) | 2 | 2 | 65 | `lifetime2455381412` |
| 5810255963295 (left-right symmetric) | 3 | 1 | 2194 | `lifetime5810255963295` |

Maximality (that no rule in the family lives longer) is not claimed.

**Rule numbering** is Wolfram's (`CellularAutomaton[{n, k, r}]`). The new color of a cell is the
base-`k` digit of `n` at position `Σ_i a_i k^(2r-i)`, where `a_0, …, a_{2r}` are the colors of
the cells at offsets `-r, …, r`.

**Method** (as in `LongLifetimeK3`).
- Configurations are stored as bit-planes in a frame moving left by `r` cells per step, so no bit
  is ever shifted out.
- Each rule's one-step formula of `&&&`, `|||`, `^^^` and `<<<` is proved correct bit by bit, by
  `decide` over all neighbourhoods.
- The kernel then runs the steps (`decide +kernel`).
- The general frame lemmas (`TwoColor.lifetime_of_lives` and `ThreeColor.lifetime_of_lives`) are
  proved once for every rule.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace BusyBeaverLifetimes

/-- `x ∧ ¬ y`, bitwise. -/
def andNot (x y : Nat) : Nat := x ^^^ (x &&& y)

theorem testBit_andNot (x y j : Nat) : (andNot x y).testBit j = (x.testBit j && !y.testBit j) := by
  simp only [andNot, Nat.testBit_xor, Nat.testBit_and]
  cases x.testBit j <;> cases y.testBit j <;> rfl

theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp) init]
    exact foldl_congr l _ fun y hy acc => h y (by simp [hy]) acc

theorem eq_zero_of_testBit {x : Nat} (h : ∀ j, x.testBit j = false) : x = 0 :=
  Nat.eq_of_testBit_eq fun j => by rw [h j, Nat.zero_testBit]

/-! ## Two colors, radius `r` -/

namespace TwoColor

/-- The neighbourhood index of colors `a 0, …, a (2 r)` (left to right): the binary number
`a 0 a 1 ⋯ a (2 r)`. -/
def index (r : Nat) (a : Nat → Bool) : Nat :=
  (List.range (2 * r + 1)).foldl (fun acc i => 2 * acc + (if a i then 1 else 0)) 0

theorem index_congr {r : Nat} {a b : Nat → Bool} (h : ∀ i, i ≤ 2 * r → a i = b i) :
    index r a = index r b :=
  foldl_congr _ _ fun i hi acc => by
    rw [h i (by simp at hi; omega)]

theorem index_false (r : Nat) : index r (fun _ => false) = 0 := by
  unfold index
  generalize List.range (2 * r + 1) = l
  induction l with
  | nil => rfl
  | cons x l ih => simpa using ih

theorem index_two (a : Nat → Bool) : index 2 a =
    (if a 0 then 16 else 0) + (if a 1 then 8 else 0) + (if a 2 then 4 else 0) +
      (if a 3 then 2 else 0) + (if a 4 then 1 else 0) := by
  unfold index
  rw [show List.range (2 * 2 + 1) = [0, 1, 2, 3, 4] from rfl]
  simp only [List.foldl]
  cases a 0 <;> cases a 1 <;> cases a 2 <;> cases a 3 <;> cases a 4 <;> rfl

/-- Rule `n` with two colors and radius `r`, run from a single `1` at position `0`:
`cell n r t p` is the color (`true` = `1`) at position `p` after `t` steps. -/
def cell (n r : Nat) : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => n.testBit (index r fun i => cell n r t (p - r + i))

/-- Nothing reaches beyond the light cone (for a rule with `000…0 → 0`). -/
theorem cell_eq_false_of_lt {n r : Nat} (hn : n.testBit 0 = false) :
    ∀ (t : Nat) (p : Int), p < -((r * t : Nat) : Int) → cell n r t p = false
  | 0, p, h => by
    simp only [cell, decide_eq_false_iff_not]
    simp at h
    omega
  | t + 1, p, h => by
    show n.testBit (index r fun i => cell n r t (p - r + i)) = false
    rw [index_congr (b := fun _ => false) (fun i hi => cell_eq_false_of_lt hn t _ (by
      rw [Nat.mul_succ] at h
      push_cast at h ⊢
      omega)), index_false]
    exact hn

/-- After `t` steps, bit `j` of `A` is the cell at position `j - r t - r`. -/
def Rep (n r t A : Nat) : Prop :=
  ∀ j : Nat, cell n r t ((j : Int) - ((r * t : Nat) : Int) - r) = A.testBit j

/-- `F` computes one step of rule `n` in the moving frame: new bit `j` applies the rule to old
bits `j - 2r, …, j`. -/
def StepCorrect (n r : Nat) (F : Nat → Nat) : Prop :=
  ∀ A j, (F A).testBit j = n.testBit (index r fun i => (A <<< (2 * r - i)).testBit j)

theorem stepCorrect_two {n : Nat} {F : Nat → Nat} {g : Bool → Bool → Bool → Bool → Bool → Bool}
    (hF : ∀ A j, (F A).testBit j = g ((A <<< 4).testBit j) ((A <<< 3).testBit j)
      ((A <<< 2).testBit j) ((A <<< 1).testBit j) (A.testBit j))
    (hg : ∀ b0 b1 b2 b3 b4 : Bool, g b0 b1 b2 b3 b4 = n.testBit ((if b0 then 16 else 0) +
      (if b1 then 8 else 0) + (if b2 then 4 else 0) + (if b3 then 2 else 0) + (if b4 then 1 else 0))) :
    StepCorrect n 2 F := by
  intro A j
  rw [hF, hg, index_two]
  rfl

theorem rep_step {n r t A : Nat} {F : Nat → Nat} (hn : n.testBit 0 = false)
    (hF : StepCorrect n r F) (h : Rep n r t A) : Rep n r (t + 1) (F A) := by
  intro j
  rw [hF A j]
  show n.testBit (index r fun i => cell n r t ((j : Int) - ((r * (t + 1) : Nat) : Int) - r - r + i)) = _
  congr 1
  apply index_congr
  intro i hi
  rw [Nat.testBit_shiftLeft]
  by_cases hj : 2 * r - i ≤ j
  · rw [decide_eq_true hj, Bool.true_and, ← h (j - (2 * r - i))]
    congr 1
    rw [Nat.mul_succ]
    push_cast
    omega
  · rw [decide_eq_false hj, Bool.false_and]
    apply cell_eq_false_of_lt hn t
    rw [Nat.mul_succ]
    push_cast
    omega

theorem rep_zero_iff {n r t A : Nat} (hn : n.testBit 0 = false) (h : Rep n r t A) :
    (∀ p, cell n r t p = false) ↔ A = 0 := by
  constructor
  · intro hz
    exact eq_zero_of_testBit fun j => (h j).symm.trans (hz _)
  · rintro rfl p
    by_cases hp : p < -((r * t : Nat) : Int) - r
    · exact cell_eq_false_of_lt hn t p (by omega)
    · have := h (p + ((r * t : Nat) : Int) + r).toNat
      rw [show (((p + ((r * t : Nat) : Int) + r).toNat : Nat) : Int) - ((r * t : Nat) : Int) - r = p by
        omega] at this
      rw [this, Nat.zero_testBit]

theorem rep_init (n r : Nat) : Rep n r 0 (2 ^ r) := by
  intro j
  rw [Nat.testBit_two_pow]
  show decide (((j : Int) - ((r * 0 : Nat) : Int) - r) = 0) = decide (r = j)
  simp only [Nat.mul_zero, Int.natCast_zero, Int.sub_zero]
  by_cases hj : r = j
  · subst hj; simp
  · rw [decide_eq_false (by omega), decide_eq_false hj]

/-- `lives F k A`: the plane is nonzero now and for the next `k - 1` steps, and `0` after `k`. -/
def lives (F : Nat → Nat) : Nat → Nat → Bool
  | 0, A => A == 0
  | k + 1, A => A != 0 && lives F k (F A)

theorem lives_spec {n r : Nat} {F : Nat → Nat} (hn : n.testBit 0 = false) (hF : StepCorrect n r F) :
    ∀ (k t A : Nat), Rep n r t A → lives F k A = true →
      (∀ s, s < k → ∃ p, cell n r (t + s) p = true) ∧ ∀ p, cell n r (t + k) p = false
  | 0, t, A, h, hl => by
    simp only [lives, beq_iff_eq] at hl
    exact ⟨fun s hs => absurd hs (Nat.not_lt_zero s), (rep_zero_iff hn h).2 hl⟩
  | k + 1, t, A, h, hl => by
    simp only [lives, Bool.and_eq_true, bne_iff_ne, ne_eq] at hl
    obtain ⟨hnz, hl⟩ := hl
    obtain ⟨ih₁, ih₂⟩ := lives_spec hn hF k (t + 1) (F A) (rep_step hn hF h) hl
    refine ⟨fun s hs => ?_, fun p => by rw [show t + (k + 1) = t + 1 + k by omega]; exact ih₂ p⟩
    cases s with
    | zero =>
      refine Classical.byContradiction fun hc => hnz ((rep_zero_iff hn h).1 fun p => ?_)
      cases hp : cell n r t p with
      | false => rfl
      | true => exact absurd ⟨p, hp⟩ hc
    | succ s =>
      obtain ⟨p, hp⟩ := ih₁ s (by omega)
      exact ⟨p, by rw [show t + (s + 1) = t + 1 + s by omega]; exact hp⟩

/-- A lifetime certificate: if the bit-plane run dies after exactly `T` steps, so does the rule. -/
theorem lifetime_of_lives {n r T : Nat} {F : Nat → Nat} (hn : n.testBit 0 = false)
    (hF : StepCorrect n r F) (hl : lives F T (2 ^ r) = true) :
    (∀ t, t < T → ∃ p, cell n r t p = true) ∧ ∀ p, cell n r T p = false := by
  obtain ⟨h₁, h₂⟩ := lives_spec hn hF T 0 (2 ^ r) (rep_init n r) hl
  exact ⟨fun t ht => by simpa using h₁ t ht, fun p => by simpa using h₂ p⟩

end TwoColor

/-! ## Three colors, radius 1 -/

namespace ThreeColor

/-- The new color of a cell with neighbourhood `l, c, r`: base-3 digit `9 l + 3 c + r` of `n`. -/
def rule (n l c r : Nat) : Nat := n / 3 ^ (9 * l + 3 * c + r) % 3

/-- Rule `n` with three colors and radius 1, run from a single cell of color `1` at `0`. -/
def cell (n : Nat) : Nat → Int → Nat
  | 0, p => if p = 0 then 1 else 0
  | t + 1, p => rule n (cell n t (p - 1)) (cell n t p) (cell n t (p + 1))

theorem cell_eq_zero_of_lt {n : Nat} (hn : rule n 0 0 0 = 0) :
    ∀ (t : Nat) (p : Int), p < -(t : Int) → cell n t p = 0
  | 0, p, h => by
    show (if p = 0 then 1 else 0) = 0
    rw [ite_eq_right (by omega)]
  | t + 1, p, h => by
    show rule n (cell n t (p - 1)) (cell n t p) (cell n t (p + 1)) = 0
    rw [cell_eq_zero_of_lt hn t (p - 1) (by omega), cell_eq_zero_of_lt hn t p (by omega),
      cell_eq_zero_of_lt hn t (p + 1) (by omega)]
    exact hn

/-- The color stored in a bit of `A` and the same bit of `B`. -/
def dec (a b : Bool) : Nat := if a then 1 else if b then 2 else 0

/-- After `t` steps, bit `j` of `(A, B)` is the cell at position `j - t - 1`. -/
def Rep (n t A B : Nat) : Prop :=
  ∀ j : Nat, cell n t ((j : Int) - t - 1) = dec (A.testBit j) (B.testBit j)

/-- `F` computes one step of rule `n` in the moving frame. -/
def StepCorrect (n : Nat) (F : Nat → Nat → Nat × Nat) : Prop :=
  ∀ A B j, dec ((F A B).1.testBit j) ((F A B).2.testBit j) =
    rule n (dec ((A <<< 2).testBit j) ((B <<< 2).testBit j))
      (dec ((A <<< 1).testBit j) ((B <<< 1).testBit j)) (dec (A.testBit j) (B.testBit j))

theorem rep_shift {n t A B : Nat} (hn : rule n 0 0 0 = 0) (h : Rep n t A B) (k j : Nat) :
    cell n t ((j : Int) - k - t - 1) = dec ((A <<< k).testBit j) ((B <<< k).testBit j) := by
  simp only [Nat.testBit_shiftLeft]
  by_cases hj : k ≤ j
  · have := h (j - k)
    rw [show ((j - k : Nat) : Int) - t - 1 = (j : Int) - k - t - 1 by omega] at this
    rw [this, decide_eq_true (show j ≥ k from hj)]
    rfl
  · rw [cell_eq_zero_of_lt hn t _ (by omega), decide_eq_false (show ¬ j ≥ k by omega)]
    rfl

theorem rep_step {n t A B : Nat} {F : Nat → Nat → Nat × Nat} (hn : rule n 0 0 0 = 0)
    (hF : StepCorrect n F) (h : Rep n t A B) : Rep n (t + 1) (F A B).1 (F A B).2 := by
  intro j
  rw [hF A B j, ← rep_shift hn h 2 j, ← rep_shift hn h 1 j, ← h j]
  show rule n (cell n t ((j : Int) - (t + 1 : Nat) - 1 - 1)) (cell n t ((j : Int) - (t + 1 : Nat) - 1))
      (cell n t ((j : Int) - (t + 1 : Nat) - 1 + 1)) = _
  congr 2 <;> omega

theorem dec_eq_zero {a b : Bool} : dec a b = 0 ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> decide

theorem rep_zero_iff {n t A B : Nat} (hn : rule n 0 0 0 = 0) (h : Rep n t A B) :
    (∀ p, cell n t p = 0) ↔ (A = 0 ∧ B = 0) := by
  constructor
  · intro hz
    have hb : ∀ j, A.testBit j = false ∧ B.testBit j = false := fun j =>
      dec_eq_zero.1 ((h j).symm.trans (hz _))
    exact ⟨eq_zero_of_testBit fun j => (hb j).1, eq_zero_of_testBit fun j => (hb j).2⟩
  · rintro ⟨rfl, rfl⟩ p
    by_cases hp : p < -(t : Int) - 1
    · exact cell_eq_zero_of_lt hn t p (by omega)
    · have := h (p + t + 1).toNat
      rw [show (((p + t + 1).toNat : Nat) : Int) - t - 1 = p by omega] at this
      rw [this, Nat.zero_testBit]
      rfl

theorem rep_init (n : Nat) : Rep n 0 2 0 := by
  intro j
  rw [Nat.zero_testBit, show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]
  show (if ((j : Int) - (0 : Nat) - 1) = 0 then 1 else 0) = _
  by_cases hj : j = 1
  · subst hj; decide
  · rw [ite_eq_right (by omega), decide_eq_false (by omega)]
    rfl

/-- `lives F k A B`: the planes are nonzero now and for the next `k - 1` steps, and both `0`
after `k` steps. -/
def lives (F : Nat → Nat → Nat × Nat) : Nat → Nat → Nat → Bool
  | 0, A, B => A == 0 && B == 0
  | k + 1, A, B => (A != 0 || B != 0) && lives F k (F A B).1 (F A B).2

theorem lives_spec {n : Nat} {F : Nat → Nat → Nat × Nat} (hn : rule n 0 0 0 = 0)
    (hF : StepCorrect n F) : ∀ (k t A B : Nat), Rep n t A B → lives F k A B = true →
      (∀ s, s < k → ∃ p, cell n (t + s) p ≠ 0) ∧ ∀ p, cell n (t + k) p = 0
  | 0, t, A, B, h, hl => by
    simp only [lives, Bool.and_eq_true, beq_iff_eq] at hl
    exact ⟨fun s hs => absurd hs (Nat.not_lt_zero s), (rep_zero_iff hn h).2 hl⟩
  | k + 1, t, A, B, h, hl => by
    simp only [lives, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hl
    obtain ⟨hnz, hl⟩ := hl
    obtain ⟨ih₁, ih₂⟩ := lives_spec hn hF k (t + 1) _ _ (rep_step hn hF h) hl
    refine ⟨fun s hs => ?_, fun p => by rw [show t + (k + 1) = t + 1 + k by omega]; exact ih₂ p⟩
    cases s with
    | zero =>
      refine Classical.byContradiction fun hc => ?_
      have hz : ∀ p, cell n t p = 0 := fun p =>
        Classical.byContradiction fun hp => hc ⟨p, hp⟩
      have := (rep_zero_iff hn h).1 hz
      rcases hnz with hA | hB
      · exact hA this.1
      · exact hB this.2
    | succ s =>
      obtain ⟨p, hp⟩ := ih₁ s (by omega)
      exact ⟨p, by rw [show t + (s + 1) = t + 1 + s by omega]; exact hp⟩

theorem lifetime_of_lives {n T : Nat} {F : Nat → Nat → Nat × Nat} (hn : rule n 0 0 0 = 0)
    (hF : StepCorrect n F) (hl : lives F T 2 0 = true) :
    (∀ t, t < T → ∃ p, cell n t p ≠ 0) ∧ ∀ p, cell n T p = 0 := by
  obtain ⟨h₁, h₂⟩ := lives_spec hn hF T 0 2 0 (rep_init n) hl
  exact ⟨fun t ht => by simpa using h₁ t ht, fun p => by simpa using h₂ p⟩

end ThreeColor

/-! ### Rule 450504084 (`k = 2`, `r = 2`) -/

/-- One step of rule 450504084 on the bit-plane. -/
def step450504084 (A : Nat) : Nat :=
  let a0 := A <<< 4
  let a1 := A <<< 3
  let a2 := A <<< 2
  let a3 := A <<< 1
  let a4 := A
  andNot (a3) (a0 ||| a1 ||| a2 ||| a4) |||
    andNot (a2) (a0 ||| a1 ||| a3 ||| a4) |||
    andNot (a2 &&& a3 &&& a4) (a0 ||| a1) |||
    andNot (a1) (a0 ||| a2 ||| a3 ||| a4) |||
    andNot (a1 &&& a3) (a0 ||| a2 ||| a4) |||
    andNot (a1 &&& a2 &&& a4) (a0 ||| a3) |||
    andNot (a0 &&& a4) (a1 ||| a2 ||| a3) |||
    andNot (a0 &&& a3 &&& a4) (a1 ||| a2) |||
    andNot (a0 &&& a2) (a1 ||| a3 ||| a4) |||
    andNot (a0 &&& a2 &&& a3) (a1 ||| a4) |||
    andNot (a0 &&& a2 &&& a3 &&& a4) (a1) |||
    andNot (a0 &&& a1 &&& a4) (a2 ||| a3) |||
    andNot (a0 &&& a1 &&& a3 &&& a4) (a2) |||
    andNot (a0 &&& a1 &&& a2) (a3 ||| a4)

/-- Rule 450504084 as a Boolean function of the neighbourhood, left to right. -/
def bit450504084 (a0 a1 a2 a3 a4 : Bool) : Bool :=
  ((a3) && !(a0 || a1 || a2 || a4)) ||
  ((a2) && !(a0 || a1 || a3 || a4)) ||
  ((a2 && a3 && a4) && !(a0 || a1)) ||
  ((a1) && !(a0 || a2 || a3 || a4)) ||
  ((a1 && a3) && !(a0 || a2 || a4)) ||
  ((a1 && a2 && a4) && !(a0 || a3)) ||
  ((a0 && a4) && !(a1 || a2 || a3)) ||
  ((a0 && a3 && a4) && !(a1 || a2)) ||
  ((a0 && a2) && !(a1 || a3 || a4)) ||
  ((a0 && a2 && a3) && !(a1 || a4)) ||
  ((a0 && a2 && a3 && a4) && !(a1)) ||
  ((a0 && a1 && a4) && !(a2 || a3)) ||
  ((a0 && a1 && a3 && a4) && !(a2)) ||
  ((a0 && a1 && a2) && !(a3 || a4))

theorem step450504084_correct : TwoColor.StepCorrect 450504084 2 step450504084 :=
  TwoColor.stepCorrect_two (g := bit450504084)
    (fun A j => by
      simp only [step450504084, bit450504084, Nat.testBit_or, Nat.testBit_and, testBit_andNot])
    (by decide)

theorem lives450504084 : TwoColor.lives step450504084 308 (2 ^ 2) = true := by decide +kernel

/-- **Rule 450504084 lives exactly 308 steps** from a single cell. -/
theorem lifetime450504084 :
    (∀ t, t < 308 → ∃ p, TwoColor.cell 450504084 2 t p = true) ∧ ∀ p, TwoColor.cell 450504084 2 308 p = false :=
  TwoColor.lifetime_of_lives (by decide) step450504084_correct lives450504084

/-! ### Rule 977937844 (`k = 2`, `r = 2`) — the mirror image of rule 450504084 -/

/-- One step of rule 977937844 on the bit-plane. -/
def step977937844 (A : Nat) : Nat :=
  let a0 := A <<< 4
  let a1 := A <<< 3
  let a2 := A <<< 2
  let a3 := A <<< 1
  let a4 := A
  andNot (a3) (a0 ||| a1 ||| a2 ||| a4) |||
    andNot (a2) (a0 ||| a1 ||| a3 ||| a4) |||
    andNot (a2 &&& a4) (a0 ||| a1 ||| a3) |||
    andNot (a2 &&& a3 &&& a4) (a0 ||| a1) |||
    andNot (a1) (a0 ||| a2 ||| a3 ||| a4) |||
    andNot (a1 &&& a3) (a0 ||| a2 ||| a4) |||
    andNot (a1 &&& a2 &&& a4) (a0 ||| a3) |||
    andNot (a0 &&& a4) (a1 ||| a2 ||| a3) |||
    andNot (a0 &&& a3 &&& a4) (a1 ||| a2) |||
    andNot (a0 &&& a2 &&& a3) (a1 ||| a4) |||
    andNot (a0 &&& a1 &&& a4) (a2 ||| a3) |||
    andNot (a0 &&& a1 &&& a3 &&& a4) (a2) |||
    andNot (a0 &&& a1 &&& a2) (a3 ||| a4) |||
    andNot (a0 &&& a1 &&& a2 &&& a4) (a3)

/-- Rule 977937844 as a Boolean function of the neighbourhood, left to right. -/
def bit977937844 (a0 a1 a2 a3 a4 : Bool) : Bool :=
  ((a3) && !(a0 || a1 || a2 || a4)) ||
  ((a2) && !(a0 || a1 || a3 || a4)) ||
  ((a2 && a4) && !(a0 || a1 || a3)) ||
  ((a2 && a3 && a4) && !(a0 || a1)) ||
  ((a1) && !(a0 || a2 || a3 || a4)) ||
  ((a1 && a3) && !(a0 || a2 || a4)) ||
  ((a1 && a2 && a4) && !(a0 || a3)) ||
  ((a0 && a4) && !(a1 || a2 || a3)) ||
  ((a0 && a3 && a4) && !(a1 || a2)) ||
  ((a0 && a2 && a3) && !(a1 || a4)) ||
  ((a0 && a1 && a4) && !(a2 || a3)) ||
  ((a0 && a1 && a3 && a4) && !(a2)) ||
  ((a0 && a1 && a2) && !(a3 || a4)) ||
  ((a0 && a1 && a2 && a4) && !(a3))

theorem step977937844_correct : TwoColor.StepCorrect 977937844 2 step977937844 :=
  TwoColor.stepCorrect_two (g := bit977937844)
    (fun A j => by
      simp only [step977937844, bit977937844, Nat.testBit_or, Nat.testBit_and, testBit_andNot])
    (by decide)

theorem lives977937844 : TwoColor.lives step977937844 308 (2 ^ 2) = true := by decide +kernel

/-- **Rule 977937844 lives exactly 308 steps** from a single cell. -/
theorem lifetime977937844 :
    (∀ t, t < 308 → ∃ p, TwoColor.cell 977937844 2 t p = true) ∧ ∀ p, TwoColor.cell 977937844 2 308 p = false :=
  TwoColor.lifetime_of_lives (by decide) step977937844_correct lives977937844

/-! ### Rule 2455381412 (`k = 2`, `r = 2`), left-right symmetric -/

/-- One step of rule 2455381412 on the bit-plane. -/
def step2455381412 (A : Nat) : Nat :=
  let a0 := A <<< 4
  let a1 := A <<< 3
  let a2 := A <<< 2
  let a3 := A <<< 1
  let a4 := A
  andNot (a3) (a0 ||| a1 ||| a2 ||| a4) |||
    andNot (a2 &&& a4) (a0 ||| a1 ||| a3) |||
    andNot (a2 &&& a3 &&& a4) (a0 ||| a1) |||
    andNot (a1) (a0 ||| a2 ||| a3 ||| a4) |||
    andNot (a1 &&& a3) (a0 ||| a2 ||| a4) |||
    andNot (a1 &&& a2 &&& a4) (a0 ||| a3) |||
    andNot (a0 &&& a4) (a1 ||| a2 ||| a3) |||
    andNot (a0 &&& a3 &&& a4) (a1 ||| a2) |||
    andNot (a0 &&& a2) (a1 ||| a3 ||| a4) |||
    andNot (a0 &&& a2 &&& a3) (a1 ||| a4) |||
    andNot (a0 &&& a1 &&& a4) (a2 ||| a3) |||
    andNot (a0 &&& a1 &&& a2) (a3 ||| a4) |||
    (a0 &&& a1 &&& a2 &&& a3 &&& a4)

/-- Rule 2455381412 as a Boolean function of the neighbourhood, left to right. -/
def bit2455381412 (a0 a1 a2 a3 a4 : Bool) : Bool :=
  ((a3) && !(a0 || a1 || a2 || a4)) ||
  ((a2 && a4) && !(a0 || a1 || a3)) ||
  ((a2 && a3 && a4) && !(a0 || a1)) ||
  ((a1) && !(a0 || a2 || a3 || a4)) ||
  ((a1 && a3) && !(a0 || a2 || a4)) ||
  ((a1 && a2 && a4) && !(a0 || a3)) ||
  ((a0 && a4) && !(a1 || a2 || a3)) ||
  ((a0 && a3 && a4) && !(a1 || a2)) ||
  ((a0 && a2) && !(a1 || a3 || a4)) ||
  ((a0 && a2 && a3) && !(a1 || a4)) ||
  ((a0 && a1 && a4) && !(a2 || a3)) ||
  ((a0 && a1 && a2) && !(a3 || a4)) ||
  (a0 && a1 && a2 && a3 && a4)

theorem step2455381412_correct : TwoColor.StepCorrect 2455381412 2 step2455381412 :=
  TwoColor.stepCorrect_two (g := bit2455381412)
    (fun A j => by
      simp only [step2455381412, bit2455381412, Nat.testBit_or, Nat.testBit_and, testBit_andNot])
    (by decide)

theorem lives2455381412 : TwoColor.lives step2455381412 65 (2 ^ 2) = true := by decide +kernel

/-- **Rule 2455381412 lives exactly 65 steps** from a single cell. -/
theorem lifetime2455381412 :
    (∀ t, t < 65 → ∃ p, TwoColor.cell 2455381412 2 t p = true) ∧ ∀ p, TwoColor.cell 2455381412 2 65 p = false :=
  TwoColor.lifetime_of_lives (by decide) step2455381412_correct lives2455381412

/-! ### Rule 5810255963295 (`k = 3`, `r = 1`, left-right symmetric) -/

/-- One step of rule 5810255963295 on the bit-planes. -/
def step5810255963295 (A B : Nat) : Nat × Nat :=
  let lA := A <<< 2
  let lB := B <<< 2
  let cA := A <<< 1
  let cB := B <<< 1
  let rA := A
  let rB := B
  (andNot (cA) (lA ||| lB ||| andNot rB rA) |||
    andNot (cB &&& rA) (lA ||| lB ||| cA) |||
    andNot (lA &&& rB) (cA ||| cB ||| rA) |||
    andNot (lA &&& cA) (rA ||| rB) |||
    andNot (lA &&& cB) (cA ||| rA ||| rB) |||
    andNot (lB &&& (rA ||| rB)) (lA ||| cA ||| cB) |||
    andNot (lB &&& cA &&& rB) (lA ||| rA),
   andNot (rA) (lA ||| lB ||| cA ||| cB) |||
    andNot (cB &&& rB) (lA ||| lB ||| cA ||| rA) |||
    andNot (lA) (cA ||| cB ||| andNot rB rA) |||
    andNot (lA &&& cA &&& rB) (rA) |||
    andNot (lA &&& cB &&& rA) (cA) |||
    andNot (lB &&& cA &&& rA) (lA) |||
    andNot (lB &&& cB) (lA ||| cA ||| rA))

def bitA5810255963295 (lA lB cA cB rA rB : Bool) : Bool :=
  ((cA) && !(lA || lB || (rB && !rA))) ||
  ((cB && rA) && !(lA || lB || cA)) ||
  ((lA && rB) && !(cA || cB || rA)) ||
  ((lA && cA) && !(rA || rB)) ||
  ((lA && cB) && !(cA || rA || rB)) ||
  ((lB && (rA || rB)) && !(lA || cA || cB)) ||
  ((lB && cA && rB) && !(lA || rA))

def bitB5810255963295 (lA lB cA cB rA rB : Bool) : Bool :=
  ((rA) && !(lA || lB || cA || cB)) ||
  ((cB && rB) && !(lA || lB || cA || rA)) ||
  ((lA) && !(cA || cB || (rB && !rA))) ||
  ((lA && cA && rB) && !(rA)) ||
  ((lA && cB && rA) && !(cA)) ||
  ((lB && cA && rA) && !(lA)) ||
  ((lB && cB) && !(lA || cA || rA))

theorem bit5810255963295 : ∀ lA lB cA cB rA rB : Bool,
    ThreeColor.dec (bitA5810255963295 lA lB cA cB rA rB) (bitB5810255963295 lA lB cA cB rA rB) =
      ThreeColor.rule 5810255963295 (ThreeColor.dec lA lB) (ThreeColor.dec cA cB)
        (ThreeColor.dec rA rB) := by
  decide

theorem step5810255963295_correct : ThreeColor.StepCorrect 5810255963295 step5810255963295 := by
  intro A B j
  have h1 : (step5810255963295 A B).1.testBit j = bitA5810255963295 ((A <<< 2).testBit j)
      ((B <<< 2).testBit j) ((A <<< 1).testBit j) ((B <<< 1).testBit j) (A.testBit j)
      (B.testBit j) := by
    simp only [step5810255963295, bitA5810255963295, Nat.testBit_or, Nat.testBit_and,
      testBit_andNot]
  have h2 : (step5810255963295 A B).2.testBit j = bitB5810255963295 ((A <<< 2).testBit j)
      ((B <<< 2).testBit j) ((A <<< 1).testBit j) ((B <<< 1).testBit j) (A.testBit j)
      (B.testBit j) := by
    simp only [step5810255963295, bitB5810255963295, Nat.testBit_or, Nat.testBit_and,
      testBit_andNot]
  rw [h1, h2, bit5810255963295]

theorem lives5810255963295 : ThreeColor.lives step5810255963295 2194 2 0 = true := by
  decide +kernel

/-- **Rule 5810255963295 lives exactly 2194 steps** from a single cell of color `1`. -/
theorem lifetime5810255963295 :
    (∀ t, t < 2194 → ∃ p, ThreeColor.cell 5810255963295 t p ≠ 0) ∧
      ∀ p, ThreeColor.cell 5810255963295 2194 p = 0 :=
  ThreeColor.lifetime_of_lives (by decide) step5810255963295_correct lives5810255963295

end BusyBeaverLifetimes
end Ruliology.CellularAutomata
