module

public import Rule30Equivalents.Basic
public import Ruliology.CellularAutomata.Rule30WhiteSeed
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Ring

/-!
# Problem 1 for rules 86, 135 and 149: the symmetries of rule 30

Elementary cellular automata have two symmetries: **reflection**, which swaps left and right, and
**conjugation**, which swaps black and white in both the input and the output. Together they send
rule 30 to rules 86, 135 and 149, the other members of its class. So Problem 1 can be asked about
any of the four rules, as long as the seed is transformed too.

## Statements

* Rule 30 from a single black cell, run by the general `evolve`, is
  `Rule30Jen.cell` (`evolve_30`), so `c` is its center column.
* Rule 86, the mirror image of rule 30, started from a single black cell, draws the rule-30
  pattern reflected by `p ↦ -p` (`evolve_86`). Its center column is exactly `c` (`center_86`).
* Rule 135, the conjugate of rule 30, started from a single **white** cell on an all-black
  background, draws the rule-30 pattern with the colors swapped (`evolve_135`). Its center column
  is `!c` (`center_135`).
* Rule 149 is the mirror image of 135 and the conjugate of 86. From a single white cell it draws
  the reflected and color-swapped pattern (`evolve_149`), so its center column is also `!c`
  (`center_149`).
* A sequence is eventually periodic exactly when its complement is
  (`eventuallyPeriodic_not_iff`). In particular `!c` is eventually periodic iff `c` is
  (`eventuallyPeriodic_not_center_iff`).

Hence `Problem1` is equivalent to each of: the center column of rule 86 from a single black cell
is not eventually periodic (`problem1_iff_rule86`), and the same for rule 135
(`problem1_iff_rule135`) or rule 149 (`problem1_iff_rule149`) from a single white cell.

The seed matters. Rule 135 from a single *black* cell is
`Rule30WhiteSeed.cell135` (`evolve_135_blackSeed`). Its center column is column `-1` of rule 30,
complemented and delayed by one step. Whether that column is eventually periodic is a different
question, not known to be equivalent to Problem 1.

## Proof idea

`evolve rule init` is the general elementary cellular automaton with Wolfram's numbering: the new
cell is bit `4l + 2c + r` of `rule`. Two lemmas hold for every pair of rules and every initial row,
both by induction on time:

* If the table of rule `m` is the mirror image of the table of rule `n`, then `m` started from the
  mirrored row draws the mirrored pattern (`evolve_reflect`).
* If it is the conjugate, then `m` started from the complemented row draws the complemented
  pattern (`evolve_complement`).

The single black seed is its own mirror image, and the single white seed is its complement.
`decide` checks the rule numbers on their 8-entry tables (`ruleBit_86`, `ruleBit_135`,
`ruleBit_149`). It also computes them from 30 with `mirror` and `conjugate` (`mirror_30`,
`conjugate_30`, `mirror_135`). Since a rule number below 256 is determined by its table
(`eq_of_ruleBit`), 86, 135 and 149 are the only numbers below 256 that work. As a check on these
definitions, `decide` also confirms the classical count of 88 classes among the 256 rules
(`card_classes`).

## Sources

* The rule numbering: S. Wolfram, *Statistical mechanics of cellular automata*, Rev. Mod. Phys. 55
  (1983) 601–644.
* Reflection and conjugation as symmetries of the elementary rules, and the 88 classes they leave:
  W. Li and N. Packard, *The structure of the elementary cellular automata rule space*, Complex
  Systems 4 (1990) 281–297.
* Rule 30's class {30, 86, 135, 149} is computed here (`class_30`). The equivalences with Problem 1
  are immediate consequences of these symmetries. We know of no separate source for them.
-/

@[expose] public section

namespace Rule30Equivalents
namespace Symmetry

open Ruliology.CellularAutomata

/-! ### Elementary cellular automata in Wolfram's numbering -/

/-- The local rule of elementary rule number `rule`. A cell whose left neighbor, own color and
right neighbor are `l`, `c`, `r` (`true` = black) becomes bit `4l + 2c + r` of `rule`. -/
def ruleBit (rule : Nat) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `evolve rule init t p` is the color of cell `p` after `t` steps of elementary rule `rule`,
started from the row `init`. -/
def evolve (rule : Nat) (init : Int → Bool) : Nat → Int → Bool
  | 0, p => init p
  | t + 1, p =>
    ruleBit rule (evolve rule init t (p - 1)) (evolve rule init t p) (evolve rule init t (p + 1))

/-- A single black cell at position `0` on an all-white background. -/
def blackSeed (p : Int) : Bool := decide (p = 0)

/-- A single white cell at position `0` on an all-black background. -/
def whiteSeed (p : Int) : Bool := !blackSeed p

theorem blackSeed_neg (p : Int) : blackSeed (-p) = blackSeed p := by
  simp [blackSeed]

theorem whiteSeed_neg (p : Int) : whiteSeed (-p) = whiteSeed p := by
  simp [whiteSeed, blackSeed_neg]

/-! ### Rule numbers of mirror images and conjugates -/

/-- The number of the elementary rule with local rule `f`: the sum of `2 ^ (4l + 2c + r)` over
the neighborhoods `(l, c, r)` that `f` turns black. -/
def ofTable (f : Bool → Bool → Bool → Bool) : Nat :=
  (f false false false).toNat + 2 * (f false false true).toNat +
    4 * (f false true false).toNat + 8 * (f false true true).toNat +
    16 * (f true false false).toNat + 32 * (f true false true).toNat +
    64 * (f true true false).toNat + 128 * (f true true true).toNat

/-- Reading back the table of `ofTable f` gives `f`. -/
theorem ruleBit_ofTable (f : Bool → Bool → Bool → Bool) (l c r : Bool) :
    ruleBit (ofTable f) l c r = f l c r := by
  have key : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ l c r : Bool,
      ruleBit (b₀.toNat + 2 * b₁.toNat + 4 * b₂.toNat + 8 * b₃.toNat + 16 * b₄.toNat +
        32 * b₅.toNat + 64 * b₆.toNat + 128 * b₇.toNat) l c r =
      (bif l then (bif c then (bif r then b₇ else b₆) else (bif r then b₅ else b₄))
        else (bif c then (bif r then b₃ else b₂) else (bif r then b₁ else b₀))) := by
    decide +kernel
  rw [ofTable, key]
  cases l <;> cases c <;> cases r <;> rfl

/-- Every rule number below `256` is the number of its own table. -/
theorem ofTable_ruleBit : ∀ n, n < 256 → ofTable (ruleBit n) = n := by
  decide +kernel

/-- Two rule numbers below `256` with the same table are equal. -/
theorem eq_of_ruleBit {m n : Nat} (hm : m < 256) (hn : n < 256)
    (h : ∀ l c r, ruleBit m l c r = ruleBit n l c r) : m = n := by
  have e : ruleBit m = ruleBit n := funext fun l => funext fun c => funext fun r => h l c r
  rw [← ofTable_ruleBit m hm, ← ofTable_ruleBit n hn, e]

/-- The number of the mirror image of rule `n`, with left and right swapped. -/
def mirror (n : Nat) : Nat := ofTable fun l c r => ruleBit n r c l

/-- The number of the conjugate of rule `n`, with black and white swapped in both the input and
the output. -/
def conjugate (n : Nat) : Nat := ofTable fun l c r => !ruleBit n (!l) (!c) (!r)

theorem ruleBit_mirror (n : Nat) (l c r : Bool) : ruleBit (mirror n) l c r = ruleBit n r c l :=
  ruleBit_ofTable _ l c r

theorem ruleBit_conjugate (n : Nat) (l c r : Bool) :
    ruleBit (conjugate n) l c r = !ruleBit n (!l) (!c) (!r) :=
  ruleBit_ofTable _ l c r

/-! ### The rule numbers, checked on the 8-entry tables -/

/-- `Rule30Jen.rule`, `l xor (c || r)`, is rule 30. -/
theorem ruleBit_30 : ∀ l c r, ruleBit 30 l c r = Rule30Jen.rule l c r := by decide

/-- **Rule 86 is the mirror image of rule 30.** -/
theorem ruleBit_86 : ∀ l c r, ruleBit 86 l c r = ruleBit 30 r c l := by decide

/-- **Rule 135 is the conjugate of rule 30.** -/
theorem ruleBit_135 : ∀ l c r, ruleBit 135 l c r = !ruleBit 30 (!l) (!c) (!r) := by decide

/-- **Rule 149 is the mirror image of rule 135.** -/
theorem ruleBit_149 : ∀ l c r, ruleBit 149 l c r = ruleBit 135 r c l := by decide

/-- Rule 149 is also the conjugate of rule 86. -/
theorem ruleBit_149_conjugate_86 : ∀ l c r, ruleBit 149 l c r = !ruleBit 86 (!l) (!c) (!r) := by
  decide

/-- `Rule30WhiteSeed.rule135`, `!l xor (c && r)`, is rule 135. -/
theorem ruleBit_135_eq_catalog : ∀ l c r, ruleBit 135 l c r = Rule30WhiteSeed.rule135 l c r := by
  decide

/-- The numbers computed from rule 30: its mirror image is 86 and its conjugate is 135. -/
theorem mirror_30 : mirror 30 = 86 := by decide

theorem conjugate_30 : conjugate 30 = 135 := by decide

theorem mirror_135 : mirror 135 = 149 := by decide

theorem conjugate_86 : conjugate 86 = 149 := by decide

/-- **Rule 30's class.** The set `{30, 86, 135, 149}` is closed under reflection and conjugation,
and it is generated by `30`. -/
theorem class_30 :
    mirror 30 = 86 ∧ conjugate 30 = 135 ∧ mirror 86 = 30 ∧ conjugate 86 = 149 ∧
      mirror 135 = 149 ∧ conjugate 135 = 30 ∧ mirror 149 = 135 ∧ conjugate 149 = 86 := by
  decide

/-- On the rules below `256`, `mirror` and `conjugate` are commuting involutions. So the class of
`n` under reflection and conjugation is `{n, mirror n, conjugate n, mirror (conjugate n)}`. -/
theorem mirror_conjugate_involutions : ∀ n, n < 256 →
    mirror (mirror n) = n ∧ conjugate (conjugate n) = n ∧
      mirror (conjugate n) = conjugate (mirror n) := by
  decide +kernel

/-- **88 classes.** Each class has exactly one least element, and by
`mirror_conjugate_involutions` the class of `n` is
`{n, mirror n, conjugate n, mirror (conjugate n)}`. Counting the `n` that are least in their class
shows that the 256 elementary rules fall into 88 classes under reflection and conjugation. -/
theorem card_classes :
    ((List.range 256).filter fun n =>
      decide (n ≤ mirror n) && decide (n ≤ conjugate n) &&
        decide (n ≤ mirror (conjugate n))).length = 88 := by
  decide +kernel

/-! ### Reflection and conjugation of whole patterns -/

/-- **Reflection.** If rule `m` is the mirror image of rule `n`, then rule `m` started from the
mirrored row draws the mirrored pattern. -/
theorem evolve_reflect {m n : Nat} (h : ∀ l c r, ruleBit m l c r = ruleBit n r c l)
    (init : Int → Bool) :
    ∀ (t : Nat) (p : Int), evolve m (fun q => init (-q)) t p = evolve n init t (-p)
  | 0, _ => rfl
  | t + 1, p => by
    show ruleBit m (evolve m (fun q => init (-q)) t (p - 1)) (evolve m (fun q => init (-q)) t p)
        (evolve m (fun q => init (-q)) t (p + 1)) =
      ruleBit n (evolve n init t (-p - 1)) (evolve n init t (-p)) (evolve n init t (-p + 1))
    rw [evolve_reflect h init t (p - 1), evolve_reflect h init t p,
      evolve_reflect h init t (p + 1), h, show -(p + 1) = -p - 1 by omega,
      show -(p - 1) = -p + 1 by omega]

/-- **Conjugation.** If rule `m` is the conjugate of rule `n`, then rule `m` started from the
complemented row draws the complemented pattern. -/
theorem evolve_complement {m n : Nat} (h : ∀ l c r, ruleBit m l c r = !ruleBit n (!l) (!c) (!r))
    (init : Int → Bool) :
    ∀ (t : Nat) (p : Int), evolve m (fun q => !init q) t p = !evolve n init t p
  | 0, _ => rfl
  | t + 1, p => by
    show ruleBit m (evolve m (fun q => !init q) t (p - 1)) (evolve m (fun q => !init q) t p)
        (evolve m (fun q => !init q) t (p + 1)) =
      !ruleBit n (evolve n init t (p - 1)) (evolve n init t p) (evolve n init t (p + 1))
    rw [evolve_complement h init t (p - 1), evolve_complement h init t p,
      evolve_complement h init t (p + 1), h]
    simp only [Bool.not_not]

/-- `evolve_reflect` for the computed mirror image `mirror n`. -/
theorem evolve_mirror (n : Nat) (init : Int → Bool) (t : Nat) (p : Int) :
    evolve (mirror n) (fun q => init (-q)) t p = evolve n init t (-p) :=
  evolve_reflect (ruleBit_mirror n) init t p

/-- `evolve_complement` for the computed conjugate `conjugate n`. -/
theorem evolve_conjugate (n : Nat) (init : Int → Bool) (t : Nat) (p : Int) :
    evolve (conjugate n) (fun q => !init q) t p = !evolve n init t p :=
  evolve_complement (ruleBit_conjugate n) init t p

/-! ### Rules 30, 86, 135 and 149 from a single seed -/

/-- Rule 30 from a single black cell is the pattern `Rule30Jen.cell`. -/
theorem evolve_30 : ∀ (t : Nat) (p : Int), evolve 30 blackSeed t p = Rule30Jen.cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show ruleBit 30 (evolve 30 blackSeed t (p - 1)) (evolve 30 blackSeed t p)
        (evolve 30 blackSeed t (p + 1)) =
      Rule30Jen.rule (Rule30Jen.cell t (p - 1)) (Rule30Jen.cell t p) (Rule30Jen.cell t (p + 1))
    rw [evolve_30 t (p - 1), evolve_30 t p, evolve_30 t (p + 1), ruleBit_30]

/-- **Rule 86** from a single black cell draws the rule-30 pattern reflected by `p ↦ -p`. -/
theorem evolve_86 (t : Nat) (p : Int) : evolve 86 blackSeed t p = Rule30Jen.cell t (-p) := by
  have h := evolve_reflect ruleBit_86 blackSeed t p
  rw [show (fun q => blackSeed (-q)) = blackSeed from funext blackSeed_neg] at h
  rw [h, evolve_30]

/-- **Rule 135** from a single white cell on an all-black background draws the rule-30 pattern
with the colors swapped. -/
theorem evolve_135 (t : Nat) (p : Int) : evolve 135 whiteSeed t p = !Rule30Jen.cell t p := by
  rw [← evolve_30]
  exact evolve_complement ruleBit_135 blackSeed t p

/-- **Rule 149** from a single white cell on an all-black background draws the rule-30 pattern
reflected and with the colors swapped. -/
theorem evolve_149 (t : Nat) (p : Int) : evolve 149 whiteSeed t p = !Rule30Jen.cell t (-p) := by
  have h := evolve_reflect ruleBit_149 whiteSeed t p
  rw [show (fun q => whiteSeed (-q)) = whiteSeed from funext whiteSeed_neg] at h
  rw [h, evolve_135]

/-- Rule 135 from a single *black* cell is `Rule30WhiteSeed.cell135`. Its center
column is column `-1` of rule 30, complemented and delayed by one step
(`Rule30WhiteSeed.center135_succ`), not the center column `c`. So Problem 1 needs the white
seed. -/
theorem evolve_135_blackSeed :
    ∀ (t : Nat) (p : Int), evolve 135 blackSeed t p = Rule30WhiteSeed.cell135 t p
  | 0, _ => rfl
  | t + 1, p => by
    show ruleBit 135 (evolve 135 blackSeed t (p - 1)) (evolve 135 blackSeed t p)
        (evolve 135 blackSeed t (p + 1)) =
      Rule30WhiteSeed.rule135 (Rule30WhiteSeed.cell135 t (p - 1)) (Rule30WhiteSeed.cell135 t p)
        (Rule30WhiteSeed.cell135 t (p + 1))
    rw [evolve_135_blackSeed t (p - 1), evolve_135_blackSeed t p, evolve_135_blackSeed t (p + 1),
      ruleBit_135_eq_catalog]

/-! ### Center columns -/

/-- The center column of rule 30 from a single black cell is `c`. -/
theorem center_30 (t : Nat) : evolve 30 blackSeed t 0 = c t :=
  evolve_30 t 0

/-- The center column of rule 86 from a single black cell is `c`. -/
theorem center_86 (t : Nat) : evolve 86 blackSeed t 0 = c t :=
  (evolve_86 t 0).trans (congrArg (Rule30Jen.cell t) (Int.neg_zero))

/-- The center column of rule 135 from a single white cell is `!c`. -/
theorem center_135 (t : Nat) : evolve 135 whiteSeed t 0 = !c t :=
  evolve_135 t 0

/-- The center column of rule 149 from a single white cell is `!c`. -/
theorem center_149 (t : Nat) : evolve 149 whiteSeed t 0 = !c t :=
  (evolve_149 t 0).trans (congrArg (fun q => !Rule30Jen.cell t q) (Int.neg_zero))

/-! ### Complemented sequences -/

/-- **Complementing a sequence does not change whether it is eventually periodic.** -/
theorem eventuallyPeriodic_not_iff (b : Nat → Bool) :
    EventuallyPeriodic (fun t => !b t) ↔ EventuallyPeriodic b := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun t ht => Bool.not_inj (h t ht)⟩
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun t ht => congrArg (!·) (h t ht)⟩

/-- The complemented center column `!c` is eventually periodic iff `c` is. -/
theorem eventuallyPeriodic_not_center_iff :
    EventuallyPeriodic (fun t => !c t) ↔ EventuallyPeriodic c :=
  eventuallyPeriodic_not_iff c

/-! ### Problem 1 for the class of rule 30 -/

/-- Problem 1 for the complemented center column. -/
theorem problem1_iff_complement :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => !c t) :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr eventuallyPeriodic_not_center_iff.symm)

/-- Problem 1 for any sequence equal to the center column. -/
theorem problem1_iff_of_eq {b : Nat → Bool} (h : ∀ t, b t = c t) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic b := by
  have hb : b = c := funext h
  subst hb
  exact problem1_iff_not_eventuallyPeriodic

/-- Problem 1 for any sequence equal to the complemented center column. -/
theorem problem1_iff_of_eq_not {b : Nat → Bool} (h : ∀ t, b t = !c t) :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic b := by
  have hb : b = fun t => !c t := funext h
  subst hb
  exact problem1_iff_complement

/-- Problem 1 restated with `evolve`: the center column of rule 30 from a single black cell is not
eventually periodic. -/
theorem problem1_iff_rule30 :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 30 blackSeed t 0) :=
  problem1_iff_of_eq center_30

/-- **Rule 86.** Problem 1 holds iff the center column of rule 86 from a single black cell is not
eventually periodic. -/
theorem problem1_iff_rule86 :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 86 blackSeed t 0) :=
  problem1_iff_of_eq center_86

/-- **Rule 135.** Problem 1 holds iff the center column of rule 135 from a single white cell on
an all-black background is not eventually periodic. -/
theorem problem1_iff_rule135 :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 135 whiteSeed t 0) :=
  problem1_iff_of_eq_not center_135

/-- **Rule 149.** Problem 1 holds iff the center column of rule 149 from a single white cell on
an all-black background is not eventually periodic. -/
theorem problem1_iff_rule149 :
    Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 149 whiteSeed t 0) :=
  problem1_iff_of_eq_not center_149

/-! ### Problem 2 for the class of rule 30 -/

/-- Black cells have density `1/2` in `b`, in the integer form of `Rule30Prize.Problem2`: for every
`k > 0`, eventually `k · |2 · #{t < n : b t} − n| ≤ n`. -/
def HalfDensity (b : Nat → Bool) : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n →
    k * (2 * (((List.range n).filter b).length : Int) - n).natAbs ≤ n

theorem problem2_iff_halfDensity : Rule30Prize.Problem2 ↔ HalfDensity c := Iff.rfl

/-- **Complementing a sequence does not change whether its density is `1/2`.** -/
theorem halfDensity_not_iff (b : Nat → Bool) :
    HalfDensity (fun t => !b t) ↔ HalfDensity b := by
  have key : ∀ n, (2 * (((List.range n).filter fun t => !b t).length : Int) - n).natAbs =
      (2 * (((List.range n).filter b).length : Int) - n).natAbs := fun n => by
    have h := List.length_eq_length_filter_add (l := List.range n) b
    rw [List.length_range] at h
    have h' : ((((List.range n).filter fun t => !b t).length : ℕ) : Int) =
        n - (((List.range n).filter b).length : Int) := by omega
    rw [h', ← Int.natAbs_neg]
    congr 1
    ring
  unfold HalfDensity
  simp only [key]

theorem halfDensity_of_eq {b b' : Nat → Bool} (h : ∀ t, b t = b' t) :
    HalfDensity b ↔ HalfDensity b' := by
  rw [show b = b' from funext h]

/-- **Rule 86.** Problem 2 holds iff black cells have density `1/2` in the center column of rule 86
from a single black cell. -/
theorem problem2_iff_rule86 :
    Rule30Prize.Problem2 ↔ HalfDensity (fun t => evolve 86 blackSeed t 0) :=
  (halfDensity_of_eq center_86).symm

/-- **Rule 135.** Problem 2 holds iff black cells have density `1/2` in the center column of rule
135 from a single white cell on an all-black background. -/
theorem problem2_iff_rule135 :
    Rule30Prize.Problem2 ↔ HalfDensity (fun t => evolve 135 whiteSeed t 0) :=
  ((halfDensity_of_eq center_135).trans (halfDensity_not_iff c)).symm

/-- **Rule 149.** Problem 2 holds iff black cells have density `1/2` in the center column of rule
149 from a single white cell on an all-black background. -/
theorem problem2_iff_rule149 :
    Rule30Prize.Problem2 ↔ HalfDensity (fun t => evolve 149 whiteSeed t 0) :=
  ((halfDensity_of_eq center_149).trans (halfDensity_not_iff c)).symm

end Symmetry
end Rule30Equivalents
