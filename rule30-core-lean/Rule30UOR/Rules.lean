module
public import Rule30UOR.Interfaces
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The facet across all elementary rules

Every elementary rule is a Boolean function of three cells and has a unique
algebraic normal form over `F₂`: a constant, a linear part in `a`, `b`, `c`,
and the nonlinear monomials `ab`, `ac`, `bc`, `abc`. The ledger
decomposition of `Ledger` is the statement that an orbit is the linear
evolution of the seed XOR the accumulated nonlinear corrections, and it is
available for every rule with zero constant term. What is specific to
Rule 30 is its normal form `a ⊕ b ⊕ c ⊕ bc`: the single quadratic monomial
`bc` (the carry) and the linear occurrence of `a`, which is left-permutivity
and hence the bijectivity of the row map on every `Z/2^n`, the backward
determinacy of the center's past, and Jen's theorem. The coherence of all
rules is therefore real but not the solution: rules with a periodic center
exist, and their normal forms share the decomposition. The solution is a
property of this one nonlinear term. -/

@[expose] public section

namespace Rule30UOR.Rules

open Rule30UOR.Core

/-- The elementary rule with Wolfram code `n`: bit `4a + 2b + c` of `n`. -/
def wolfram (n : Nat) (a b c : Bool) : Bool :=
  n.testBit (4 * a.toNat + 2 * b.toNat + c.toNat)

/-- The algebraic normal form with the eight monomial coefficients
`(k, ka, kb, kc, kab, kac, kbc, kabc)`. -/
structure ANF where
  k : Bool
  ka : Bool
  kb : Bool
  kc : Bool
  kab : Bool
  kac : Bool
  kbc : Bool
  kabc : Bool
  deriving DecidableEq

def ANF.eval (f : ANF) (a b c : Bool) : Bool :=
  bxor (bxor (bxor (bxor (bxor (bxor (bxor f.k (f.ka && a)) (f.kb && b)) (f.kc && c))
    (f.kab && (a && b))) (f.kac && (a && c))) (f.kbc && (b && c))) (f.kabc && (a && (b && c)))

/-- The linear part of a normal form. -/
def ANF.linear (f : ANF) (a b c : Bool) : Bool :=
  bxor (bxor (bxor f.k (f.ka && a)) (f.kb && b)) (f.kc && c)

/-- The nonlinear part: the corrections the ledger accumulates. -/
def ANF.nonlinear (f : ANF) (a b c : Bool) : Bool :=
  bxor (bxor (bxor (f.kab && (a && b)) (f.kac && (a && c))) (f.kbc && (b && c))) (f.kabc && (a && (b && c)))

/-- Every normal form is its linear part XOR its nonlinear part. -/
theorem ANF.eval_split_fields : ∀ (k ka kb kc kab kac kbc kabc a b c : Bool),
    (ANF.mk k ka kb kc kab kac kbc kabc).eval a b c =
      bxor ((ANF.mk k ka kb kc kab kac kbc kabc).linear a b c)
        ((ANF.mk k ka kb kc kab kac kbc kabc).nonlinear a b c) := by
  decide

theorem ANF.eval_split (f : ANF) (a b c : Bool) :
    f.eval a b c = bxor (f.linear a b c) (f.nonlinear a b c) := by
  cases f
  exact ANF.eval_split_fields _ _ _ _ _ _ _ _ a b c

/-- The Möbius transform: the normal form of the rule with code `n`. -/
def anfOf (n : Nat) : ANF :=
  let r := wolfram n
  let k := r false false false
  let ka := bxor (r true false false) k
  let kb := bxor (r false true false) k
  let kc := bxor (r false false true) k
  let kab := bxor (bxor (bxor (r true true false) k) ka) kb
  let kac := bxor (bxor (bxor (r true false true) k) ka) kc
  let kbc := bxor (bxor (bxor (r false true true) k) kb) kc
  let kabc := bxor (bxor (bxor (bxor (bxor (bxor (bxor (r true true true) k) ka) kb) kc) kab) kac) kbc
  ⟨k, ka, kb, kc, kab, kac, kbc, kabc⟩

/-- **Every elementary rule is its normal form**: for all 256 codes and all
inputs, decided by the kernel. -/
theorem wolfram_eq_anf : ∀ n, n < 256 → ∀ a b c, wolfram n a b c = (anfOf n).eval a b c := by
  decide

/-- Rule 30 is the rule with code 30. -/
theorem rule_eq_wolfram_thirty (a b c : Bool) : rule a b c = wolfram 30 a b c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The normal form of Rule 30 is `a ⊕ b ⊕ c ⊕ bc`: zero constant, the full
linear part, and the single quadratic monomial `bc`, the carry. -/
theorem anf_thirty : anfOf 30 = ⟨false, true, true, true, false, false, true, false⟩ := by
  decide

/-- Rule 30 as linear part XOR carry, on cells: the local form of
`Ledger.phi_eq_linear_xor_carry`. -/
theorem rule_eq_linear_xor_carry (a b c : Bool) :
    rule a b c = bxor (bxor (bxor a b) c) (b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- A rule is left-permutive when `a` occurs only linearly: no monomial
containing `a` beyond `ka`. Then the row map is a bijection on every `Z/2^n`
(each new bit is the previous bit XOR a function of lower bits), which is the
backward determinacy behind Jen's theorem. -/
def ANF.leftPermutive (f : ANF) : Bool :=
  f.ka && !f.kab && !f.kac && !f.kabc

theorem anf_thirty_leftPermutive : (anfOf 30).leftPermutive = true := by
  decide

/-- The left-permutive rules among the 256: exactly those whose normal form
has `a` linearly and in no product. -/
def leftPermutiveCodes : List Nat := (List.range 256).filter fun n => (anfOf n).leftPermutive

theorem leftPermutiveCodes_count : leftPermutiveCodes.length = 16 := by
  decide

theorem thirty_mem_leftPermutive : 30 ∈ leftPermutiveCodes := by
  decide

/-- Among the left-permutive rules, Rule 30 is the one whose nonlinear part is
exactly the carry `bc` with the full linear part and zero constant. -/
theorem thirty_unique_carry_rule :
    ∀ n, n < 256 → anfOf n = ⟨false, true, true, true, false, false, true, false⟩ → n = 30 := by
  decide

end Rule30UOR.Rules
