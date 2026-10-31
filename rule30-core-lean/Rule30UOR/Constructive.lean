module

public import Init
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Meta.Tactic.Clear

/-!
# Choice-free replacements for classical steps

The research modules use no `Classical.choice`. Every theorem here depends at
most on `propext` and `Quot.sound`. The helpers replace the classical steps that
earlier proofs took: an existential extracted from a negated bounded universal,
the top bit of a nonzero word, and the duplicate-freeness of `List.range`. Each
one uses only decidability that the statement already has.
-/

@[expose] public section

namespace Rule30UOR.Constructive

/-- A negated bounded universal over a decidable predicate has a witness, in the
same shape that `Classical.not_forall` would return. -/
theorem exists_not_of_not_forall_le (N : Nat) {Q : Nat → Prop} [DecidablePred Q]
    (h : ¬ ∀ s : Nat, s ≤ N → Q s) : ∃ s : Nat, ¬ (s ≤ N → Q s) := by
  induction N with
  | zero =>
    exact ⟨0, fun hq => h (fun s hs => by
      have : s = 0 := Nat.le_zero.mp hs
      subst this
      exact hq (Nat.le_refl 0))⟩
  | succ N ih =>
    by_cases hq : Q (N + 1)
    · have h' : ¬ ∀ s : Nat, s ≤ N → Q s := fun hall => h (fun s hs => by
        rcases Nat.lt_or_ge s (N + 1) with hlt | hge
        · exact hall s (Nat.le_of_lt_succ hlt)
        · have : s = N + 1 := Nat.le_antisymm hs hge
          subst this
          exact hq)
      obtain ⟨s, hs⟩ := ih h'
      exact ⟨s, fun himp => hs (fun hle => himp (Nat.le_succ_of_le hle))⟩
    · exact ⟨N + 1, fun himp => hq (himp (Nat.le_refl _))⟩

private theorem shiftRight_log2_eq_one (n : Nat) (hn : n ≠ 0) : n >>> n.log2 = 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hlo : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn
  have hhi : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hpos : 0 < 2 ^ n.log2 := Nat.two_pow_pos _
  have h1 : 1 ≤ n / 2 ^ n.log2 := (Nat.le_div_iff_mul_le hpos).2 (by simpa using hlo)
  have h2 : n / 2 ^ n.log2 < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by
    rw [Nat.pow_succ] at hhi
    rw [Nat.mul_comm]
    exact hhi)
  omega

/-- The leading bit of a nonzero word is set. -/
theorem testBit_log2 {n : Nat} (hn : n ≠ 0) : n.testBit n.log2 = true := by
  rw [Nat.testBit, shiftRight_log2_eq_one n hn]
  decide

/-- `List.range n` has no duplicates. -/
theorem nodup_range (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ]
    unfold List.Nodup
    rw [List.pairwise_append]
    refine ⟨ih, List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact Nat.ne_of_lt (List.mem_range.mp ha)

theorem int_between_iff (a b : Int) (R : Int → Prop) :
    (∃ x : Int, a ≤ x ∧ x ≤ b ∧ R x) ↔
      ∃ k : Nat, k ≤ (b - a).toNat ∧ (a ≤ b ∧ R (a + k)) := by
  constructor
  · rintro ⟨x, h1, h2, hr⟩
    refine ⟨(x - a).toNat, by omega, by omega, ?_⟩
    rw [show a + ((x - a).toNat : Int) = x by omega]
    exact hr
  · rintro ⟨k, hk, hab, hr⟩
    exact ⟨a + k, by omega, by omega, hr⟩

/-- An existential over a bounded integer interval is decidable. -/
instance decidableExistsIntBetween (a b : Int) (R : Int → Prop) [DecidablePred R] :
    Decidable (∃ x : Int, a ≤ x ∧ x ≤ b ∧ R x) :=
  decidable_of_iff _ (int_between_iff a b R).symm

theorem two_mul_le_iff (d : Nat) (R : Nat → Prop) :
    (∃ s : Nat, 2 * s ≤ d ∧ R s) ↔ ∃ s : Nat, s ≤ d ∧ (2 * s ≤ d ∧ R s) := by
  constructor
  · rintro ⟨s, h, hr⟩
    exact ⟨s, by omega, h, hr⟩
  · rintro ⟨s, _, h, hr⟩
    exact ⟨s, h, hr⟩

/-- An existential over `2 s ≤ d` is a bounded search. -/
instance decidableExistsTwoMulLE (d : Nat) (R : Nat → Prop) [DecidablePred R] :
    Decidable (∃ s : Nat, 2 * s ≤ d ∧ R s) :=
  decidable_of_iff _ (two_mul_le_iff d R).symm

theorem int_between_lt_iff (a b : Int) (R : Int → Prop) :
    (∃ x : Int, a < x ∧ x ≤ b ∧ R x) ↔ ∃ x : Int, a + 1 ≤ x ∧ x ≤ b ∧ R x := by
  constructor
  · rintro ⟨x, h1, h2, hr⟩; exact ⟨x, by omega, h2, hr⟩
  · rintro ⟨x, h1, h2, hr⟩; exact ⟨x, by omega, h2, hr⟩

/-- An existential over a half-open integer interval is decidable. -/
instance decidableExistsIntBetweenLt (a b : Int) (R : Int → Prop) [DecidablePred R] :
    Decidable (∃ x : Int, a < x ∧ x ≤ b ∧ R x) :=
  decidable_of_iff _ (int_between_lt_iff a b R).symm

theorem nat_between_lt_iff (a b : Nat) (R : Nat → Prop) :
    (∃ x : Nat, a < x ∧ x ≤ b ∧ R x) ↔ ∃ x : Nat, x ≤ b ∧ (a < x ∧ R x) := by
  constructor
  · rintro ⟨x, h1, h2, hr⟩; exact ⟨x, h2, h1, hr⟩
  · rintro ⟨x, h2, h1, hr⟩; exact ⟨x, h1, h2, hr⟩

/-- An existential over a half-open natural interval is decidable. -/
instance decidableExistsNatBetweenLt (a b : Nat) (R : Nat → Prop) [DecidablePred R] :
    Decidable (∃ x : Nat, a < x ∧ x ≤ b ∧ R x) :=
  decidable_of_iff _ (nat_between_lt_iff a b R).symm

theorem nat_between_le_iff (a b : Nat) (R : Nat → Prop) :
    (∃ x : Nat, a ≤ x ∧ x ≤ b ∧ R x) ↔ ∃ x : Nat, x ≤ b ∧ (a ≤ x ∧ R x) := by
  constructor
  · rintro ⟨x, h1, h2, hr⟩; exact ⟨x, h2, h1, hr⟩
  · rintro ⟨x, h2, h1, hr⟩; exact ⟨x, h1, h2, hr⟩

/-- An existential over a closed natural interval is decidable. -/
instance decidableExistsNatBetweenLe (a b : Nat) (R : Nat → Prop) [DecidablePred R] :
    Decidable (∃ x : Nat, a ≤ x ∧ x ≤ b ∧ R x) :=
  decidable_of_iff _ (nat_between_le_iff a b R).symm

theorem succ_lt_iff (k : Nat) (R : Nat → Prop) :
    (∃ s : Nat, s + 1 < k ∧ R s) ↔ ∃ s : Nat, s < k ∧ (s + 1 < k ∧ R s) := by
  constructor
  · rintro ⟨s, h, hr⟩; exact ⟨s, by omega, h, hr⟩
  · rintro ⟨s, _, h, hr⟩; exact ⟨s, h, hr⟩

/-- An existential over `s + 1 < k` is a bounded search. -/
instance decidableExistsSuccLt (k : Nat) (R : Nat → Prop) [DecidablePred R] :
    Decidable (∃ s : Nat, s + 1 < k ∧ R s) :=
  decidable_of_iff _ (succ_lt_iff k R).symm

theorem nat_forall_between_iff (a b : Nat) (R : Nat → Prop) :
    (∀ j : Nat, a ≤ j → j < b → R j) ↔ ∀ j : Nat, j < b → (a ≤ j → R j) := by
  constructor
  · exact fun h j hb ha => h j ha hb
  · exact fun h j ha hb => h j hb ha

/-- A universal over a half-open natural interval is decidable. -/
instance decidableForallNatBetween (a b : Nat) (R : Nat → Prop) [DecidablePred R] :
    Decidable (∀ j : Nat, a ≤ j → j < b → R j) :=
  decidable_of_iff _ (nat_forall_between_iff a b R).symm

/-! ### Double negation

A classical existential extracted by an unbounded search is replaced by its
double negation. These combinators chain such statements. -/

theorem nn_pure {p : Prop} (h : p) : ¬ ¬ p := fun hn => hn h

theorem nn_map {p q : Prop} (f : p → q) (h : ¬ ¬ p) : ¬ ¬ q :=
  fun hq => h (fun hp => hq (f hp))

theorem nn_bind {p q : Prop} (h : ¬ ¬ p) (f : p → ¬ ¬ q) : ¬ ¬ q :=
  fun hq => h (fun hp => f hp hq)

theorem int_forall_between_lt_iff (a b : Int) (R : Int → Prop) :
    (∀ p : Int, a < p → p ≤ b → R p) ↔ ∀ k : Nat, k < (b - a).toNat → R (a + 1 + k) := by
  constructor
  · intro h k hk
    exact h _ (by omega) (by omega)
  · intro h p h1 h2
    have := h (p - a - 1).toNat (by omega)
    rwa [show a + 1 + ((p - a - 1).toNat : Int) = p by omega] at this

/-- A universal over a half-open integer interval is decidable. -/
instance decidableForallIntBetweenLt (a b : Int) (R : Int → Prop) [DecidablePred R] :
    Decidable (∀ p : Int, a < p → p ≤ b → R p) :=
  decidable_of_iff _ (int_forall_between_lt_iff a b R).symm

theorem int_forall_between_iff (a b : Int) (R : Int → Prop) :
    (∀ p : Int, a ≤ p → p ≤ b → R p) ↔ ∀ k : Nat, k < (b - a + 1).toNat → R (a + k) := by
  constructor
  · intro h k hk
    exact h _ (by omega) (by omega)
  · intro h p h1 h2
    have := h (p - a).toNat (by omega)
    rwa [show a + ((p - a).toNat : Int) = p by omega] at this

/-- A universal over a closed integer interval is decidable. -/
instance decidableForallIntBetween (a b : Int) (R : Int → Prop) [DecidablePred R] :
    Decidable (∀ p : Int, a ≤ p → p ≤ b → R p) :=
  decidable_of_iff _ (int_forall_between_iff a b R).symm

/-! ### Linear arithmetic without classical preprocessing

`omega` turns every implication, iff, negated conjunction and existential
hypothesis it finds into a fact using `Classical.propDecidable` or
`Exists.choose_spec`, and pushes the negation of a propositional goal the same
way. `cfomega` clears hypotheses of those shapes, negates a decidable goal itself,
pushes that negation with the decidable lemmas, and only then runs `omega`. -/

open Lean Meta Elab Tactic in
private meta def classicalShape (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  match t with
  | .forallE _ x y _ => return t.isArrow && (← isProp x) && (← isProp y)
  | _ =>
    match_expr t with
    | Exists _ _ => return true
    | Iff _ _ => return true
    | Not P =>
      let P ← whnfR P
      match P with
      | .forallE _ x y _ => return P.isArrow && (← isProp x) && (← isProp y)
      | _ =>
        match_expr P with
        | And _ _ => return true
        | Iff _ _ => return true
        | Not _ => return true
        | _ => return false
    | _ => return false

/-- `omega` on the arithmetic part of the context, without classical preprocessing. -/
syntax "cfomega" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| cfomega) => do
  liftMetaTactic fun g => do
    let mut g := g
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      if ← isProp d.type then
        if ← classicalShape d.type then
          try g ← g.clear d.fvarId catch _ => pure ()
    return [g]
  evalTactic (← `(tactic| first
    | (refine Iff.intro (fun hlia => ?_) (fun hlia => ?_) <;> cfomega)
    | (refine Decidable.byContradiction fun hlia => ?_
       try simp only [not_or, Decidable.not_and_iff_not_or_not, Decidable.not_imp_iff_and_not,
         Nat.not_le, Nat.not_lt, Int.not_le, Int.not_lt, Decidable.not_not, ne_eq] at hlia
       omega)
    | omega))

end Rule30UOR.Constructive

/-! ### Case splits use decidability

Core `by_cases` elaborates under `open Classical`, so a case split on a
proposition without a `Decidable` instance silently uses `Classical.choice`.
In the research modules a case split must use the proposition's own
decidability. This rule takes precedence over the core one: a split on an
undecidable proposition is a compile error rather than a hidden axiom. -/

macro_rules
  | `(tactic| by_cases $h : $e) => `(tactic| refine if $h:ident : $e then ?pos else ?neg)

