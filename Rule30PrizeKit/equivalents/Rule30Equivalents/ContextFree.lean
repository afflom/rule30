module

public import Mathlib.Computability.ContextFreeGrammar
public import Rule30Equivalents.LogicAutomata
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Problem 1 and context-free languages

The unary language `{1ⁿ : c(n) = 1}` and the language of prefixes of the center column are
context-free only when they are regular, so by the regular-language forms (`LogicAutomata`)
Problem 1 holds iff neither is context-free.

Mathlib defines context-free grammars, but it has neither the pumping lemma nor the fact that
regular languages are context-free. Both are proved here for every grammar.

* `pumping`: **the pumping lemma** (Bar-Hillel, Perles and Shamir 1961). Every context-free
  language has a constant `p` such that each member `w` with `p ≤ |w|` splits as `u v x y z` with
  `v y ≠ []` and `|v x y| ≤ p`, and every `u vⁱ x yⁱ z` is a member.
  - The proof works with derivation forests (`Der`) and forests with one hole (`Ctx`).
  - Take a derivation of `w` with the fewest rule applications. If no node has a descendant with
    its own label, the yield is short: at most `b ^ N`, where `b` bounds the lengths of the rules
    and `N` counts the nonterminals (`Der.length_yield_le`).
  - Otherwise some node has a descendant with its label, while none of its children does
    (`Der.repeatFree_or_exists`). The two equal labels give the split, and minimality makes `v y`
    nonempty.
* `isContextFree_of_isRegular`: over a finite alphabet every regular language is context-free,
  through the right-linear grammar of a DFA.
* `eventuallyPeriodic_iff_unary_isContextFree`: `{1ⁿ : b(n) = 1}` is context-free iff `b` is
  eventually periodic. Each long member has a pump of length at most `p`, so membership is monotone
  along steps of `p!` and therefore eventually periodic (Ginsburg and Rice 1962).
* `eventuallyPeriodic_iff_prefLang_isContextFree`: the prefix language of `b` is context-free iff
  `b` is eventually periodic (Book 1977). Pumping one long prefix makes every `u vⁱ` a prefix of
  `b`, so `b` is periodic after `u`.
* `problem1_iff_unary_not_contextFree` and `problem1_iff_prefixes_not_contextFree`.

Sources: Y. Bar-Hillel, M. Perles, E. Shamir, *On formal properties of simple phrase structure
grammars*, Z. Phonetik Sprachwiss. Kommunikationsforsch. 14 (1961) 143–172; S. Ginsburg, H. G. Rice,
*Two families of languages related to ALGOL*, J. ACM 9 (1962) 350–371; R. V. Book, *On languages
with a certain prefix property*, Math. Systems Theory 10 (1977) 229–237.
-/

@[expose] public section

universe u

namespace Rule30Equivalents.ContextFree

open Ruliology.CellularAutomata ContextFreeGrammar

section Grammar

variable {T : Type u} (g : ContextFreeGrammar T)

/-- A derivation forest of `g`: one derivation tree for each symbol of the sentential form, with
terminal leaves. -/
inductive Der : List (Symbol T g.NT) → Type u
  /-- The empty forest. -/
  | nil : Der []
  /-- A terminal leaf, followed by a forest. -/
  | leaf (t : T) {ss : List (Symbol T g.NT)} : Der ss → Der (.terminal t :: ss)
  /-- A node that applies the rule `r`, with its children, followed by a forest. -/
  | node (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules) {ss : List (Symbol T g.NT)} :
      Der r.output → Der ss → Der (.nonterminal r.input :: ss)

/-- A derivation forest with one hole: a leaf labeled by the nonterminal `A` and left unexpanded. -/
inductive Ctx (A : g.NT) : List (Symbol T g.NT) → Type u
  /-- The hole, followed by a forest. -/
  | hole {ss : List (Symbol T g.NT)} : Der g ss → Ctx A (.nonterminal A :: ss)
  /-- A terminal leaf, followed by a forest with the hole. -/
  | leaf (t : T) {ss : List (Symbol T g.NT)} : Ctx A ss → Ctx A (.terminal t :: ss)
  /-- A node with the hole among its descendants, followed by a forest. -/
  | down (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules) {ss : List (Symbol T g.NT)} :
      Ctx A r.output → Der g ss → Ctx A (.nonterminal r.input :: ss)
  /-- A node, followed by a forest with the hole. -/
  | next (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules) {ss : List (Symbol T g.NT)} :
      Der g r.output → Ctx A ss → Ctx A (.nonterminal r.input :: ss)

variable {g}

namespace Der

/-- The word derived by a forest. -/
def yield : {ss : List (Symbol T g.NT)} → Der g ss → List T
  | _, nil => []
  | _, leaf t d => t :: d.yield
  | _, node _ _ d₁ d₂ => d₁.yield ++ d₂.yield

/-- The number of rule applications. -/
def size : {ss : List (Symbol T g.NT)} → Der g ss → ℕ
  | _, nil => 0
  | _, leaf _ d => d.size
  | _, node _ _ d₁ d₂ => d₁.size + d₂.size + 1

/-- The forest of leaves of a terminal word. -/
def ofWord : (w : List T) → Der g (w.map .terminal)
  | [] => nil
  | t :: w => leaf t (ofWord w)

/-- Concatenation of forests. -/
def append : {ss₁ ss₂ : List (Symbol T g.NT)} → Der g ss₁ → Der g ss₂ → Der g (ss₁ ++ ss₂)
  | _, _, nil, e => e
  | _, _, leaf t d, e => leaf t (d.append e)
  | _, _, node r hr d₁ d₂, e => node r hr d₁ (d₂.append e)

@[simp] theorem yield_ofWord (w : List T) : (ofWord (g := g) w).yield = w := by
  induction w with
  | nil => rfl
  | cons t w ih => simp [ofWord, yield, ih]

@[simp] theorem yield_append {ss₁ ss₂ : List (Symbol T g.NT)} (d : Der g ss₁) (e : Der g ss₂) :
    (d.append e).yield = d.yield ++ e.yield := by
  induction d with
  | nil => rfl
  | leaf t d ih => simp [append, yield, ih]
  | node r hr d₁ d₂ _ ih => simp [append, yield, ih]

@[simp] theorem size_append {ss₁ ss₂ : List (Symbol T g.NT)} (d : Der g ss₁) (e : Der g ss₂) :
    (d.append e).size = d.size + e.size := by
  induction d with
  | nil => simp [append, size]
  | leaf t d ih => simp [append, size, ih]
  | node r hr d₁ d₂ _ ih => simp only [append, size, ih]; omega

/-- A forest of a concatenation splits into forests of the two parts. -/
theorem exists_split : ∀ {ss₁ ss₂ : List (Symbol T g.NT)} (d : Der g (ss₁ ++ ss₂)),
    ∃ (d₁ : Der g ss₁) (d₂ : Der g ss₂), d₁.yield ++ d₂.yield = d.yield ∧
      d₁.size + d₂.size = d.size
  | [], _, d => ⟨nil, d, by simp [yield], by simp [size]⟩
  | .terminal _ :: _, _, leaf t d => by
    obtain ⟨d₁, d₂, h₁, h₂⟩ := exists_split d
    exact ⟨leaf t d₁, d₂, by simp [yield, ← h₁], by simp [size, h₂]⟩
  | .nonterminal _ :: _, _, node r hr e d => by
    obtain ⟨d₁, d₂, h₁, h₂⟩ := exists_split d
    exact ⟨node r hr e d₁, d₂, by simp [yield, ← h₁], by simp only [size, ← h₂]; omega⟩

/-- A forest is a derivation. -/
theorem derives {ss : List (Symbol T g.NT)} (d : Der g ss) :
    g.Derives ss (d.yield.map .terminal) := by
  induction d with
  | nil => exact Relation.ReflTransGen.refl
  | leaf t d ih => simpa [yield] using ih.append_left [.terminal t]
  | @node r hr ss d₁ d₂ ih₁ ih₂ =>
    have h₀ : g.Produces (.nonterminal r.input :: ss) (r.output ++ ss) := ⟨r, hr, .head ss⟩
    simpa [yield] using h₀.single.trans ((ih₁.append_right _).trans (ih₂.append_left _))

/-- Every derivation of a terminal word comes from a forest. -/
theorem exists_of_derives {ss : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives ss (w.map .terminal)) : ∃ d : Der g ss, d.yield = w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨ofWord w, yield_ofWord w⟩
  | head hp _ ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨r, hr, hrw⟩ := hp
    obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
    obtain ⟨d₁₂, d₃, h₁, -⟩ := exists_split (ss₁ := p ++ r.output) d
    obtain ⟨d₁, d₂, h₂, -⟩ := exists_split d₁₂
    rw [List.append_assoc]
    refine ⟨d₁.append ((node r hr d₂ nil).append d₃), ?_⟩
    rw [← hd, ← h₁, ← h₂]
    simp [yield, append]

theorem mem_language_iff {w : List T} :
    w ∈ g.language ↔ ∃ d : Der g [.nonterminal g.initial], d.yield = w :=
  ⟨fun h => exists_of_derives ((ContextFreeGrammar.mem_language_iff g w).1 h),
    fun ⟨d, hd⟩ => (ContextFreeGrammar.mem_language_iff g w).2 (hd ▸ d.derives)⟩

end Der

namespace Ctx

variable {A : g.NT}

/-- The terminals left of the hole. -/
def lhs : {ss : List (Symbol T g.NT)} → Ctx g A ss → List T
  | _, hole _ => []
  | _, leaf t c => t :: c.lhs
  | _, down _ _ c _ => c.lhs
  | _, next _ _ d c => d.yield ++ c.lhs

/-- The terminals right of the hole. -/
def rhs : {ss : List (Symbol T g.NT)} → Ctx g A ss → List T
  | _, hole d => d.yield
  | _, leaf _ c => c.rhs
  | _, down _ _ c d => c.rhs ++ d.yield
  | _, next _ _ _ c => c.rhs

/-- The number of rule applications. -/
def size : {ss : List (Symbol T g.NT)} → Ctx g A ss → ℕ
  | _, hole d => d.size
  | _, leaf _ c => c.size
  | _, down _ _ c d => c.size + d.size + 1
  | _, next _ _ d c => d.size + c.size + 1

/-- Fill the hole with a derivation tree of `A`. -/
def plug : {ss : List (Symbol T g.NT)} → Ctx g A ss → Der g [.nonterminal A] → Der g ss
  | _, hole d, e => e.append d
  | _, leaf t c, e => .leaf t (c.plug e)
  | _, down r hr c d, e => .node r hr (c.plug e) d
  | _, next r hr d c, e => .node r hr d (c.plug e)

@[simp] theorem yield_plug {ss : List (Symbol T g.NT)} (c : Ctx g A ss)
    (e : Der g [.nonterminal A]) : (c.plug e).yield = c.lhs ++ e.yield ++ c.rhs := by
  induction c with
  | hole d => exact (Der.yield_append e d).trans (by simp [lhs, rhs])
  | leaf t c ih => simp [plug, lhs, rhs, Der.yield, ih]
  | down r hr c d ih => simp [plug, lhs, rhs, Der.yield, ih]
  | next r hr d c ih => simp [plug, lhs, rhs, Der.yield, ih]

@[simp] theorem size_plug {ss : List (Symbol T g.NT)} (c : Ctx g A ss)
    (e : Der g [.nonterminal A]) : (c.plug e).size = c.size + e.size := by
  induction c with
  | hole d => exact (Der.size_append e d).trans (Nat.add_comm _ _)
  | leaf t c ih => simp only [plug, size, Der.size, ih]
  | down r hr c d ih => simp only [plug, size, Der.size, ih]; omega
  | next r hr d c ih => simp only [plug, size, Der.size, ih]; omega

/-- Iterate a derivation `A ⇒ r.output ⇒* v A y` (with `A = r.input`) on a derivation `e` of
`x` from `A`: the result derives `vⁱ x yⁱ`. -/
def pump {r : ContextFreeRule T g.NT} (c : Ctx g r.input r.output) (hr : r ∈ g.rules)
    (e : Der g [.nonterminal r.input]) : ℕ → Der g [.nonterminal r.input]
  | 0 => e
  | i + 1 => .node r hr (c.plug (pump c hr e i)) .nil

theorem yield_pump {r : ContextFreeRule T g.NT} (c : Ctx g r.input r.output) (hr : r ∈ g.rules)
    (e : Der g [.nonterminal r.input]) (i : ℕ) :
    (c.pump hr e i).yield =
      (List.replicate i c.lhs).flatten ++ e.yield ++ (List.replicate i c.rhs).flatten := by
  induction i with
  | zero => simp [pump]
  | succ i ih =>
    have h₁ : (List.replicate (i + 1) c.lhs).flatten = c.lhs ++ (List.replicate i c.lhs).flatten :=
      by simp only [List.replicate_succ, List.flatten_cons]
    have h₂ : (List.replicate (i + 1) c.rhs).flatten = (List.replicate i c.rhs).flatten ++ c.rhs :=
      by simp only [List.replicate_succ', List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil]
    rw [h₁, h₂]
    simp [pump, Der.yield, ih]

end Ctx

/-! ### Repeated labels -/

section Labels

variable [DecidableEq g.NT]

namespace Der

/-- The nonterminals at the nodes of a forest. -/
def labels : {ss : List (Symbol T g.NT)} → Der g ss → Finset g.NT
  | _, nil => ∅
  | _, leaf _ d => d.labels
  | _, node r _ d₁ d₂ => insert r.input (d₁.labels ∪ d₂.labels)

/-- No node has a descendant with its own label. -/
def RepeatFree : {ss : List (Symbol T g.NT)} → Der g ss → Prop
  | _, nil => True
  | _, leaf _ d => d.RepeatFree
  | _, node r _ d₁ d₂ => r.input ∉ d₁.labels ∧ d₁.RepeatFree ∧ d₂.RepeatFree

theorem labels_subset {ss : List (Symbol T g.NT)} (d : Der g ss) :
    d.labels ⊆ g.rules.image (·.input) := by
  induction d with
  | nil => simp [labels]
  | leaf t d ih => exact ih
  | node r hr d₁ d₂ ih₁ ih₂ =>
    simp only [labels, Finset.insert_subset_iff, Finset.union_subset_iff]
    exact ⟨Finset.mem_image_of_mem _ hr, ih₁, ih₂⟩

/-- A repeat-free forest is short: each tree yields at most `b ^ k` letters, where `b` bounds the
lengths of the rules and `k` is the number of labels. -/
theorem length_yield_le {b : ℕ} (hb : 1 ≤ b) (hg : ∀ r ∈ g.rules, r.output.length ≤ b)
    {ss : List (Symbol T g.NT)} (d : Der g ss) (h : d.RepeatFree) :
    d.yield.length ≤ ss.length * b ^ d.labels.card := by
  induction d with
  | nil => simp [yield]
  | leaf t d ih =>
    have ih := ih h
    have h₁ : 1 ≤ b ^ d.labels.card := Nat.one_le_pow _ _ hb
    simp only [yield, labels, List.length_cons]
    nlinarith
  | @node r hr ss d₁ d₂ ih₁ ih₂ =>
    obtain ⟨hr₁, h₁, h₂⟩ := h
    have ih₁ := ih₁ h₁
    have ih₂ := ih₂ h₂
    have hK₁ : d₁.labels.card + 1 ≤ (insert r.input (d₁.labels ∪ d₂.labels)).card := by
      rw [← Finset.card_insert_of_notMem hr₁]
      exact Finset.card_le_card (Finset.insert_subset_insert _ Finset.subset_union_left)
    have hK₂ : d₂.labels.card ≤ (insert r.input (d₁.labels ∪ d₂.labels)).card :=
      Finset.card_le_card (Finset.subset_union_right.trans (Finset.subset_insert _ _))
    have e₁ := Nat.pow_le_pow_right hb hK₁
    have e₂ := Nat.mul_le_mul_left ss.length (Nat.pow_le_pow_right hb hK₂)
    have e₃ : r.output.length * b ^ d₁.labels.card ≤ b ^ (d₁.labels.card + 1) := by
      rw [pow_succ']
      exact Nat.mul_le_mul_right _ (hg r hr)
    simp only [yield, labels, List.length_append, List.length_cons]
    nlinarith

/-- An occurrence of a label cuts a forest into a context and a tree. -/
theorem exists_ctx_of_mem_labels {A : g.NT} {ss : List (Symbol T g.NT)} (d : Der g ss)
    (h : A ∈ d.labels) : ∃ (c : Ctx g A ss) (e : Der g [.nonterminal A]),
      c.lhs ++ e.yield ++ c.rhs = d.yield ∧ c.size + e.size = d.size := by
  induction d with
  | nil => simp [labels] at h
  | leaf t d ih =>
    obtain ⟨c, e, h₁, h₂⟩ := ih h
    exact ⟨.leaf t c, e, by simp [Ctx.lhs, Ctx.rhs, yield, ← h₁], by simp [Ctx.size, size, h₂]⟩
  | node r hr d₁ d₂ ih₁ ih₂ =>
    simp only [labels, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact ⟨.hole d₂, .node r hr d₁ .nil, by simp [Ctx.lhs, Ctx.rhs, yield],
        by simp only [Ctx.size, size]; omega⟩
    · obtain ⟨c, e, h₁, h₂⟩ := ih₁ h
      exact ⟨.down r hr c d₂, e, by simp [Ctx.lhs, Ctx.rhs, yield, ← h₁],
        by simp only [Ctx.size, size]; omega⟩
    · obtain ⟨c, e, h₁, h₂⟩ := ih₂ h
      exact ⟨.next r hr d₁ c, e, by simp [Ctx.lhs, Ctx.rhs, yield, ← h₁],
        by simp only [Ctx.size, size]; omega⟩

/-- A forest is repeat-free, or it has a node with a descendant of the same label whose children
are repeat-free. -/
theorem repeatFree_or_exists {ss : List (Symbol T g.NT)} (d : Der g ss) : d.RepeatFree ∨
    ∃ (r : ContextFreeRule T g.NT) (_ : r ∈ g.rules) (c : Ctx g r.input ss) (e : Der g r.output),
      e.RepeatFree ∧ r.input ∈ e.labels ∧ c.lhs ++ e.yield ++ c.rhs = d.yield ∧
        c.size + e.size + 1 = d.size := by
  induction d with
  | nil => exact Or.inl trivial
  | leaf t d ih =>
    rcases ih with h | ⟨r, hr, c, e, h₁, h₂, h₃, h₄⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, .leaf t c, e, h₁, h₂, by simp [Ctx.lhs, Ctx.rhs, yield, ← h₃],
        by simp [Ctx.size, size, h₄]⟩
  | node r hr d₁ d₂ ih₁ ih₂ =>
    rcases ih₁ with h₁ | ⟨r', hr', c, e, h₁, h₂, h₃, h₄⟩
    · rcases ih₂ with h₂ | ⟨r', hr', c, e, h₁', h₂', h₃, h₄⟩
      · by_cases hA : r.input ∈ d₁.labels
        · exact Or.inr ⟨r, hr, .hole d₂, d₁, h₁, hA, by simp [Ctx.lhs, Ctx.rhs, yield],
            by simp only [Ctx.size, size]; omega⟩
        · exact Or.inl ⟨hA, h₁, h₂⟩
      · exact Or.inr ⟨r', hr', .next r hr d₁ c, e, h₁', h₂',
          by simp [Ctx.lhs, Ctx.rhs, yield, ← h₃], by simp only [Ctx.size, size]; omega⟩
    · exact Or.inr ⟨r', hr', .down r hr c d₂, e, h₁, h₂, by simp [Ctx.lhs, Ctx.rhs, yield, ← h₃],
        by simp only [Ctx.size, size]; omega⟩

end Der

end Labels

/-! ### The pumping lemma -/

/-- **The pumping lemma for context-free languages** (Bar-Hillel, Perles and Shamir). -/
theorem pumping (g : ContextFreeGrammar T) : ∃ p, ∀ w ∈ g.language, p ≤ w.length →
    ∃ u v x y z : List T, w = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧
      (v ++ x ++ y).length ≤ p ∧ ∀ i : ℕ,
        u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈ g.language := by
  classical
  obtain ⟨b, hb₂, hb⟩ : ∃ b, 2 ≤ b ∧ ∀ r ∈ g.rules, r.output.length ≤ b :=
    ⟨max 2 (g.rules.sup fun r => r.output.length), le_max_left _ _,
      fun r hr => (Finset.le_sup (f := fun r => r.output.length) hr).trans (le_max_right _ _)⟩
  set N := (g.rules.image (·.input)).card
  have hpow : ∀ k, k ≤ N → b ^ k ≤ b ^ N := fun k hk => Nat.pow_le_pow_right (by omega) hk
  refine ⟨b ^ (N + 1), fun w hw hlen => ?_⟩
  rw [Der.mem_language_iff] at hw
  have hex : ∃ n, ∃ d : Der g [.nonterminal g.initial], d.yield = w ∧ d.size = n :=
    let ⟨d, hd⟩ := hw; ⟨_, d, hd, rfl⟩
  obtain ⟨d, hdw, hdn⟩ := Nat.find_spec hex
  have hmin : ∀ d' : Der g [.nonterminal g.initial], d'.yield = w → d.size ≤ d'.size :=
    fun d' h => hdn ▸ Nat.find_min' hex ⟨d', h, rfl⟩
  rcases d.repeatFree_or_exists with hrf | ⟨r, hr, c, e, herf, hmem, hyield, hsize⟩
  · have h₁ := d.length_yield_le (by omega) hb hrf
    have h₂ := hpow _ (Finset.card_le_card d.labels_subset)
    have h₃ : b ^ N < b ^ (N + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [hdw, List.length_singleton, one_mul] at h₁
    omega
  · obtain ⟨c₂, β, hy₂, hs₂⟩ := e.exists_ctx_of_mem_labels hmem
    refine ⟨c.lhs, c₂.lhs, β.yield, c₂.rhs, c.rhs, ?_, ?_, ?_, fun i => ?_⟩
    · rw [← hdw, ← hyield, ← hy₂]
      simp
    · intro h0
      obtain ⟨hv, hy⟩ := List.append_eq_nil_iff.1 h0
      have := hmin (c.plug β) (by rw [Ctx.yield_plug, ← hdw, ← hyield, ← hy₂, hv, hy]; simp)
      rw [Ctx.size_plug] at this
      omega
    · rw [hy₂]
      calc e.yield.length ≤ r.output.length * b ^ e.labels.card :=
            e.length_yield_le (by omega) hb herf
        _ ≤ b * b ^ N := Nat.mul_le_mul (hb r hr) (hpow _ (Finset.card_le_card e.labels_subset))
        _ = b ^ (N + 1) := (pow_succ' b N).symm
    · rw [Der.mem_language_iff]
      exact ⟨c.plug (c₂.pump hr β i), by simp [Ctx.yield_pump]⟩

/-- The pumping lemma for a context-free language. -/
theorem _root_.Language.IsContextFree.pumping {L : Language T} (h : L.IsContextFree) :
    ∃ p, ∀ w ∈ L, p ≤ w.length →
      ∃ u v x y z : List T, w = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧
        (v ++ x ++ y).length ≤ p ∧ ∀ i : ℕ,
          u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := h
  exact ContextFree.pumping g

end Grammar

/-! ### Regular languages are context-free -/

section Regular

variable {T : Type u} {σ : Type} (M : DFA T σ) [Fintype T] [DecidableEq T] [Fintype σ]
  [DecidableEq σ] [DecidablePred (· ∈ M.accept)]

/-- The right-linear grammar of a DFA: `q → a (δ q a)` for every state `q` and letter `a`, and
`q → ε` for every accepting state `q`. -/
abbrev dfaGrammar : ContextFreeGrammar T where
  NT := σ
  initial := M.start
  rules := (Finset.univ.image fun qa : σ × T =>
      (⟨qa.1, [.terminal qa.2, .nonterminal (M.step qa.1 qa.2)]⟩ : ContextFreeRule T σ)) ∪
    (Finset.univ.filter (· ∈ M.accept)).image fun q => (⟨q, []⟩ : ContextFreeRule T σ)

theorem dfaGrammar_der_iff (w : List T) : ∀ q : σ,
    (∃ d : Der (dfaGrammar M) [.nonterminal q], d.yield = w) ↔ M.evalFrom q w ∈ M.accept := by
  induction w with
  | nil =>
    intro q
    constructor
    · rintro ⟨d, hd⟩
      cases d with
      | node r hr d₁ d₂ =>
        cases d₂
        rcases Finset.mem_union.1 hr with h | h
        · obtain ⟨⟨q', a⟩, -, rfl⟩ := Finset.mem_image.1 h
          cases d₁ with
          | leaf _ d₃ => simp [Der.yield] at hd
        · obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 h
          simpa using hq'
    · intro hq
      let r : ContextFreeRule T σ := ⟨q, []⟩
      have hr : r ∈ (dfaGrammar M).rules := Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩))
      have key : ∃ d : Der (dfaGrammar M) [.nonterminal r.input], d.yield = [] :=
        ⟨Der.node (g := dfaGrammar M) r hr .nil .nil, rfl⟩
      exact key
  | cons a w ih =>
    intro q
    rw [DFA.evalFrom_cons, ← ih]
    constructor
    · rintro ⟨d, hd⟩
      cases d with
      | node r hr d₁ d₂ =>
        cases d₂
        rcases Finset.mem_union.1 hr with h | h
        · obtain ⟨⟨q', a'⟩, -, rfl⟩ := Finset.mem_image.1 h
          cases d₁ with
          | leaf _ d₃ =>
            simp only [Der.yield, List.append_nil, List.cons.injEq] at hd
            obtain ⟨rfl, hd⟩ := hd
            exact ⟨d₃, hd⟩
        · obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 h
          cases d₁
          simp [Der.yield] at hd
    · rintro ⟨d, hd⟩
      let r : ContextFreeRule T σ := ⟨q, [.terminal a, .nonterminal (M.step q a)]⟩
      have hr : r ∈ (dfaGrammar M).rules :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (q, a)))
      have key : ∃ d' : Der (dfaGrammar M) [.nonterminal r.input], d'.yield = a :: w :=
        ⟨Der.node (g := dfaGrammar M) r hr (.leaf a d) .nil, by simp [Der.yield, hd]⟩
      exact key

theorem language_dfaGrammar : (dfaGrammar M).language = M.accepts := by
  ext w
  rw [Der.mem_language_iff]
  exact dfaGrammar_der_iff M w M.start

end Regular

/-- Over a finite alphabet, a regular language is context-free. -/
theorem isContextFree_of_isRegular {T : Type u} [Fintype T] {L : Language T} (h : L.IsRegular) :
    L.IsContextFree := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨dfaGrammar M, language_dfaGrammar M⟩

/-! ### The two languages of a `Bool` sequence -/

/-- If `b n` forces `b (n + M)` for all `n ≥ p`, then `b` is eventually periodic: along each
residue class mod `M` the sequence is monotone, so it is eventually constant. -/
theorem eventuallyPeriodic_of_imp {b : ℕ → Bool} {p M : ℕ} (hM : 0 < M)
    (h : ∀ n, p ≤ n → b n = true → b (n + M) = true) : EventuallyPeriodic b := by
  let F : ℕ →o (Fin M → Bool) :=
    ⟨fun j r => b (p + r + j * M), monotone_nat_of_le_succ fun j r => by
      rw [Bool.le_iff_imp]
      intro hj
      have := h _ (by omega) hj
      rwa [show p + r + j * M + M = p + r + (j + 1) * M by ring] at this⟩
  obtain ⟨J, hJ⟩ := WellFoundedGT.monotone_chain_condition F
  refine ⟨p + J * M, M, hM, fun t ht => ?_⟩
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < M ∧ t = p + r + j * M :=
    ⟨(t - p) / M, (t - p) % M, Nat.mod_lt _ hM, by
      have := Nat.mod_add_div (t - p) M
      rw [Nat.mul_comm] at this
      omega⟩
  have hj : J ≤ j := by
    by_contra hlt
    have : (j + 1) * M ≤ J * M := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  have e₁ : b (p + r + J * M) = b (p + r + j * M) := congrFun (hJ j hj) ⟨r, hr⟩
  have e₂ : b (p + r + J * M) = b (p + r + (j + 1) * M) := congrFun (hJ (j + 1) (by omega)) ⟨r, hr⟩
  rw [show p + r + j * M + M = p + r + (j + 1) * M by ring, ← e₂, e₁]

/-- **A unary context-free language is eventually periodic** (Ginsburg and Rice). -/
theorem eventuallyPeriodic_of_unary_isContextFree {b : ℕ → Bool}
    (h : (LogicAutomata.unaryLang b).IsContextFree) : EventuallyPeriodic b := by
  obtain ⟨p, hp⟩ := h.pumping
  refine eventuallyPeriodic_of_imp (p := p) (Nat.factorial_pos p) fun n hn hb => ?_
  obtain ⟨u, v, x, y, z, hw, hvy, hlen, hpump⟩ :=
    hp (List.replicate n ()) (show b (List.replicate n ()).length = true by simpa using hb)
      (by simpa using hn)
  have hk : 1 ≤ v.length + y.length := by
    by_contra h0
    exact hvy (by simp_all)
  have hkp : v.length + y.length ≤ p := by
    simp only [List.length_append] at hlen
    omega
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (by omega) hkp
  have h₁ : b (u ++ (List.replicate (m + 1) v).flatten ++ x ++
      (List.replicate (m + 1) y).flatten ++ z).length = true := hpump (m + 1)
  have h₂ := congrArg List.length hw
  simp at h₁ h₂
  convert h₁ using 2
  rw [hm, h₂]
  ring

theorem eventuallyPeriodic_iff_unary_isContextFree (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ (LogicAutomata.unaryLang b).IsContextFree :=
  ⟨fun h => isContextFree_of_isRegular
    ((LogicAutomata.eventuallyPeriodic_iff_unary_isRegular b).1 h),
    eventuallyPeriodic_of_unary_isContextFree⟩

/-- **Problem 1 ⟺ the unary language `{1ⁿ : c(n) = 1}` is not context-free**. -/
theorem problem1_iff_unary_not_contextFree :
    Rule30Prize.Problem1 ↔ ¬ (LogicAutomata.unaryLang c).IsContextFree :=
  not_congr (eventuallyPeriodic_iff_unary_isContextFree c)

theorem mem_prefLang_iff {b : ℕ → Bool} {l : List Bool} :
    l ∈ LogicAutomata.prefLang b ↔ ∀ k < l.length, l[k]? = some (b k) := by
  rw [LogicAutomata.mem_prefLang]
  constructor
  · intro h k hk
    rw [h]
    simp [hk]
  · intro h
    apply List.ext_getElem?
    intro k
    by_cases hk : k < l.length
    · rw [h k hk]
      simp [hk]
    · simp [hk]

theorem mem_prefLang_of_append {b : ℕ → Bool} {l m : List Bool}
    (h : l ++ m ∈ LogicAutomata.prefLang b) : l ∈ LogicAutomata.prefLang b := by
  rw [mem_prefLang_iff] at h ⊢
  intro k hk
  have := h k (by simp; omega)
  rwa [List.getElem?_append_left hk] at this

/-- If every `u vⁱ` is a prefix of `b`, then `b` has period `|v|` after `u`. -/
theorem periodic_of_pumped_prefixes {b : ℕ → Bool} {u v : List Bool} (hv : v ≠ [])
    (h : ∀ i, u ++ (List.replicate i v).flatten ∈ LogicAutomata.prefLang b) :
    ∀ t, u.length ≤ t → b (t + v.length) = b t := by
  intro t ht
  obtain ⟨s, rfl⟩ : ∃ s, t = u.length + s := ⟨t - u.length, by omega⟩
  have hv₀ : 0 < v.length := List.length_pos_iff.2 hv
  set V := (List.replicate (s + 1) v).flatten with hV
  have hVlen : V.length = (s + 1) * v.length := by simp [hV]
  have hs : s < V.length := by rw [hVlen]; nlinarith
  have e₁ : (List.replicate (s + 2) v).flatten = v ++ V := by
    rw [hV, List.replicate_succ, List.flatten_cons]
  have e₂ : (List.replicate (s + 2) v).flatten = V ++ v := by
    rw [hV, List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil]
  have hl : (u ++ (List.replicate (s + 2) v).flatten).length = u.length + (s + 2) * v.length := by
    simp
  have a₁ := mem_prefLang_iff.1 (h (s + 2)) (u.length + s) (by rw [hl]; nlinarith)
  have a₂ := mem_prefLang_iff.1 (h (s + 2)) (u.length + s + v.length) (by rw [hl]; nlinarith)
  rw [e₂, List.getElem?_append_right (by omega), List.getElem?_append_left (by omega),
    show u.length + s - u.length = s by omega] at a₁
  rw [e₁, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
    show u.length + s + v.length - u.length - v.length = s by omega, a₁] at a₂
  exact (Option.some.inj a₂).symm

/-- **A context-free prefix language is eventually periodic** (Book). -/
theorem eventuallyPeriodic_of_prefLang_isContextFree {b : ℕ → Bool}
    (h : (LogicAutomata.prefLang b).IsContextFree) : EventuallyPeriodic b := by
  obtain ⟨p, hp⟩ := h.pumping
  obtain ⟨u, v, x, y, z, -, hvy, -, hpump⟩ :=
    hp _ (LogicAutomata.range_mem_prefLang b p) (by simp)
  have hmem : ∀ i, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ∈
      LogicAutomata.prefLang b := fun i => mem_prefLang_of_append (hpump i)
  by_cases hv : v = []
  · have hy : y ≠ [] := by simpa [hv] using hvy
    have := periodic_of_pumped_prefixes hy (u := u ++ x) fun i => by simpa [hv] using hmem i
    exact ⟨(u ++ x).length, y.length, List.length_pos_iff.2 hy, this⟩
  · have := periodic_of_pumped_prefixes hv (u := u) fun i =>
      mem_prefLang_of_append (m := x ++ (List.replicate i y).flatten) (by simpa using hmem i)
    exact ⟨u.length, v.length, List.length_pos_iff.2 hv, this⟩

theorem eventuallyPeriodic_iff_prefLang_isContextFree (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ (LogicAutomata.prefLang b).IsContextFree :=
  ⟨fun h => isContextFree_of_isRegular
    ((LogicAutomata.eventuallyPeriodic_iff_prefLang_isRegular b).1 h),
    eventuallyPeriodic_of_prefLang_isContextFree⟩

/-- **Problem 1 ⟺ the language of prefixes of the center column is not context-free**. -/
theorem problem1_iff_prefixes_not_contextFree :
    Rule30Prize.Problem1 ↔ ¬ (LogicAutomata.prefLang c).IsContextFree :=
  not_congr (eventuallyPeriodic_iff_prefLang_isContextFree c)

end Rule30Equivalents.ContextFree
