module

public import Rule30Equivalents.Substitutive
public import Rule30Equivalents.ShiftOrbit
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Primitive substitutive sequences are linearly recurrent

A sequence `x` is linearly recurrent with constant `L` (`IsLinearlyRecurrent`) if every nonempty
word `u` that occurs in `x` occurs at some position in every interval `[i, i + L |u|]`.

* `isLinearlyRecurrent_of_isPrimitive`: the fixed point `x` of a substitution `σ` prolongable on
  `x 0` with primitive incidence matrix is linearly recurrent, and so is every coding of it
  (`IsLinearlyRecurrent.comp`).
* `length_lt_of_occursAt` (Durand–Host–Skau): in a linearly recurrent sequence with constant `L`
  that is not eventually periodic, two occurrences `p < p + d` of a word `u` have `|u| < L d`.

The proof is combinatorial. Some `σᵏ(b)` contains every letter, so `|σⁿ(b)| ≤ |σⁿ⁺ᵏ(b')|` for all
letters `b, b'`. The fixed point is a concatenation of the blocks `σⁿ(x i)` (`occursAt_iter_seg`).
Every two-letter factor of `x` lies in every block `σᵐ(d)` for one `m`. A word `u` shorter than
every block of level `n` lies in two adjacent blocks, so in `σⁿ(x i x (i+1))`, so in every block
of level `n + m`; if `n` is the least such level, these blocks have length `O(|u|)`.

Sources: F. Durand, *A characterization of substitutive sequences using return words*, Discrete
Math. 179 (1998) 89–101; F. Durand, B. Host, C. Skau, *Substitutional dynamical systems, Bratteli
diagrams and dimension groups*, Ergodic Theory Dynam. Systems 19 (1999) 953–993.
-/

@[expose] public section

namespace Rule30Equivalents.LinearRecurrence

open Substitutive

variable {A : Type*}

/-! ### Words in a sequence -/

/-- The word `u` occurs in `x` at position `i`. -/
def OccursAt (x : ℕ → A) (u : List A) (i : ℕ) : Prop :=
  ∀ t (ht : t < u.length), x (i + t) = u[t]

/-- `x` is linearly recurrent with constant `L`: every nonempty word `u` occurring in `x` occurs at
some position in every interval `[i, i + L |u|]`. -/
def IsLinearlyRecurrent (x : ℕ → A) (L : ℕ) : Prop :=
  ∀ u : List A, u ≠ [] → (∃ p, OccursAt x u p) →
    ∀ i, ∃ j, i ≤ j ∧ j ≤ i + L * u.length ∧ OccursAt x u j

theorem OccursAt.of_infix {x : ℕ → A} {w u : List A} {p : ℕ} (hw : OccursAt x w p)
    (h : u <:+: w) : ∃ q, p ≤ q ∧ q + u.length ≤ p + w.length ∧ OccursAt x u q := by
  obtain ⟨s, t, rfl⟩ := h
  refine ⟨p + s.length, by omega, by simp; omega, fun j hj => ?_⟩
  have h := hw (s.length + j) (by simp; omega)
  rw [← add_assoc] at h
  rw [h, List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem infix_of_occursAt {x : ℕ → A} {w u : List A} {p q : ℕ} (hw : OccursAt x w p)
    (hu : OccursAt x u q) (hpq : p ≤ q) (hle : q + u.length ≤ p + w.length) : u <:+: w := by
  have e : u = (w.drop (q - p)).take u.length := by
    apply List.ext_getElem
    · simp
      omega
    · intro t h1 h2
      simp only [List.getElem_take, List.getElem_drop]
      rw [← hu t h1, ← hw (q - p + t) (by omega)]
      congr 1
      omega
  rw [e]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- A coding of a linearly recurrent sequence is linearly recurrent. -/
theorem IsLinearlyRecurrent.comp {B : Type*} {x : ℕ → A} {L : ℕ} (h : IsLinearlyRecurrent x L)
    (φ : A → B) : IsLinearlyRecurrent (φ ∘ x) L := by
  rintro u hu ⟨p, hp⟩ i
  set v : List A := (List.range u.length).map fun t => x (p + t) with hv
  have hvl : v.length = u.length := by simp [hv]
  have hvp : OccursAt x v p := fun t ht => by simp [hv]
  have hv0 : v ≠ [] := by
    rw [← List.length_pos_iff, hvl]
    exact List.length_pos_iff.2 hu
  obtain ⟨j, hij, hj, hocc⟩ := h v hv0 ⟨p, hvp⟩ i
  refine ⟨j, hij, hvl ▸ hj, fun t ht => ?_⟩
  have h1 := hocc t (hvl ▸ ht)
  have h2 := hp t ht
  simp only [Function.comp] at h2 ⊢
  rw [h1, ← h2]
  simp [hv]

/-! ### Iterates of a substitution -/

/-- The image `σ(w)` of a word. -/
def img (σ : A → List A) (w : List A) : List A := w.flatMap σ

/-- The iterate `σⁿ(w)`. -/
def iter (σ : A → List A) (n : ℕ) (w : List A) : List A := (img σ)^[n] w

variable {σ : A → List A}

theorem img_append (u v : List A) : img σ (u ++ v) = img σ u ++ img σ v := List.flatMap_append

theorem img_singleton (a : A) : img σ [a] = σ a := by simp [img]

theorem iter_zero (w : List A) : iter σ 0 w = w := rfl

theorem iter_succ (n : ℕ) (w : List A) : iter σ (n + 1) w = iter σ n (img σ w) :=
  Function.iterate_succ_apply _ _ _

theorem iter_succ' (n : ℕ) (w : List A) : iter σ (n + 1) w = img σ (iter σ n w) :=
  Function.iterate_succ_apply' _ _ _

theorem iter_add (m n : ℕ) (w : List A) : iter σ (m + n) w = iter σ m (iter σ n w) :=
  Function.iterate_add_apply _ _ _ _

theorem iter_one (a : A) : iter σ 1 [a] = σ a := by rw [iter_succ, img_singleton, iter_zero]

theorem iter_append (n : ℕ) (u v : List A) : iter σ n (u ++ v) = iter σ n u ++ iter σ n v := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih => rw [iter_succ, iter_succ, iter_succ, img_append, ih]

theorem iter_nil (n : ℕ) : iter σ n [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, show img σ [] = [] from rfl, ih]

theorem iter_cons (n : ℕ) (a : A) (w : List A) : iter σ n (a :: w) = iter σ n [a] ++ iter σ n w :=
  iter_append n [a] w

theorem iter_infix {u w : List A} (h : u <:+: w) (n : ℕ) : iter σ n u <:+: iter σ n w := by
  obtain ⟨s, t, rfl⟩ := h
  rw [iter_append, iter_append]
  exact List.infix_append _ _ _

theorem iter_infix_of_mem {a : A} {w : List A} (h : a ∈ w) (n : ℕ) :
    iter σ n [a] <:+: iter σ n w := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact iter_infix ⟨s, t, by simp⟩ n

theorem length_img_ge (hσ : ∀ b, σ b ≠ []) (w : List A) : w.length ≤ (img σ w).length := by
  induction w with
  | nil => simp [img]
  | cons a w ih =>
    rw [show a :: w = [a] ++ w from rfl, img_append, img_singleton, List.length_append,
      List.length_append]
    have := List.length_pos_iff.2 (hσ a)
    simp only [List.length_singleton]
    omega

theorem length_iter_ge (hσ : ∀ b, σ b ≠ []) (n : ℕ) (w : List A) :
    w.length ≤ (iter σ n w).length := by
  induction n generalizing w with
  | zero => exact le_rfl
  | succ n ih =>
    rw [iter_succ]
    exact (length_img_ge hσ w).trans (ih _)

theorem length_iter_le {n Λ : ℕ} (h : ∀ b, (iter σ n [b]).length ≤ Λ) (w : List A) :
    (iter σ n w).length ≤ w.length * Λ := by
  induction w with
  | nil => simp [iter_nil]
  | cons a w ih =>
    rw [iter_cons, List.length_append, List.length_cons, add_mul, one_mul]
    have := h a
    omega

/-! ### The fixed point as a concatenation of blocks -/

/-- The prefix `x 0 ⋯ x (m - 1)`. -/
def pre (x : ℕ → A) (m : ℕ) : List A := (List.range m).map x

/-- The factor `x i ⋯ x (i + r - 1)`. -/
def seg (x : ℕ → A) (i r : ℕ) : List A := (List.range r).map fun t => x (i + t)

variable {x : ℕ → A}

theorem length_pre (m : ℕ) : (pre x m).length = m := by simp [pre]

theorem length_seg (i r : ℕ) : (seg x i r).length = r := by simp [seg]

theorem pre_add (m r : ℕ) : pre x (m + r) = pre x m ++ seg x m r := by
  simp [pre, seg, List.range_add]

theorem seg_one (i : ℕ) : seg x i 1 = [x i] := by simp [seg]

theorem seg_two (i : ℕ) : seg x i 2 = [x i, x (i + 1)] := by simp [seg, List.range_succ]

theorem occursAt_seg (i r : ℕ) : OccursAt x (seg x i r) i := fun t ht => by simp [seg]

theorem img_pre (hx : IsFixedPoint σ x) (i : ℕ) : img σ (pre x i) = pre x (start σ x i) := by
  induction i with
  | zero => simp [pre, img, start]
  | succ i ih =>
    rw [pre_add, seg_one, img_append, ih, img_singleton]
    have hs : start σ x (i + 1) = start σ x i + (σ (x i)).length := Finset.sum_range_succ _ _
    rw [hs, pre_add]
    congr 1
    apply List.ext_getElem (by simp [length_seg])
    intro t h1 h2
    simp only [seg, List.getElem_map, List.getElem_range]
    exact (hx i t h1).symm

theorem iter_pre (hx : IsFixedPoint σ x) (n i : ℕ) :
    iter σ n (pre x i) = pre x (iter σ n (pre x i)).length := by
  induction n generalizing i with
  | zero => rw [iter_zero, length_pre]
  | succ n ih =>
    rw [iter_succ', ih i, img_pre hx, length_pre]

/-- The start `|σⁿ(x 0 ⋯ x (i - 1))|` of the `i`-th block of level `n`. -/
def pos (σ : A → List A) (x : ℕ → A) (n i : ℕ) : ℕ := (iter σ n (pre x i)).length

theorem pos_add (n i r : ℕ) : pos σ x n (i + r) = pos σ x n i + (iter σ n (seg x i r)).length := by
  simp only [pos, pre_add, iter_append, List.length_append]

/-- **Desubstitution**: `x` is the concatenation of the blocks `σⁿ(x i)`; more generally
`σⁿ(x i ⋯ x (i + r - 1))` occurs in `x` at the start of the `i`-th block of level `n`. -/
theorem occursAt_iter_seg (hx : IsFixedPoint σ x) (n i r : ℕ) :
    OccursAt x (iter σ n (seg x i r)) (pos σ x n i) := by
  intro t ht
  unfold pos
  set P := (iter σ n (pre x i)).length with hP
  set W := iter σ n (seg x i r) with hW
  have h := iter_pre hx n (i + r)
  rw [pre_add, iter_append, iter_pre hx n i, ← hP, ← hW] at h
  have hlen : (pre x P ++ W).length = P + W.length := by rw [List.length_append, length_pre]
  rw [hlen] at h
  have h2 := congrArg (fun l => l[P + t]?) h
  rw [List.getElem?_append_right (by rw [length_pre]; omega), length_pre, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem ht, pre, List.getElem?_map, List.getElem?_range (by omega),
    Option.map_some] at h2
  exact (Option.some.inj h2).symm

theorem exists_block {P : ℕ → ℕ} (h0 : P 0 = 0) (hP : ∀ j, P j < P (j + 1)) (i : ℕ) :
    ∃ j, P j ≤ i ∧ i < P (j + 1) := by
  have hge : ∀ j, j ≤ P j := fun j => by
    induction j with
    | zero => omega
    | succ j ih =>
      have := hP j
      omega
  classical
  have hex : ∃ j, i < P (j + 1) := ⟨i, by have := hge (i + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h, h0]
    omega
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel h] at this
    omega

/-! ### Primitive incidence matrices -/

theorem count_img [Fintype A] [DecidableEq A] (w : List A) (c : A) :
    (img σ w).count c = ∑ d, w.count d * (σ d).count c := by
  induction w with
  | nil => simp [img]
  | cons a w ih =>
    rw [show a :: w = [a] ++ w from rfl, img_append, img_singleton, List.count_append, ih]
    simp [List.count_cons, add_mul, Finset.sum_add_distrib, add_comm]

theorem incidence_pow_apply [Fintype A] [DecidableEq A] (n : ℕ) (b c : A) :
    (incidence σ ^ n) b c = ((iter σ n [b]).count c : ℝ) := by
  induction n generalizing c with
  | zero =>
    rw [pow_zero, iter_zero, Matrix.one_apply, List.count_singleton]
    by_cases h : b = c <;> simp [h]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, iter_succ', count_img]
    push_cast
    exact Finset.sum_congr rfl fun d _ => by rw [ih, incidence, Matrix.of_apply]

theorem mem_iter_of_isPrimitive [Fintype A] [DecidableEq A] (hprim : (incidence σ).IsPrimitive) :
    ∃ k, 0 < k ∧ ∀ b c, c ∈ iter σ k [b] := by
  obtain ⟨k, hk, hpos⟩ := hprim.exists_pos_pow
  refine ⟨k, hk, fun b c => List.count_pos_iff.1 ?_⟩
  have := hpos b c
  rw [incidence_pow_apply] at this
  exact_mod_cast this

/-- `max_b |σⁿ(b)|`. -/
def maxLen [Fintype A] (σ : A → List A) (n : ℕ) : ℕ := Finset.univ.sup fun b => (iter σ n [b]).length

theorem length_le_maxLen [Fintype A] (n : ℕ) (b : A) : (iter σ n [b]).length ≤ maxLen σ n :=
  Finset.le_sup (f := fun b => (iter σ n [b]).length) (Finset.mem_univ b)

theorem maxLen_zero_le [Fintype A] : maxLen σ 0 ≤ 1 :=
  Finset.sup_le fun b _ => by simp [iter_zero]

theorem maxLen_add_le [Fintype A] (n j : ℕ) : maxLen σ (n + j) ≤ maxLen σ 1 ^ j * maxLen σ n := by
  induction j with
  | zero => simp
  | succ j ih =>
    refine Finset.sup_le fun b _ => ?_
    rw [← add_assoc, iter_succ, img_singleton]
    calc (iter σ (n + j) (σ b)).length ≤ (σ b).length * maxLen σ (n + j) :=
          length_iter_le (fun c => length_le_maxLen _ c) _
      _ ≤ maxLen σ 1 * (maxLen σ 1 ^ j * maxLen σ n) := by
          gcongr
          · simpa [iter_one] using length_le_maxLen (σ := σ) 1 b
      _ = maxLen σ 1 ^ (j + 1) * maxLen σ n := by ring

theorem pos_zero (n : ℕ) : pos σ x n 0 = 0 := by simp [pos, pre, iter_nil]

theorem pos_lt_pos_succ (hσ : ∀ b, σ b ≠ []) (n j : ℕ) : pos σ x n j < pos σ x n (j + 1) := by
  rw [pos_add, seg_one]
  have := length_iter_ge hσ n [x j]
  simp only [List.length_singleton] at this
  omega

/-! ### Linear recurrence -/

/-- **Primitive substitutive sequences are linearly recurrent**: the fixed point of a substitution
prolongable on `x 0` with primitive incidence matrix is linearly recurrent. -/
theorem isLinearlyRecurrent_of_isPrimitive [Fintype A] [DecidableEq A] (hx : IsFixedPoint σ x)
    (hprol : 1 < (σ (x 0)).length) (hprim : (incidence σ).IsPrimitive) :
    ∃ L, IsLinearlyRecurrent x L := by
  obtain ⟨k, hk, hmem⟩ := mem_iter_of_isPrimitive hprim
  -- the substitution is non-erasing
  have hσ : ∀ b, σ b ≠ [] := fun b h => by
    have hc := hmem b (x 0)
    rw [show k = (k - 1) + 1 by omega, iter_succ, img_singleton, h, iter_nil] at hc
    simp at hc
  -- `σ(x 0) = x 0 r` with `r` nonempty, so `|σⁿ(x 0)| > n`
  have hfirst : (σ (x 0))[0]'(by omega) = x 0 := by
    have := hx 0 0 (by omega)
    simpa [start] using this.symm
  obtain ⟨r, hr, hσ0⟩ : ∃ r : List A, r ≠ [] ∧ σ (x 0) = x 0 :: r := by
    refine ⟨(σ (x 0)).tail, ?_, ?_⟩
    · rw [← List.length_pos_iff, List.length_tail]
      omega
    · conv_lhs => rw [← List.cons_head_tail (hσ (x 0))]
      rw [List.head_eq_getElem, hfirst]
  have hgrow : ∀ n, n + 1 ≤ (iter σ n [x 0]).length := fun n => by
    induction n with
    | zero => simp [iter_zero]
    | succ n ih =>
      rw [iter_succ, img_singleton, hσ0, iter_cons, List.length_append]
      have := length_iter_ge hσ n r
      have := List.length_pos_iff.2 hr
      omega
  have hp1 : pre x 1 = [x 0] := by simp [pre]
  -- `σʲ(x 0)` starts with `x 0`, so `σⁿ(x 0)` is a prefix of `σⁿ⁺ʲ(x 0)`
  have hstart0 : ∀ j, ∃ t, iter σ j [x 0] = x 0 :: t := fun j => by
    have h := iter_pre hx j 1
    have hl := length_iter_ge hσ j (pre x 1)
    rw [length_pre] at hl
    rw [show (iter σ j (pre x 1)).length = 1 + ((iter σ j (pre x 1)).length - 1) by omega,
      pre_add, hp1] at h
    exact ⟨_, h⟩
  have hpre0 : ∀ n j, iter σ n [x 0] <+: iter σ (n + j) [x 0] := fun n j => by
    obtain ⟨t, ht⟩ := hstart0 j
    rw [iter_add, ht, iter_cons n (x 0) t]
    exact List.prefix_append _ _
  -- every two-letter factor of `x` lies in every block `σᵐ(d)`
  have hpair0 : ∀ i, [x i, x (i + 1)] <:+: iter σ (i + 1) [x 0] := fun i => by
    have h := iter_pre hx (i + 1) 1
    rw [hp1] at h
    have hl := hgrow (i + 1)
    rw [h, show (iter σ (i + 1) [x 0]).length =
      i + 2 + ((iter σ (i + 1) [x 0]).length - (i + 2)) by omega, pre_add, pre_add, seg_two]
    exact List.infix_append _ _ _
  classical
  let g : A × A → ℕ := fun q =>
    if h : ∃ i, x i = q.1 ∧ x (i + 1) = q.2 then Classical.choose h + 1 else 0
  set M₀ := Finset.univ.sup g with hM₀
  have hpair : ∀ i d, [x i, x (i + 1)] <:+: iter σ (M₀ + k) [d] := fun i d => by
    have h : ∃ i', x i' = (x i, x (i + 1)).1 ∧ x (i' + 1) = (x i, x (i + 1)).2 := ⟨i, rfl, rfl⟩
    have hspec := Classical.choose_spec h
    have hg : g (x i, x (i + 1)) = Classical.choose h + 1 := dite_eq_left h
    have hle : Classical.choose h + 1 ≤ M₀ := hg ▸ Finset.le_sup (f := g) (Finset.mem_univ _)
    have h1 := hpair0 (Classical.choose h)
    rw [hspec.1, hspec.2] at h1
    have h2 : iter σ (Classical.choose h + 1) [x 0] <+: iter σ M₀ [x 0] := by
      have := hpre0 (Classical.choose h + 1) (M₀ - (Classical.choose h + 1))
      rwa [Nat.add_sub_cancel' hle] at this
    have h3 : iter σ M₀ [x 0] <:+: iter σ (M₀ + k) [d] := by
      rw [iter_add]
      exact iter_infix_of_mem (hmem d (x 0)) M₀
    exact h1.trans (h2.isInfix.trans h3)
  set m := M₀ + k with hm
  set s := maxLen σ 1 with hsdef
  have hs : 1 ≤ s := by
    have := length_le_maxLen (σ := σ) 1 (x 0)
    rw [iter_one] at this
    omega
  refine ⟨2 * s ^ (m + 1 + k), fun u hu ⟨p, hp⟩ i => ?_⟩
  have hu1 : 1 ≤ u.length := List.length_pos_iff.2 hu
  -- the least level `n` whose blocks are all longer than `u`
  have hex : ∃ n, ∀ b, u.length < (iter σ n [b]).length := ⟨u.length + k, fun b => by
    have h1 := hgrow u.length
    have h2 : iter σ u.length [x 0] <:+: iter σ (u.length + k) [b] := by
      rw [iter_add]
      exact iter_infix_of_mem (hmem b (x 0)) _
    have := h2.length_le
    omega⟩
  set n := Nat.find hex with hn
  have hnspec : ∀ b, u.length < (iter σ n [b]).length := Nat.find_spec hex
  have hn0 : n ≠ 0 := fun h => by
    have := hnspec (x 0)
    rw [h, iter_zero] at this
    simp only [List.length_singleton] at this
    omega
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, (iter σ n' [b₀]).length ≤ u.length := by
    have := Nat.find_min hex (show n' < Nat.find hex by omega)
    push Not at this
    exact this
  -- `u` lies in two adjacent blocks of level `n`, so in every block of level `n + m`
  obtain ⟨i₀, hi₀1, hi₀2⟩ := exists_block (pos_zero (x := x) n) (pos_lt_pos_succ (x := x) hσ n) p
  have hW := occursAt_iter_seg hx n i₀ 2
  rw [seg_two] at hW
  have hlen2 : pos σ x n (i₀ + 2) = pos σ x n i₀ + (iter σ n [x i₀, x (i₀ + 1)]).length := by
    rw [pos_add, seg_two]
  have hlen1 : pos σ x n (i₀ + 2) = pos σ x n (i₀ + 1) + (iter σ n [x (i₀ + 1)]).length := by
    rw [show i₀ + 2 = (i₀ + 1) + 1 by ring, pos_add, seg_one]
  have huW : u <:+: iter σ n [x i₀, x (i₀ + 1)] :=
    infix_of_occursAt hW hp hi₀1 (by have := hnspec (x (i₀ + 1)); omega)
  have hblock : ∀ d, u <:+: iter σ (n + m) [d] := fun d => by
    rw [iter_add]
    exact huW.trans (iter_infix (hpair i₀ d) n)
  -- the blocks of level `n + m` have length `O(|u|)`
  have hΛ : maxLen σ (n + m) ≤ s ^ (m + 1 + k) * u.length := by
    rcases le_or_gt k n' with hkn | hkn
    · have h1 : maxLen σ (n' - k) ≤ u.length := Finset.sup_le fun b _ => by
        have h := iter_infix_of_mem (σ := σ) (hmem b₀ b) (n' - k)
        rw [← iter_add, Nat.sub_add_cancel hkn] at h
        exact h.length_le.trans hb₀
      have h2 := maxLen_add_le (σ := σ) (n' - k) (m + 1 + k)
      rw [show n' - k + (m + 1 + k) = n + m by omega] at h2
      exact h2.trans (Nat.mul_le_mul_left _ h1)
    · have h2 := maxLen_add_le (σ := σ) 0 (n + m)
      rw [zero_add] at h2
      calc maxLen σ (n + m) ≤ s ^ (n + m) * maxLen σ 0 := h2
        _ ≤ s ^ (m + 1 + k) * 1 :=
            Nat.mul_le_mul (Nat.pow_le_pow_right hs (by omega)) maxLen_zero_le
        _ ≤ s ^ (m + 1 + k) * u.length := Nat.mul_le_mul_left _ hu1
  -- the block of level `n + m` after the one containing `i` contains `u`
  obtain ⟨j, hj1, hj2⟩ := exists_block (pos_zero (x := x) (n + m)) (pos_lt_pos_succ (x := x) hσ (n + m)) i
  have hB := occursAt_iter_seg hx (n + m) (j + 1) 1
  rw [seg_one] at hB
  obtain ⟨q, hq1, hq2, hq⟩ := hB.of_infix (hblock (x (j + 1)))
  have hbj : pos σ x (n + m) (j + 1) ≤ i + maxLen σ (n + m) := by
    have := pos_add (σ := σ) (x := x) (n + m) j 1
    rw [seg_one] at this
    have := length_le_maxLen (σ := σ) (n + m) (x j)
    omega
  have hbj1 := length_le_maxLen (σ := σ) (n + m) (x (j + 1))
  have hqi : i ≤ q := le_trans (Nat.le_of_lt hj2) hq1
  have hq3 : q + u.length ≤ pos σ x (n + m) (j + 1) + maxLen σ (n + m) :=
    hq2.trans (Nat.add_le_add_left hbj1 _)
  refine ⟨q, hqi, ?_, hq⟩
  calc q ≤ i + 2 * maxLen σ (n + m) := by omega
    _ ≤ i + 2 * (s ^ (m + 1 + k) * u.length) := by omega
    _ = i + 2 * s ^ (m + 1 + k) * u.length := by ring

/-- A coding of the fixed point of a primitive substitution is linearly recurrent. -/
theorem isLinearlyRecurrent_comp_of_isPrimitive [Fintype A] [DecidableEq A] {B : Type*}
    (hx : IsFixedPoint σ x) (hprol : 1 < (σ (x 0)).length) (hprim : (incidence σ).IsPrimitive)
    (φ : A → B) : ∃ L, IsLinearlyRecurrent (φ ∘ x) L :=
  (isLinearlyRecurrent_of_isPrimitive hx hprol hprim).imp fun _ h => h.comp φ

/-! ### Return words are long -/

/-- **Durand–Host–Skau**: in a linearly recurrent sequence with constant `L` that is not eventually
periodic, two occurrences `p < p + d` of a word `u` satisfy `|u| < L d`. Otherwise `z` has period
`d` on `[p, p + d + |u|)`, and every factor of length `d`, occurring somewhere in `[p, p + L d]`,
is a rotation of `z p ⋯ z (p + d - 1)`: at most `d` factors of length `d`, so `z` would be eventually
periodic by Morse–Hedlund. -/
theorem length_lt_of_occursAt {z : ℕ → Bool} {L : ℕ} (hz : IsLinearlyRecurrent z L)
    (hnp : ¬ EventuallyPeriodic z) {u : List Bool} {p d : ℕ} (hd : 0 < d)
    (hp : OccursAt z u p) (hpd : OccursAt z u (p + d)) : u.length < L * d := by
  by_contra hle
  push Not at hle
  -- `z` has period `d` on `[p, p + d + |u|)`
  have hper : ∀ a, p ≤ a → a < p + u.length → z (a + d) = z a := fun a ha1 ha2 => by
    have h1 := hpd (a - p) (by omega)
    have h2 := hp (a - p) (by omega)
    rw [show p + d + (a - p) = a + d by omega] at h1
    rw [show p + (a - p) = a by omega] at h2
    rw [h1, h2]
  have hrot : ∀ a, p ≤ a → a < p + d + u.length → z a = z (p + (a - p) % d) := fun a => by
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha1 ha2
      by_cases h : a - p < d
      · rw [Nat.mod_eq_of_lt h, show p + (a - p) = a by omega]
      · have h1 := hper (a - d) (by omega) (by omega)
        rw [show a - d + d = a by omega] at h1
        rw [h1, ih (a - d) (by omega) (by omega) (by omega),
          Nat.mod_eq_sub_mod (show d ≤ a - p by omega), show a - p - d = a - d - p by omega]
  -- every factor of length `d` is a rotation of `z p ⋯ z (p + d - 1)`
  have hsub : ShiftOrbit.factors z d ⊆
      Set.range fun r : Fin d => fun j : Fin d => z (p + (r + j) % d) := by
    rintro f ⟨i, rfl⟩
    set w : List Bool := (List.range d).map fun t => z (i + t) with hw
    have hwl : w.length = d := by simp [hw]
    have hw0 : w ≠ [] := by
      rw [← List.length_pos_iff, hwl]
      exact hd
    have hwocc : OccursAt z w i := fun t ht => by simp [hw]
    obtain ⟨j₀, hj1, hj2, hj⟩ := hz w hw0 ⟨i, hwocc⟩ p
    rw [hwl] at hj2
    refine ⟨⟨(j₀ - p) % d, Nat.mod_lt _ hd⟩, funext fun j => ?_⟩
    have e1 : z (i + j) = z (j₀ + j) := by
      rw [hj j (by rw [hwl]; exact j.2)]
      simp [hw]
    have hj3 : j₀ + j < p + d + u.length := by
      have := j.2
      nlinarith
    simp only
    rw [e1, hrot (j₀ + j) (by omega) hj3, show j₀ + ↑j - p = (j₀ - p) + ↑j by omega,
      Nat.mod_add_mod]
  have hcard : (ShiftOrbit.factors z d).ncard ≤ d := by
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    rw [← Set.image_univ]
    exact le_trans Set.ncard_image_le (by simp [Set.ncard_univ])
  exact hnp ((ShiftOrbit.eventuallyPeriodic_iff_exists_ncard_factors_le z).2 ⟨d, hcard⟩)

end Rule30Equivalents.LinearRecurrence
