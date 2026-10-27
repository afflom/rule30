module

public import Mathlib.Data.List.Lex
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.Monotone.Basic

/-!
# Lyndon words and the Ehrenfeucht–Silberger theorem for infinite words

A word is *bordered* when a nonempty proper prefix of it is also a suffix. A *Lyndon word* is a
nonempty word that is strictly smaller, lexicographically, than each of its proper nonempty
suffixes.

* `IsLyndon.not_bordered`: a Lyndon word is unbordered. A border would be a proper prefix, hence
  smaller than the word, and a proper suffix, hence larger.
* `IsLyndon.append`: if `u < v` are Lyndon words, so is `u ++ v`.
* `eventuallyPeriodic_of_bordered` (**Ehrenfeucht–Silberger** for infinite words): over a finite
  ordered alphabet, an infinite word whose factors of length at least `L` are all bordered is
  eventually periodic. Its Lyndon factors are unbordered, hence shorter than `L`. Cutting off the
  longest Lyndon prefix again and again gives Lyndon words `l₀ ≥ l₁ ≥ ⋯`: if `lₖ < lₖ₊₁` then
  `lₖ lₖ₊₁` would be a longer Lyndon prefix. Finitely many words are that short, so the sequence is
  eventually constant, and the word is eventually `l^ω`.

The converse is elementary (`bordered_of_periodic` in `WordForms`): in a periodic stretch with
period `P`, every factor longer than `P` is bordered.

Sources: A. Ehrenfeucht, D. M. Silberger, *Periodicity and unbordered segments of words*, Discrete
Math. 26 (1979) 101–109. K. T. Chen, R. H. Fox, R. C. Lyndon, *Free differential calculus IV*,
Ann. of Math. 68 (1958) 81–95. M. Lothaire, *Combinatorics on Words*, Chapter 5. The proof through
the Lyndon factorization is written for this library.
-/

@[expose] public section

namespace Rule30Equivalents.Lyndon

variable {α : Type*}

/-- A word is bordered when a nonempty proper prefix of it is also a suffix. -/
def Bordered (w : List α) : Prop :=
  ∃ k, 0 < k ∧ k < w.length ∧ w.take k = w.drop (w.length - k)

/-- The factor `x(i), x(i + 1), …, x(i + ℓ - 1)` of an infinite word. -/
def factor (x : ℕ → α) (i ℓ : ℕ) : List α := (List.range ℓ).map fun j => x (i + j)

@[simp] theorem length_factor (x : ℕ → α) (i ℓ : ℕ) : (factor x i ℓ).length = ℓ := by
  simp [factor]

theorem factor_add (x : ℕ → α) (i a b : ℕ) :
    factor x i (a + b) = factor x i a ++ factor x (i + a) b := by
  simp only [factor, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Function.comp, Nat.add_assoc]

theorem getElem?_factor (x : ℕ → α) {i ℓ j : ℕ} (hj : j < ℓ) :
    (factor x i ℓ)[j]? = some (x (i + j)) := by
  simp [factor, hj]

variable [LinearOrder α]

/-- A Lyndon word: nonempty, and strictly smaller than each of its proper nonempty suffixes. -/
def IsLyndon (w : List α) : Prop :=
  w ≠ [] ∧ ∀ i, 0 < i → i < w.length → w < w.drop i

/-- A word is smaller than its proper extensions. -/
theorem lt_append_of_ne_nil : ∀ (u : List α) {t : List α}, t ≠ [] → u < u ++ t
  | [], t, ht => by
    obtain ⟨a, t', rfl⟩ := List.exists_cons_of_ne_nil ht
    exact List.Lex.nil
  | a :: u, t, ht => List.Lex.cons (lt_append_of_ne_nil u ht)

/-- A proper prefix is lexicographically smaller. -/
theorem lt_of_prefix_of_ne {u v : List α} (h : u <+: v) (hne : u ≠ v) : u < v := by
  obtain ⟨t, rfl⟩ := h
  exact lt_append_of_ne_nil u fun ht => hne (by simp [ht])

/-- If `u < s` is decided before `u` ends, appending anything to both keeps the order. -/
theorem lex_append_of_not_prefix {u s : List α} (h : List.Lex (· < ·) u s) (hp : ¬ u <+: s)
    (v w : List α) : List.Lex (· < ·) (u ++ v) (s ++ w) := by
  induction h with
  | nil => exact absurd (List.nil_prefix) hp
  | rel hab => exact List.Lex.rel hab
  | cons h ih => exact List.Lex.cons (ih fun h' => hp (List.cons_prefix_cons.2 ⟨rfl, h'⟩))

theorem singleton_isLyndon (a : α) : IsLyndon [a] :=
  ⟨List.cons_ne_nil a [], fun i hi hi' => by simp at hi'; omega⟩

/-- **A Lyndon word is unbordered.** -/
theorem IsLyndon.not_bordered {w : List α} (h : IsLyndon w) : ¬ Bordered w := by
  rintro ⟨k, hk0, hkw, hb⟩
  have h1 := h.2 (w.length - k) (by omega) (by omega)
  rw [← hb] at h1
  have h2 : w.take k < w := lt_of_prefix_of_ne (List.take_prefix k w) fun he => by
    have := congrArg List.length he
    simp at this
    omega
  exact lt_asymm h1 h2

/-- **The product of Lyndon words `u < v` is a Lyndon word.** -/
theorem IsLyndon.append {u v : List α} (hu : IsLyndon u) (hv : IsLyndon v) (huv : u < v) :
    IsLyndon (u ++ v) := by
  have hu0 : 0 < u.length := List.length_pos_iff.2 hu.1
  have hv0 : 0 < v.length := List.length_pos_iff.2 hv.1
  -- the key comparison `u ++ v < v`
  have key : u ++ v < v := by
    by_cases hp : u <+: v
    · obtain ⟨v', rfl⟩ := hp
      have hv' : v' ≠ [] := by
        rintro rfl
        simp at huv
      have := hv.2 u.length hu0 (by simp; exact List.length_pos_iff.2 hv')
      rw [List.drop_left] at this
      exact List.append_left_lt this
    · have := lex_append_of_not_prefix huv hp v []
      simpa using this
  refine ⟨by simp [hu.1], fun i hi0 hi => ?_⟩
  rcases lt_trichotomy i u.length with h | h | h
  · rw [List.drop_append_of_le_length h.le]
    have hnp : ¬ u <+: u.drop i := fun hp => by
      have := hp.length_le
      simp at this
      omega
    exact lex_append_of_not_prefix (hu.2 i hi0 h) hnp v v
  · subst h
    rw [List.drop_left]
    exact key
  · have hd : (u ++ v).drop i = v.drop (i - u.length) := by
      rw [show i = u.length + (i - u.length) by omega, List.drop_append]
      simp
    rw [hd]
    simp at hi
    exact lt_trans key (hv.2 (i - u.length) (by omega) (by omega))

/-! ### Infinite words -/

section Factorization

variable {x : ℕ → α} {L : ℕ}
  (hL : ∀ i ℓ, L ≤ ℓ → Bordered (factor x i ℓ))
include hL

theorem lyndon_factor_short {i ℓ : ℕ} (h : IsLyndon (factor x i ℓ)) : ℓ < L := by
  by_contra hle
  exact h.not_bordered (hL i ℓ (by omega))

theorem one_lt_L : 1 < L := by
  have := lyndon_factor_short hL (i := 0) (ℓ := 1) (by
    simpa [factor] using singleton_isLyndon (x 0))
  exact this

open Classical in
/-- The length of the longest Lyndon prefix of the tail at `i`. -/
noncomputable def lyn (x : ℕ → α) (L i : ℕ) : ℕ :=
  Nat.findGreatest (fun ℓ => IsLyndon (factor x i ℓ)) L

theorem lyn_isLyndon (i : ℕ) : IsLyndon (factor x i (lyn x L i)) := by
  classical
  exact Nat.findGreatest_spec (P := fun ℓ => IsLyndon (factor x i ℓ)) (m := 1)
    (one_lt_L hL).le (by simpa [factor] using singleton_isLyndon (x i))

theorem one_le_lyn (i : ℕ) : 1 ≤ lyn x L i := by
  classical
  exact Nat.le_findGreatest (P := fun ℓ => IsLyndon (factor x i ℓ)) (one_lt_L hL).le
    (by simpa [factor] using singleton_isLyndon (x i))

theorem le_lyn {i ℓ : ℕ} (h : IsLyndon (factor x i ℓ)) : ℓ ≤ lyn x L i := by
  classical
  exact Nat.le_findGreatest (P := fun ℓ => IsLyndon (factor x i ℓ))
    (lyndon_factor_short hL h).le h

/-- The cut points of the Lyndon factorization. -/
noncomputable def cut (x : ℕ → α) (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cut x L k + lyn x L (cut x L k)

/-- The Lyndon factors. -/
noncomputable def piece (x : ℕ → α) (L k : ℕ) : List α := factor x (cut x L k) (lyn x L (cut x L k))

/-- **The Lyndon factors do not increase.** -/
theorem piece_succ_le (k : ℕ) : piece x L (k + 1) ≤ piece x L k := by
  by_contra hlt
  rw [not_le] at hlt
  have hcat := (lyn_isLyndon hL (cut x L k)).append (lyn_isLyndon hL (cut x L (k + 1))) hlt
  have e : factor x (cut x L k) (lyn x L (cut x L k)) ++
      factor x (cut x L (k + 1)) (lyn x L (cut x L (k + 1))) =
      factor x (cut x L k) (lyn x L (cut x L k) + lyn x L (cut x L (k + 1))) := by
    rw [factor_add]
    rfl
  rw [e] at hcat
  have := le_lyn hL hcat
  have := one_le_lyn hL (cut x L (k + 1))
  omega

/-- **Over a finite alphabet, the Lyndon factors are eventually constant.** -/
theorem exists_piece_const [Finite α] : ∃ k₀, ∀ k, k₀ ≤ k → piece x L k = piece x L k₀ := by
  have hanti : Antitone (piece x L) := antitone_nat_of_succ_le (piece_succ_le hL)
  have hfin : (Set.range (piece x L)).Finite :=
    (List.finite_length_le (α := α) (n := L)).subset (by
      rintro _ ⟨k, rfl⟩
      have := lyndon_factor_short hL (lyn_isLyndon hL (cut x L k))
      show (piece x L k).length ≤ L
      simp [piece]
      omega)
  obtain ⟨_, ⟨k₀, rfl⟩, hmin⟩ := Set.exists_min_image _ id hfin (Set.range_nonempty _)
  exact ⟨k₀, fun k hk => le_antisymm (hanti hk) (hmin _ ⟨k, rfl⟩)⟩

end Factorization

/-- **Ehrenfeucht–Silberger for infinite words**: over a finite ordered alphabet, if every factor
of length at least `L` is bordered, the word is eventually periodic. -/
theorem eventuallyPeriodic_of_bordered [Finite α] {x : ℕ → α} {L : ℕ}
    (hL : ∀ i ℓ, L ≤ ℓ → Bordered (factor x i ℓ)) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → x (t + P) = x t := by
  obtain ⟨k₀, hk₀⟩ := exists_piece_const hL
  set m := lyn x L (cut x L k₀) with hm
  have hm1 : 1 ≤ m := one_le_lyn hL _
  have hlyn : ∀ k, k₀ ≤ k → lyn x L (cut x L k) = m := fun k hk => by
    have := congrArg List.length (hk₀ k hk)
    simpa [piece] using this
  have hcut : ∀ q, cut x L (k₀ + q) = cut x L k₀ + q * m := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show k₀ + (q + 1) = (k₀ + q) + 1 by omega, cut, hlyn (k₀ + q) (by omega), ih,
        Nat.succ_mul]
      omega
  refine ⟨cut x L k₀, m, hm1, fun t ht => ?_⟩
  obtain ⟨q, j, hj, rfl⟩ : ∃ q j, j < m ∧ t = cut x L k₀ + q * m + j :=
    ⟨(t - cut x L k₀) / m, (t - cut x L k₀) % m, Nat.mod_lt _ hm1, by
      have := Nat.div_add_mod (t - cut x L k₀) m
      rw [Nat.mul_comm] at this
      omega⟩
  have hpieces : piece x L (k₀ + q + 1) = piece x L (k₀ + q) :=
    (hk₀ _ (by omega)).trans (hk₀ _ (by omega)).symm
  have hidx := congrArg (fun l : List α => l[j]?) hpieces
  simp only [piece] at hidx
  rw [getElem?_factor x (by rw [hlyn _ (by omega)]; exact hj),
    getElem?_factor x (by rw [hlyn _ (by omega)]; exact hj), hcut,
    show k₀ + q + 1 = k₀ + (q + 1) by omega, hcut, Option.some.injEq] at hidx
  rw [show cut x L k₀ + q * m + j + m = cut x L k₀ + (q + 1) * m + j by rw [Nat.succ_mul]; omega]
  exact hidx

end Rule30Equivalents.Lyndon
