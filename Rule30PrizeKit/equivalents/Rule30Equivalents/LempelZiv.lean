module

public import Rule30Equivalents.WordForms
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Problem 1 ⟺ the Lempel–Ziv complexity of the prefixes is unbounded

`WordForms.lzComplexity b n` is the fewest components of a Lempel–Ziv (1976) history of the
prefix of length `n`: cut points `0 = x₀ < ⋯ < x_r = n`, each component a single letter or, apart
from its last letter, a copy of an earlier stretch.

* `eventuallyPeriodic_iff_lz_bounded`: a `Bool` sequence is eventually periodic iff the Lempel–Ziv
  complexity of its prefixes is bounded.
* `problem1_iff_lz_unbounded`: Problem 1 holds iff the Lempel–Ziv complexity of the
  prefixes of the center column is unbounded.

**Proof of the converse.** Suppose every prefix has a history with at most `K + 1` cut points.
* `exists_long_component`: some cut point `p` starts arbitrarily long components. Otherwise every
  cut point `p` is followed by another within a bound `L_p`. Then, from the cut `0`, every history
  of a long enough prefix has `k + 1` cut points below a bound `B_k` (`cuts_below`), for every `k`;
  at `k = K + 1` that is too many.
* A component longer than one letter is a copy from a source `s < p`. There are finitely many
  sources, so one `s` works for arbitrarily long components, and `b(s + j) = b(p + j)` for every `j`:
  `b` has period `p - s` from `s`.

The argument avoids extracting subsequences, and it needs no optimality theorem of Lempel and Ziv.

Sources: A. Lempel and J. Ziv, *On the complexity of finite sequences*, IEEE Trans. Inform. Theory
22 (1976) 75–81.
-/

@[expose] public section

namespace Rule30Equivalents.LempelZiv

open Ruliology.CellularAutomata WordForms

/-- In a strictly increasing list, every element below another one has a successor: the least
larger element, and the two are adjacent. -/
theorem exists_next {l : List ℕ} (hl : l.Pairwise (· < ·)) {p : ℕ} (hp : p ∈ l)
    (hr : ∃ r ∈ l, p < r) :
    ∃ q, (p, q) ∈ l.zip l.tail ∧ p < q ∧ ∀ r ∈ l, p < r → q ≤ r := by
  induction l with
  | nil => simp at hp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hl
    by_cases hpx : p = x
    · subst hpx
      obtain ⟨r, hr, hpr⟩ := hr
      cases xs with
      | nil => simp at hr; omega
      | cons y ys =>
        refine ⟨y, by simp, hl.1 y (by simp), fun r hr hpr => ?_⟩
        rcases List.mem_cons.1 hr with rfl | hr'
        · omega
        · rcases List.mem_cons.1 hr' with rfl | hr''
          · exact le_refl _
          · exact (List.pairwise_cons.1 hl.2).1 r hr'' |>.le
    · have hpxs : p ∈ xs := by
        rcases List.mem_cons.1 hp with h | h
        · exact absurd h hpx
        · exact h
      have hxp : x < p := hl.1 p hpxs
      obtain ⟨q, hq, hpq, hmin⟩ := ih hl.2 hpxs (by
        obtain ⟨r, hr, hpr⟩ := hr
        rcases List.mem_cons.1 hr with rfl | hr'
        · omega
        · exact ⟨r, hr', hpr⟩)
      refine ⟨q, ?_, hpq, fun r hr hpr => ?_⟩
      · cases xs with
        | nil => simp at hpxs
        | cons y ys => simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr hq
      · rcases List.mem_cons.1 hr with rfl | hr'
        · omega
        · exact hmin r hr' hpr

/-- The bounds of the iteration: `bnd Lf (k + 1) = bnd Lf k + max_{p ≤ bnd Lf k} Lf p`. -/
def bnd (Lf : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bnd Lf k + (Finset.range (bnd Lf k + 1)).sup Lf

section Converse
variable {b : ℕ → Bool} {K : ℕ} (cuts : ℕ → List ℕ) (hist : ∀ n, IsLZHistory b n (cuts n))
  (hlen : ∀ n, (cuts n).length ≤ K + 1)
include hist hlen

omit hlen in
theorem zero_mem (n : ℕ) : 0 ∈ cuts n := by
  have h := (hist n).1
  exact List.mem_of_mem_head? h

omit hlen in
theorem self_mem (n : ℕ) : n ∈ cuts n := by
  have h := (hist n).2.1
  exact List.mem_of_getLast? h

/-- **Some cut point starts arbitrarily long components.** -/
theorem exists_long_component :
    ∃ p, ∀ L, ∃ n, p ∈ cuts n ∧ p + L < n ∧ ∀ q ∈ cuts n, p < q → p + L < q := by
  classical
  by_contra hcon
  push Not at hcon
  choose Lf hLf using hcon
  -- the bounds `B k`
  let B : ℕ → ℕ := bnd Lf
  have hB : ∀ k, B (k + 1) = B k + (Finset.range (B k + 1)).sup Lf := fun _ => rfl
  have hBmono : ∀ k, B k ≤ B (k + 1) := fun k => by rw [hB]; omega
  -- `k + 1` cut points below `B k` in every long enough history
  have cuts_below : ∀ k n, B k < n → k + 1 ≤ ((cuts n).toFinset.filter (· ≤ B k)).card := by
    intro k
    induction k with
    | zero =>
      intro n _
      exact Finset.card_pos.2 ⟨0, by simp [zero_mem cuts hist n, B, bnd]⟩
    | succ k ih =>
      intro n hn
      have hn' : B k < n := lt_of_le_of_lt (hBmono k) hn
      have hS := ih n hn'
      have hne : ((cuts n).toFinset.filter (· ≤ B k)).Nonempty := Finset.card_pos.1 (by omega)
      set pmax := ((cuts n).toFinset.filter (· ≤ B k)).max' hne with hpmax
      have hpmem := Finset.max'_mem _ hne
      rw [← hpmax, Finset.mem_filter, List.mem_toFinset] at hpmem
      have hLp : Lf pmax ≤ (Finset.range (B k + 1)).sup Lf :=
        Finset.le_sup (Finset.mem_range.2 (by omega))
      obtain ⟨q, hq, hpq, hqL⟩ := hLf pmax n hpmem.1 (by rw [hB] at hn; omega)
      have hqB : B k < q := by
        by_contra hle
        push Not at hle
        have : q ≤ pmax := Finset.le_max' _ q (by simp [hq, hle])
        omega
      have hsub : insert q ((cuts n).toFinset.filter (· ≤ B k)) ⊆
          (cuts n).toFinset.filter (· ≤ B (k + 1)) := by
        intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨hq, by rw [hB]; omega⟩
        · simp only [Finset.mem_filter, List.mem_toFinset] at hr ⊢
          exact ⟨hr.1, le_trans hr.2 (hBmono k)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp; omega)] at this
      omega
  have h1 := cuts_below (K + 1) (B (K + 1) + 1) (by omega)
  have h2 : ((cuts (B (K + 1) + 1)).toFinset.filter (· ≤ B (K + 1))).card ≤ K + 1 :=
    le_trans (Finset.card_filter_le _ _)
      (le_trans (List.toFinset_card_le _) (hlen _))
  omega

omit hlen in
/-- A long component at `p` copies from some source `s < p`, for arbitrarily long stretches. -/
theorem exists_copy_source {p : ℕ}
    (hp : ∀ L, ∃ n, p ∈ cuts n ∧ p + L < n ∧ ∀ q ∈ cuts n, p < q → p + L < q) :
    ∀ L, ∃ s < p, ∀ j, j < L → b (s + j) = b (p + j) := by
  intro L
  obtain ⟨n, hpn, hLn, hlong⟩ := hp (L + 1)
  have hpw : (cuts n).Pairwise (· < ·) := (hist n).2.2.1.pairwise
  obtain ⟨q, hq, hpq, -⟩ := exists_next hpw hpn ⟨n, self_mem cuts hist n, by omega⟩
  have hqmem : q ∈ cuts n := List.mem_of_mem_tail (List.of_mem_zip hq).2
  have hqL : p + (L + 1) < q := hlong q hqmem hpq
  rcases (hist n).2.2.2 (p, q) hq with h | ⟨s, hs, hcopy⟩
  · simp only at h; omega
  · exact ⟨s, hs, fun j hj => hcopy j (by simp only; omega)⟩

end Converse

/-- **Bounded Lempel–Ziv complexity forces eventual periodicity.** -/
theorem eventuallyPeriodic_of_lz_bounded {b : ℕ → Bool} {K : ℕ}
    (h : ∀ n, lzComplexity b n ≤ K) : EventuallyPeriodic b := by
  classical
  -- an optimal history for every prefix
  have hex : ∀ n, ∃ cuts, IsLZHistory b n cuts ∧ cuts.length ≤ K + 1 := by
    intro n
    have hne : {k | ∃ cuts, IsLZHistory b n cuts ∧ cuts.length = k + 1}.Nonempty :=
      ⟨n, List.range (n + 1), isLZHistory_range b n, by simp⟩
    obtain ⟨cuts, hc, hl⟩ := Nat.sInf_mem hne
    exact ⟨cuts, hc, by rw [hl]; have := h n; unfold lzComplexity at this; omega⟩
  choose cuts hist hlen using hex
  obtain ⟨p, hp⟩ := exists_long_component cuts hist hlen
  have hsrc := exists_copy_source cuts hist hp
  -- one source works for every length
  obtain ⟨s, hs, hall⟩ : ∃ s < p, ∀ j, b (s + j) = b (p + j) := by
    by_contra hcon
    push Not at hcon
    choose J hJ using hcon
    let L := (Finset.range p).sup fun s => if hs : s < p then J s hs + 1 else 0
    obtain ⟨s, hs, hagree⟩ := hsrc L
    have hle : J s hs + 1 ≤ L := by
      have h1 : (if hs' : s < p then J s hs' + 1 else 0) ≤ L :=
        Finset.le_sup (f := fun s => if hs : s < p then J s hs + 1 else 0) (Finset.mem_range.2 hs)
      rw [dite_eq_left hs] at h1
      exact h1
    exact hJ s hs (hagree (J s hs) (by omega))
  refine ⟨s, p - s, by omega, fun t ht => ?_⟩
  have := hall (t - s)
  rw [show s + (t - s) = t by omega, show p + (t - s) = t + (p - s) by omega] at this
  exact this.symm

/-- **A `Bool` sequence is eventually periodic iff its Lempel–Ziv complexity is bounded.** -/
theorem eventuallyPeriodic_iff_lz_bounded (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ K, ∀ n, lzComplexity b n ≤ K :=
  ⟨lzComplexity_le_of_eventuallyPeriodic, fun ⟨_, hK⟩ => eventuallyPeriodic_of_lz_bounded hK⟩

/-- **Problem 1 ⟺ the Lempel–Ziv complexity of the prefixes of the center column is unbounded**. -/
theorem problem1_iff_lz_unbounded :
    Rule30Prize.Problem1 ↔ ∀ K, ∃ n, K < lzComplexity c n := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_lz_bounded]
  push Not
  rfl

end Rule30Equivalents.LempelZiv
