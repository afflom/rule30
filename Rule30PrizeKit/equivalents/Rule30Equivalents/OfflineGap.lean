module

public import Rule30Equivalents.OneTapeRegular
public import Rule30Equivalents.LogicAutomata
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Offline Turing machines: the `log log n` space gap

**Stearns, Hartmanis and Lewis** (1965): a deterministic
Turing machine with a read-only input tape and a work tape that decides a language in space
`o(log log n)` decides a regular language (`DecidesInSpace.isRegular`), for every input alphabet.
Conversely a finite automaton is such a machine that uses no work space, so a language is regular
iff some such machine decides it in space `o(log log n)`
(`isRegular_iff_exists_small_space_decider`).

* `OTM α`: finitely many states and work symbols, a two-way read-only input tape holding a word
  over `α` with blanks on both sides, and a two-way infinite work tape. `OTM.toMachine` is the same
  machine seen on its input tape, with the work configurations (state, work tape, work head) as
  states, so the crossing sequences and the splicing of `OneTapeGap` and `OneTapeRegular` apply.
* `DecidesInSpace M L s`: on every input `w` the machine halts, accepting iff `w ∈ L`, and its work
  head stays within `s |w|` cells of its start.
* Crossing sequences are short: the configurations right after two rightward crossings of one
  boundary differ, or the run would loop (`rs_nodup`), so a crossing sequence over `N` work
  configurations has length at most `2N + 1` (`length_cs_le_of_mem`).
* `space_lower_bound`: in a shortest input on which the work head goes beyond `K`, the boundaries
  on each side of the input head at that moment have distinct crossing sequences, or cutting out
  the word between two of them would give a shorter one. So `n ≤ 2 (N + 1)^(2N + 1)`, where
  `N ≤ C^(2 s(n) + 1)` counts the work configurations; space `o(log log n)` rules this out for
  large `K` (`bounded_space`).
* Bounded space leaves finitely many crossing sequences, so the language is regular by
  `OneTapeRegular.DecidesLang.isRegular_of_finite`.

For Rule 30: with unary input, **Problem 1 holds iff no such machine decides
`{1ⁿ : c(n) = 1}` in space `o(log log n)`** (`problem1_iff_no_small_space_decider`); with digit
input and Cobham's theorem, iff no such machines decide `c(n)` from the base-`2` and the base-`3`
digits of `n` (`problem1_iff_no_small_space_digit_deciders`).
-/

@[expose] public section

namespace Rule30Equivalents.OfflineGap

open Ruliology.CellularAutomata OneTapeGap OneTapeRegular

/-! ### Crossing sequences of machines that do not write -/

section ReadOnly

variable {M : Machine}

theorem halt_mono {X : ℕ → Cfg M} (hX : IsRun X) {s t : ℕ} (hs : M.halt (X s).q = true)
    (hst : s ≤ t) : M.halt (X t).q = true := by
  rw [eq_of_halt hX hs hst]; exact hs

/-- A run that comes back to an earlier configuration before halting never halts. -/
theorem not_halt_of_repeat {X : ℕ → Cfg M} (hX : IsRun X) {s p : ℕ} (hrep : X (s + p + 1) = X s)
    (hnh : M.halt (X (s + p)).q = false) (t : ℕ) : M.halt (X t).q = false := by
  have hper : ∀ j, X (s + p + 1 + j) = X (s + j) := by
    intro j
    induction j with
    | zero => simpa using hrep
    | succ j ih =>
      rw [show s + p + 1 + (j + 1) = s + p + 1 + j + 1 by ring,
        show s + (j + 1) = s + j + 1 by ring, hX, hX, ih]
  have key : ∀ t, s ≤ t → M.halt (X t).q = false := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro hst
      by_cases ht : t ≤ s + p
      · cases hh : M.halt (X t).q
        · rfl
        · rw [halt_mono hX hh ht] at hnh
          exact absurd hnh (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, t = s + p + 1 + j := ⟨t - (s + p + 1), by omega⟩
        rw [hper]
        exact ih (s + j) (by omega) (by omega)
  cases hh : M.halt (X t).q
  · rfl
  · have := key (max t s) (le_max_right _ _)
    rw [halt_mono hX hh (le_max_left _ _)] at this
    exact absurd this (by simp)

/-- The states just after the rightward crossings of `b` before time `T`. -/
def rs (X : ℕ → Cfg M) (b : ℤ) (T : ℕ) : List M.Q :=
  ((List.range T).filter fun t => decide (Cross X b t ∧ (X t).h < b)).map fun t => (X (t + 1)).q

theorem rs_succ (X : ℕ → Cfg M) (b : ℤ) (T : ℕ) :
    rs X b (T + 1) =
      rs X b T ++ (if Cross X b T ∧ (X T).h < b then [(X (T + 1)).q] else []) := by
  unfold rs
  rw [List.range_succ, List.filter_append, List.map_append]
  by_cases h : Cross X b T ∧ (X T).h < b
  · rw [ite_eq_left h]; simp [h.1, h.2]
  · rw [ite_eq_right h]; simp [h]

theorem mem_cs {X : ℕ → Cfg M} {b : ℤ} {T : ℕ} {x : M.Q} (hx : x ∈ cs X b T) :
    ∃ t, (X (t + 1)).q = x := by
  unfold cs at hx
  obtain ⟨t, -, h⟩ := List.mem_map.1 hx
  exact ⟨t, h⟩

/-- Crossings alternate in direction, so at most one more of them goes left than right. -/
theorem length_cs_add (X : ℕ → Cfg M) (b : ℤ) (T : ℕ) :
    (cs X b T).length + (if (X T).h < b then 0 else 1) =
      2 * (rs X b T).length + (if (X 0).h < b then 0 else 1) := by
  induction T with
  | zero => simp [cs_zero, rs]
  | succ T ih =>
    rw [cs_succ, rs_succ]
    by_cases hc : Cross X b T
    · by_cases hl : (X T).h < b
      · have hr : ¬ (X (T + 1)).h < b := fun h => hc (iff_of_true hl h)
        rw [ite_eq_left hc, ite_eq_left (show Cross X b T ∧ (X T).h < b from ⟨hc, hl⟩),
            ite_eq_right hr,
          List.length_append, List.length_append, List.length_singleton]
        rw [ite_eq_left hl] at ih
        omega
      · have hr : (X (T + 1)).h < b := by
          by_contra h
          exact hc (iff_of_false hl h)
        rw [ite_eq_left hc, ite_eq_right (show ¬ (Cross X b T ∧ (X T).h < b) from fun h => hl h.2),
            ite_eq_left hr,
          List.length_append, List.length_append, List.length_singleton, List.length_nil]
        rw [ite_eq_right hl] at ih
        omega
    · have hside : (X T).h < b ↔ (X (T + 1)).h < b := not_not.1 hc
      rw [ite_eq_right hc, ite_eq_right (show ¬ (Cross X b T ∧ (X T).h < b) from fun h => hc h.1),
        List.append_nil, List.append_nil]
      by_cases hl : (X T).h < b
      · rw [ite_eq_left (hside.1 hl)]; rw [ite_eq_left hl] at ih; exact ih
      · rw [ite_eq_right (fun h => hl (hside.2 h))]; rw [ite_eq_right hl] at ih; exact ih

/-- **No repetition.** In a halting run that never writes, the states after two rightward
crossings of one boundary differ: equal ones would give equal configurations, and the run would
loop. -/
theorem rs_nodup {X : ℕ → Cfg M} (hX : IsRun X) (htape : ∀ t, (X t).tape = (X 0).tape) {T : ℕ}
    (hT : M.halt (X T).q = true) (b : ℤ) (T' : ℕ) : (rs X b T').Nodup := by
  have key : ∀ u v, u < v → Cross X b u → (X u).h < b → Cross X b v → (X v).h < b →
      (X (u + 1)).q ≠ (X (v + 1)).q := by
    intro u v huv hcu hlu hcv hlv hq
    have hu := (cross_iff hX b u).1 hcu
    have hv := (cross_iff hX b v).1 hcv
    have hcfg : X (u + 1 + (v - u - 1) + 1) = X (u + 1) := by
      rw [show u + 1 + (v - u - 1) + 1 = v + 1 by omega]
      exact Cfg.ext' hq.symm (by omega) (by rw [htape (v + 1), htape (u + 1)])
    have hnh : M.halt (X (u + 1 + (v - u - 1))).q = false := by
      rw [show u + 1 + (v - u - 1) = v by omega]
      cases hh : M.halt (X v).q
      · rfl
      · exact absurd hcv (not_cross_of_halt hX hh le_rfl b)
    have := not_halt_of_repeat hX hcfg hnh T
    rw [hT] at this
    exact absurd this (by simp)
  unfold rs
  refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
  intro u hu v hv heq
  rw [List.mem_filter, decide_eq_true_iff] at hu hv
  rcases lt_trichotomy u v with h | h | h
  · exact absurd heq (key u v h hu.2.1 hu.2.2 hv.2.1 hv.2.2)
  · exact h
  · exact absurd heq.symm (key v u h hv.2.1 hv.2.2 hu.2.1 hu.2.2)

/-- A crossing sequence of a halting run that never writes, through states from a set `S`, has
length at most `2 |S| + 1`. -/
theorem length_cs_le_of_mem {X : ℕ → Cfg M} (hX : IsRun X) (htape : ∀ t, (X t).tape = (X 0).tape)
    {T : ℕ} (hT : M.halt (X T).q = true) (S : Finset M.Q) (hS : ∀ t, (X t).q ∈ S) (b : ℤ)
    (T' : ℕ) : (cs X b T').length ≤ 2 * S.card + 1 := by
  classical
  have h1 := length_cs_add X b T'
  have h2 : (rs X b T').length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup (rs_nodup hX htape hT b T')]
    apply Finset.card_le_card
    intro x hx
    rw [List.mem_toFinset] at hx
    unfold rs at hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact hS (t + 1)
  split_ifs at h1 <;> omega

end ReadOnly

/-! ### Counting lists -/

theorem eq_of_getElem?_eq {α : Type*} {L : ℕ} {l l' : List α} (hl : l.length ≤ L)
    (hl' : l'.length ≤ L) (he : (fun i : Fin L => l[(i : ℕ)]?) = fun i : Fin L => l'[(i : ℕ)]?) :
    l = l' := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L
  · exact congrFun he ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Distinct words of length at most `L` over a set `S`: at most `(|S| + 1)^L` of them. -/
theorem card_le_of_lists {α ι : Type*} {S : Finset α} {L : ℕ} {g : ι → List α} {B : Finset ι}
    (hg : Set.InjOn g B) (hS : ∀ b ∈ B, ∀ x ∈ g b, x ∈ S)
    (hL : ∀ b ∈ B, (g b).length ≤ L) : B.card ≤ (S.card + 1) ^ L := by
  classical
  have : B.card ≤ (Fintype.piFinset fun _ : Fin L => S.insertNone).card := by
    refine Finset.card_le_card_of_injOn (fun b i => (g b)[(i : ℕ)]?) ?_ ?_
    · intro b hb
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_insertNone] at hb ⊢
      intro i x hx
      exact hS b hb x (List.mem_of_getElem? hx)
    · intro b hb b' hb' he
      rw [Finset.mem_coe] at hb hb'
      exact hg hb hb' (eq_of_getElem?_eq (hL b hb) (hL b' hb') he)
  rwa [Fintype.card_piFinset_const, Finset.card_insertNone] at this

theorem finite_lists {α : Type*} (S : Finset α) (L : ℕ) :
    {l : List α | l.length ≤ L ∧ ∀ x ∈ l, x ∈ S}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun l (i : Fin L) => l[(i : ℕ)]?)
    ((Fintype.piFinset fun _ : Fin L => S.insertNone).finite_toSet.subset ?_) ?_
  · rintro _ ⟨l, ⟨hl, hS⟩, rfl⟩
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_insertNone]
    intro i x hx
    exact hS x (List.mem_of_getElem? hx)
  · intro l hl l' hl' he
    exact eq_of_getElem?_eq hl.1 hl'.1 he

/-! ### Offline machines -/

/-- A deterministic Turing machine with a two-way read-only input tape holding a word over `α`, and
one work tape, with finitely many states and work symbols. -/
structure OTM (α : Type) where
  /-- States. -/
  Q : Type
  [instFintype : Fintype Q]
  /-- Work tape symbols. -/
  Γ : Type
  [instFintypeΓ : Fintype Γ]
  /-- The blank work symbol. -/
  blank : Γ
  /-- The start state. -/
  start : Q
  /-- Halting states. -/
  halt : Q → Bool
  /-- Accepting states. -/
  accept : Q → Bool
  /-- From the state, the input symbol (`none` for a blank) and the work symbol: the new state,
  the written work symbol, the move of the input head and the move of the work head. -/
  δ : Q → Option α → Γ → Q × Γ × Move × Move

attribute [instance] OTM.instFintype OTM.instFintypeΓ

namespace OTM

variable {α : Type} (M : OTM α)

/-- The machine on the input tape whose states are the work configurations (state, work tape,
work head). It writes back the symbol it reads. Its inputs are words, written with `some`
(`OneTapeGap.runW`), so its unary input symbol `one` is not used. -/
def toMachine : Machine where
  Q := M.Q × (ℤ → M.Γ) × ℤ
  Γ := Option α
  blank := none
  one := none
  start := (M.start, fun _ => M.blank, 0)
  halt w := M.halt w.1
  accept w := M.accept w.1
  δ w x := (((M.δ w.1 x (w.2.1 w.2.2)).1,
      Function.update w.2.1 w.2.2 (M.δ w.1 x (w.2.1 w.2.2)).2.1,
      w.2.2 + (M.δ w.1 x (w.2.1 w.2.2)).2.2.2.shift), x, (M.δ w.1 x (w.2.1 w.2.2)).2.2.1)

/-- `M` decides `L` in space `s`: on every input `w` it halts, accepting iff `w ∈ L`, and its
work head stays within `s |w|` cells of its start. -/
def DecidesInSpace (L : Language α) (s : ℕ → ℕ) : Prop :=
  (∃ T, DecidesLang M.toMachine some L T) ∧
    ∀ (w : List α) t, -(s w.length : ℤ) ≤ (runW M.toMachine some w t).q.2.2 ∧
      (runW M.toMachine some w t).q.2.2 ≤ s w.length

/-- The input tape never changes. -/
theorem tape_run (w : List α) (t : ℕ) :
    (runW M.toMachine some w t).tape = (initW M.toMachine some w).tape := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [isRun_runW (M := M.toMachine) some w t, ← ih]
    unfold step
    split_ifs
    · rfl
    · exact Function.update_eq_self _ _

/-- Under a space bound `K`, the work tape stays blank beyond `K`. -/
theorem work_blank {w : List α} {K : ℕ}
    (hK : ∀ t, -(K : ℤ) ≤ (runW M.toMachine some w t).q.2.2 ∧
      (runW M.toMachine some w t).q.2.2 ≤ K)
    (t : ℕ) (i : ℤ) (hi : i < -K ∨ K < i) : (runW M.toMachine some w t).q.2.1 i = M.blank := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [isRun_runW (M := M.toMachine) some w t]
    unfold step
    split_ifs
    · exact ih
    · have := hK t
      show Function.update _ _ _ i = _
      rw [Function.update_of_ne (by omega)]
      exact ih

/-- The work configurations within `K` cells of the start, blank beyond them. -/
noncomputable def cfgs (K : ℕ) : Finset M.toMachine.Q := by
  classical exact
    (Finset.univ : Finset (M.Q × (Fin (2 * K + 1) → M.Γ) × Fin (2 * K + 1))).image fun x =>
      (x.1, fun i => if h : -(K : ℤ) ≤ i ∧ i ≤ K then x.2.1 ⟨(i + K).toNat, by omega⟩ else M.blank,
        (x.2.2 : ℤ) - K)

theorem card_cfgs (K : ℕ) :
    (M.cfgs K).card ≤ Fintype.card M.Q * Fintype.card M.Γ ^ (2 * K + 1) * (2 * K + 1) := by
  classical
  unfold cfgs
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, Fintype.card_prod, mul_assoc]

theorem mem_cfgs {K : ℕ} {w : M.toMachine.Q} (hh : -(K : ℤ) ≤ w.2.2 ∧ w.2.2 ≤ K)
    (hw : ∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → w.2.1 i = M.blank) : w ∈ M.cfgs K := by
  classical
  obtain ⟨q, wt, wh⟩ := w
  unfold cfgs
  refine Finset.mem_image.2 ?_
  refine ⟨(q, fun j => wt ((j : ℤ) - K), ⟨(wh + K).toNat, by simp only at hh; omega⟩),
    Finset.mem_univ _, ?_⟩
  simp only at hh hw
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) ?_)
  · show (if h : -(K : ℤ) ≤ i ∧ i ≤ K then _ else _) = _
    split_ifs with h
    · show wt ((((i + K).toNat : ℕ) : ℤ) - K) = wt i
      congr 1
      omega
    · exact (hw i (by omega)).symm
  · show ((((wh + K).toNat : ℕ) : ℤ) - K) = wh
    omega

/-- The work head stays within `K` cells of its start on the input `w`. -/
def SpaceLE (w : List α) (K : ℕ) : Prop :=
  ∀ t, -(K : ℤ) ≤ (runW M.toMachine some w t).q.2.2 ∧ (runW M.toMachine some w t).q.2.2 ≤ K

variable {M}

theorem mem_cfgs_run {w : List α} {K : ℕ} (h : M.SpaceLE w K) (t : ℕ) :
    (runW M.toMachine some w t).q ∈ M.cfgs K :=
  M.mem_cfgs (h t) fun i hi => M.work_blank h t i hi

theorem length_cs_run_le {L : Language α} {T : ℕ → ℕ} (hT : DecidesLang M.toMachine some L T)
    {w : List α} {K : ℕ} (h : M.SpaceLE w K) (b : ℤ) (T' : ℕ) :
    (cs (runW M.toMachine some w) b T').length ≤ 2 * (M.cfgs K).card + 1 :=
  length_cs_le_of_mem (isRun_runW (M := M.toMachine) some w)
    (fun t => (M.tape_run w t).trans (M.tape_run w 0).symm)
    (hT w).1 _ (M.mem_cfgs_run h) b T'

/-- **The space bound.** Let `w` be a shortest input on which the work head goes beyond `K`. At
that moment the input head is at some cell `x₀`; cutting out the part of `w` between two
boundaries on the same side of `x₀` with equal crossing sequences would give a shorter such input.
So the boundaries `1, …, |w|` have distinct crossing sequences on each side of `x₀`, and there are
at most `(N + 1)^(2N + 1)` of those, for `N` the number of work configurations within `s |w|`. -/
theorem space_lower_bound {L : Language α} {T : ℕ → ℕ} (hT : DecidesLang M.toMachine some L T)
    {s : ℕ → ℕ} (hs : ∀ w : List α, M.SpaceLE w (s w.length)) {K : ℕ} {w : List α}
    (hmin : ∀ w' : List α, w'.length < w.length → M.SpaceLE w' K) (hbig : ¬ M.SpaceLE w K) :
    w.length ≤ 2 * ((M.cfgs (s w.length)).card + 1) ^ (2 * (M.cfgs (s w.length)).card + 1) := by
  classical
  set n := w.length with hn
  -- the moment the work head is beyond `K`, taken before halting
  obtain ⟨t₀, ht₀, hbig₀⟩ : ∃ t₀, t₀ ≤ T n ∧
      ¬ (-(K : ℤ) ≤ (runW M.toMachine some w t₀).q.2.2 ∧
        (runW M.toMachine some w t₀).q.2.2 ≤ K) := by
    obtain ⟨t, ht⟩ := not_forall.1 hbig
    rcases le_total t (T n) with h | h
    · exact ⟨t, h, ht⟩
    · exact ⟨T n, le_rfl, by rwa [← eq_of_halt (isRun_runW (M := M.toMachine) some w) (hT w).1 h]⟩
  set x₀ := (runW M.toMachine some w t₀).h
  set g : ℕ → List M.toMachine.Q := fun b => cs (runW M.toMachine some w) (b : ℤ) (T n)
  have hdist : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ((j : ℤ) ≤ x₀ ∨ x₀ < i) → g i ≠ g j := by
    intro i j hi hij hjn hside hC
    have hu : (w.take i).length = i := by rw [List.length_take]; omega
    have hu' : (w.take j).length = j := by rw [List.length_take]; omega
    have hw1 : w.take i ++ w.drop i = w := List.take_append_drop i w
    have hw2 : w.take j ++ w.drop j = w := List.take_append_drop j w
    have hv := hT.splice_visit (u := w.take i) (v := w.drop i) (u' := w.take j) (v' := w.drop j)
      (by omega) (by omega) (by rw [hw1, hw2, hu, hu']; exact hC)
    rw [hw1, hw2, hu, hu'] at hv
    obtain ⟨σ, hσ⟩ : ∃ σ, (runW M.toMachine some (w.take i ++ w.drop j) σ).q =
        (runW M.toMachine some w t₀).q := by
      rcases hside with h | h
      · exact hv.2 t₀ ht₀ h
      · exact hv.1 t₀ ht₀ h
    have hlen : (w.take i ++ w.drop j).length < w.length := by
      rw [List.length_append, hu, List.length_drop]
      omega
    have := hmin _ hlen σ
    rw [hσ] at this
    exact hbig₀ this
  set BL := (Finset.Icc 1 n).filter fun b : ℕ => (b : ℤ) ≤ x₀
  set BR := (Finset.Icc 1 n).filter fun b : ℕ => x₀ < (b : ℤ)
  have hinjL : Set.InjOn g BL := by
    intro i hi j hj he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist i j hi.1.1 h hj.1.2 (Or.inl hj.2) he
    · exact hdist j i hj.1.1 h hi.1.2 (Or.inl hi.2) he.symm
  have hinjR : Set.InjOn g BR := by
    intro i hi j hj he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist i j hi.1.1 h hj.1.2 (Or.inr hi.2) he
    · exact hdist j i hj.1.1 h hi.1.2 (Or.inr hj.2) he.symm
  have hcard : n ≤ BL.card + BR.card := by
    have hsub : Finset.Icc 1 n ⊆ BL ∪ BR := by
      intro b hb
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases le_or_gt (b : ℤ) x₀ with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le BL BR)
    simpa using this
  obtain ⟨B, hB, hinj⟩ : ∃ B : Finset ℕ, n ≤ 2 * B.card ∧ Set.InjOn g B := by
    rcases le_total BR.card BL.card with h | h
    · exact ⟨BL, by omega, hinjL⟩
    · exact ⟨BR, by omega, hinjR⟩
  have hle := card_le_of_lists (S := M.cfgs (s n)) (L := 2 * (M.cfgs (s n)).card + 1) hinj
    (fun b _ x hx => by
      obtain ⟨t, rfl⟩ := mem_cs hx
      exact M.mem_cfgs_run (hs w) _)
    (fun b _ => length_cs_run_le hT (hs w) _ _)
  omega

/-- The arithmetic at the end of the space argument: `n ≤ 2 (N + 1)^(2N + 1)` with
`N ≤ C^(2s + 1)` gives `log log n ≤ 4 (s + 1) log C`. -/
theorem loglog_bound {C N n s : ℕ} (hC : 2 ≤ C) (hN : N ≤ C ^ (2 * s + 1)) (hN1 : 1 ≤ N)
    (hn : n ≤ 2 * (N + 1) ^ (2 * N + 1)) (hn1 : 2 ≤ n) :
    Real.log (Real.log n) ≤ 4 * ((s : ℝ) + 1) * Real.log C := by
  have h1 : (N + 1) ^ (2 * N + 1) ≤ 2 ^ (N * (2 * N + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self _
  have h2 : N * (2 * N + 1) + 1 ≤ 4 * N ^ 2 := by nlinarith
  have h3 : 4 * N ^ 2 ≤ C ^ (4 * s + 4) := by
    have : N ^ 2 ≤ C ^ (4 * s + 2) := by
      calc N ^ 2 ≤ (C ^ (2 * s + 1)) ^ 2 := Nat.pow_le_pow_left hN 2
        _ = C ^ (4 * s + 2) := by rw [← pow_mul]; ring_nf
    calc 4 * N ^ 2 ≤ C ^ 2 * C ^ (4 * s + 2) := Nat.mul_le_mul (by nlinarith) this
      _ = C ^ (4 * s + 4) := by rw [← pow_add]; ring_nf
  have h4 : n ≤ 2 ^ (C ^ (4 * s + 4)) := by
    calc n ≤ 2 * (N + 1) ^ (2 * N + 1) := hn
      _ ≤ 2 * 2 ^ (N * (2 * N + 1)) := Nat.mul_le_mul_left 2 h1
      _ = 2 ^ (N * (2 * N + 1) + 1) := by ring
      _ ≤ 2 ^ (C ^ (4 * s + 4)) := Nat.pow_le_pow_right (by norm_num) (h2.trans h3)
  have hnpos : (1 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 < Real.log n := Real.log_pos hnpos
  have hCpos : (0 : ℝ) < C := by positivity
  have h5 : Real.log n ≤ (C : ℝ) ^ (4 * s + 4) * Real.log 2 := by
    have := Real.log_le_log (by positivity)
      (show (n : ℝ) ≤ (2 : ℝ) ^ (C ^ (4 * s + 4)) by exact_mod_cast h4)
    rwa [Real.log_pow, Nat.cast_pow] at this
  have h6 : Real.log n ≤ (C : ℝ) ^ (4 * s + 4) := by
    have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    nlinarith [pow_pos hCpos (4 * s + 4)]
  calc Real.log (Real.log n) ≤ Real.log ((C : ℝ) ^ (4 * s + 4)) := Real.log_le_log hlogn h6
    _ = ((4 * s + 4 : ℕ) : ℝ) * Real.log C := by rw [Real.log_pow]
    _ = 4 * ((s : ℝ) + 1) * Real.log C := by push_cast; ring

/-- **Space `o(log log n)` is bounded.** -/
theorem bounded_space {L : Language α} {T : ℕ → ℕ} (hT : DecidesLang M.toMachine some L T)
    {s : ℕ → ℕ} (hs : ∀ w : List α, M.SpaceLE w (s w.length))
    (hlo : (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n))) :
    ∃ K, ∀ w, M.SpaceLE w K := by
  classical
  by_contra hne
  push Not at hne
  set C := 2 * Fintype.card M.Q * Fintype.card M.Γ
  have hq : 1 ≤ Fintype.card M.Q := Fintype.card_pos_iff.2 ⟨M.start⟩
  have hg : 1 ≤ Fintype.card M.Γ := Fintype.card_pos_iff.2 ⟨M.blank⟩
  have hC : 2 ≤ C := by
    have := Nat.mul_le_mul hq hg
    simp only [C]
    nlinarith
  have hlogC : 0 < Real.log C := Real.log_pos (by exact_mod_cast hC)
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.1 (hlo.def (show (0 : ℝ) < 1 / (8 * Real.log C) by positivity))
  set N := max N₀ (4 ^ (C ^ 8))
  set K := ∑ n ∈ Finset.range N, s n
  -- a shortest input on which the work head goes beyond `K`
  have hex : ∃ n, ∃ w : List α, w.length = n ∧ ¬ M.SpaceLE w K := by
    obtain ⟨w, hw⟩ := hne K
    exact ⟨w.length, w, rfl, hw⟩
  obtain ⟨w, hwn, hbig⟩ := Nat.find_spec hex
  have hmin : ∀ w' : List α, w'.length < w.length → M.SpaceLE w' K := fun w' hw' => by
    by_contra hc
    exact Nat.find_min hex (by omega) ⟨w', rfl, hc⟩
  set n := w.length with hn
  have hnN : N ≤ n := by
    by_contra h
    push Not at h
    apply hbig
    intro t
    have h1 := hs w t
    rw [← hn] at h1
    have h2 : s n ≤ K :=
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 h)
    have h3 : (s n : ℤ) ≤ K := by exact_mod_cast h2
    omega
  have h4n : 4 ^ (C ^ 8) ≤ n := le_trans (le_max_right _ _) hnN
  have hn2 : 2 ≤ n := le_trans (Nat.one_lt_pow (by positivity) (by norm_num)) h4n
  -- the counting bound and its logarithm
  have hcard : (M.cfgs (s n)).card ≤ C ^ (2 * s n + 1) := by
    refine (M.card_cfgs _).trans ?_
    have h1 : Fintype.card M.Q ≤ Fintype.card M.Q ^ (2 * s n + 1) := Nat.le_self_pow (by omega) _
    have h2 : 2 * s n + 1 ≤ 2 ^ (2 * s n + 1) := Nat.lt_two_pow_self.le
    calc Fintype.card M.Q * Fintype.card M.Γ ^ (2 * s n + 1) * (2 * s n + 1)
        ≤ Fintype.card M.Q ^ (2 * s n + 1) * Fintype.card M.Γ ^ (2 * s n + 1) *
            2 ^ (2 * s n + 1) := by gcongr
      _ = C ^ (2 * s n + 1) := by simp only [C, mul_pow]; ring
  have hN1 : 1 ≤ (M.cfgs (s n)).card := Finset.card_pos.2 ⟨_, M.mem_cfgs_run (hs w) 0⟩
  have e1 := loglog_bound hC hcard hN1 (space_lower_bound hT hs hmin hbig) hn2
  -- `s n ≤ log log n / (8 log C)`
  have hlog1 : 1 ≤ Real.log n := by
    have h4 : (4 : ℝ) ^ (C ^ 8) ≤ n := by exact_mod_cast h4n
    have h5 : Real.log ((4 : ℝ) ^ (C ^ 8)) ≤ Real.log n := Real.log_le_log (by positivity) h4
    rw [Real.log_pow] at h5
    have h6 : (1 : ℝ) ≤ ((C ^ 8 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    have h7 : 1 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    nlinarith
  have hloglog : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog1
  have e2 : (s n : ℝ) ≤ 1 / (8 * Real.log C) * Real.log (Real.log n) := by
    have := hN₀ n (le_trans (le_max_left _ _) hnN)
    simp only [Real.norm_eq_abs] at this
    rwa [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hloglog] at this
  -- and `log log n > 8 log C`
  have e3 : 8 * Real.log C < Real.log (Real.log n) := by
    have h4 : (4 : ℝ) ^ (C ^ 8) ≤ n := by exact_mod_cast h4n
    have h5 : Real.log ((4 : ℝ) ^ (C ^ 8)) ≤ Real.log n := Real.log_le_log (by positivity) h4
    rw [Real.log_pow] at h5
    have h7 : 1 < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    have hC8 : (0 : ℝ) < ((C ^ 8 : ℕ) : ℝ) := by positivity
    have h8 : ((C ^ 8 : ℕ) : ℝ) < Real.log n := by nlinarith
    have h9 := Real.log_lt_log hC8 h8
    rwa [Nat.cast_pow, Real.log_pow] at h9
  have e4 : 4 * ((s n : ℝ) + 1) * Real.log C ≤ Real.log (Real.log n) / 2 + 4 * Real.log C := by
    have : 4 * (s n : ℝ) * Real.log C ≤ Real.log (Real.log n) / 2 := by
      calc 4 * (s n : ℝ) * Real.log C
          ≤ 4 * (1 / (8 * Real.log C) * Real.log (Real.log n)) * Real.log C := by gcongr
        _ = Real.log (Real.log n) / 2 := by field_simp; ring
    linarith
  linarith

/-- **The theorem of Stearns, Hartmanis and Lewis.** An offline machine that decides `L` in space
`o(log log n)` uses bounded space, so it has finitely many crossing sequences and `L` is
regular. -/
theorem DecidesInSpace.isRegular {L : Language α} {s : ℕ → ℕ} (hM : M.DecidesInSpace L s)
    (hlo : (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n))) :
    L.IsRegular := by
  obtain ⟨⟨T, hT⟩, hs⟩ := hM
  obtain ⟨K, hK⟩ := bounded_space hT hs hlo
  refine hT.isRegular_of_finite
    ((finite_lists (M.cfgs K) (2 * (M.cfgs K).card + 1)).subset ?_)
  rintro _ ⟨w, b, rfl⟩
  refine ⟨length_cs_run_le hT (hK w) b _, fun x hx => ?_⟩
  obtain ⟨t, rfl⟩ := mem_cs hx
  exact M.mem_cfgs_run (hK w) _

end OTM

/-! ### A finite automaton is an offline machine without work space -/

section DFA

variable {α σ : Type} [Fintype σ] (D : DFA α σ)

/-- The offline machine of a finite automaton: it reads the input left to right, and at the first
blank halts with the answer. It never moves its work head. -/
noncomputable def dfaOTM : OTM α where
  Q := σ ⊕ Bool
  Γ := Unit
  blank := ()
  start := Sum.inl D.start
  halt := Sum.isRight
  accept := Sum.elim (fun _ => false) id
  δ := fun s x _ => match s, x with
    | Sum.inl g, some a => (Sum.inl (D.step g a), (), Move.right, Move.stay)
    | Sum.inl g, none =>
      (Sum.inr (@decide (g ∈ D.accept) (Classical.dec _)), (), Move.right, Move.stay)
    | Sum.inr b, _ => (Sum.inr b, (), Move.stay, Move.stay)

theorem runW_dfaOTM (w : List α) {t : ℕ} (ht : t ≤ w.length) :
    runW (dfaOTM D).toMachine some w t =
      ⟨(Sum.inl (D.evalFrom D.start (w.take t)), fun _ => (), 0), t,
        (initW (dfaOTM D).toMachine some w).tape⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [(isRun_runW (M := (dfaOTM D).toMachine) some w) t, ih (by omega), step_eq rfl]
    have htape : (initW (dfaOTM D).toMachine some w).tape (t : ℤ) = some (w[t]'(by omega)) := by
      simp only [initW]
      erw [dite_eq_left (by omega)]
      simp only [Int.toNat_natCast]; rfl
    refine Cfg.ext' ?_ ?_ ?_
    · dsimp only
      rw [htape]
      show ((Sum.inl _, _, _) : _ × _ × _) = _
      refine Prod.ext ?_ (Prod.ext (funext fun _ => rfl) rfl)
      show Sum.inl _ = Sum.inl _
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        DFA.evalFrom_append_singleton]
    · dsimp only
      rw [htape]
      push_cast
      rfl
    · dsimp only
      rw [htape]
      exact Function.update_eq_self_iff.2 htape.symm

theorem runW_dfaOTM_succ (w : List α) :
    (runW (dfaOTM D).toMachine some w (w.length + 1)).q =
      (Sum.inr (@decide (D.evalFrom D.start w ∈ D.accept) (Classical.dec _)), fun _ => (), 0) := by
  rw [(isRun_runW (M := (dfaOTM D).toMachine) some w) w.length, runW_dfaOTM D w le_rfl,
    step_eq rfl]
  have htape : (initW (dfaOTM D).toMachine some w).tape (w.length : ℤ) = none := by
    simp only [initW]
    erw [dite_eq_right (by omega)]
    rfl
  dsimp only
  rw [htape]
  show ((Sum.inr _, _, _) : _ × _ × _) = _
  rw [List.take_length]
  exact Prod.ext rfl (Prod.ext (funext fun _ => rfl) rfl)

/-- **A finite automaton decides its language without work space.** -/
theorem decidesInSpace_dfaOTM : (dfaOTM D).DecidesInSpace D.accepts fun _ => 0 := by
  have hhalt : ∀ w : List α, (dfaOTM D).toMachine.halt
      (runW (dfaOTM D).toMachine some w (w.length + 1)).q = true := fun w => by
    rw [runW_dfaOTM_succ]; rfl
  refine ⟨⟨(· + 1), fun w => ⟨hhalt w, ?_⟩⟩, fun w t => ?_⟩
  · rw [runW_dfaOTM_succ, DFA.mem_accepts]
    exact ⟨@of_decide_eq_true _ (Classical.dec _), @decide_eq_true _ (Classical.dec _)⟩
  · have h0 : (runW (dfaOTM D).toMachine some w t).q.2.2 = 0 := by
      rcases le_or_gt t w.length with h | h
      · rw [runW_dfaOTM D w h]
      · rw [eq_of_halt (isRun_runW (M := (dfaOTM D).toMachine) some w) (hhalt w)
          (by omega : w.length + 1 ≤ t),
          runW_dfaOTM_succ]
    rw [h0]
    simp

end DFA

/-! ### Problem 1 in small space -/

/-- **Regular ⟺ decided in space `o(log log n)`** by an offline machine (Stearns, Hartmanis and
Lewis; the converse uses no work space). -/
theorem isRegular_iff_exists_small_space_decider {α : Type} (L : Language α) :
    L.IsRegular ↔ ∃ (M : OTM α) (s : ℕ → ℕ),
      (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n)) ∧
      M.DecidesInSpace L s := by
  constructor
  · rintro ⟨σ, _, D, rfl⟩
    exact ⟨dfaOTM D, fun _ => 0, by simp, decidesInSpace_dfaOTM D⟩
  · rintro ⟨M, s, hs, hM⟩
    exact hM.isRegular hs

/-- For unary input: a sequence is eventually periodic iff an offline machine decides
`{1ⁿ : f(n) = 1}` in space `o(log log n)`. -/
theorem eventuallyPeriodic_iff_exists_small_space_decider (f : ℕ → Bool) :
    EventuallyPeriodic f ↔ ∃ (M : OTM Unit) (s : ℕ → ℕ),
      (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n)) ∧
      M.DecidesInSpace (LogicAutomata.unaryLang f) s := by
  rw [LogicAutomata.eventuallyPeriodic_iff_unary_isRegular,
    isRegular_iff_exists_small_space_decider]

/-- **Small space.** Problem 1 holds iff no deterministic Turing machine with a read-only input
tape decides `L₁ = {1ⁿ : c(n) = 1}` in space `o(log log n)`. -/
theorem problem1_iff_no_small_space_decider : Rule30Prize.Problem1 ↔
    ¬ ∃ (M : OTM Unit) (s : ℕ → ℕ),
      (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n)) ∧
      M.DecidesInSpace (LogicAutomata.unaryLang c) s := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_small_space_decider]

/-- **Small space, digit input.** Problem 1 holds iff no offline machines decide `c(n)`
from the base-`2` and from the base-`3` digits of `n` (least significant first) in space
`o(log log ℓ)`, where `ℓ` is the number of digits. -/
theorem problem1_iff_no_small_space_digit_deciders : Rule30Prize.Problem1 ↔
    ¬ ((∃ (M : OTM (Fin 2)) (s : ℕ → ℕ),
        (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n)) ∧
          M.DecidesInSpace (digitLang 2 c) s) ∧
      (∃ (M : OTM (Fin 3)) (s : ℕ → ℕ),
        (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => Real.log (Real.log n)) ∧
          M.DecidesInSpace (digitLang 3 c) s)) := by
  rw [Cobham.problem1_iff_not_two_three_automatic, ← isRegular_digitLang_iff le_rfl,
    ← isRegular_digitLang_iff (by norm_num), isRegular_iff_exists_small_space_decider,
    isRegular_iff_exists_small_space_decider]

end Rule30Equivalents.OfflineGap
