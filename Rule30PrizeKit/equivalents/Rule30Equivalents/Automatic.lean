module

public import Rule30Equivalents.OmegaRegular
public import Mathlib.Computability.DFA
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Set.Countable
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
# Automatic sequences and automatic complexity

An eventually periodic sequence is as simple as possible for finite automata in two senses.

* **Automatic complexity**. `AutComplexityLE x K` says that some DFA with `K` states
  accepts `x` and no other word of the same length (Shallit and Wang).
  `problem1_iff_automaticComplexity_tendsto_top`: **Problem 1 holds iff the automatic complexity of
  the prefixes of the center column tends to infinity.**
  - `autComplexityLE_of_eventuallyPeriodic`: with period `P` from `T`, every prefix has automatic
    complexity at most `T + P + 1`, through the lasso automaton with a dead state (`lassoDFA`).
  - `eventuallyPeriodic_of_frequently_autComplexityLE`: conversely, if one bound `K` holds for
    infinitely many prefixes, a single DFA uniquely accepts infinitely many of them (finitely many
    DFAs on `Fin K`). Some state `q` recurs along its run on `b`, at times `t₀ < t₁ < ⋯`. Swapping
    the loop `A = b[t₀, t₁)` with a later loop `B = b[t₁, s)` gives another accepted word of the same
    length, so `B ++ A = A ++ B`. Reading the first `|B|` letters, `b(t₀ + j) = b(t₁ + j)` for
    `j < |B|`, and `|B|` is unbounded: `b` has period `t₁ - t₀` from `t₀`. No Lyndon–Schützenberger
    theorem is needed.
* **k-automatic sequences**, one direction. `IsAutomatic k f` says that the k-kernel
  `{n ↦ f(kᵉ n + r) : r < kᵉ}` is finite (Eilenberg's criterion).
  `isAutomatic_of_eventuallyPeriodic`: an eventually periodic sequence is k-automatic for every
  `k ≥ 2`. So `problem1_of_not_automatic`: if the center column is not k-automatic for some `k ≥ 2`,
  Problem 1 holds; `problem1_of_not_two_three_automatic`: the same if it is not both 2- and
  3-automatic. The converse of the second is Cobham's theorem (1969).

Sources: J. Shallit and M.-w. Wang, *Automatic complexity of strings*, J. Autom. Lang. Comb. 6
(2001) 537–554; A. Cobham, *On the base-dependence of sets of numbers recognizable by finite
automata*, Math. Systems Theory 3 (1969) 186–192; S. Eilenberg, *Automata, Languages, and Machines*
A (1974).
-/

@[expose] public section

namespace Rule30Equivalents.Automatic

open Ruliology.CellularAutomata OmegaRegular

/-! ### k-automatic sequences -/

/-- The k-kernel of `f`: the subsequences `n ↦ f(kᵉ n + r)` with `r < kᵉ`. -/
def kernel (k : ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) :=
  {g | ∃ e r, r < k ^ e ∧ g = fun n => f (k ^ e * n + r)}

/-- `f` is k-automatic: its k-kernel is finite. -/
def IsAutomatic (k : ℕ) (f : ℕ → Bool) : Prop := (kernel k f).Finite

theorem self_mem_kernel (k : ℕ) (f : ℕ → Bool) : f ∈ kernel k f :=
  ⟨0, 0, by simp, by simp⟩

/-- The kernel is closed under `g ↦ (n ↦ g(kn + r))` for `r < k`. -/
theorem mem_kernel_step {k : ℕ} {f g : ℕ → Bool} (hg : g ∈ kernel k f) {r : ℕ} (hr : r < k) :
    (fun n => g (k * n + r)) ∈ kernel k f := by
  obtain ⟨e, s, hs, rfl⟩ := hg
  refine ⟨e + 1, k ^ e * r + s, ?_, funext fun n => ?_⟩
  · calc k ^ e * r + s < k ^ e * r + k ^ e := by omega
      _ = k ^ e * (r + 1) := (Nat.mul_succ _ _).symm
      _ ≤ k ^ e * k := Nat.mul_le_mul_left _ hr
      _ = k ^ (e + 1) := (pow_succ _ _).symm
  · show f (k ^ e * (k * n + r) + s) = f (k ^ (e + 1) * n + (k ^ e * r + s))
    rw [Nat.mul_add, ← Nat.mul_assoc, ← pow_succ]
    congr 1
    omega

/-- **`k`-automatic sequences are countably many**, for `k ≥ 2`: such a sequence is determined by
the automaton of its kernel. Number the kernel `g 0, …, g (N - 1)`, with `f = g i₀`; then
`g i (k n + r) = g (δ i r) n` and `g i 0 = o i`, and these determine every `g i n` by strong
induction, since `n = k ⌊n/k⌋ + n % k` with `⌊n/k⌋ < n` for `n ≥ 1`. -/
theorem countable_setOf_isAutomatic {k : ℕ} (hk : 2 ≤ k) :
    {f : ℕ → Bool | IsAutomatic k f}.Countable := by
  let S : (Σ N : ℕ, (Fin N → Fin k → Fin N) × (Fin N → Bool) × Fin N) → Set (ℕ → Bool) :=
    fun d => {f | ∃ g : Fin d.1 → ℕ → Bool,
      (∀ i (r : Fin k) n, g i (k * n + r) = g (d.2.1 i r) n) ∧ (∀ i, g i 0 = d.2.2.1 i) ∧
        g d.2.2.2 = f}
  have hS : ∀ d, (S d).Subsingleton := by
    rintro d f ⟨g, hg, hg0, rfl⟩ f' ⟨g', hg', hg0', rfl⟩
    have key : ∀ n i, g i n = g' i n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [hg0, hg0']
        · have hlt : n / k < n := Nat.div_lt_self hn (by omega)
          have hr : n % k < k := Nat.mod_lt n (by omega)
          have h1 := hg i ⟨n % k, hr⟩ (n / k)
          have h2 := hg' i ⟨n % k, hr⟩ (n / k)
          simp only at h1 h2
          calc g i n = g i (k * (n / k) + n % k) := by rw [Nat.div_add_mod]
            _ = g (d.2.1 i ⟨n % k, hr⟩) (n / k) := h1
            _ = g' (d.2.1 i ⟨n % k, hr⟩) (n / k) := ih _ hlt _
            _ = g' i (k * (n / k) + n % k) := h2.symm
            _ = g' i n := by rw [Nat.div_add_mod]
    funext n
    exact key n _
  refine (Set.countable_iUnion fun d => (hS d).countable).mono fun f hf => ?_
  -- number the kernel
  let K := Set.Finite.toFinset (s := kernel k f) hf
  let e := K.equivFin
  let g : Fin K.card → ℕ → Bool := fun i => (e.symm i : ℕ → Bool)
  have hg : ∀ i, g i ∈ kernel k f := fun i => (Set.Finite.mem_toFinset hf).1 (e.symm i).2
  let δ : Fin K.card → Fin k → Fin K.card := fun i r =>
    e ⟨fun n => g i (k * n + r), (Set.Finite.mem_toFinset hf).2 (mem_kernel_step (hg i) r.2)⟩
  refine Set.mem_iUnion.2 ⟨⟨K.card, δ, fun i => g i 0,
    e ⟨f, (Set.Finite.mem_toFinset hf).2 (self_mem_kernel k f)⟩⟩, g, fun i r n => ?_,
    fun i => rfl, ?_⟩
  · simp only [g, δ, Equiv.symm_apply_apply]
  · simp only [g, Equiv.symm_apply_apply]

/-- On the periodic part, the value depends only on the residue mod `P`. -/
theorem eq_of_mod_eq {b : ℕ → Bool} {T P : ℕ} (hper : ∀ t, T ≤ t → b (t + P) = b t)
    {m m' : ℕ} (hm : T ≤ m) (hm' : T ≤ m') (hmod : m % P = m' % P) : b m = b m' := by
  wlog hle : m ≤ m' generalizing m m'
  · exact (this hm' hm hmod.symm (by omega)).symm
  obtain ⟨k, hk⟩ : P ∣ m' - m := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
  rw [Nat.mul_comm] at hk
  rw [show m' = m + k * P by omega]
  exact (periodic_add_mul b T P hper hm k).symm

/-- **An eventually periodic sequence is k-automatic for every `k ≥ 2`.** -/
theorem isAutomatic_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) {k : ℕ}
    (hk : 2 ≤ k) : IsAutomatic k b := by
  obtain ⟨T, P, hP, hper⟩ := h
  let F : ℕ → Bool := fun j => b (j + T * P)
  have hF : ∀ m, T ≤ m → b m = F (m % P) := fun m hm =>
    eq_of_mod_eq hper hm (by have := Nat.le_mul_of_pos_right T hP; omega)
      (by rw [Nat.add_mul_mod_self_right, Nat.mod_mod])
  let Φ : Bool × Fin P × Fin P → ℕ → Bool := fun x n =>
    if n = 0 then x.1 else F ((x.2.1 * n + x.2.2) % P)
  refine (((Finset.range T ×ˢ Finset.range T : Finset (ℕ × ℕ)).finite_toSet.image
    fun er : ℕ × ℕ => fun n => b (k ^ er.1 * n + er.2)).union (Set.finite_range Φ)).subset ?_
  rintro g ⟨e, r, hr, rfl⟩
  by_cases hsmall : k ^ e ≤ T
  · left
    have he : e < T :=
      lt_of_lt_of_le (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hk e)) hsmall
    refine ⟨(e, r), ?_, rfl⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
    omega
  · right
    refine ⟨(b r, ⟨k ^ e % P, Nat.mod_lt _ hP⟩, ⟨r % P, Nat.mod_lt _ hP⟩), ?_⟩
    funext n
    simp only [Φ]
    split_ifs with hn
    · subst hn; simp
    · have hke : k ^ e ≤ k ^ e * n := Nat.le_mul_of_pos_right _ (by omega)
      rw [hF _ (by omega)]
      congr 1
      simp [Nat.add_mod, Nat.mul_mod]

/-- **A sufficient condition**: if the center column is not k-automatic for some
`k ≥ 2`, Problem 1 holds. -/
theorem problem1_of_not_automatic {k : ℕ} (hk : 2 ≤ k) (h : ¬ IsAutomatic k c) :
    Rule30Prize.Problem1 :=
  fun hep => h (isAutomatic_of_eventuallyPeriodic hep hk)

/-- **A sufficient condition**: if the center column is not both 2-automatic and
3-automatic, Problem 1 holds. The converse is Cobham's theorem. -/
theorem problem1_of_not_two_three_automatic
    (h : ¬ (IsAutomatic 2 Rule30Prize.center ∧ IsAutomatic 3 Rule30Prize.center)) :
    Rule30Prize.Problem1 :=
  fun hep => h ⟨isAutomatic_of_eventuallyPeriodic hep le_rfl,
    isAutomatic_of_eventuallyPeriodic hep (by norm_num)⟩

/-! ### Automatic complexity -/

/-- `M` accepts `x` and no other word of the same length. -/
def UniquelyAccepts {σ : Type} (M : DFA Bool σ) (x : List Bool) : Prop :=
  x ∈ M.accepts ∧ ∀ y : List Bool, y.length = x.length → y ∈ M.accepts → y = x

/-- The automatic complexity of `x` is at most `K`. -/
def AutComplexityLE (x : List Bool) (K : ℕ) : Prop :=
  ∃ M : DFA Bool (Fin K), UniquelyAccepts M x

section Lasso
variable (b : ℕ → Bool) (T P : ℕ) (hP : 0 < P)

/-- The prefix of length `n`. -/
def prefixOf (n : ℕ) : List Bool := (List.range n).map b

theorem prefixOf_succ (n : ℕ) : prefixOf b (n + 1) = prefixOf b n ++ [b n] := by
  simp [prefixOf, List.range_succ]

/-- The live state at the lasso position of time `n`. -/
def posState (n : ℕ) : Fin (T + P + 1) := ⟨pos T P n, by have := pos_lt T P hP n; omega⟩

/-- The lasso automaton with a dead state `T + P`, accepting at the lasso position of time `n`. -/
def lassoDFA (n : ℕ) : DFA Bool (Fin (T + P + 1)) where
  step s a := if h : (s : ℕ) < T + P then
      (if a = b s then ⟨succPos T P s, by have := succPos_lt T P hP s; omega⟩ else Fin.last _)
    else Fin.last _
  start := posState T P hP 0
  accept := {posState T P hP n}

theorem lassoDFA_step_pos (n m : ℕ) (a : Bool) :
    (lassoDFA b T P hP n).step (posState T P hP m) a =
      if a = b (pos T P m) then posState T P hP (m + 1) else Fin.last _ := by
  simp only [lassoDFA, posState, dite_eq_left (pos_lt T P hP m)]
  rfl

theorem lassoDFA_step_last (n : ℕ) (a : Bool) :
    (lassoDFA b T P hP n).step (Fin.last _) a = Fin.last _ := by
  simp [lassoDFA]

theorem lassoDFA_eval (hper : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) (y : List Bool) :
    (lassoDFA b T P hP n).eval y =
      if y = prefixOf b y.length then posState T P hP y.length else Fin.last _ := by
  induction y using List.reverseRecOn with
  | nil => simp [DFA.eval_nil, lassoDFA, prefixOf]
  | append_singleton z a ih =>
    rw [DFA.eval_append_singleton, ih, List.length_append, List.length_singleton, prefixOf_succ]
    by_cases hz : z = prefixOf b z.length
    · rw [ite_eq_left hz, lassoDFA_step_pos, b_pos b T P hP hper]
      by_cases ha : a = b z.length
      · rw [ite_eq_left ha, ite_eq_left (by rw [← hz, ha])]
      · rw [ite_eq_right ha, ite_eq_right (fun h => ha (by
          have := List.append_inj' h rfl; simpa using this.2))]
    · rw [ite_eq_right hz,
        ite_eq_right (show ¬ (z ++ [a] = prefixOf b z.length ++ [b z.length]) from
        fun h => hz (List.append_inj' h rfl).1), lassoDFA_step_last]

theorem lassoDFA_uniquelyAccepts (hper : ∀ t, T ≤ t → b (t + P) = b t) (n : ℕ) :
    UniquelyAccepts (lassoDFA b T P hP n) (prefixOf b n) := by
  have hlen : (prefixOf b n).length = n := by simp [prefixOf]
  refine ⟨?_, fun y hy hacc => ?_⟩
  · rw [DFA.mem_accepts, lassoDFA_eval b T P hP hper, hlen, ite_eq_left rfl]
    rfl
  · rw [hlen] at hy
    rw [DFA.mem_accepts, lassoDFA_eval b T P hP hper, hy] at hacc
    by_contra hne
    rw [ite_eq_right hne] at hacc
    have hlt := pos_lt T P hP n
    simp only [lassoDFA, posState, Set.mem_singleton_iff, Fin.ext_iff, Fin.val_last] at hacc
    omega

end Lasso

/-- **Eventually periodic sequences have prefixes of bounded automatic complexity.** -/
theorem autComplexityLE_of_eventuallyPeriodic {b : ℕ → Bool} (h : EventuallyPeriodic b) :
    ∃ K, ∀ n, AutComplexityLE ((List.range n).map b) K := by
  obtain ⟨T, P, hP, hper⟩ := h
  exact ⟨T + P + 1, fun n => ⟨lassoDFA b T P hP n, lassoDFA_uniquelyAccepts b T P hP hper n⟩⟩

/-- **A sufficient condition**: if the automatic complexity of the prefixes of the
center column tends to infinity, Problem 1 holds. -/
theorem problem1_of_automaticComplexity_tendsto_top
    (h : ∀ K : ℕ, ∀ᶠ n in Filter.atTop,
      ¬ AutComplexityLE ((List.range n).map Rule30Prize.center) K) :
    Rule30Prize.Problem1 := by
  intro hep
  obtain ⟨K, hK⟩ := autComplexityLE_of_eventuallyPeriodic hep
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h K)
  exact hN N le_rfl (hK N)

/-! ### The converse: bounded automatic complexity forces eventual periodicity -/

/-- The word `b(a), …, b(a + n - 1)`. -/
def seg (b : ℕ → Bool) (a n : ℕ) : List Bool := (List.range n).map fun i => b (a + i)

theorem seg_add (b : ℕ → Bool) (a m n : ℕ) : seg b a (m + n) = seg b a m ++ seg b (a + m) n := by
  simp only [seg, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1
  omega

theorem prefixOf_add (b : ℕ → Bool) (m n : ℕ) : prefixOf b (m + n) = prefixOf b m ++ seg b m n := by
  simp only [prefixOf, seg, List.range_add, List.map_append, List.map_map]
  rfl

theorem length_seg (b : ℕ → Bool) (a n : ℕ) : (seg b a n).length = n := by simp [seg]

theorem getD_seg (b : ℕ → Bool) (a n : ℕ) {j : ℕ} (hj : j < n) : (seg b a n).getD j false = b (a + j) := by
  simp [seg, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-- A DFA on `Fin K` is determined by finitely many data. -/
instance finite_dfa (K : ℕ) : Finite (DFA Bool (Fin K)) :=
  Finite.of_injective (fun M : DFA Bool (Fin K) => (M.step, M.start, M.accept)) fun M₁ M₂ h => by
    cases M₁; cases M₂; simp only [Prod.mk.injEq] at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl

/-- **Bounded automatic complexity forces eventual periodicity.** If some DFA with `K` states
uniquely accepts infinitely many prefixes of `b`, a state recurs along the run on `b`, and swapping
two loops at that state gives `B ++ A = A ++ B`; so `b` has period `|A|` from the first visit. -/
theorem eventuallyPeriodic_of_frequently_autComplexityLE {b : ℕ → Bool} {K : ℕ}
    (h : ∃ᶠ n in Filter.atTop, AutComplexityLE ((List.range n).map b) K) : EventuallyPeriodic b := by
  classical
  -- one DFA uniquely accepts infinitely many prefixes
  have hN : {n | AutComplexityLE (prefixOf b n) K}.Infinite :=
    Set.infinite_of_forall_exists_gt fun a => by
      obtain ⟨n, hn, hA⟩ := Filter.frequently_atTop.1 h (a + 1)
      exact ⟨n, hA, by omega⟩
  have := hN.to_subtype
  obtain ⟨D, hD⟩ := Finite.exists_infinite_fiber
    (fun n : {n | AutComplexityLE (prefixOf b n) K} => Classical.choose n.2)
  have hDinf : ((Subtype.val) '' ((fun n : {n | AutComplexityLE (prefixOf b n) K} =>
      Classical.choose n.2) ⁻¹' {D})).Infinite :=
    (Set.infinite_coe_iff.1 hD).image Subtype.val_injective.injOn
  have hgood : ∀ k, ∃ n, k ≤ n ∧ UniquelyAccepts D (prefixOf b n) := by
    intro k
    obtain ⟨n, ⟨m, hm, rfl⟩, hkn⟩ := hDinf.exists_gt k
    refine ⟨m, hkn.le, ?_⟩
    have := Classical.choose_spec m.2
    rw [show Classical.choose m.2 = D from hm] at this
    exact this
  -- a recurring state along the run on `b`
  let r : ℕ → Fin K := fun t => D.eval (prefixOf b t)
  obtain ⟨q, hq⟩ := Finite.exists_infinite_fiber r
  have hqinf : ∀ k, ∃ t, k ≤ t ∧ r t = q := by
    intro k
    obtain ⟨t, ht, hkt⟩ := (Set.infinite_coe_iff.1 hq).exists_gt k
    exact ⟨t, hkt.le, ht⟩
  obtain ⟨t₀, -, ht₀⟩ := hqinf 0
  obtain ⟨t₁, ht₁, ht₁q⟩ := hqinf (t₀ + 1)
  -- the run returns to `q` along each loop
  have hloop : ∀ u v, u ≤ v → r u = q → r v = q → D.evalFrom q (seg b u (v - u)) = q := by
    intro u v huv hu hv
    have e : prefixOf b v = prefixOf b u ++ seg b u (v - u) := by
      rw [← prefixOf_add, show u + (v - u) = v by omega]
    have := hv
    simp only [r, DFA.eval, e, DFA.evalFrom_of_append] at this
    simp only [r, DFA.eval] at hu
    rwa [hu] at this
  -- swapping the loop `A` with a later loop `B`
  have key : ∀ s, t₁ ≤ s → r s = q → ∀ j, j < s - t₁ → b (t₀ + j) = b (t₁ + j) := by
    intro s hs hsq j hj
    obtain ⟨n, hn, hU⟩ := hgood s
    set A := seg b t₀ (t₁ - t₀) with hAdef
    set B := seg b t₁ (s - t₁) with hBdef
    set R := seg b s (n - s) with hRdef
    have hpre : prefixOf b n = prefixOf b t₀ ++ (A ++ (B ++ R)) := by
      have e1 : prefixOf b n = prefixOf b s ++ R := by rw [← prefixOf_add, show s + (n - s) = n by omega]
      have e2 : prefixOf b s = prefixOf b t₁ ++ B := by rw [← prefixOf_add, show t₁ + (s - t₁) = s by omega]
      have e3 : prefixOf b t₁ = prefixOf b t₀ ++ A := by
        rw [← prefixOf_add, show t₀ + (t₁ - t₀) = t₁ by omega]
      rw [e1, e2, e3]
      simp only [List.append_assoc]
    have hA := hloop t₀ t₁ (by omega) ht₀ ht₁q
    have hB := hloop t₁ s hs ht₁q hsq
    have hstart : D.evalFrom D.start (prefixOf b t₀) = q := ht₀
    have hacc : prefixOf b t₀ ++ (B ++ (A ++ R)) ∈ D.accepts := by
      have h1 := hU.1
      rw [DFA.mem_accepts, DFA.eval, hpre] at h1
      rw [DFA.mem_accepts, DFA.eval]
      simp only [DFA.evalFrom_of_append, hstart] at h1 ⊢
      rw [hA] at h1
      rw [hB, hA]
      rwa [hB] at h1
    have hlen : (prefixOf b t₀ ++ (B ++ (A ++ R))).length = (prefixOf b n).length := by
      rw [hpre]; simp only [List.length_append]; omega
    have heq := hU.2 _ hlen hacc
    rw [hpre] at heq
    have hBA : B ++ A = A ++ B := by
      have h1 := List.append_cancel_left heq
      rw [← List.append_assoc, ← List.append_assoc] at h1
      exact List.append_cancel_right h1
    -- read the first `|B|` letters of both sides
    have hAB : A ++ B = seg b t₀ ((s - t₁) + (t₁ - t₀)) := by
      rw [hAdef, hBdef, show (s - t₁) + (t₁ - t₀) = (t₁ - t₀) + (s - t₁) by omega, seg_add,
        show t₀ + (t₁ - t₀) = t₁ by omega]
    have htake := congrArg (fun l => l.take (s - t₁)) hBA
    rw [List.take_left' (length_seg b t₁ (s - t₁)), hAB, seg_add,
      List.take_left' (length_seg b t₀ (s - t₁))] at htake
    have hget := congrArg (fun l => l.getD j false) htake
    rw [getD_seg b t₁ _ hj, getD_seg b t₀ _ hj] at hget
    exact hget.symm
  refine ⟨t₀, t₁ - t₀, by omega, fun t ht => ?_⟩
  obtain ⟨s, hs, hsq⟩ := hqinf (t + t₁ + 1)
  have := key s (by omega) hsq (t - t₀) (by omega)
  rw [show t₀ + (t - t₀) = t by omega, show t₁ + (t - t₀) = t + (t₁ - t₀) by omega] at this
  exact this.symm

/-- **Problem 1 ⟺ the automatic complexity of the prefixes of the center column tends to
infinity**. -/
theorem problem1_iff_automaticComplexity_tendsto_top : Rule30Prize.Problem1 ↔
    ∀ K : ℕ, ∀ᶠ n in Filter.atTop,
      ¬ AutComplexityLE ((List.range n).map Rule30Prize.center) K := by
  refine ⟨fun h K => ?_, problem1_of_automaticComplexity_tendsto_top⟩
  by_contra hK
  rw [Filter.not_eventually] at hK
  simp only [not_not] at hK
  exact h (eventuallyPeriodic_of_frequently_autComplexityLE hK)

end Rule30Equivalents.Automatic
