module

public import Rule30Equivalents.Basic
public import Ruliology.CellularAutomata.Rule30FiniteConfigs
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The right halves of rule 30 have infinitely many limit points

Theorems 4.6 and 4.7 of J. Kopra, *Rapid left expansivity, a commonality between Wolfram's
Rule 30 and powers of p/q*, for rule 30. Read the cells `p ≥ 0` of
row `t` as a point of `{0,1}^ℕ`, the right half of the row. Then:

* `exists_periodic_window` (Kopra's Theorem 4.6, for radius-1 automata): if the right halves have
  finitely many limit points, then for every `w` some window of `w + 1` adjacent columns is
  eventually periodic. The windows that occur infinitely often number at most the limit points
  (a limit point extends each of them, by compactness of `{0,1}^ℕ`), and they do not get fewer
  when the window grows. Along `k + 1` nested windows, each two cells narrower than the last, the
  count cannot drop `k` times; where it does not drop, the window at the next time is determined
  by the narrower window, which the local rule computes from the window now. So the window is
  eventually periodic.
* `infinite_limitPoints_cell`, `infinite_limitPoints_evol` (Kopra's Theorem 4.7 for rule 30):
  from the single black cell, and from every configuration with a leftmost black cell, the right
  halves have infinitely many limit points. Otherwise two adjacent columns would be eventually
  periodic, which Jen's theorem rules out.
* `half_cell_eq_zero_iff` (Kopra's Theorem 4.5 for the single black cell): the right half returns
  to that of the seed only at time `0`, since the right edge carries a black cell at `t`. For
  every configuration with a leftmost black cell, including those infinite to the right, it is
  `RightHalfReturns.finite_returns`.

In terms of `y_t = Σ_{p ≥ 0} cell(t, p) 2^-(p+1)`, this is the rule-30 analogue of the theorem of
Pisot and Vijayaraghavan that `(p/q)ⁿ mod 1` has infinitely many limit points. It neither implies
nor follows from Problem 1.
-/

@[expose] public section

namespace Rule30Equivalents.LimitPoints

open Filter Topology Ruliology.CellularAutomata

variable {X : ℕ → ℤ → Bool}

/-- The window of `n` cells starting at cell `i`, at time `t`. -/
def win (X : ℕ → ℤ → Bool) (t i n : ℕ) : Fin n → Bool := fun m => X t ((i : ℤ) + (m : ℕ))

/-- The windows of `n` cells at `i` that occur at infinitely many times. -/
def W (X : ℕ → ℤ → Bool) (i n : ℕ) : Set (Fin n → Bool) := {u | ∃ᶠ t in atTop, win X t i n = u}

/-- The right half of row `t`: its cells `p ≥ 0`. -/
def half (X : ℕ → ℤ → Bool) (t : ℕ) : ℕ → Bool := fun p => X t p

/-- The limit points of the right halves. -/
def limitPoints (X : ℕ → ℤ → Bool) : Set (ℕ → Bool) := {y | MapClusterPt y atTop (half X)}

theorem W_nonempty (i n : ℕ) : (W X i n).Nonempty := by
  obtain ⟨u, hu⟩ := Finite.exists_infinite_fiber fun t => win X t i n
  exact ⟨u, Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 hu)⟩

/-- A word that occurs infinitely often extends to a limit point. -/
theorem exists_limitPoint {i n : ℕ} {u : Fin n → Bool} (hu : u ∈ W X i n) :
    ∃ y ∈ limitPoints X, ∀ m : Fin n, y (i + m) = u m := by
  have : NeBot (atTop ⊓ 𝓟 {t | win X t i n = u}) := frequently_iff_neBot.1 hu
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace
    (map (half X) (atTop ⊓ 𝓟 {t | win X t i n = u}))
  refine ⟨y, hy.mono (map_mono inf_le_left), ?_⟩
  have hC : IsClosed {z : ℕ → Bool | ∀ m : Fin n, z (i + m) = u m} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun m => isClosed_eq (continuous_apply _) continuous_const
  have hmem : {z : ℕ → Bool | ∀ m : Fin n, z (i + m) = u m} ∈
      map (half X) (atTop ⊓ 𝓟 {t | win X t i n = u}) := by
    refine mem_map.2 (mem_inf_of_right (mem_principal.2 fun t ht m => ?_))
    have := congrFun ht m
    simpa [win, half] using this
  have := hy.mem_closure_of_mem _ hmem
  rw [hC.closure_eq] at this
  exact this

/-- At most as many words occur infinitely often as there are limit points. -/
theorem ncard_W_le (hfin : (limitPoints X).Finite) (i n : ℕ) :
    (W X i n).ncard ≤ (limitPoints X).ncard := by
  classical
  choose! y hy hyu using fun u (hu : u ∈ W X i n) => exists_limitPoint hu
  refine Set.ncard_le_ncard_of_injOn y hy (fun u hu v hv huv => funext fun m => ?_) hfin
  rw [← hyu u hu m, ← hyu v hv m, huv]

/-- A word that occurs infinitely often in a window is the restriction of one that occurs
infinitely often in a larger window. -/
theorem exists_extension {i n i' n' : ℕ} (hi : i' ≤ i) (hn : i + n ≤ i' + n') {u : Fin n → Bool}
    (hu : u ∈ W X i n) :
    ∃ v ∈ W X i' n', ∀ m : Fin n, v ⟨i - i' + m, by omega⟩ = u m := by
  have hinf : Set.Infinite {t | win X t i n = u} := Nat.frequently_atTop_iff_infinite.1 hu
  have hex : ∃ v, Set.Infinite {t | win X t i' n' = v ∧ win X t i n = u} := by
    by_contra hcon
    simp only [not_exists, Set.not_infinite] at hcon
    exact hinf ((Set.finite_iUnion hcon).subset fun t ht =>
      Set.mem_iUnion.2 ⟨win X t i' n', rfl, ht⟩)
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, Nat.frequently_atTop_iff_infinite.2 (hv.mono fun t ht => ht.1), fun m => ?_⟩
  obtain ⟨t, ht1, ht2⟩ := hv.nonempty
  have h1 := congrFun ht1 ⟨i - i' + m, by omega⟩
  have h2 := congrFun ht2 m
  simp only [win] at h1 h2
  rw [← h1, ← h2]
  congr 1
  push_cast
  omega

/-- Larger windows have at least as many words that occur infinitely often. -/
theorem ncard_W_mono {i n i' n' : ℕ} (hi : i' ≤ i) (hn : i + n ≤ i' + n') :
    (W X i n).ncard ≤ (W X i' n').ncard := by
  let ρ : (Fin n' → Bool) → (Fin n → Bool) := fun v m => v ⟨i - i' + m, by omega⟩
  have hsub : W X i n ⊆ ρ '' W X i' n' := fun u hu => by
    obtain ⟨v, hv, hvu⟩ := exists_extension hi hn hu
    exact ⟨v, hv, funext hvu⟩
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

/-- From some time on, every window is one that occurs infinitely often. -/
theorem eventually_mem_W (i n : ℕ) : ∀ᶠ t in atTop, win X t i n ∈ W X i n := by
  have h : ∀ u : Fin n → Bool, ∀ᶠ t in atTop, u ∈ W X i n ∨ win X t i n ≠ u := by
    intro u
    by_cases hu : u ∈ W X i n
    · exact Eventually.of_forall fun _ => Or.inl hu
    · exact (not_frequently.1 hu).mono fun t ht => Or.inr ht
  filter_upwards [eventually_all.2 h] with t ht
  rcases ht (win X t i n) with h | h
  · exact h
  · exact absurd rfl h

/-- **Kopra's Theorem 4.6, for radius-1 automata.** If the right halves of the rows have finitely
many limit points, then for every `w` the `w + 1` columns from some `i ≥ 0` on are eventually
periodic. -/
theorem exists_periodic_window {g : Bool → Bool → Bool → Bool}
    (hX : ∀ t p, X (t + 1) p = g (X t (p - 1)) (X t p) (X t (p + 1)))
    (hfin : (limitPoints X).Finite) (w : ℕ) :
    ∃ i : ℕ, ∀ q ≤ w, EventuallyPeriodic fun t => X t ((i : ℤ) + q) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, (limitPoints X).ncard = k := ⟨_, rfl⟩
  -- nested windows `[m, m + (2k + w + 3 - 2m))`, two cells narrower at each step
  let f : ℕ → ℕ := fun m => (W X m (2 * k + w + 3 - 2 * m)).ncard
  have hpos : ∀ m, 1 ≤ f m := fun m => (Set.ncard_pos (Set.toFinite _)).2 (W_nonempty _ _)
  have hle : ∀ m, f m ≤ k := fun m => hk ▸ ncard_W_le hfin _ _
  have hmono : ∀ m, m < k → f (m + 1) ≤ f m := fun m hm => ncard_W_mono (by omega) (by omega)
  -- the count cannot drop at each of `k` steps
  obtain ⟨m, hm, hfm⟩ : ∃ m, m < k ∧ f m ≤ f (m + 1) := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hdrop : ∀ j, j ≤ k → f j + j ≤ f 0 := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 := hcon j (by omega)
        have h2 := ih (by omega)
        omega
    have h1 := hdrop k le_rfl
    have h2 := hle 0
    have h3 := hpos k
    omega
  obtain ⟨LB, hLB⟩ : ∃ LB, 2 * k + w + 3 - 2 * m = LB := ⟨_, rfl⟩
  obtain ⟨LS, hLS⟩ : ∃ LS, 2 * k + w + 3 - 2 * (m + 1) = LS := ⟨_, rfl⟩
  have hLSB : LS + 2 = LB := by omega
  have hfm' : (W X m LB).ncard ≤ (W X (m + 1) LS).ncard := by
    rw [← hLB, ← hLS]
    exact hfm
  -- restriction to the narrower window is injective on the words that occur infinitely often
  let ρ : (Fin LB → Bool) → (Fin LS → Bool) := fun v j => v ⟨1 + j, by have := j.2; omega⟩
  have hsub : W X (m + 1) LS ⊆ ρ '' W X m LB := fun u hu => by
    obtain ⟨v, hv, hvu⟩ := exists_extension (i' := m) (n' := LB) (by omega) (by omega) hu
    refine ⟨v, hv, funext fun j => ?_⟩
    rw [← hvu j]
    show v _ = v _
    congr 1
    exact Fin.ext (by simp only; omega)
  have hinj : Set.InjOn ρ (W X m LB) := by
    refine (Set.ncard_image_iff (Set.toFinite _)).1 (le_antisymm (Set.ncard_image_le
      (Set.toFinite _)) ?_)
    exact hfm'.trans (Set.ncard_le_ncard hsub (Set.toFinite _))
  -- the local rule computes the narrower window at the next time from the window now
  have hstep : ∀ t₁ t₂, win X t₁ m LB = win X t₂ m LB →
      ρ (win X (t₁ + 1) m LB) = ρ (win X (t₂ + 1) m LB) := by
    intro t₁ t₂ h
    have e : ∀ d : ℕ, d < LB → X t₁ ((m : ℤ) + d) = X t₂ ((m : ℤ) + d) :=
      fun d hd => congrFun h ⟨d, hd⟩
    funext j
    have hj := j.2
    simp only [ρ, win]
    rw [hX, hX]
    have e1 : (m : ℤ) + ((1 + (j : ℕ) : ℕ) : ℤ) - 1 = (m : ℤ) + ((j : ℕ) : ℤ) := by omega
    have e2 : (m : ℤ) + ((1 + (j : ℕ) : ℕ) : ℤ) + 1 = (m : ℤ) + (((j : ℕ) + 2 : ℕ) : ℤ) := by
      omega
    rw [e1, e2, e _ (by omega), e _ (by omega), e _ (by omega)]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (eventually_mem_W (X := X) m LB)
  have hdet : ∀ t₁ t₂, T₀ ≤ t₁ → T₀ ≤ t₂ → win X t₁ m LB = win X t₂ m LB →
      win X (t₁ + 1) m LB = win X (t₂ + 1) m LB :=
    fun t₁ t₂ h1 h2 h => hinj (hT₀ _ (by omega)) (hT₀ _ (by omega)) (hstep t₁ t₂ h)
  -- two equal windows from `T₀` on: the window repeats from then on
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite fun s => win X (T₀ + s) m LB
  have key : ∀ a b, a < b → win X (T₀ + a) m LB = win X (T₀ + b) m LB →
      ∃ i : ℕ, ∀ q ≤ w, EventuallyPeriodic fun t => X t ((i : ℤ) + q) := by
    intro a b hab heq
    have hall : ∀ s, win X (T₀ + a + s) m LB = win X (T₀ + b + s) m LB := by
      intro s
      induction s with
      | zero => simpa using heq
      | succ s ih =>
        rw [← add_assoc, ← add_assoc]
        exact hdet _ _ (by omega) (by omega) ih
    refine ⟨m, fun q hq => ⟨T₀ + a, b - a, by omega, fun t ht => ?_⟩⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = T₀ + a + s := ⟨t - (T₀ + a), by omega⟩
    have := congrFun (hall s) ⟨q, by omega⟩
    simp only [win] at this
    rw [show T₀ + a + s + (b - a) = T₀ + b + s by omega]
    exact this.symm
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h heq
  · exact key b a h heq.symm

/-! ### Rule 30 -/

/-- **Kopra's Theorem 4.7 for rule 30**, single black cell: the right halves of the rows have
infinitely many limit points in `{0,1}^ℕ`. -/
theorem infinite_limitPoints_cell : (limitPoints Rule30Jen.cell).Infinite := by
  intro hfin
  obtain ⟨i, hi⟩ := exists_periodic_window (g := Rule30Jen.rule) (fun _ _ => rfl) hfin 1
  exact Rule30Jen.not_adjacent i (by simpa using hi 0 (Nat.zero_le 1)) (by simpa using hi 1 le_rfl)

/-- **Kopra's Theorem 4.5 for rule 30**, single black cell: the right half of row `t` is that of the
seed only for `t = 0`. -/
theorem half_cell_eq_zero_iff (t : ℕ) : half Rule30Jen.cell t = half Rule30Jen.cell 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have h1 := congrFun h t
    have h2 := Rule30Diagonals.R_zero t
    simp only [half, Rule30Diagonals.R] at h1 h2
    rw [show ((t : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = ((t : ℕ) : ℤ) by simp] at h2
    rw [h2] at h1
    simp [Rule30Jen.cell, ht] at h1
  · rintro rfl
    rfl

/-- **Kopra's Theorem 4.7 for rule 30**, every configuration with a leftmost black cell: the right
halves of the rows have infinitely many limit points. -/
theorem infinite_limitPoints_evol {x : ℤ → Bool} {lo : ℤ} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) : (limitPoints (Rule30Realization.evol x)).Infinite := by
  intro hfin
  obtain ⟨i, hi⟩ := exists_periodic_window (g := Rule30Jen.rule) (fun _ _ => rfl) hfin 1
  exact Rule30FiniteConfigs.not_adjacent hlo hzero i (by simpa using hi 0 (Nat.zero_le 1))
    (by simpa using hi 1 le_rfl)

end Rule30Equivalents.LimitPoints
