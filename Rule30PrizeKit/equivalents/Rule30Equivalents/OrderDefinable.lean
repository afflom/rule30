module

public import Rule30Equivalents.Basic
public import Mathlib.ModelTheory.Order
public import Mathlib.ModelTheory.Definability
public import Mathlib.Data.Finset.Max

/-!
# The black times are not first-order definable in `(ℕ, <)`

A statement weaker than Problem 1, and proved: the set `S` of black times of the center column is
not definable in first-order logic over `(ℕ, ≤)`, even with parameters
(`not_definable_order`). The sets definable there are exactly the finite and the cofinite ones
(`eventually_const_of_definable`), and the center column is not eventually constant
(`Rule30Prize.center_not_eventually_constant`).

The proof is an Ehrenfeucht–Fraïssé argument on distances, written without games.
* `clamp K d` cuts an integer distance `d` off at `± K`. Two assignments are similar at `K` when
  their values, together with the constants of the formula and `0`, have the same clamped pairwise
  distances.
* `exists_extension` (the duplicator move): similarity at `2K` lets every new point be matched by a
  new point with similarity at `K`. A point within `K` of an old point is copied at the same offset
  from the matching point; a point far from all old points is put at distance `K` above the
  matching point of the largest old point below it.
* `realize_iff_of_clamp`: similar assignments at `2^d` satisfy the same formulas of quantifier
  depth `d`.
* Two values of `x` beyond all constants of a formula by at least `2^d` are similar, so a formula in
  one variable is eventually constant.
-/

@[expose] public section

namespace Rule30Equivalents.OrderDefinable

/-! ### Clamped distances and the duplicator move -/

/-- The integer `d` cut off at `± K`. -/
def clamp (K : ℕ) (d : ℤ) : ℤ := max (-(K : ℤ)) (min d K)

theorem clamp_eq_zero_iff {K : ℕ} (hK : 0 < K) {d : ℤ} : clamp K d = 0 ↔ d = 0 := by
  simp only [clamp]; omega

theorem clamp_nonpos_iff {K : ℕ} (hK : 0 < K) {d : ℤ} : clamp K d ≤ 0 ↔ d ≤ 0 := by
  simp only [clamp]; omega

theorem clamp_mono {K K' : ℕ} (h : K' ≤ K) {d d' : ℤ} (hd : clamp K d = clamp K d') :
    clamp K' d = clamp K' d' := by
  simp only [clamp] at hd ⊢; omega

theorem clamp_neg {K : ℕ} {d d' : ℤ} (hd : clamp K d = clamp K d') :
    clamp K (-d) = clamp K (-d') := by
  simp only [clamp] at hd ⊢; omega

/-- **The duplicator move.** Let the points `W a` and `W' a` have the same distances clamped at
`2K`, with a common point at `0`. Then every new point `y` has a partner `y'` whose distances to the
points, clamped at `K`, are those of `y`. -/
theorem exists_extension {J : Type*} [Finite J] {W W' : J → ℕ} {K : ℕ} (hK : 0 < K)
    (h : ∀ a b, clamp (2 * K) ((W a : ℤ) - W b) = clamp (2 * K) ((W' a : ℤ) - W' b))
    {a₀ : J} (h₀ : W a₀ = 0) (h₀' : W' a₀ = 0) (y : ℕ) :
    ∃ y' : ℕ, ∀ a, clamp K ((y : ℤ) - W a) = clamp K ((y' : ℤ) - W' a) := by
  classical
  have hJ := Fintype.ofFinite J
  by_cases hnear : ∃ a, (y : ℤ) - W a < K ∧ (W a : ℤ) - y < K
  · -- copy the offset from a nearby point
    obtain ⟨a, ha1, ha2⟩ := hnear
    have h0 := h a a₀
    rw [h₀, h₀'] at h0
    simp only [clamp, Nat.cast_zero, sub_zero] at h0
    refine ⟨((W' a : ℤ) + ((y : ℤ) - W a)).toNat, fun b => ?_⟩
    have hb := h a b
    rw [Int.toNat_of_nonneg (by omega)]
    simp only [clamp] at hb ⊢
    omega
  · -- far from all points: just above the matching point of the largest point below `y`
    push Not at hnear
    obtain ⟨lo, hlo, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun a => W a < y) W
      ⟨a₀, by
        have := hnear a₀
        simp only [h₀, Nat.cast_zero, sub_zero] at this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, h₀]
        omega⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlo hmax
    refine ⟨W' lo + K, fun b => ?_⟩
    have hb := h b lo
    have hlo' := hnear lo
    have hb' := hnear b
    push_cast
    by_cases hby : W b < y
    · have := hmax b hby
      simp only [clamp] at hb ⊢
      omega
    · simp only [clamp] at hb ⊢
      omega

/-! ### Formulas of `(ℕ, ≤)` with parameters -/

open FirstOrder Language Structure Ruliology.CellularAutomata

attribute [local instance] Language.orderStructure

/-- The constants occurring in a function symbol of `order[[A]]`. -/
def funConsts {A : Set ℕ} : {l : ℕ} → Language.order[[A]].Functions l → Finset ℕ
  | 0, Sum.inr c => {((c : A) : ℕ)}
  | _, _ => ∅

/-- The constants occurring in a term. -/
def termConsts {A : Set ℕ} {β : Type*} : Language.order[[A]].Term β → Finset ℕ
  | .var _ => ∅
  | .func f _ => funConsts f

/-- The constants occurring in a formula. -/
def formConsts {A : Set ℕ} {α : Type*} : ∀ {n}, Language.order[[A]].BoundedFormula α n → Finset ℕ
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => termConsts t₁ ∪ termConsts t₂
  | _, .rel _ ts => Finset.univ.biUnion fun i => termConsts (ts i)
  | _, .imp φ ψ => formConsts φ ∪ formConsts ψ
  | _, .all φ => formConsts φ

/-- Quantifier depth. -/
def qdepth {L : Language} {α : Type*} : ∀ {n}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qdepth φ) (qdepth ψ)
  | _, .all φ => qdepth φ + 1

/-- The points of an assignment: its free and bound variables, and the constants in `F`. -/
def W {α : Type*} (F : Finset ℕ) {n : ℕ} (v : α → ℕ) (xs : Fin n → ℕ) : (α ⊕ Fin n) ⊕ F → ℕ :=
  Sum.elim (Sum.elim v xs) fun c => (c : ℕ)

/-- A term's value is one of the points. -/
theorem exists_point {A : Set ℕ} {α : Type*} {F : Finset ℕ} {n : ℕ}
    (t : Language.order[[A]].Term (α ⊕ Fin n)) (ht : termConsts t ⊆ F) :
    ∃ a, ∀ (v : α → ℕ) (xs : Fin n → ℕ), t.realize (Sum.elim v xs) = W F v xs a := by
  cases t with
  | var b => exact ⟨Sum.inl b, fun _ _ => rfl⟩
  | @func l f ts =>
    rcases f with f | c
    · exact isEmptyElim f
    · cases l with
      | zero =>
        have hc : ((c : A) : ℕ) ∈ F := ht (by simp [termConsts, funConsts])
        exact ⟨Sum.inr ⟨_, hc⟩, fun _ _ => rfl⟩
      | succ l => exact isEmptyElim c

/-- The points after adding a bound variable `y`. -/
theorem W_snoc {α : Type*} {F : Finset ℕ} {n : ℕ} (v : α → ℕ) (xs : Fin n → ℕ) (y : ℕ)
    (v' : α → ℕ) (xs' : Fin n → ℕ) (y' : ℕ) (a : (α ⊕ Fin (n + 1)) ⊕ F) :
    (W F v (Fin.snoc xs y) a = y ∧ W F v' (Fin.snoc xs' y') a = y') ∨
      ∃ b, W F v (Fin.snoc xs y) a = W F v xs b ∧ W F v' (Fin.snoc xs' y') a = W F v' xs' b := by
  rcases a with (a | i) | c
  · exact Or.inr ⟨Sum.inl (Sum.inl a), rfl, rfl⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · left
      simp [W]
    · right
      exact ⟨Sum.inl (Sum.inr j), by simp [W], by simp [W]⟩
  · exact Or.inr ⟨Sum.inr c, rfl, rfl⟩

theorem eq_iff_of_clamp {K : ℕ} (hK : 0 < K) {x y x' y' : ℕ}
    (h : clamp K ((x : ℤ) - y) = clamp K ((x' : ℤ) - y')) : x = y ↔ x' = y' := by
  simp only [clamp] at h
  constructor <;> intro h' <;> omega

theorem le_iff_of_clamp {K : ℕ} (hK : 0 < K) {x y x' y' : ℕ}
    (h : clamp K ((x : ℤ) - y) = clamp K ((x' : ℤ) - y')) : x ≤ y ↔ x' ≤ y' := by
  simp only [clamp] at h
  constructor <;> intro h' <;> omega

/-- **Similar assignments satisfy the same formulas**: clamped at `2^d`, for quantifier depth
`d`. -/
theorem realize_iff_of_clamp {A : Set ℕ} {α : Type*} [Finite α] {F : Finset ℕ} (h0F : 0 ∈ F) :
    ∀ {n} (φ : Language.order[[A]].BoundedFormula α n), formConsts φ ⊆ F →
    ∀ {K : ℕ}, 2 ^ qdepth φ ≤ K → ∀ (v v' : α → ℕ) (xs xs' : Fin n → ℕ),
      (∀ a b, clamp K ((W F v xs a : ℤ) - W F v xs b) =
        clamp K ((W F v' xs' a : ℤ) - W F v' xs' b)) →
      (φ.Realize v xs ↔ φ.Realize v' xs')
  | _, .falsum, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, hF, K, hK, v, v', xs, xs', h => by
    have hK0 : 0 < K := lt_of_lt_of_le (Nat.two_pow_pos _) hK
    obtain ⟨a₁, h₁⟩ := exists_point t₁ (fun c hc => hF (Finset.mem_union_left _ hc))
    obtain ⟨a₂, h₂⟩ := exists_point t₂ (fun c hc => hF (Finset.mem_union_right _ hc))
    simp only [BoundedFormula.Realize, h₁, h₂]
    exact eq_iff_of_clamp hK0 (h a₁ a₂)
  | _, .rel R ts, hF, K, hK, v, v', xs, xs', h => by
    have hK0 : 0 < K := lt_of_lt_of_le (Nat.two_pow_pos _) hK
    rcases R with R | R
    · cases R
      obtain ⟨a₀, h₀⟩ := exists_point (ts 0)
        (fun c hc => hF (Finset.mem_biUnion.2 ⟨0, Finset.mem_univ _, hc⟩))
      obtain ⟨a₁, h₁⟩ := exists_point (ts 1)
        (fun c hc => hF (Finset.mem_biUnion.2 ⟨1, Finset.mem_univ _, hc⟩))
      show (ts 0).realize (Sum.elim v xs) ≤ (ts 1).realize (Sum.elim v xs) ↔
        (ts 0).realize (Sum.elim v' xs') ≤ (ts 1).realize (Sum.elim v' xs')
      rw [h₀, h₀, h₁, h₁]
      exact le_iff_of_clamp hK0 (h a₀ a₁)
    · exact Empty.elim R
  | _, .imp φ ψ, hF, K, hK, v, v', xs, xs', h => by
    have hφ := realize_iff_of_clamp h0F φ (fun c hc => hF (Finset.mem_union_left _ hc))
      (le_trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) hK) v v' xs xs' h
    have hψ := realize_iff_of_clamp h0F ψ (fun c hc => hF (Finset.mem_union_right _ hc))
      (le_trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)) hK) v v' xs xs' h
    simp only [BoundedFormula.realize_imp, hφ, hψ]
  | n, .all φ, hF, K, hK, v, v', xs, xs', h => by
    have hd : 2 ^ qdepth φ ≤ K / 2 := by
      have : 2 ^ (qdepth φ + 1) ≤ K := hK
      rw [pow_succ] at this
      omega
    have hK2 : 0 < K / 2 := lt_of_lt_of_le (Nat.two_pow_pos _) hd
    have h2 : ∀ a b, clamp (2 * (K / 2)) ((W F v xs a : ℤ) - W F v xs b) =
        clamp (2 * (K / 2)) ((W F v' xs' a : ℤ) - W F v' xs' b) :=
      fun a b => clamp_mono (by omega) (h a b)
    -- one direction, used for both
    have key : ∀ (u u' : α → ℕ) (ys ys' : Fin n → ℕ),
        (∀ a b, clamp (2 * (K / 2)) ((W F u ys a : ℤ) - W F u ys b) =
          clamp (2 * (K / 2)) ((W F u' ys' a : ℤ) - W F u' ys' b)) →
        (∀ y', φ.Realize u' (Fin.snoc ys' y')) → ∀ y, φ.Realize u (Fin.snoc ys y) := by
      intro u u' ys ys' hs hall y
      obtain ⟨y', hy'⟩ := exists_extension hK2 hs (a₀ := Sum.inr ⟨0, h0F⟩) rfl rfl y
      refine (realize_iff_of_clamp h0F φ hF hd u u' (Fin.snoc ys y) (Fin.snoc ys' y') ?_).2
        (hall y')
      intro a b
      rcases W_snoc u ys y u' ys' y' a with ⟨ha, ha'⟩ | ⟨a', ha, ha'⟩ <;>
        rcases W_snoc u ys y u' ys' y' b with ⟨hb, hb'⟩ | ⟨b', hb, hb'⟩ <;>
        rw [ha, ha', hb, hb']
      · simp
      · exact hy' b'
      · have := clamp_neg (hy' a')
        rwa [neg_sub, neg_sub] at this
      · exact clamp_mono (by omega) (hs a' b')
    simp only [BoundedFormula.realize_all]
    exact ⟨fun hall => key v' v xs' xs (fun a b => (h2 a b).symm) hall,
      fun hall => key v v' xs xs' h2 hall⟩

/-! ### Definable sets of `(ℕ, ≤)` -/

/-- **Definable in `(ℕ, ≤)` ⟹ eventually constant**, with any parameters: beyond all constants of
the formula by `2^d`, all values of `x` are similar. -/
theorem eventually_const_of_definable {A S : Set ℕ} (h : A.Definable₁ Language.order S) :
    ∃ N, (∀ x, N ≤ x → x ∈ S) ∨ (∀ x, N ≤ x → x ∉ S) := by
  obtain ⟨φ, hφ⟩ := h
  set F := insert 0 (formConsts φ) with hFdef
  have hFne : F.Nonempty := Finset.insert_nonempty _ _
  set N := F.max' hFne + 2 ^ qdepth φ with hNdef
  have hcN : ∀ c ∈ F, c + 2 ^ qdepth φ ≤ N := fun c hc => by
    have := F.le_max' c hc
    omega
  have e : ∀ z, z ∈ S ↔ φ.Realize (fun _ => z) := fun z => by
    have := congrArg (fun s : Set (Fin 1 → ℕ) => (fun _ => z) ∈ s) hφ
    simpa using this
  have hx : ∀ x, N ≤ x → (x ∈ S ↔ N ∈ S) := by
    intro x hxN
    rw [e, e]
    unfold Formula.Realize
    refine realize_iff_of_clamp (Finset.mem_insert_self 0 _) φ (Finset.subset_insert _ _) le_rfl
      (fun _ => x) (fun _ => N) _ _ ?_
    intro a b
    rcases a with (a | i) | ⟨c, hc⟩
    · rcases b with (b | j) | ⟨d, hd⟩
      · simp [W]
      · exact j.elim0
      · have := hcN d hd
        simp only [W, Sum.elim_inl, Sum.elim_inr, clamp]
        omega
    · exact i.elim0
    · rcases b with (b | j) | ⟨d, hd⟩
      · have := hcN c hc
        simp only [W, Sum.elim_inl, Sum.elim_inr, clamp]
        omega
      · exact j.elim0
      · rfl
  by_cases hN : N ∈ S
  · exact ⟨N, Or.inl fun x hx' => (hx x hx').2 hN⟩
  · exact ⟨N, Or.inr fun x hx' hxs => hN ((hx x hx').1 hxs)⟩

/-- **The black times are not first-order definable in `(ℕ, ≤)`**, with any parameters `A`. -/
theorem not_definable (A : Set ℕ) :
    ¬ A.Definable₁ Language.order {t | Rule30Prize.center t = true} := by
  intro h
  obtain ⟨N, hN | hN⟩ := eventually_const_of_definable h
  · exact Rule30Prize.center_not_eventually_constant ⟨N, true, fun t ht => hN t ht⟩
  · exact Rule30Prize.center_not_eventually_constant ⟨N, false, fun t ht => by simpa using hN t ht⟩

/-- **`S` is not definable in `(ℕ, ≤)`**, with `orderStructure` given explicitly. -/
theorem not_definable_order :
    letI := Language.orderStructure (M := ℕ)
    ¬ (Set.univ : Set ℕ).Definable₁ Language.order {t | Rule30Prize.center t = true} :=
  not_definable Set.univ

end Rule30Equivalents.OrderDefinable
