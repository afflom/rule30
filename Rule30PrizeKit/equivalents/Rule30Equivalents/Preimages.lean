module

public import Rule30Equivalents.Genericity
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
# Preimages under rule 30

Rule 30 is onto (`Genericity.surjective_evol_one`) and not one-to-one. This file bounds the
preimages, using only left-permutivity: `F(x)_q = x_{q-1} ⊕ (x_q ∨ x_{q+1})`, so `x_{q-1}` is
determined by `F(x)_q`, `x_q` and `x_{q+1}`.

* `eq_of_evol_one_eq`: two configurations with the same image that agree on two adjacent cells
  `k`, `k + 1` agree at every cell left of them; locally, down to the cell `p` when the images
  agree on the cells from `p + 1` to `k + 1` (`eq_of_evol_one_eq_on`).
* `eq_of_evol_one_eq_of_right`: so rule 30 is injective on configurations that agree far to the
  right, in particular pre-injective (as the Garden of Eden theorem requires of an onto map).
* `card_le_three`: **every configuration has at most three preimages**, sharper than Hedlund's
  bound `|A|^(2r) = 4` (`card_le_four`). Distinct preimages differ on the pair of cells `N, N + 1`
  far enough to the right, and at each position one of the four pairs is impossible. Three is
  attained: the all-black configuration has the three shifts of `(100)^∞` as preimages
  (`exists_card_eq_three`).
* `evol_one_eq_iff_of_eventually_white`: **a configuration that is white from some cell on has
  exactly two preimages**, one white and one black from that cell on (`extendLeft`): there the
  preimage satisfies `x_{q-1} = x_q ∨ x_{q+1}`, which forces it to be constant
  (`eq_of_evol_one_white`). Every finite configuration is one, such as each row of rule 30 from the
  single black cell, whose two preimages are the row before it and one that is black far to the
  right (`evol_one_eq_row_iff`); for the white configuration, `preimage_white`: all white and all
  black.
* `evol_one_eq_iff_of_eventually_black`: **a configuration that is black from some cell on has
  exactly three preimages**, repeating `100` in each of the three phases from that cell on
  (`eq_third_of_evol_one_black`). So the counts `1` (almost every configuration), `2` and `3` all
  occur, and three is the most (`card_le_three`); each occurs on a dense set
  (`dense_two_preimages`, `dense_three_preimages`).
* `eq_of_evol_one_eq_of_frequently`: **a configuration that shows `010` arbitrarily far to the
  right has exactly one preimage**. An image showing `010` at `q, q + 1, q + 2` forces the
  preimage to be black at `q - 1` (`eq_true_of_window`), and then the image at `q - 1` fixes the
  cell `q - 2`. Almost every configuration, and a comeager set of them, show `010` so
  (`Mixing.ae_existsUnique_preimage`, `Mixing.residual_existsUnique_preimage`). The inverse looks
  only to the right: the cell `p` of the preimage is determined by the image on the cells
  `p + 1, …, q + 2` for any such `q > p` (`eq_of_evol_one_eq_on_of_window`).
* `exists_ne_left_eq`: rule 30 is not injective on left-asymptotic configurations. Black only at
  `0` on the left, then `(0110)^∞` against `(1000)^∞` from the cell `1` on, have the same
  image. A preimage can branch only after a black cell, and these two branches run around a cycle
  of length `4` of pairs of states. So `not_positivelyExpansive`: **rule 30 is not positively
  expansive**; for every window `[-n, n]` two different configurations have orbits that agree on
  it at all times.
-/

@[expose] public section

namespace Rule30Equivalents.Preimages

open Ruliology.CellularAutomata Rule30Realization

/-- One step of rule 30, cell by cell. -/
theorem evol_one (x : ℤ → Bool) (q : ℤ) : evol x 1 q = xor (x (q - 1)) (x q || x (q + 1)) := rfl

/-- **Left determinism, locally**: configurations whose images agree on the cells `j` with
`p < j ≤ k + 1`, and which agree on `k` and `k + 1`, agree on every cell from `p` to `k + 1`. -/
theorem eq_of_evol_one_eq_on {x y : ℤ → Bool} {p k : ℤ}
    (h : ∀ j, p < j → j ≤ k + 1 → evol x 1 j = evol y 1 j) (hk : x k = y k)
    (hk1 : x (k + 1) = y (k + 1)) : ∀ q, p ≤ q → q ≤ k + 1 → x q = y q := by
  have step : ∀ n : ℕ, p ≤ k - n → x (k - n) = y (k - n) ∧ x (k - n + 1) = y (k - n + 1) := by
    intro n
    induction n with
    | zero => intro _; simpa using ⟨hk, hk1⟩
    | succ n ih =>
      intro hn
      have ih' := ih (by push_cast at hn; omega)
      have e := h (k - n) (by push_cast at hn; omega) (by omega)
      rw [evol_one, evol_one, ih'.1, ih'.2] at e
      refine ⟨?_, ?_⟩
      · have : x (k - n - 1) = y (k - n - 1) := by
          generalize (y (k - n) || y (k - n + 1)) = c at e
          cases c <;> simpa using e
        rwa [show k - ((n + 1 : ℕ) : ℤ) = k - n - 1 by push_cast; ring]
      · rw [show k - ((n + 1 : ℕ) : ℤ) + 1 = k - n by push_cast; ring]
        exact ih'.1
  intro q hpq hq
  rcases eq_or_lt_of_le hq with rfl | hlt
  · exact hk1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = k - n := ⟨(k - q).toNat, by omega⟩
    rw [hn]
    exact (step n (by omega)).1

/-- **Left determinism**: configurations with the same image that agree on `k` and `k + 1` agree
at every cell `q ≤ k + 1`. -/
theorem eq_of_evol_one_eq {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {k : ℤ}
    (hk : x k = y k) (hk1 : x (k + 1) = y (k + 1)) : ∀ q, q ≤ k + 1 → x q = y q := fun q hq =>
  eq_of_evol_one_eq_on (p := q) (fun j _ _ => congrFun h j) hk hk1 q le_rfl hq

/-- **Rule 30 is injective on right-asymptotic configurations**: two configurations with the same
image that agree right of some cell are equal. In particular rule 30 is pre-injective. -/
theorem eq_of_evol_one_eq_of_right {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {k : ℤ}
    (hr : ∀ q, k ≤ q → x q = y q) : x = y := by
  funext q
  rcases le_or_gt q (k + 1) with hq | hq
  · exact eq_of_evol_one_eq h (hr k le_rfl) (hr (k + 1) (by omega)) q hq
  · exact hr q (by omega)

/-- **Every configuration has at most three preimages**, sharper than Hedlund's general bound
`|A|^(2r) = 4`. Distinct preimages have distinct pairs of cells `x_N, x_{N+1}` far enough to the
right (left determinism), but at every position one of the four pairs is impossible: `(0, 1)` if
the image is white at `N + 1`, `(1, 1)` if it is black there. -/
theorem card_le_three (y : ℤ → Bool) (s : Finset (ℤ → Bool)) (hs : ∀ x ∈ s, evol x 1 = y) :
    s.card ≤ 3 := by
  by_contra hcard
  push Not at hcard
  -- four distinct preimages
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
  let e : Fin 4 ≃ t := (Fintype.equivFinOfCardEq (by simp [htc])).symm
  let x : Fin 4 → ℤ → Bool := fun j => (e j).1
  have hx : ∀ j, evol (x j) 1 = y := fun j => hs _ (hts (e j).2)
  have hinj : Function.Injective x := fun j j' h => e.injective (Subtype.ext h)
  -- a position right of a difference of every two of them
  have hdiff : ∀ j j' : Fin 4, ∃ m : ℤ, j ≠ j' → x j m ≠ x j' m := fun j j' => by
    by_cases h : j = j'
    · exact ⟨0, fun h' => absurd h h'⟩
    · by_contra hall
      push Not at hall
      exact h (hinj (funext fun q => (hall q).2))
  choose m hm using hdiff
  let N : ℤ := ∑ j, ∑ j', |m j j'|
  have hN : ∀ j j', m j j' ≤ N := fun j j' => by
    have h1 : |m j j'| ≤ ∑ j'', |m j j''| :=
      Finset.single_le_sum (f := fun j'' => |m j j''|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j')
    have h2 : ∑ j'', |m j j''| ≤ N :=
      Finset.single_le_sum (f := fun j => ∑ j'', |m j j''|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    exact (le_abs_self _).trans (h1.trans h2)
  -- there the pairs `(x_N, x_{N+1})` are pairwise different
  have hpair : Function.Injective fun j => (x j N, x j (N + 1)) := by
    intro j j' hjj
    by_contra hne
    have := eq_of_evol_one_eq ((hx j).trans (hx j').symm) (Prod.ext_iff.1 hjj).1
      (Prod.ext_iff.1 hjj).2 (m j j') (by have := hN j j'; omega)
    exact hm j j' hne this
  -- but one pair is impossible
  obtain ⟨p, hp⟩ : ∃ p : Bool × Bool, ∀ j, (x j N, x j (N + 1)) ≠ p := by
    cases hy : y (N + 1)
    · refine ⟨(false, true), fun j h => ?_⟩
      simp only [Prod.mk.injEq] at h
      have e1 := congrFun (hx j) (N + 1)
      rw [evol_one, show N + 1 - 1 = N by ring, hy, h.1, h.2] at e1
      simp at e1
    · refine ⟨(true, true), fun j h => ?_⟩
      simp only [Prod.mk.injEq] at h
      have e1 := congrFun (hx j) (N + 1)
      rw [evol_one, show N + 1 - 1 = N by ring, hy, h.1, h.2] at e1
      simp at e1
  have hcardle := Fintype.card_le_of_injective
    (fun j => (⟨(x j N, x j (N + 1)), hp j⟩ : {q : Bool × Bool // q ≠ p}))
    fun j j' h => hpair (congrArg Subtype.val h)
  simp [Fintype.card_subtype_compl] at hcardle

/-- The configuration that is black exactly at the cells `p ≡ r (mod 3)`. -/
def third (r p : ℤ) : Bool := decide (p % 3 = r % 3)

/-- Each shift of `(100)^∞` maps to the all-black configuration: exactly one of the cells
`q - 1, q, q + 1` is black. -/
theorem evol_third (r : ℤ) : evol (third r) 1 = fun _ => true := by
  funext q
  rw [evol_one]
  simp only [third]
  rcases (by omega : (q - 1) % 3 = r % 3 ∨ q % 3 = r % 3 ∨ (q + 1) % 3 = r % 3) with h | h | h
  · simp [h, show ¬ q % 3 = r % 3 by omega, show ¬ (q + 1) % 3 = r % 3 by omega]
  · simp [h, show ¬ (q - 1) % 3 = r % 3 by omega]
  · simp [h, show ¬ (q - 1) % 3 = r % 3 by omega]

/-- **Three is sharp**: the all-black configuration has the three preimages `(100)^∞`, shifted. -/
theorem exists_card_eq_three : ∃ s : Finset (ℤ → Bool), s.card = 3 ∧
    ∀ x ∈ s, evol x 1 = fun _ => true := by
  classical
  have h01 : third 0 ≠ third 1 := fun h => by simpa [third] using congrFun h 0
  have h02 : third 0 ≠ third 2 := fun h => by simpa [third] using congrFun h 0
  have h12 : third 1 ≠ third 2 := fun h => by simpa [third] using congrFun h 1
  refine ⟨{third 0, third 1, third 2}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact evol_third _

/-- Hedlund's bound for rule 30: at most four preimages. -/
theorem card_le_four (y : ℤ → Bool) (s : Finset (ℤ → Bool)) (hs : ∀ x ∈ s, evol x 1 = y) :
    s.card ≤ 4 :=
  (card_le_three y s hs).trans (by norm_num)

/-! ### Configurations that are eventually white or black -/

/-- Left determinism from a tail: the cells `x_{N-k}, x_{N-k+1}` of the configuration that agrees
with `z` from `N` on and whose image is `y` up to `N`. -/
def leftPair (y : ℤ → Bool) (N : ℤ) (z : ℤ → Bool) : ℕ → Bool × Bool
  | 0 => (z N, z (N + 1))
  | k + 1 => (xor (y (N - k)) ((leftPair y N z k).1 || (leftPair y N z k).2), (leftPair y N z k).1)

/-- The configuration that agrees with `z` from `N` on and whose image is `y` up to `N`. -/
def extendLeft (y : ℤ → Bool) (N : ℤ) (z : ℤ → Bool) (p : ℤ) : Bool :=
  if N ≤ p then z p else (leftPair y N z (N - p).toNat).1

theorem extendLeft_eq (y : ℤ → Bool) (N : ℤ) (z : ℤ → Bool) (k : ℕ) :
    extendLeft y N z (N - k) = (leftPair y N z k).1 := by
  unfold extendLeft
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [leftPair]
  · rw [ite_eq_right (by omega), show (N - (N - k)).toNat = k by omega]

theorem extendLeft_succ (y : ℤ → Bool) (N : ℤ) (z : ℤ → Bool) (k : ℕ) :
    extendLeft y N z (N - k + 1) = (leftPair y N z k).2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [extendLeft, leftPair]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show N - ((j + 1 : ℕ) : ℤ) + 1 = N - j by push_cast; ring, extendLeft_eq]
    rfl

/-- `extendLeft y N z` is a preimage of `y` whenever `z` is one right of `N`. -/
theorem evol_extendLeft {y z : ℤ → Bool} {N : ℤ} (hz : ∀ q, N < q → evol z 1 q = y q) :
    evol (extendLeft y N z) 1 = y := by
  funext q
  rw [evol_one]
  rcases le_or_gt q N with hq | hq
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = N - k := ⟨(N - q).toNat, by omega⟩
    rw [show N - (k : ℤ) - 1 = N - ((k + 1 : ℕ) : ℤ) by push_cast; ring, extendLeft_eq,
      extendLeft_eq, extendLeft_succ]
    simp only [leftPair]
    cases y (N - k) <;> cases (leftPair y N z k).1 || (leftPair y N z k).2 <;> rfl
  · simp only [extendLeft, ite_eq_left (show N ≤ q - 1 by omega), ite_eq_left hq.le,
      ite_eq_left (show N ≤ q + 1 by omega)]
    have := hz q hq
    rwa [evol_one] at this

/-- If the image is white right of `N`, a preimage is constant from `N` on: there
`x_{q-1} = x_q ∨ x_{q+1}`, so a white cell makes every later cell white and the cell before it,
when that is still at least `N`, white too. -/
theorem eq_of_evol_one_white {x : ℤ → Bool} {N : ℤ}
    (hy : ∀ q, N < q → evol x 1 q = false) : ∀ p, N ≤ p → x p = x N := by
  have hrel : ∀ q, N < q → x (q - 1) = (x q || x (q + 1)) := fun q hq => by
    have := hy q hq
    rw [evol_one] at this
    revert this
    cases x (q - 1) <;> cases x q || x (q + 1) <;> simp
  -- a white cell at `p ≥ N` makes every later cell white
  have hfwd : ∀ p, N ≤ p → x p = false → ∀ k : ℕ, x (p + k) = false := by
    intro p hp h0 k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have := hrel (p + k + 1) (by omega)
      rw [show p + k + 1 - 1 = p + (k : ℤ) by ring, ih] at this
      have h' := (Bool.or_eq_false_iff.1 this.symm).1
      rwa [show p + ((k + 1 : ℕ) : ℤ) = p + k + 1 by push_cast; ring]
  intro p hp
  cases hN : x N
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = N + k := ⟨(p - N).toNat, by omega⟩
    exact hfwd N le_rfl hN k
  · by_contra hne
    have hp0 : x p = false := by simpa using hne
    -- white cells propagate back down to `N`
    have hback : ∀ k : ℕ, (k : ℤ) ≤ p - N → x (p - k) = false := by
      intro k hk
      induction k with
      | zero => simpa using hp0
      | succ k ih =>
        have h1 := ih (by omega)
        have h2 : x (p - k + 1) = false := by
          have := hfwd (p - k) (by omega) h1 1
          simpa using this
        have := hrel (p - k) (by push_cast at hk; omega)
        rw [h1, h2] at this
        rw [show p - ((k + 1 : ℕ) : ℤ) = p - k - 1 by push_cast; ring]
        simpa using this
    have := hback (p - N).toNat (by omega)
    rw [show p - ((p - N).toNat : ℤ) = N by omega, hN] at this
    exact absurd this (by decide)

/-- **A configuration that is white from some cell on has exactly two preimages**: one white and
one black from that cell on (`extendLeft`). This generalizes `preimage_white`, and it applies to
every finite configuration, such as each row of rule 30 from the single black cell. -/
theorem evol_one_eq_iff_of_eventually_white {y : ℤ → Bool} {N : ℤ}
    (hy : ∀ q, N < q → y q = false) (x : ℤ → Bool) :
    evol x 1 = y ↔ x = extendLeft y N (fun _ => false) ∨ x = extendLeft y N (fun _ => true) := by
  have hz : ∀ b : Bool, ∀ q, N < q → evol (fun _ => b) 1 q = y q := fun b q hq => by
    rw [evol_one, hy q hq]
    cases b <;> rfl
  constructor
  · intro hx
    have hconst := eq_of_evol_one_white (x := x) (N := N) fun q hq => by rw [hx]; exact hy q hq
    have hagree : ∀ b, x N = b → x = extendLeft y N (fun _ => b) := fun b hb =>
      eq_of_evol_one_eq_of_right (hx.trans (evol_extendLeft (hz b)).symm) (k := N)
        fun q hq => by
          rw [hconst q hq, hb]
          simp [extendLeft, hq]
    cases hN : x N
    · exact Or.inl (hagree false hN)
    · exact Or.inr (hagree true hN)
  · rintro (rfl | rfl) <;> exact evol_extendLeft (hz _)

theorem extendLeft_false_ne_true (y : ℤ → Bool) (N : ℤ) :
    extendLeft y N (fun _ => false) ≠ extendLeft y N (fun _ => true) := fun h => by
  have := congrFun h N
  simp [extendLeft] at this

/-- For the all-white image, `extendLeft` is constant. -/
theorem extendLeft_white (N : ℤ) (b : Bool) :
    extendLeft (fun _ => false) N (fun _ => b) = fun _ => b := by
  have h : ∀ k, leftPair (fun _ => false) N (fun _ => b) k = (b, b) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [leftPair, ih, Bool.or_self, Bool.false_xor]
  funext p
  simp only [extendLeft, h]
  split_ifs <;> rfl

/-- **The all-white configuration has exactly two preimages**: all white and all black. -/
theorem preimage_white (x : ℤ → Bool) :
    evol x 1 = (fun _ => false) ↔ x = (fun _ => false) ∨ x = (fun _ => true) := by
  rw [evol_one_eq_iff_of_eventually_white (N := 0) (fun _ _ => rfl), extendLeft_white,
    extendLeft_white]

/-- If the image is black right of `N`, a preimage repeats with period `3` from `N` on, with one
black cell in each period: there `x_{q-1} = ¬(x_q ∨ x_{q+1})`. -/
theorem eq_third_of_evol_one_black {x : ℤ → Bool} {N : ℤ}
    (hy : ∀ q, N < q → evol x 1 q = true) : ∃ r : ℤ, ∀ p, N ≤ p → x p = third r p := by
  have hrel : ∀ p, N ≤ p → x p = !(x (p + 1) || x (p + 2)) := fun p hp => by
    have := hy (p + 1) (by omega)
    rw [evol_one, show p + 1 - 1 = p by ring, show p + 1 + 1 = p + 2 by ring] at this
    revert this
    cases x p <;> cases x (p + 1) || x (p + 2) <;> simp
  -- period `3`
  have hper : ∀ p, N ≤ p → x (p + 3) = x p := by
    intro p hp
    have h0 := hrel p hp
    have h1 := hrel (p + 1) (by omega)
    have h2 := hrel (p + 2) (by omega)
    rw [show p + 1 + 1 = p + 2 by ring, show p + 1 + 2 = p + 3 by ring] at h1
    rw [show p + 2 + 1 = p + 3 by ring, show p + 2 + 2 = p + 4 by ring] at h2
    revert h0 h1 h2
    cases x p <;> cases x (p + 1) <;> cases x (p + 2) <;> cases x (p + 3) <;>
      cases x (p + 4) <;> simp
  have hperj : ∀ (j i : ℕ), x (N + i + 3 * j) = x (N + i) := by
    intro j i
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show N + (i : ℤ) + 3 * ((j + 1 : ℕ) : ℤ) = N + i + 3 * j + 3 by push_cast; ring,
        hper _ (by omega), ih]
  have hthird : ∀ (r : ℤ) (j i : ℕ), third r (N + i + 3 * j) = third r (N + i) := by
    intro r j i
    simp only [third]
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
  -- the first period has exactly one black cell
  have h0 := hrel N le_rfl
  have h1 := hrel (N + 1) (by omega)
  rw [show N + 1 + 1 = N + 2 by ring, show N + 1 + 2 = N + 3 by ring, hper N le_rfl] at h1
  have hbase : ∃ r : ℤ, ∀ i : ℕ, i < 3 → x (N + i) = third r (N + i) := by
    cases hN : x N <;> cases hN1 : x (N + 1) <;> cases hN2 : x (N + 2) <;>
      simp only [hN, hN1, hN2] at h0 h1 <;> simp at h0 h1
    · refine ⟨N + 2, fun i hi => ?_⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [third, hN, hN1, hN2] <;> omega
    · refine ⟨N + 1, fun i hi => ?_⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [third, hN, hN1, hN2] <;> omega
    · refine ⟨N, fun i hi => ?_⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [third, hN, hN1, hN2] <;> omega
  obtain ⟨r, hr⟩ := hbase
  refine ⟨r, fun p hp => ?_⟩
  obtain ⟨i, j, hi, rfl⟩ : ∃ i j : ℕ, i < 3 ∧ p = N + i + 3 * j :=
    ⟨((p - N) % 3).toNat, ((p - N) / 3).toNat, by omega, by omega⟩
  rw [hperj, hthird, hr i hi]

/-- **A configuration that is black from some cell on has exactly three preimages**, which
repeat `100` with each of the three phases from that cell on (`extendLeft` of the shifts
`third`). With `card_le_three`, three is the most any configuration has. -/
theorem evol_one_eq_iff_of_eventually_black {y : ℤ → Bool} {N : ℤ}
    (hy : ∀ q, N < q → y q = true) (x : ℤ → Bool) :
    evol x 1 = y ↔ x = extendLeft y N (third N) ∨ x = extendLeft y N (third (N + 1)) ∨
      x = extendLeft y N (third (N + 2)) := by
  have hz : ∀ r, ∀ q, N < q → evol (third r) 1 q = y q := fun r q hq => by
    rw [evol_third, hy q hq]
  have hthird : ∀ r r' : ℤ, r % 3 = r' % 3 → third r = third r' := fun r r' h => by
    funext p
    simp only [third, h]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := eq_third_of_evol_one_black (x := x) (N := N) fun q hq => by
      rw [hx]
      exact hy q hq
    have hagree : x = extendLeft y N (third r) :=
      eq_of_evol_one_eq_of_right (hx.trans (evol_extendLeft (hz r)).symm) (k := N)
        fun q hq => by
          rw [hr q hq]
          simp [extendLeft, hq]
    rcases (by omega : r % 3 = N % 3 ∨ r % 3 = (N + 1) % 3 ∨ r % 3 = (N + 2) % 3) with
      h | h | h
    · exact Or.inl (hagree.trans (by rw [hthird r N h]))
    · exact Or.inr (Or.inl (hagree.trans (by rw [hthird r (N + 1) h])))
    · exact Or.inr (Or.inr (hagree.trans (by rw [hthird r (N + 2) h])))
  · rintro (rfl | rfl | rfl) <;> exact evol_extendLeft (hz _)

/-- **Each row of rule 30 from the single black cell has exactly two preimages**: the row before
it, and one that is black from the cell `t + 1` on. -/
theorem evol_one_eq_row_iff (t : ℕ) (x : ℤ → Bool) :
    evol x 1 = evol seed (t + 1) ↔
      x = evol seed t ∨ x = extendLeft (evol seed (t + 1)) ((t : ℤ) + 1) (fun _ => true) := by
  have hy : ∀ q, (t : ℤ) + 1 < q → evol seed (t + 1) q = false := fun q hq => by
    rw [evol_seed]
    exact Rule30Diagonals.cell_eq_false_of_gt _ _ (by push_cast; omega)
  have hprev : evol (evol seed t) 1 = evol seed (t + 1) :=
    funext fun p => Rule30ZeroBoundaryBarriers.evol_restart seed t 1 p
  have hwhite : evol seed t = extendLeft (evol seed (t + 1)) ((t : ℤ) + 1) (fun _ => false) := by
    rcases (evol_one_eq_iff_of_eventually_white hy (evol seed t)).1 hprev with h | h
    · exact h
    · exfalso
      have h1 := congrFun h ((t : ℤ) + 1)
      rw [evol_seed, Rule30Diagonals.cell_eq_false_of_gt _ _ (by omega)] at h1
      simp [extendLeft] at h1
  rw [evol_one_eq_iff_of_eventually_white hy, ← hwhite]

/-- The configurations that are constant `b` from some cell on are dense: cut any configuration
off far to the right. -/
theorem dense_eventually_const (b : Bool) :
    Dense {y : ℤ → Bool | ∃ N : ℤ, ∀ q, N < q → y q = b} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨v, hv⟩
  obtain ⟨n, hn⟩ := Genericity.exists_window_subset (hU.mem_nhds hv)
  refine ⟨fun q => if q ≤ n then v q else b, hn fun p _ hp => by simp [hp], n, fun q hq => ?_⟩
  simp [show ¬ q ≤ (n : ℤ) by omega]

/-- **The configurations with exactly two preimages are dense** (the eventually white ones). -/
theorem dense_two_preimages : Dense {y : ℤ → Bool |
    ∃ x₀ x₁, x₀ ≠ x₁ ∧ ∀ x, evol x 1 = y ↔ x = x₀ ∨ x = x₁} :=
  (dense_eventually_const false).mono fun y hy => by
    obtain ⟨N, hN⟩ := hy
    exact ⟨_, _, extendLeft_false_ne_true y N, evol_one_eq_iff_of_eventually_white hN⟩

/-- **The configurations with exactly three preimages are dense** (the eventually black ones). So
each of the counts `1`, `2` and `3` occurs on a dense set; the count `1` on a comeager set of full
measure (`Mixing.residual_existsUnique_preimage`, `Mixing.ae_existsUnique_preimage`). -/
theorem dense_three_preimages : Dense {y : ℤ → Bool | ∃ x₀ x₁ x₂, x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂ ∧
    ∀ x, evol x 1 = y ↔ x = x₀ ∨ x = x₁ ∨ x = x₂} := by
  refine (dense_eventually_const true).mono fun y hy => ?_
  obtain ⟨N, hN⟩ := hy
  refine ⟨_, _, _, ?_, ?_, ?_, evol_one_eq_iff_of_eventually_black hN⟩
  all_goals intro h
  -- the three tails differ at `N` or at `N + 1`
  · have := congrFun h N
    rw [show extendLeft y N (third N) N = third N N from ite_eq_left le_rfl,
      show extendLeft y N (third (N + 1)) N = third (N + 1) N from ite_eq_left le_rfl] at this
    have h2 : third (N + 1) N = false := by
      simp only [third, decide_eq_false_iff_not]
      omega
    rw [h2] at this
    simp [third] at this
  · have := congrFun h N
    rw [show extendLeft y N (third N) N = third N N from ite_eq_left le_rfl,
      show extendLeft y N (third (N + 2)) N = third (N + 2) N from ite_eq_left le_rfl] at this
    have h2 : third (N + 2) N = false := by
      simp only [third, decide_eq_false_iff_not]
      omega
    rw [h2] at this
    simp [third] at this
  · have := congrFun h (N + 1)
    rw [show extendLeft y N (third (N + 1)) (N + 1) = third (N + 1) (N + 1) from
        ite_eq_left (by omega),
      show extendLeft y N (third (N + 2)) (N + 1) = third (N + 2) (N + 1) from
        ite_eq_left (by omega)] at this
    have h2 : third (N + 2) (N + 1) = false := by
      simp only [third, decide_eq_false_iff_not]
      omega
    rw [h2] at this
    simp [third] at this

/-! ### Configurations with a unique preimage -/

/-- **The word `010` pins its left neighbour**: if the image of `x` shows `0, 1, 0` at the cells
`q, q + 1, q + 2`, then `x` is black at `q - 1`. Were it white, `F(x)_q = 0` would make `x_q` and
`x_{q+1}` white, then `F(x)_{q+1} = 1` would make `x_{q+2}` black and `F(x)_{q+2} = 1`. -/
theorem eq_true_of_window {x : ℤ → Bool} {q : ℤ} (h0 : evol x 1 q = false)
    (h1 : evol x 1 (q + 1) = true) (h2 : evol x 1 (q + 2) = false) : x (q - 1) = true := by
  rw [evol_one] at h0
  rw [evol_one, show q + 1 - 1 = q by ring, show q + 1 + 1 = q + 2 by ring] at h1
  rw [evol_one, show q + 2 - 1 = q + 1 by ring] at h2
  revert h0 h1 h2
  cases x (q - 1) <;> cases x q <;> cases x (q + 1) <;> cases x (q + 2) <;>
    cases x (q + 2 + 1) <;> decide

/-- **The inverse of rule 30 looks only to the right**: if the image of `x` shows `010` at the
cells `q, q + 1, q + 2` with `p < q`, then the cell `p` of `x` is determined by the image on the
cells `p + 1, …, q + 2`. Both preimages are black at `q - 1` (`eq_true_of_window`), so the image
at `q - 1` fixes the cell `q - 2`, and left determinism runs down to `p`. -/
theorem eq_of_evol_one_eq_on_of_window {x y : ℤ → Bool} {p q : ℤ} (hpq : p < q)
    (h : ∀ j, p < j → j ≤ q + 2 → evol x 1 j = evol y 1 j)
    (h0 : evol x 1 q = false) (h1 : evol x 1 (q + 1) = true) (h2 : evol x 1 (q + 2) = false) :
    x p = y p := by
  have hx := eq_true_of_window h0 h1 h2
  have hy := eq_true_of_window (x := y) (q := q) (by rw [← h q hpq (by omega)]; exact h0)
    (by rw [← h (q + 1) (by omega) (by omega)]; exact h1)
    (by rw [← h (q + 2) (by omega) le_rfl]; exact h2)
  rcases eq_or_lt_of_le (show p ≤ q - 1 by omega) with hp | hp
  · rw [hp, hx, hy]
  have h2' : x (q - 2) = y (q - 2) := by
    have e := h (q - 1) hp (by omega)
    rw [evol_one, evol_one, show q - 1 - 1 = q - 2 by ring, hx, hy] at e
    simpa using e
  exact eq_of_evol_one_eq_on (k := q - 2) (fun j hj hj' => h j hj (by omega)) h2'
    (by rw [show q - 2 + 1 = q - 1 by ring, hx, hy]) p le_rfl (by omega)

/-- Two preimages of a configuration agree at every cell left of an occurrence of `010` in it. -/
theorem eq_of_evol_one_eq_of_window {x y : ℤ → Bool} (h : evol x 1 = evol y 1) {q : ℤ}
    (h0 : evol x 1 q = false) (h1 : evol x 1 (q + 1) = true) (h2 : evol x 1 (q + 2) = false) :
    ∀ p, p ≤ q - 1 → x p = y p := fun p hp =>
  eq_of_evol_one_eq_on_of_window (by omega) (fun j _ _ => congrFun h j) h0 h1 h2

/-- **Unique preimages**: a configuration that shows `010` arbitrarily far to the right has
exactly one preimage. -/
theorem eq_of_evol_one_eq_of_frequently {x y : ℤ → Bool} (h : evol x 1 = evol y 1)
    (hw : ∀ n : ℤ, ∃ q ≥ n,
      evol x 1 q = false ∧ evol x 1 (q + 1) = true ∧ evol x 1 (q + 2) = false) :
    x = y := by
  funext p
  obtain ⟨q, hq, h0, h1, h2⟩ := hw (p + 1)
  exact eq_of_evol_one_eq_of_window h h0 h1 h2 p (by omega)

/-! ### Left-asymptotic pairs -/

/-- Black only at `0` on the left, then `(0110)^∞` from the cell `1` on. -/
def pairL (q : ℤ) : Bool := if q ≤ 0 then decide (q = 0) else decide (q % 4 = 2 ∨ q % 4 = 3)

/-- Black only at `0` on the left, then `(1000)^∞` from the cell `1` on. -/
def pairR (q : ℤ) : Bool := if q ≤ 0 then decide (q = 0) else decide (q % 4 = 1)

theorem evol_one_pairL_eq : evol pairL 1 = evol pairR 1 := by
  funext q
  rw [evol_one, evol_one]
  rcases le_or_gt q (-1) with hq | hq
  · simp only [pairL, pairR, ite_eq_left (show q - 1 ≤ 0 by omega),
      ite_eq_left (show q ≤ 0 by omega),
      ite_eq_left (show q + 1 ≤ 0 by omega)]
  rcases (show q = 0 ∨ q = 1 ∨ 2 ≤ q by omega) with rfl | rfl | hq2
  · decide
  · decide
  · have h4 : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
    simp only [pairL, pairR, ite_eq_right (show ¬ q - 1 ≤ 0 by omega),
        ite_eq_right (show ¬ q ≤ 0 by omega),
      ite_eq_right (show ¬ q + 1 ≤ 0 by omega)]
    rcases h4 with h | h | h | h
    · rw [show (q - 1) % 4 = 3 by omega, show (q + 1) % 4 = 1 by omega, h]
      decide
    · rw [show (q - 1) % 4 = 0 by omega, show (q + 1) % 4 = 2 by omega, h]
      decide
    · rw [show (q - 1) % 4 = 1 by omega, show (q + 1) % 4 = 3 by omega, h]
      decide
    · rw [show (q - 1) % 4 = 2 by omega, show (q + 1) % 4 = 0 by omega, h]
      decide

/-- **Rule 30 is not injective on left-asymptotic configurations**: two different configurations
that agree at every cell `q ≤ 0` have the same image. -/
theorem exists_ne_left_eq :
    ∃ x y : ℤ → Bool, x ≠ y ∧ (∀ q, q ≤ 0 → x q = y q) ∧ evol x 1 = evol y 1 :=
  ⟨pairL, pairR, fun h => absurd (congrFun h 1) (by decide), fun q hq => by
    simp [pairL, pairR, hq], evol_one_pairL_eq⟩

/-- **Rule 30 is not positively expansive**: for every window `[-n, n]`, two different
configurations have orbits that agree on the window at all times. -/
theorem not_positivelyExpansive (n : ℕ) :
    ∃ x y : ℤ → Bool, x ≠ y ∧
      ∀ (t : ℕ) (p : ℤ), -(n : ℤ) ≤ p → p ≤ n → evol x t p = evol y t p := by
  obtain ⟨x, y, hne, hleft, himg⟩ := exists_ne_left_eq
  -- shift the pair `n` cells to the right
  let x' : ℤ → Bool := fun q => x (q - n)
  let y' : ℤ → Bool := fun q => y (q - n)
  have hshift : ∀ (z : ℤ → Bool) (t : ℕ) (q : ℤ),
      evol (fun q => z (q - n)) t q = evol z t (q - n) := fun z t q => by
    have := Rule30ZeroBoundaryBarriers.evol_shift_all (x := z) (x' := fun q => z (q - n))
      (d := n) (fun p => by simp) t (q - n)
    rwa [sub_add_cancel] at this
  have h1 : evol x' 1 = evol y' 1 := funext fun q => by
    rw [hshift x 1 q, hshift y 1 q, himg]
  refine ⟨x', y', fun h => hne (funext fun q => by
    have := congrFun h (q + n)
    simpa [x', y'] using this), fun t p _ hp2 => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact hleft (p - n) (by omega)
  · obtain ⟨s, rfl⟩ : ∃ s, t = 1 + s := ⟨t - 1, by omega⟩
    rw [← Rule30ZeroBoundaryBarriers.evol_restart x' 1 s p,
      ← Rule30ZeroBoundaryBarriers.evol_restart y' 1 s p]
    show evol (fun p => evol x' 1 p) s p = evol (fun p => evol y' 1 p) s p
    rw [show (fun p => evol x' 1 p) = evol y' 1 from h1]

end Rule30Equivalents.Preimages
