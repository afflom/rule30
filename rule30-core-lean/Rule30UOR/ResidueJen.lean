module
public import Rule30UOR.DiagonalCone
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # Jen's step on residue classes of the driven left half

For a boundary column `c` and a lag `Q`, the lag-`Q` defect of column `−k` of the half `Fixed.Lh c`
driven from white is `lagDefect c Q k t = Lh c (t + Q) (−k) ⊕ Lh c t (−k)`.

* `lagDefect_sideways`: left-permutivity on residue classes. The defect of column `−(k+2)` at `t` is
  the defect of column `−(k+1)` at `t + 1`, plus the defects of columns `−(k+1)` and `−k` at `t`
  gated by the OR-gate's other input. It holds for every `c`.
* `lagDefect_one_black`: black-time consistency pins column `−1` across the lag at every black time
  of a boundary that is `Q`-periodic from `S`.
* `lagDefect_two_of_btc`: under black-time consistency the defect of column `−2` is the discrete
  derivative of the defect of column `−1`: at white times the OR-gate is unsaturated and the
  transmission is linear.
* `btc_run_triangle`, `btc_black_window_pinned`: over a black run `c (a + i) = 1` (`i < k`),
  `c (a + k) = 0`, black-time consistency fixes the whole triangle `i + j ≤ k`: column `−j` at time
  `a + i` is the parity of `j` with the last entry `i + j = k` flipped: at `i = 0` the kit's word
  `Rule30DrivenLeft.alt` with its apex flipped. The finite-run form, for every consistent boundary,
  of the pinning behind the kit's `ones_fails` (driver `≡ 1`, `alt_fixed`).
* `lagAgree_window`, `lagDefect_edge`, `unmasked_in_window`, `white_defect_in_window`: residue-masked
  Jen. Lag agreement of column `−1` on a mask propagates leftward only through full windows, and the
  edge is a lag defect on the front `t = k − Q`, so every window `[k + 1 − Q, 2k + 1 − Q]` with
  `k + 1 ≥ S + Q` holds a lag defect of column `−1` at a white time of `c`. The mirror, in the driven
  half, of the kit's masked Jen window. It is a window, not a time.

None of these is a route: they locate where black-time consistency stops (at the white residues).
-/

@[expose] public section

namespace Rule30UOR.ResidueJen

open Rule30UOR.Core Rule30UOR.EdgeParity Rule30UOR.Fixed Rule30UOR.DiagonalCone

/-- Lag-`Q` defect of column `−k` of the driven half. Column `0` is `c` (`Lh_col0`). -/
def lagDefect (c : Nat → Bool) (Q k t : Nat) : Bool :=
  bxor (Lh c (t + Q) (-(k : Int))) (Lh c t (-(k : Int)))

/-- The boundary column is `Q`-periodic from `S`. -/
def BoundaryPeriodic (c : Nat → Bool) (S Q : Nat) : Prop := ∀ t, S ≤ t → c (t + Q) = c t

/-- The boundary column is black on `[s, s + k)`. -/
def BlackRun (c : Nat → Bool) (s k : Nat) : Prop := ∀ i, i < k → c (s + i) = true

/-! ## Left-permutivity on residue classes -/

/-- Left-permutive inversion inside the driven half (the `Lh` form of `Rule30DrivenLeft.L_left`). -/
theorem Lh_left (c : Nat → Bool) (t : Nat) (p : Int) (hp : p < 0) :
    Lh c t (p - 1) = bxor (Lh c (t + 1) p) (Lh c t p || Lh c t (p + 1)) := by
  rw [Lh_succ_neg c t p hp]
  cases Lh c t (p - 1) <;> cases Lh c t p <;> cases Lh c t (p + 1) <;> rfl

/-- Left-permutive inversion at column `−(k+2)`. -/
theorem Lh_left_nat (c : Nat → Bool) (t k : Nat) :
    Lh c t (-((k + 2 : Nat) : Int)) =
      bxor (Lh c (t + 1) (-((k + 1 : Nat) : Int))) (Lh c t (-((k + 1 : Nat) : Int)) || Lh c t (-(k : Int))) := by
  have h := Lh_left c t (-((k + 1 : Nat) : Int)) (by cfomega)
  rw [show -((k + 1 : Nat) : Int) - 1 = -((k + 2 : Nat) : Int) by cfomega,
    show -((k + 1 : Nat) : Int) + 1 = -(k : Int) by cfomega] at h
  exact h

/-- The OR-gate on two rows: `(b ∨ c) ⊕ (b' ∨ c') = ((b ⊕ b') ∧ ¬c) ⊕ ((c ⊕ c') ∧ ¬b')`. -/
theorem or_lag (a1 b1 c1 a2 b2 c2 : Bool) :
    bxor (bxor a1 (b1 || c1)) (bxor a2 (b2 || c2)) =
      bxor (bxor (bxor a1 a2) (bxor b1 b2 && !c1)) (bxor c1 c2 && !b2) := by
  cases a1 <;> cases b1 <;> cases c1 <;> cases a2 <;> cases b2 <;> cases c2 <;> rfl

/-- **The sideways lag-defect law.** For every boundary `c`. -/
theorem lagDefect_sideways (c : Nat → Bool) (Q k t : Nat) :
    lagDefect c Q (k + 2) t =
      bxor (bxor (lagDefect c Q (k + 1) (t + 1))
          (lagDefect c Q (k + 1) t && !Lh c (t + Q) (-(k : Int))))
        (lagDefect c Q k t && !Lh c t (-((k + 1 : Nat) : Int))) := by
  unfold lagDefect
  rw [Lh_left_nat c (t + Q) k, Lh_left_nat c t k, show t + Q + 1 = t + 1 + Q by cfomega]
  exact or_lag _ _ _ _ _ _

/-- Column `0` has no lag defect where `c` is periodic. -/
theorem lagDefect_zero (c : Nat → Bool) (S Q : Nat) (hc : BoundaryPeriodic c S Q) (t : Nat)
    (ht : S ≤ t) : lagDefect c Q 0 t = false := by
  unfold lagDefect
  rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0, Lh_col0, hc t ht]
  cases c t <;> rfl

/-! ## Black-time consistency on residue classes -/

/-- **Black-time consistency pins column `−1` on the black residues.** -/
theorem lagDefect_one_black (c : Nat → Bool) (S Q : Nat) (hb : BlackTimeConsistent c)
    (hc : BoundaryPeriodic c S Q) (t : Nat) (ht : S ≤ t) (hct : c t = true) :
    lagDefect c Q 1 t = false := by
  unfold lagDefect
  have h1 : c (t + Q) = true := by rw [hc t ht]; exact hct
  have h2 := hb t hct
  have h3 := hb (t + Q) h1
  have h4 : c (t + Q + 1) = c (t + 1) := by
    rw [show t + Q + 1 = t + 1 + Q by cfomega]
    exact hc (t + 1) (by cfomega)
  have e1 : Lh c t (-1) = !c (t + 1) := by rw [h2]; cases Lh c t (-1) <;> rfl
  have e2 : Lh c (t + Q) (-1) = !c (t + Q + 1) := by rw [h3]; cases Lh c (t + Q) (-1) <;> rfl
  rw [show (-((1 : Nat) : Int)) = -1 by cfomega, e1, e2, h4]
  cases c (t + 1) <;> rfl

/-- **Under black-time consistency the defect of column `−2` is the discrete derivative of the
defect of column `−1`.** -/
theorem lagDefect_two_of_btc (c : Nat → Bool) (S Q : Nat) (hb : BlackTimeConsistent c)
    (hc : BoundaryPeriodic c S Q) (t : Nat) (ht : S ≤ t) :
    lagDefect c Q 2 t = bxor (lagDefect c Q 1 (t + 1)) (lagDefect c Q 1 t) := by
  have hs : lagDefect c Q 2 t =
      bxor (bxor (lagDefect c Q 1 (t + 1)) (lagDefect c Q 1 t && !Lh c (t + Q) (-((0 : Nat) : Int))))
        (lagDefect c Q 0 t && !Lh c t (-((1 : Nat) : Int))) := lagDefect_sideways c Q 0 t
  have hq : Lh c (t + Q) (-((0 : Nat) : Int)) = c t := by
    rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0, hc t ht]
  rw [hq, lagDefect_zero c S Q hc t ht] at hs
  rw [hs]
  cases hct : c t with
  | false => cases lagDefect c Q 1 (t + 1) <;> cases lagDefect c Q 1 t <;> rfl
  | true =>
    rw [lagDefect_one_black c S Q hb hc t ht hct]
    cases lagDefect c Q 1 (t + 1) <;> rfl

/-! ## The triangle over a black run -/

theorem even_succ (j : Nat) : decide ((j + 1) % 2 = 0) = !decide (j % 2 = 0) := by
  cases h : decide (j % 2 = 0) with
  | false =>
    have h1 : ¬ (j % 2 = 0) := of_decide_eq_false h
    exact decide_eq_true (by cfomega)
  | true =>
    have h1 : j % 2 = 0 := of_decide_eq_true h
    exact decide_eq_false (by cfomega)

theorem even_eq_not_timeParity (j : Nat) : decide (j % 2 = 0) = !timeParity j := by
  unfold timeParity
  cases h : decide (j % 2 = 0) with
  | false =>
    have h1 : ¬ (j % 2 = 0) := of_decide_eq_false h
    rw [decide_eq_true (by cfomega : j % 2 = 1)]
    rfl
  | true =>
    have h1 : j % 2 = 0 := of_decide_eq_true h
    rw [decide_eq_false (by cfomega : ¬ (j % 2 = 1))]
    rfl

theorem even_add_two (j : Nat) : decide ((j + 2) % 2 = 0) = decide (j % 2 = 0) := by
  rw [show j + 2 = j + 1 + 1 by cfomega, even_succ (j + 1), even_succ j]
  cases decide (j % 2 = 0) <;> rfl

/-- **The triangle over a black run is pinned.** Under black-time consistency, over a black run
`[a, a + k)` ending white at `a + k`, column `−j` at time `a + i` (`i + j ≤ k`) is the parity of `j`,
flipped on the last entry `i + j = k`. -/
theorem btc_run_triangle (c : Nat → Bool) (hb : BlackTimeConsistent c) (a k : Nat)
    (hrun : BlackRun c a k) (hend : c (a + k) = false) :
    ∀ j i, i + j ≤ k → Lh c (a + i) (-(j : Int)) = bxor (decide (j % 2 = 0)) (decide (i + j = k)) := by
  have base0 : ∀ i, i + 0 ≤ k →
      Lh c (a + i) (-((0 : Nat) : Int)) = bxor (decide (0 % 2 = 0)) (decide (i + 0 = k)) := by
    intro i hi
    rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0, decide_eq_true (by cfomega : 0 % 2 = 0)]
    rcases Nat.lt_or_ge i k with h | h
    · rw [hrun i h, decide_eq_false (by cfomega : ¬ (i + 0 = k))]; rfl
    · rw [show a + i = a + k by cfomega, hend, decide_eq_true (by cfomega : i + 0 = k)]; rfl
  have base1 : ∀ i, i + 1 ≤ k →
      Lh c (a + i) (-((1 : Nat) : Int)) = bxor (decide (1 % 2 = 0)) (decide (i + 1 = k)) := by
    intro i hi
    have hn := hb (a + i) (hrun i (by cfomega))
    have e : Lh c (a + i) (-1) = !c (a + i + 1) := by rw [hn]; cases Lh c (a + i) (-1) <;> rfl
    rw [show (-((1 : Nat) : Int)) = -1 by cfomega, decide_eq_false (by cfomega : ¬ (1 % 2 = 0)), e]
    rcases Nat.lt_or_ge (i + 1) k with h | h
    · rw [show a + i + 1 = a + (i + 1) by cfomega, hrun (i + 1) h,
        decide_eq_false (by cfomega : ¬ (i + 1 = k))]; rfl
    · rw [show a + i + 1 = a + k by cfomega, hend, decide_eq_true (by cfomega : i + 1 = k)]; rfl
  have pair : ∀ j,
      (∀ i, i + j ≤ k → Lh c (a + i) (-(j : Int)) = bxor (decide (j % 2 = 0)) (decide (i + j = k))) ∧
      (∀ i, i + (j + 1) ≤ k → Lh c (a + i) (-((j + 1 : Nat) : Int)) =
        bxor (decide ((j + 1) % 2 = 0)) (decide (i + (j + 1) = k))) := by
    intro j
    induction j with
    | zero => exact ⟨base0, base1⟩
    | succ j ih =>
      refine ⟨ih.2, fun i hi => ?_⟩
      have hl : Lh c (a + i) (-((j + 1 + 1 : Nat) : Int)) = Lh c (a + i) (-((j + 2 : Nat) : Int)) := rfl
      have hd : decide ((j + 1 + 1) % 2 = 0) = decide ((j + 2) % 2 = 0) := rfl
      rw [hl, hd, Lh_left_nat c (a + i) j, show a + i + 1 = a + (i + 1) by cfomega,
        ih.2 (i + 1) (by cfomega), ih.2 i (by cfomega), ih.1 i (by cfomega),
        decide_eq_false (by cfomega : ¬ (i + (j + 1) = k)), decide_eq_false (by cfomega : ¬ (i + j = k)),
        show i + 1 + (j + 1) = i + (j + 1 + 1) by cfomega, even_add_two j, even_succ j]
      cases decide (j % 2 = 0) <;> cases decide (i + (j + 1 + 1) = k) <;> rfl
  intro j i hij
  exact (pair j).1 i hij

/-- **The row at the start of a black run is pinned**: the kit's `alt` word with its apex flipped. -/
theorem btc_black_window_pinned (c : Nat → Bool) (hb : BlackTimeConsistent c) (a k : Nat)
    (hrun : BlackRun c a k) (hend : c (a + k) = false) :
    ∀ j, 1 ≤ j → j ≤ k → Lh c a (-(j : Int)) = bxor (decide (j % 2 = 0)) (decide (j = k)) := by
  intro j _ hjk
  have h := btc_run_triangle c hb a k hrun hend j 0 (by cfomega)
  rw [Nat.add_zero, Nat.zero_add] at h
  exact h

/-! ## Residue-masked Jen: lag agreement propagates only through full windows -/

/-- The edge of the half driven from white: white beyond column `−u` at time `u`, black at `−u`. -/
theorem Lh_edge (c : Nat → Bool) (h0 : c 0 = true) : ∀ u : Nat,
    (∀ p : Int, p < -(u : Int) → Lh c u p = false) ∧ Lh c u (-(u : Int)) = true := by
  intro u
  induction u with
  | zero =>
    refine ⟨fun p hp => Lh_zero_neg c p (by cfomega), ?_⟩
    rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0, h0]
  | succ u ih =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [Lh_succ_neg c u p (by cfomega), ih.1 (p - 1) (by cfomega), ih.1 p (by cfomega),
        ih.1 (p + 1) (by cfomega)]
      rfl
    · rw [Lh_succ_neg c u (-((u + 1 : Nat) : Int)) (by cfomega),
        ih.1 (-((u + 1 : Nat) : Int) - 1) (by cfomega), ih.1 (-((u + 1 : Nat) : Int)) (by cfomega),
        show -((u + 1 : Nat) : Int) + 1 = -(u : Int) by cfomega, ih.2]
      rfl

/-- **The edge is a lag defect on the front `t = k − Q`.** -/
theorem lagDefect_edge (c : Nat → Bool) (h0 : c 0 = true) (Q k : Nat) (hQ : 0 < Q) (hk : Q ≤ k) :
    lagDefect c Q k (k - Q) = true := by
  unfold lagDefect
  rw [show k - Q + Q = k by cfomega, (Lh_edge c h0 k).2,
    (Lh_edge c h0 (k - Q)).1 (-(k : Int)) (by cfomega)]
  rfl

/-- **Residue-masked Jen.** If column `−1` has no lag defect at the masked times from `S`, column
`−(k+1)` has none at `t ≥ S` whenever the mask covers the whole window `[t, t + k]`. -/
theorem lagAgree_window (c : Nat → Bool) (S Q : Nat) (hc : BoundaryPeriodic c S Q) (m : Nat → Bool)
    (hm : ∀ t, S ≤ t → m t = true → lagDefect c Q 1 t = false) :
    ∀ k t, S ≤ t → (∀ i, i ≤ k → m (t + i) = true) → lagDefect c Q (k + 1) t = false := by
  have pair : ∀ k,
      (∀ t, S ≤ t → (∀ i, i ≤ k → m (t + i) = true) → lagDefect c Q k t = false) ∧
      (∀ t, S ≤ t → (∀ i, i ≤ k → m (t + i) = true) → lagDefect c Q (k + 1) t = false) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t ht _ => lagDefect_zero c S Q hc t ht, fun t ht hw => ?_⟩
      have h := hw 0 (Nat.le_refl 0)
      rw [Nat.add_zero] at h
      exact hm t ht h
    | succ k ih =>
      refine ⟨fun t ht hw => ih.2 t ht (fun i hi => hw i (by cfomega)), fun t ht hw => ?_⟩
      have hs := lagDefect_sideways c Q k t
      have h1 : lagDefect c Q (k + 1) (t + 1) = false :=
        ih.2 (t + 1) (by cfomega) (fun i hi => by
          rw [show t + 1 + i = t + (i + 1) by cfomega]
          exact hw (i + 1) (by cfomega))
      rw [h1, ih.2 t ht (fun i hi => hw i (by cfomega)), ih.1 t ht (fun i hi => hw i (by cfomega))] at hs
      rw [show k + 1 + 1 = k + 2 by cfomega, hs]
      rfl
  intro k t ht hw
  exact (pair k).2 t ht hw

/-- A search of `[0, n]` for a white value, by recursion on `n`. -/
theorem search_le (f : Nat → Bool) : ∀ n, (∃ i, i ≤ n ∧ f i = false) ∨ (∀ i, i ≤ n → f i = true) := by
  intro n
  induction n with
  | zero =>
    cases h : f 0 with
    | false => exact Or.inl ⟨0, Nat.le_refl 0, h⟩
    | true => exact Or.inr (fun i hi => by rw [show i = 0 by cfomega]; exact h)
  | succ n ih =>
    cases ih with
    | inl hl =>
      obtain ⟨i, hi, hf⟩ := hl
      exact Or.inl ⟨i, by cfomega, hf⟩
    | inr hr =>
      cases h : f (n + 1) with
      | false => exact Or.inl ⟨n + 1, Nat.le_refl _, h⟩
      | true =>
        refine Or.inr (fun i hi => ?_)
        rcases Nat.lt_or_ge i (n + 1) with hlt | hge
        · exact hr i (by cfomega)
        · rw [show i = n + 1 by cfomega]; exact h

/-- **The front never advances**: every window `[k + 1 − Q, 2k + 1 − Q]` with `k + 1 ≥ S + Q`
contains an unmasked time. -/
theorem unmasked_in_window (c : Nat → Bool) (h0 : c 0 = true) (S Q : Nat) (hQ : 0 < Q)
    (hc : BoundaryPeriodic c S Q) (m : Nat → Bool)
    (hm : ∀ t, S ≤ t → m t = true → lagDefect c Q 1 t = false) :
    ∀ k, S + Q ≤ k + 1 → ∃ i, i ≤ k ∧ m (k + 1 - Q + i) = false := by
  intro k hk
  cases search_le (fun i => m (k + 1 - Q + i)) k with
  | inl hl => exact hl
  | inr hr =>
    have hd := lagAgree_window c S Q hc m hm k (k + 1 - Q) (by cfomega) hr
    rw [lagDefect_edge c h0 Q (k + 1) hQ (by cfomega)] at hd
    exact absurd hd (by decide)

/-- **The exact white-time residue statement.** Under black-time consistency and a period `Q` from
`S`, every window `[k + 1 − Q, 2k + 1 − Q]` with `k + 1 ≥ S + Q` holds a lag-`Q` defect of column
`−1` at a white time of `c`. -/
theorem white_defect_in_window (c : Nat → Bool) (h0 : c 0 = true) (S Q : Nat) (hQ : 0 < Q)
    (hc : BoundaryPeriodic c S Q) (hb : BlackTimeConsistent c) :
    ∀ k, S + Q ≤ k + 1 →
      ∃ i, i ≤ k ∧ c (k + 1 - Q + i) = false ∧ lagDefect c Q 1 (k + 1 - Q + i) = true := by
  intro k hk
  have hm : ∀ t, S ≤ t → (fun u => !lagDefect c Q 1 u) t = true → lagDefect c Q 1 t = false := by
    intro t _ h
    have h2 : (!lagDefect c Q 1 t) = true := h
    cases e : lagDefect c Q 1 t with
    | false => rfl
    | true => rw [e] at h2; exact absurd h2 (by decide)
  obtain ⟨i, hi, hmi⟩ := unmasked_in_window c h0 S Q hQ hc (fun u => !lagDefect c Q 1 u) hm k hk
  have hmi2 : (!lagDefect c Q 1 (k + 1 - Q + i)) = false := hmi
  have hd : lagDefect c Q 1 (k + 1 - Q + i) = true := by
    cases e : lagDefect c Q 1 (k + 1 - Q + i) with
    | true => rfl
    | false => rw [e] at hmi2; exact absurd hmi2 (by decide)
  refine ⟨i, hi, ?_, hd⟩
  cases e : c (k + 1 - Q + i) with
  | false => rfl
  | true =>
    rw [lagDefect_one_black c S Q hb hc (k + 1 - Q + i) (by cfomega) e] at hd
    exact absurd hd (by decide)

/-! ## First-order statements -/

section FirstOrder

/-- Column `−j` of the half driven by `c` from white, at time `t`. -/
def leftColumn (c : Nat → Bool) (j t : Nat) : Bool := Lh c t (-(j : Int))

/-- For every boundary, the sideways lag-defect law. -/
def LagDefectSideways : Prop :=
  ∀ (c : Nat → Bool) (Q k t : Nat), lagDefect c Q (k + 2) t =
    bxor (bxor (lagDefect c Q (k + 1) (t + 1)) (lagDefect c Q (k + 1) t && !leftColumn c k (t + Q)))
      (lagDefect c Q k t && !leftColumn c (k + 1) t)

/-- **The sideways lag-defect law.** -/
theorem lagDefectSideways : LagDefectSideways := fun c Q k t => lagDefect_sideways c Q k t

/-- Black-time consistency pins column `−1` across the lag at every black time of the period. -/
def BlackResidueLagAgree : Prop :=
  ∀ (c : Nat → Bool) (S Q t : Nat), BlackTimeConsistent c → BoundaryPeriodic c S Q → S ≤ t →
    c t = true → lagDefect c Q 1 t = false

/-- **Black-time consistency pins column `−1` on the black residues.** -/
theorem blackResidueLagAgree : BlackResidueLagAgree :=
  fun c S Q t hb hc ht hct => lagDefect_one_black c S Q hb hc t ht hct

/-- Under black-time consistency the lag defect of column `−2` is the discrete derivative of the
lag defect of column `−1`. -/
def LagDefectDerivative : Prop :=
  ∀ (c : Nat → Bool) (S Q t : Nat), BlackTimeConsistent c → BoundaryPeriodic c S Q → S ≤ t →
    lagDefect c Q 2 t = bxor (lagDefect c Q 1 (t + 1)) (lagDefect c Q 1 t)

/-- **The column `−2` defect is the derivative of the column `−1` defect.** -/
theorem lagDefectDerivative : LagDefectDerivative :=
  fun c S Q t hb hc ht => lagDefect_two_of_btc c S Q hb hc t ht

/-- Inside the triangle over a black run, column `−j` is the complement of the parity of `j`. -/
def BlackRunTriangle : Prop :=
  ∀ (c : Nat → Bool) (s k j i : Nat), BlackTimeConsistent c → BlackRun c s k → c (s + k) = false →
    i + j < k → leftColumn c j (s + i) = !timeParity j

/-- **The triangle over a black run is pinned.** -/
theorem blackRunTriangle : BlackRunTriangle := by
  intro c s k j i hb hrun hend hij
  have h := btc_run_triangle c hb s k hrun hend j i (by cfomega)
  rw [decide_eq_false (by cfomega : ¬ (i + j = k)), even_eq_not_timeParity] at h
  show Lh c (s + i) (-(j : Int)) = !timeParity j
  rw [h]
  cases timeParity j <;> rfl

/-- On the hypotenuse `i + j = k` of the triangle over a black run, column `−j` is the parity
of `j`. -/
def BlackRunHypotenuse : Prop :=
  ∀ (c : Nat → Bool) (s k j i : Nat), BlackTimeConsistent c → BlackRun c s k → c (s + k) = false →
    i + j = k → leftColumn c j (s + i) = timeParity j

/-- **The hypotenuse of the triangle over a black run is pinned.** -/
theorem blackRunHypotenuse : BlackRunHypotenuse := by
  intro c s k j i hb hrun hend hij
  have h := btc_run_triangle c hb s k hrun hend j i (by cfomega)
  rw [decide_eq_true hij, even_eq_not_timeParity] at h
  show Lh c (s + i) (-(j : Int)) = timeParity j
  rw [h]
  cases timeParity j <;> rfl

/-- The edge of the half driven from white is a lag defect on the front `t = k − Q`. -/
def LagDefectEdge : Prop :=
  ∀ (c : Nat → Bool) (Q k : Nat), c 0 = true → 0 < Q → Q ≤ k → lagDefect c Q k (k - Q) = true

/-- **The edge is a lag defect.** -/
theorem lagDefectEdge : LagDefectEdge := fun c Q k h0 hQ hk => lagDefect_edge c h0 Q k hQ hk

/-- Column `−1` has a lag-`Q` defect at a white time of `c` in `[u, u + k]`. -/
def WhiteLagDefectWithin (c : Nat → Bool) (Q u k : Nat) : Prop :=
  ∃ i, i ≤ k ∧ c (u + i) = false ∧ lagDefect c Q 1 (u + i) = true

/-- Under black-time consistency and a period `Q` from `S`, every window `[k + 1 − Q, 2k + 1 − Q]`
with `k + 1 ≥ S + Q` holds a lag defect of column `−1` at a white time of `c`. -/
def WhiteDefectInWindow : Prop :=
  ∀ (c : Nat → Bool) (S Q k : Nat), c 0 = true → 0 < Q → BoundaryPeriodic c S Q →
    BlackTimeConsistent c → S + Q ≤ k + 1 → WhiteLagDefectWithin c Q (k + 1 - Q) k

/-- **Every window holds a white-time lag defect of column `−1`.** -/
theorem whiteDefectInWindow : WhiteDefectInWindow :=
  fun c S Q k h0 hQ hc hb hk => white_defect_in_window c h0 S Q hQ hc hb k hk

end FirstOrder

end Rule30UOR.ResidueJen
