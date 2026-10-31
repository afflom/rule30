module

public import Rule30UOR.Intent

/-!
# The zero-state recompiles infinitely often

The zero-state `E` (`Rule30Intent`) is the eventual pattern of every left diagonal. Its diagonal
`j + 2` is computed from diagonals `j` and `j + 1` (`E_step`), and conversely diagonal `j` is
recovered from diagonals `j + 1` and `j + 2` (`E_back`): the depth step is reversible. A diagonal
that is identically white (a *zero diagonal*) is the only place where this step forgets nothing
yet determines nothing: behind it the next diagonal only accumulates its input, and its period can
double. These are the points where the zero-state recompiles.

* `E_per`: every zero-state diagonal is purely periodic, with period `2 ^ j`.
* `period_prop`: behind a nonzero diagonal, a common period of two consecutive diagonals passes to
  the next one.
* `fwd_det`, `bwd_det`: equal consecutive pairs of diagonals propagate forward (past nonzero
  diagonals) and backward (always).
* `infinitely_many_zero_diagonals`: **for every `N` there is a zero diagonal at depth `≥ N`.**
  Otherwise all diagonals from `N` on share one period `P`, a pair of consecutive diagonals repeats
  (pigeonhole over `2 ^ (2P)` pairs), reversibility makes the whole zero-state periodic in depth,
  and the zero diagonal at depth `2` recurs beyond `N`.
-/

@[expose] public section

namespace Rule30UOR.ZeroDiagonals

open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30UOR.Intent

/-- Two runs of one one-bit recurrence agree from the step after a time where the transition
forgets its state. -/
theorem agree_after_reset {x y : Nat → Bool} {F : Nat → Bool → Bool} {T s : Nat}
    (hx : ∀ t, T ≤ t → x (t + 1) = F t (x t)) (hy : ∀ t, T ≤ t → y (t + 1) = F t (y t))
    (hs : T ≤ s) (hc : F s true = F s false) : ∀ t, s < t → x t = y t := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rw [hx t (by omega), hy t (by omega)]
    rcases Nat.lt_or_ge s t with h | h
    · rw [ih h]
    · have e : t = s := by omega
      subst e
      cases x t <;> cases y t <;> simp [hc]

/-! ### Periodicity and reversibility of the zero-state -/

theorem E_per (j t : Nat) : E j (t + 2 ^ j) = E j t := by
  unfold E
  have hX : 0 < 2 ^ j := Nat.two_pow_pos j
  have h1 : bound j ≤ bound j * 2 ^ j := Nat.le_mul_of_pos_right _ hX
  have hs := settle_le_bound j
  rw [show t + 2 ^ j + bound j * 2 ^ j = (t + bound j * 2 ^ j) + 2 ^ j by omega,
    settle_spec j _ (by omega)]

theorem E_per_mul (j : Nat) : ∀ k t, E j (t + k * 2 ^ j) = E j t := by
  intro k
  induction k with
  | zero => intro t; simp
  | succ k ih =>
    intro t
    rw [show t + (k + 1) * 2 ^ j = (t + k * 2 ^ j) + 2 ^ j by rw [Nat.succ_mul]; omega, E_per, ih]

/-- Reversibility: diagonal `j` is recovered from diagonals `j + 1` and `j + 2`. -/
theorem E_back (j t : Nat) : E j t = xor (E (j + 2) (t + 1)) (E (j + 1) t || E (j + 2) t) := by
  rw [E_step]; cases E j t <;> cases (E (j + 1) t || E (j + 2) t) <;> rfl

/-- Two functions with periods `P` and `Q` that agree from some time on agree everywhere. -/
theorem eq_of_eventually {x y : Nat → Bool} {P Q s : Nat} (hP : 0 < P) (hQ : 0 < Q)
    (hx : ∀ t, x (t + P) = x t) (hy : ∀ t, y (t + Q) = y t) (h : ∀ t, s < t → x t = y t) :
    ∀ t, x t = y t := by
  have hxm : ∀ k t, x (t + k * (P * Q)) = x t := by
    intro k; induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have hxq : ∀ m t, x (t + m * P) = x t := by
        intro m; induction m with
        | zero => intro t; simp
        | succ m ihm => intro t; rw [show t + (m + 1) * P = (t + m * P) + P by rw [Nat.succ_mul]; omega, hx, ihm]
      rw [show t + (k + 1) * (P * Q) = (t + k * (P * Q)) + Q * P by rw [Nat.succ_mul, Nat.mul_comm P Q]; omega,
        hxq Q, ih]
  have hym : ∀ k t, y (t + k * (P * Q)) = y t := by
    intro k; induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have hyq : ∀ m t, y (t + m * Q) = y t := by
        intro m; induction m with
        | zero => intro t; simp
        | succ m ihm => intro t; rw [show t + (m + 1) * Q = (t + m * Q) + Q by rw [Nat.succ_mul]; omega, hy, ihm]
      rw [show t + (k + 1) * (P * Q) = (t + k * (P * Q)) + P * Q by rw [Nat.succ_mul]; omega, hyq P, ih]
  intro t
  have hPQ : 1 ≤ P * Q := Nat.mul_pos hP hQ
  have hk : s < t + (s + 1) * (P * Q) := by
    have : s + 1 ≤ (s + 1) * (P * Q) := Nat.le_mul_of_pos_right _ hPQ
    omega
  rw [← hxm (s + 1) t, ← hym (s + 1) t, h _ hk]

/-- **Period propagation.** Behind a nonzero diagonal, a common period of diagonals `j` and `j + 1`
is a period of diagonal `j + 2`. -/
theorem period_prop {P j : Nat} (hP0 : 0 < P) (hP : ∀ t, E j (t + P) = E j t)
    (hP1 : ∀ t, E (j + 1) (t + P) = E (j + 1) t) (hnz : ∃ s, E (j + 1) s = true) :
    ∀ t, E (j + 2) (t + P) = E (j + 2) t := by
  obtain ⟨s, hs⟩ := hnz
  have agree := agree_after_reset (x := fun t => E (j + 2) (t + P)) (y := fun t => E (j + 2) t)
    (F := fun t b => xor (E j t) (E (j + 1) t || b)) (T := 0)
    (fun t _ => by
      show E (j + 2) (t + 1 + P) = _
      rw [show t + 1 + P = (t + P) + 1 by omega, E_step, hP, hP1])
    (fun t _ => E_step j t) (Nat.zero_le s) (by simp [hs])
  exact eq_of_eventually (P := 2 ^ (j + 2)) (Q := 2 ^ (j + 2)) (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    (fun t => by show E (j + 2) (t + 2 ^ (j + 2) + P) = E (j + 2) (t + P)
                 rw [show t + 2 ^ (j + 2) + P = (t + P) + 2 ^ (j + 2) by omega, E_per])
    (fun t => E_per (j + 2) t) agree

/-- **Forward determinism.** Equal consecutive pairs, the second nonzero, give equal next diagonals. -/
theorem fwd_det {a b : Nat} (h0 : ∀ t, E a t = E b t) (h1 : ∀ t, E (a + 1) t = E (b + 1) t)
    (hnz : ∃ s, E (a + 1) s = true) : ∀ t, E (a + 2) t = E (b + 2) t := by
  obtain ⟨s, hs⟩ := hnz
  have agree := agree_after_reset (x := fun t => E (a + 2) t) (y := fun t => E (b + 2) t)
    (F := fun t c => xor (E a t) (E (a + 1) t || c)) (T := 0)
    (fun t _ => E_step a t)
    (fun t _ => by show E (b + 2) (t + 1) = _; rw [E_step, h0, h1])
    (Nat.zero_le s) (by simp [hs])
  exact eq_of_eventually (Nat.two_pow_pos (a + 2)) (Nat.two_pow_pos (b + 2)) (E_per _) (E_per _) agree

/-- **Backward determinism.** -/
theorem bwd_det {a b : Nat} (h1 : ∀ t, E (a + 1) t = E (b + 1) t) (h2 : ∀ t, E (a + 2) t = E (b + 2) t) :
    ∀ t, E a t = E b t := by
  intro t; rw [E_back a t, E_back b t, h1, h2, h2]

/-! ### Depth 2 is a zero diagonal -/

theorem D2_late (s : Nat) : D 2 (s + 2) = false := by
  rw [show s + 2 = (s + 1) + 1 by omega, D_step 0 (s + 1), D_zero, D_one]; rfl

theorem settle_two_pos : 1 ≤ settle 2 := by
  rcases Nat.eq_zero_or_pos (settle 2) with h | h
  · have e := settle_spec 2 1 (by omega)
    rw [show (1 : Nat) + 2 ^ 2 = 3 + 2 by rfl, D2_late] at e
    have h1 : D 2 1 = true := by rw [show (1 : Nat) = 0 + 1 by rfl, D_step 0 0]; decide
    rw [h1] at e; exact absurd e (by decide)
  · exact h

theorem E_two (t : Nat) : E 2 t = false := by
  unfold E
  have hb : 1 ≤ bound 2 := Nat.le_trans settle_two_pos (settle_le_bound 2)
  obtain ⟨s, hs⟩ : ∃ s, t + bound 2 * 2 ^ 2 = s + 2 := ⟨t + bound 2 * 4 - 2, by
    simp only [show (2 : Nat) ^ 2 = 4 by rfl]; omega⟩
  rw [hs]; exact D2_late s

/-! ### Infinitely many zero diagonals -/

/-- The pair of diagonals `(j, j+1)` on one period window, as a list. -/
noncomputable def pairList (P j : Nat) : List Bool :=
  (List.range P).map (fun t => E j t) ++ (List.range P).map (fun t => E (j + 1) t)

theorem pairList_length (P j : Nat) : (pairList P j).length = 2 * P := by
  simp [pairList]; omega

theorem per_mul_gen {f : Nat → Bool} {P : Nat} (hf : ∀ t, f (t + P) = f t) : ∀ k s, f (s + k * P) = f s := by
  intro k; induction k with
  | zero => intro s; simp
  | succ k ih => intro s; rw [show s + (k + 1) * P = (s + k * P) + P by rw [Nat.succ_mul]; omega, hf, ih]

theorem reduce_mod {f : Nat → Bool} {P : Nat} (hf : ∀ t, f (t + P) = f t) (t : Nat) : f t = f (t % P) := by
  have := per_mul_gen hf (t / P) (t % P)
  rw [show t % P + t / P * P = t by rw [Nat.mul_comm]; exact Nat.mod_add_div t P] at this
  exact this

theorem eq_of_range {f g : Nat → Bool} {P : Nat} (hP0 : 0 < P) (hf : ∀ t, f (t + P) = f t)
    (hg : ∀ t, g (t + P) = g t) (h : (List.range P).map f = (List.range P).map g) : ∀ t, f t = g t := by
  have hr := List.map_inj_left.1 h
  intro t
  rw [reduce_mod hf t, reduce_mod hg t]
  exact hr _ (List.mem_range.2 (Nat.mod_lt _ hP0))

theorem eq_of_pairList {P a b : Nat} (hP0 : 0 < P) (ha0 : ∀ t, E a (t + P) = E a t)
    (ha1 : ∀ t, E (a + 1) (t + P) = E (a + 1) t) (hb0 : ∀ t, E b (t + P) = E b t)
    (hb1 : ∀ t, E (b + 1) (t + P) = E (b + 1) t) (h : pairList P a = pairList P b) :
    (∀ t, E a t = E b t) ∧ (∀ t, E (a + 1) t = E (b + 1) t) := by
  unfold pairList at h
  have hl := List.append_inj h (by simp)
  exact ⟨eq_of_range hP0 ha0 hb0 hl.1, eq_of_range hP0 ha1 hb1 hl.2⟩

/-- A diagonal is identically white exactly when one period of it is. -/
theorem zero_diag_iff_bounded (z : Nat) :
    (∀ t, E z t = false) ↔ ∀ t, t < 2 ^ z → E z t = false := by
  constructor
  · exact fun h t _ => h t
  · intro h t
    rw [reduce_mod (E_per z) t]
    exact h _ (Nat.mod_lt _ (Nat.two_pow_pos z))

instance (z : Nat) : Decidable (∀ t, E z t = false) :=
  decidable_of_iff _ (zero_diag_iff_bounded z).symm

/-- A diagonal that is not identically white has a black cell within one period. -/
theorem nonzero_witness (z : Nat) (h : ¬ ∀ t, E z t = false) : ∃ s, E z s = true := by
  have hw : ∃ t, t < 2 ^ z ∧ E z t = true := by
    refine Decidable.byContradiction fun hn => h ?_
    rw [zero_diag_iff_bounded]
    intro t ht
    cases hE : E z t
    · rfl
    · exact absurd ⟨t, ht, hE⟩ hn
  obtain ⟨t, -, ht⟩ := hw
  exact ⟨t, ht⟩

/-- A black cell somewhere on diagonal `z` is decided by one period. -/
instance (z : Nat) : Decidable (∃ s, E z s = true) :=
  decidable_of_iff (¬ ∀ t, E z t = false)
    ⟨nonzero_witness z, fun ⟨s, hs⟩ hz => by rw [hz s] at hs; exact Bool.false_ne_true hs⟩

/-- The depth by which a zero diagonal at depth at least `N` is found. -/
def zeroDiagBound (N : Nat) : Nat := N + 3 + (N + 1) * 2 ^ (2 * 2 ^ (N + 1))

/-- **A bounded zero diagonal.** Some diagonal of depth in `[N, zeroDiagBound N]` is
identically white. The search space is finite, and every nonzero diagonal the
argument uses lies inside it. -/
theorem zero_diagonal_bounded (N : Nat) :
    ∃ z, z ≤ zeroDiagBound N ∧ (N ≤ z ∧ ∀ t, E z t = false) := by
  refine Decidable.byContradiction fun hno => ?_
  let B := zeroDiagBound N
  have hnz : ∀ z, N ≤ z → z ≤ B → ∃ s, E z s = true := fun z hz hzB =>
    nonzero_witness z (fun hall => hno ⟨z, hzB, hz, hall⟩)
  let P := 2 ^ (N + 1)
  let W := 2 ^ (2 * P)
  have hB : B = N + 3 + (N + 1) * W := rfl
  have hP0 : 0 < P := Nat.two_pow_pos _
  have hper : ∀ k, k ≤ W → (∀ t, E (N + k) (t + P) = E (N + k) t) ∧
      (∀ t, E (N + k + 1) (t + P) = E (N + k + 1) t) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun t => ?_, fun t => E_per (N + 1) t⟩
      have := E_per_mul N 2 t
      rw [show 2 * 2 ^ N = P by simp [P, Nat.pow_succ]; omega] at this
      simpa using this
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hW : W ≤ (N + 1) * W := Nat.le_mul_of_pos_left W (by omega)
      refine ⟨by simpa [Nat.add_assoc] using ih'.2, ?_⟩
      have := period_prop (j := N + k) hP0 ih'.1 ih'.2 (hnz _ (by omega) (by omega))
      intro t; rw [show N + (k + 1) + 1 = N + k + 2 by omega]; exact this t
  obtain ⟨m, n, hmn, hnW, he⟩ :=
    Rule30UOR.KitConstructive.pigeonhole (2 * P) (fun m => pairList P (N + m))
      (fun m => pairList_length P _)
  obtain ⟨e0, e1⟩ := eq_of_pairList hP0 (hper m (by omega)).1 (hper m (by omega)).2
    (hper n hnW).1 (hper n hnW).2 he
  have fwd : ∀ k, N + m + k + 1 ≤ B → (∀ t, E (N + m + k) t = E (N + n + k) t) ∧
      (∀ t, E (N + m + k + 1) t = E (N + n + k + 1) t) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨e0, e1⟩
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      refine ⟨by simpa [Nat.add_assoc] using ih'.2, ?_⟩
      have := fwd_det ih'.1 ih'.2 (hnz _ (by omega) (by omega))
      intro t; rw [show N + m + (k + 1) + 1 = N + m + k + 2 by omega,
        show N + n + (k + 1) + 1 = N + n + k + 2 by omega]; exact this t
  have bwd : ∀ k, k ≤ N + m → (∀ t, E (N + m - k) t = E (N + n - k) t) ∧
      (∀ t, E (N + m - k + 1) t = E (N + n - k + 1) t) := by
    intro k
    induction k with
    | zero => intro _; simpa using And.intro e0 e1
    | succ k ih =>
      intro hk
      have h := ih (by omega)
      refine ⟨?_, ?_⟩
      · have := bwd_det (a := N + m - (k + 1)) (b := N + n - (k + 1))
          (by intro t; rw [show N + m - (k + 1) + 1 = N + m - k by omega,
                show N + n - (k + 1) + 1 = N + n - k by omega]; exact h.1 t)
          (by intro t; rw [show N + m - (k + 1) + 2 = N + m - k + 1 by omega,
                show N + n - (k + 1) + 2 = N + n - k + 1 by omega]; exact h.2 t)
        exact this
      · intro t; rw [show N + m - (k + 1) + 1 = N + m - k by omega,
          show N + n - (k + 1) + 1 = N + n - k by omega]; exact h.1 t
  have hd : ∀ i t, i + 1 ≤ B → E i t = E (i + (n - m)) t := by
    intro i t hi
    rcases Nat.lt_or_ge i (N + m) with hlt | hge
    · have := (bwd (N + m - i) (by omega)).1 t
      rwa [show N + m - (N + m - i) = i by omega,
        show N + n - (N + m - i) = i + (n - m) by omega] at this
    · have := (fwd (i - (N + m)) (by omega)).1 t
      rwa [show N + m + (i - (N + m)) = i by omega,
        show N + n + (i - (N + m)) = i + (n - m) by omega] at this
  have hgap : n - m ≤ W := by omega
  have hNW : N * (n - m) ≤ N * W := Nat.mul_le_mul_left N hgap
  have hW1 : N * W ≤ (N + 1) * W := Nat.mul_le_mul_right W (by omega)
  have hrep : ∀ k t, k ≤ N → E (2 + k * (n - m)) t = false := by
    intro k
    induction k with
    | zero => intro t _; simpa using E_two t
    | succ k ih =>
      intro t hk
      have hkm : k * (n - m) ≤ N * (n - m) := Nat.mul_le_mul_right _ (by omega)
      rw [show 2 + (k + 1) * (n - m) = (2 + k * (n - m)) + (n - m) by rw [Nat.succ_mul]; omega,
        ← hd _ t (by omega), ih t (by omega)]
  have hpos : N ≤ N * (n - m) := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨s, hs⟩ := hnz (2 + N * (n - m)) (by omega) (by omega)
  rw [hrep N s (Nat.le_refl N)] at hs; exact absurd hs (by decide)

/-- **Infinitely many zero diagonals.** For every `N` some diagonal of depth `≥ N` is identically
white. -/
theorem infinitely_many_zero_diagonals (N : Nat) : ∃ z, N ≤ z ∧ ∀ t, E z t = false := by
  obtain ⟨z, -, hz, h⟩ := zero_diagonal_bounded N
  exact ⟨z, hz, h⟩

/-! ### Unbounded periods -/

theorem E_zero' (t : Nat) : E 0 t = true := D_zero _

theorem settle_one_pos' : 1 ≤ settle 1 := by
  rcases Nat.eq_zero_or_pos (settle 1) with h | h
  · have e := settle_spec 1 0 (by omega)
    rw [show (0 : Nat) + 2 ^ 1 = 1 + 1 by rfl, D_one] at e
    exact absurd e (by decide)
  · exact h

theorem E_one' (t : Nat) : E 1 t = true := by
  have hb : 1 ≤ bound 1 := Nat.le_trans settle_one_pos' (settle_le_bound 1)
  unfold E
  obtain ⟨s, hs⟩ : ∃ s, t + bound 1 * 2 ^ 1 = s + 1 := ⟨t + bound 1 * 2 - 1, by
    simp only [Nat.pow_one]; omega⟩
  rw [hs]; exact D_one s

/-- A period of diagonal `j` is checked on one period of `E j`. -/
theorem per_iff_bounded (j P : Nat) :
    (∀ t, E j (t + P) = E j t) ↔ ∀ t, t < 2 ^ j → E j (t + P) = E j t := by
  constructor
  · exact fun h t _ => h t
  · intro h t
    have hl := reduce_mod (f := fun t => E j (t + P)) (P := 2 ^ j)
      (fun t => by
        show E j (t + 2 ^ j + P) = E j (t + P)
        rw [show t + 2 ^ j + P = (t + P) + 2 ^ j by omega, E_per]) t
    have hr := reduce_mod (E_per j) t
    rw [hl, hr]
    exact h _ (Nat.mod_lt _ (Nat.two_pow_pos j))

instance (j P : Nat) : Decidable (∀ t, E j (t + P) = E j t) :=
  decidable_of_iff _ (per_iff_bounded j P).symm

/-- **Finite core of `unbounded_periods`.** No `P > 0` is a common period of the
diagonals through depth `2 ^ (2 P) + 1`. -/
theorem common_period_fails_by (P : Nat) (hP0 : 0 < P) :
    ¬ ∀ j, j ≤ 2 ^ (2 * P) + 1 → ∀ t, E j (t + P) = E j t := by
  intro hper'
  obtain ⟨m, n, hmn, hnW, he⟩ := Rule30UOR.KitConstructive.pigeonhole (2 * P) (fun m => pairList P m) (fun m => pairList_length P _)
  obtain ⟨e0, e1⟩ := eq_of_pairList hP0 (hper' m (by cfomega)) (hper' (m + 1) (by cfomega))
    (hper' n (by cfomega)) (hper' (n + 1) (by cfomega)) he
  have bwd : ∀ k, k ≤ m → (∀ t, E (m - k) t = E (n - k) t) ∧ (∀ t, E (m - k + 1) t = E (n - k + 1) t) := by
    intro k
    induction k with
    | zero => intro _; simpa using And.intro e0 e1
    | succ k ih =>
      intro hk
      have h := ih (by cfomega)
      refine ⟨?_, ?_⟩
      · exact bwd_det (a := m - (k + 1)) (b := n - (k + 1))
          (by intro t; rw [show m - (k + 1) + 1 = m - k by cfomega, show n - (k + 1) + 1 = n - k by cfomega]; exact h.1 t)
          (by intro t; rw [show m - (k + 1) + 2 = m - k + 1 by cfomega, show n - (k + 1) + 2 = n - k + 1 by cfomega]; exact h.2 t)
      · intro t; rw [show m - (k + 1) + 1 = m - k by cfomega, show n - (k + 1) + 1 = n - k by cfomega]; exact h.1 t
  obtain ⟨b0, b1⟩ := bwd m (Nat.le_refl _)
  simp only [Nat.sub_self, Nat.zero_add] at b0 b1
  -- the edge pair recurs at depth d = n - m
  have hd0 : ∀ t, E (n - m) t = true := fun t => by rw [← b0, E_zero']
  have hd1 : ∀ t, E (n - m + 1) t = true := fun t => by rw [← b1, E_one']
  rcases Nat.lt_or_ge (n - m) 2 with hsmall | hbig
  · have : n - m = 1 := by cfomega
    have := hd1 0; rw [show n - m + 1 = 2 by cfomega, E_two] at this; exact absurd this (by decide)
  · -- every diagonal below depth n - m is white
    have hw1 : ∀ t, E (n - m - 1) t = false := by
      intro t; rw [E_back, show n - m - 1 + 2 = n - m + 1 by cfomega, show n - m - 1 + 1 = n - m by cfomega,
        hd1, hd0]; rfl
    have hw2 : ∀ t, E (n - m - 2) t = false := by
      intro t; rw [E_back, show n - m - 2 + 2 = n - m by cfomega, show n - m - 2 + 1 = n - m - 1 by cfomega,
        hw1]
      simp [hd0]
    have down : ∀ k, k + 2 ≤ n - m → (∀ t, E (n - m - 1 - k) t = false) ∧ (∀ t, E (n - m - 2 - k) t = false) := by
      intro k
      induction k with
      | zero => intro _; exact ⟨hw1, hw2⟩
      | succ k ih =>
        intro hk
        have h := ih (by cfomega)
        refine ⟨by intro t; rw [show n - m - 1 - (k + 1) = n - m - 2 - k by cfomega]; exact h.2 t, ?_⟩
        intro t
        rw [E_back, show n - m - 2 - (k + 1) + 2 = n - m - 1 - k by cfomega,
          show n - m - 2 - (k + 1) + 1 = n - m - 2 - k by cfomega]
        simp [h.1, h.2]
    have := (down (n - m - 2) (by cfomega)).2 0
    rw [show n - m - 2 - (n - m - 2) = 0 by cfomega, E_zero'] at this
    exact absurd this (by decide)

/-- **The zero-state has unbounded periods** (no common period for all depths). If every diagonal
had period `P`, a pair of consecutive diagonals would repeat; reversibility carries the repeat down
to the edge pair `(E 0, E 1) = (black, black)`, which recurs at some depth `d ≥ 1`; but two black
diagonals force every diagonal below them to be white, against the black edge. -/
theorem unbounded_periods (P : Nat) (hP0 : 0 < P) : ¬ ∀ j t, E j (t + P) = E j t :=
  fun hper => common_period_fails_by P hP0 (fun j _ t => hper j t)

end Rule30UOR.ZeroDiagonals

namespace Rule30UOR.ZeroDiagonals

/-- Depth `z` is a zero diagonal: the zero-state is white there at every time. -/
def IsZeroDiag (z : Nat) : Prop := ∀ t, Rule30UOR.Intent.E z t = false

theorem zero_diagonals_unbounded (N : Nat) : ∃ z, N ≤ z ∧ IsZeroDiag z :=
  infinitely_many_zero_diagonals N

end Rule30UOR.ZeroDiagonals

namespace Rule30UOR.ZeroDiagonals

/-- `P` is a common period of every diagonal of the zero-state. -/
def CommonPeriod (P : Nat) : Prop := ∀ j t, Rule30UOR.Intent.E j (t + P) = Rule30UOR.Intent.E j t

theorem no_common_period (P : Nat) (hP : 0 < P) : ¬ CommonPeriod P := unbounded_periods P hP

end Rule30UOR.ZeroDiagonals
