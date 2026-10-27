module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Rule 30, period 2: barriers for invariant and ranking-function proofs

Which proof shapes cannot work for `Q01` (`Rule30ZeroBoundary.Q01`) or for period 2 itself.

**Truncated stripes survive arbitrarily long.** `trunc n` is the stripe `…10101` cut off at the odd
depth `n`. `trunc_survives`: the constrained ZBL run from `trunc n` keeps depth `1` black at every
time `t ≤ n` and turns it white at time `n + 1`. So constrained runs from finite starts have
unbounded length, and:
* `finite_abstraction_has_lasso`, `finite_abstraction_has_lasso_gen` (barrier B1): every abstraction
  of the states into a finite set repeats a value along one run of surviving double steps from a
  finite start; `sound_abstraction_has_reachable_cycle`, `no_finite_abstract_ranking`: no ranking
  through a finite abstraction decreases along all surviving double steps.
* `no_local_ranking` (barrier B2): no function of (width, wall window, edge window) into `Nat`
  strictly decreases along every surviving double step of every finite start.
* `no_edge_dfa_ranking` (barrier B6): no finite automaton reading the configuration from its edge
  gives such a ranking, whatever its number of states.

Scope: these witnesses only respect the left half. Their free bits begin with `11111`, which a real
period-2 tail forbids (`Rule30ZeroBoundary.free_bits_no00_no11111`), so they are never the left half
of rule 30 at the start of an alternating tail (`trunc_not_left_half`): the barriers B1, B2, B6 are
about arguments that use `Q01` alone.

**Two-sided barrier.** `c7` (black exactly at `p ≡ 6 mod 7`) is a rule-30 orbit of temporal period
`4` whose column `0` alternates (`c7_center`); its truncations are finite configurations whose
center alternates for about `7 N` steps. `no_joint_local_ranking`: no function of (leftmost and
rightmost black positions, center window, left-edge window, right-edge window) into `Nat` strictly
decreases at every step where the center column flips, over all finite configurations.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryBarriers

open Rule30Jen Rule30ZeroBoundary

/-! ### Truncated stripes -/

theorem zrow_zero' {s : Nat → Bool} {k : Nat} (hk : k ≠ 0) : zrow s 0 k = s k :=
  zrow_zero_of_pos s (by omega)

theorem zrow_succ' {s : Nat → Bool} {t k : Nat} (hk : k ≠ 0) :
    zrow s (t + 1) k = xor (zrow s t (k + 1)) (zrow s t k || zrow s t (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem stripe_step' (k : Nat) (hk : k ≠ 0) :
    xor (stripe (k + 1)) (stripe k || stripe (k - 1)) = stripe k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 by omega, show j + 1 - 1 = j by omega, ← stripe_step]

/-- The stripe cut off at depth `n`. -/
def trunc (n : Nat) : Nat → Bool := truncate stripe n

theorem trunc_width {n : Nat} (hn : n % 2 = 1) : trunc n n = true ∧ ∀ k, n < k → trunc n k = false := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [trunc, truncate, stripe, hn]
  · simp [trunc, truncate]; omega

/-- Inside the light cone of the untouched region the truncated stripe evolves as the stripe. -/
theorem trunc_agree {n : Nat} (hn : n % 2 = 1) :
    ∀ t k, k + t ≤ n + 1 → zrow (trunc n) t k = stripe k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0; rw [zrow_wall]; rfl
    · rw [zrow_zero' h0]
      by_cases hle : k ≤ n
      · simp [trunc, truncate, hle]
      · have hk' : k = n + 1 := by omega
        subst hk'
        have : (n + 1) % 2 = 0 := by omega
        simp [trunc, truncate, stripe, this]
  | succ t ih =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0; rw [zrow_wall]; rfl
    · rw [zrow_succ' h0, ih (k + 1) (by omega), ih k (by omega), ih (k - 1) (by omega),
        stripe_step' k h0]

/-- On the next anti-diagonal the truncated stripe is the complement of the stripe. -/
theorem trunc_antidiag {n : Nat} (hn : n % 2 = 1) :
    ∀ t k, k ≠ 0 → k + t = n + 2 → zrow (trunc n) t k = !stripe k := by
  intro t
  induction t with
  | zero =>
    intro k h0 hk
    rw [zrow_zero' h0]
    have hk' : k = n + 2 := by omega
    subst hk'
    have : (n + 2) % 2 = 1 := by omega
    simp [trunc, truncate, stripe, this]
  | succ t ih =>
    intro k h0 hk
    rw [zrow_succ' h0, ih (k + 1) (by omega) (by omega), trunc_agree hn t k (by omega),
      trunc_agree hn t (k - 1) (by omega)]
    have := stripe_step' k h0
    revert this
    cases stripe (k + 1) <;> cases stripe k <;> cases stripe (k - 1) <;> simp

/-- **Unbounded survival.** For odd `n`, depth `1` is black at every time `t ≤ n` and white at time
`n + 1` (an even time): the constrained run from the finite start `trunc n` lives exactly through
time `n`. -/
theorem trunc_survives {n : Nat} (hn : n % 2 = 1) :
    (∀ t, t ≤ n → zrow (trunc n) t 1 = true) ∧ zrow (trunc n) (n + 1) 1 = false := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [trunc_agree hn t 1 (by omega)]; rfl
  · rw [trunc_antidiag hn (n + 1) 1 (by omega) (by omega)]; rfl

/-- **Scope of the truncated-stripe witnesses.** For odd `n ≥ 9`, `trunc n` is never the left half
of rule 30 at the start `T` of an alternating tail (black first): its free bits begin with `11111`,
which `Rule30ZeroBoundary.free_bits_no00_no11111` forbids. -/
theorem trunc_not_left_half {T n : Nat} (hn : n % 2 = 1) (h9 : 9 ≤ n)
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) :
    ¬ ∀ k, 1 ≤ k → leftRow T k = trunc n k := by
  intro heq
  have hw : ∀ t, T ≤ t → (Rule30Prize.center t && Rule30Prize.center (t + 1)) = false := by
    intro t ht
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
    · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
      rw [(h j).2]; cases cell (T + 2 * j) 0 <;> rfl
    · show (cell (T + 2 * j + 1) 0 && cell (T + 2 * j + 1 + 1) 0) = false
      rw [(h j).2]; rfl
  apply (free_bits_no00_no11111 h 0).2
  intro i hi
  have e := left_half_is_zbl hw (2 * i + 1) 1 (Nat.le_refl 1)
  rw [zrow_congr heq, (trunc_survives hn).1 _ (by omega)] at e
  rw [show T + 2 * (0 + i) + 1 = T + (2 * i + 1) by omega]
  exact e.symm

/-! ### Barrier B1: finite abstractions -/

/-- The state after `j` double steps. -/
def iter (s : Nat → Bool) (j : Nat) : Nat → Bool := fun k => zrow s (2 * j) k

/-- A double step survives when depth `1` is black at times `0` and `2`. -/
def Survives (s : Nat → Bool) : Prop := zrow s 0 1 = true ∧ zrow s 2 1 = true

theorem iter_zrow (s : Nat → Bool) (j a : Nat) (k : Nat) : zrow (iter s j) a k = zrow s (2 * j + a) k :=
  (zrow_shift s (2 * j) a k).symm

theorem iter_survives {n : Nat} (hn : n % 2 = 1) {j : Nat} (hj : 2 * j + 2 ≤ n) :
    Survives (iter (trunc n) j) := by
  unfold Survives
  rw [iter_zrow, iter_zrow]
  exact ⟨(trunc_survives hn).1 _ (by omega), (trunc_survives hn).1 _ (by omega)⟩

/-- **B1.** Any abstraction `α` of states into bit-lists of length `w` takes the same value twice
along one run of surviving double steps from a finite start. -/
theorem finite_abstraction_has_lasso (w : Nat) (α : (Nat → Bool) → List Bool)
    (hα : ∀ s, (α s).length = w) :
    ∃ n m m', n % 2 = 1 ∧ m < m' ∧ (∀ j, j ≤ m' → Survives (iter (trunc n) j)) ∧
      α (iter (trunc n) m) = α (iter (trunc n) m') := by
  obtain ⟨m, m', hlt, hle, heq⟩ := pigeonhole w (fun j => α (iter (trunc (2 * 2 ^ w + 3)) j))
    (fun j => hα _)
  exact ⟨2 * 2 ^ w + 3, m, m', by omega, hlt, fun j hj => iter_survives (by omega) (by omega), heq⟩

/-- Pigeonhole for a sequence with values in a list `L`. -/
theorem pigeonhole_gen {A : Type} (L : List A) (f : Nat → A) (hf : ∀ m, f m ∈ L) :
    ∃ m n, m < n ∧ n ≤ L.length ∧ f m = f n := by
  classical
  refine Classical.byContradiction fun hne => ?_
  have hinj : ∀ m ∈ List.range (L.length + 1), ∀ n ∈ List.range (L.length + 1), f m = f n → m = n := by
    intro m hm n hn e
    simp only [List.mem_range] at hm hn
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd ⟨m, n, h, by omega, e⟩ hne
    · exact h
    · exact absurd ⟨n, m, h, by omega, e.symm⟩ hne
  have hnd := nodup_map_of_inj f List.nodup_range hinj
  have := length_le_of_subset hnd fun x hx => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    exact hf m
  simp only [List.length_map, List.length_range] at this
  omega

/-- **B1 for an abstraction into any finite set** of abstract values (listed by `L`). -/
theorem finite_abstraction_has_lasso_gen {A : Type} (L : List A) (α : (Nat → Bool) → A)
    (hα : ∀ s, α s ∈ L) :
    ∃ n m m', n % 2 = 1 ∧ m < m' ∧ (∀ j, j ≤ m' → Survives (iter (trunc n) j)) ∧
      α (iter (trunc n) m) = α (iter (trunc n) m') := by
  obtain ⟨m, m', hlt, hle, heq⟩ :=
    pigeonhole_gen L (fun j => α (iter (trunc (2 * L.length + 3)) j)) (fun j => hα _)
  exact ⟨2 * L.length + 3, m, m', by omega, hlt, fun j hj => iter_survives (by omega) (by omega), heq⟩

/-- Reflexive-transitive closure. -/
inductive RTG {A : Type} (R : A → A → Prop) : A → A → Prop
  | refl (a : A) : RTG R a a
  | tail {a b c : A} : RTG R a b → R b c → RTG R a c

/-- One double step. -/
def dstep (s : Nat → Bool) : Nat → Bool := fun k => zrow s 2 k

theorem iter_dstep (s : Nat → Bool) (j : Nat) : iter s (j + 1) = dstep (iter s j) := by
  funext k
  unfold dstep
  rw [iter_zrow, show 2 * j + 2 = 2 * (j + 1) by omega]
  rfl

theorem iter_zero_trunc (n : Nat) : iter (trunc n) 0 = trunc n := by
  funext k
  unfold iter
  by_cases hk : k = 0
  · subst hk; rw [zrow_wall]; rfl
  · simp only [Nat.mul_zero]; exact zrow_zero' hk

/-- Every state on the run is finitely supported. -/
theorem iter_finite {n : Nat} (hn : n % 2 = 1) (j : Nat) :
    ∀ k, n + 2 * j < k → iter (trunc n) j k = false := by
  intro k hk
  have hedge : trunc n n = true := (trunc_width hn).1
  exact (zrow_edge (L := trunc n) (m := n) (by omega) hedge (trunc_width hn).2 (2 * j)).2 k hk

/-- Every abstract transition relation that is sound for surviving double steps between finitely
supported states has a cycle reachable from the image of a finite start. -/
theorem sound_abstraction_has_reachable_cycle {A : Type} (L : List A) (α : (Nat → Bool) → A)
    (hα : ∀ s, α s ∈ L) (R : A → A → Prop)
    (hR : ∀ s, (∃ W, ∀ k, W < k → s k = false) → Survives s → R (α s) (α (dstep s))) :
    ∃ n, n % 2 = 1 ∧ (∀ k, n < k → trunc n k = false) ∧
      ∃ a, RTG R (α (trunc n)) a ∧ Relation.TransGen R a a := by
  obtain ⟨n, m, m', hn, hlt, hsurv, heq⟩ := finite_abstraction_has_lasso_gen L α hα
  have step : ∀ j, j < m' → R (α (iter (trunc n) j)) (α (iter (trunc n) (j + 1))) := by
    intro j hj
    rw [iter_dstep]
    exact hR _ ⟨n + 2 * j, iter_finite hn j⟩ (hsurv j (by omega))
  have reach : ∀ j, j ≤ m' → RTG R (α (trunc n)) (α (iter (trunc n) j)) := by
    intro j
    induction j with
    | zero => intro _; rw [iter_zero_trunc]; exact RTG.refl _
    | succ j ih => intro hj; exact RTG.tail (ih (by omega)) (step j (by omega))
  have cyc : ∀ i, 1 ≤ i → m + i ≤ m' →
      Relation.TransGen R (α (iter (trunc n) m)) (α (iter (trunc n) (m + i))) := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hi
      by_cases h0 : i = 0
      · subst h0; exact Relation.TransGen.single (step m (by omega))
      · refine Relation.TransGen.tail (ih (by omega) (by omega)) ?_
        rw [show m + (i + 1) = (m + i) + 1 by omega]
        exact step (m + i) (by omega)
  refine ⟨n, hn, (trunc_width hn).2, α (iter (trunc n) m), reach m (by omega), ?_⟩
  have h := cyc (m' - m) (by omega) (by omega)
  rw [show m + (m' - m) = m' by omega, ← heq] at h
  exact h

/-- **No ranking function through a finite abstraction** decreases along all surviving double
steps between finitely supported states. -/
theorem no_finite_abstract_ranking {A : Type} (L : List A) (α : (Nat → Bool) → A) (hα : ∀ s, α s ∈ L)
    (rank : A → Nat) :
    ¬ (∀ s, (∃ W, ∀ k, W < k → s k = false) → Survives s → rank (α (dstep s)) < rank (α s)) := by
  intro h
  obtain ⟨n, -, -, a, -, hc⟩ :=
    sound_abstraction_has_reachable_cycle L α hα (fun a b => rank b < rank a) h
  have key : ∀ x y, Relation.TransGen (fun a b => rank b < rank a) x y → rank y < rank x := by
    intro x y hxy
    induction hxy with
    | single h => exact h
    | tail _ h ih => exact Nat.lt_trans h ih
  exact Nat.lt_irrefl _ (key a a hc)

/-! ### Barrier B2: rankings through width, wall window and edge window -/

theorem trunc_shift (n m k : Nat) : trunc (n + 2 * m) (k + 2 * m) = trunc n k := by
  unfold trunc truncate stripe
  have h1 : (k + 2 * m) % 2 = k % 2 := by omega
  rw [h1]
  by_cases hk : k ≤ n
  · have : k + 2 * m ≤ n + 2 * m := by omega
    simp [hk, this]
  · have : ¬ (k + 2 * m ≤ n + 2 * m) := by omega
    simp [hk, this]

/-- Wall window (depths `1..w`) and edge window (depths `W, W - 1, …, W - e + 1`). -/
def wallW (w : Nat) (s : Nat → Bool) : List Bool := (List.range w).map fun i => s (i + 1)
def edgeW (e : Nat) (s : Nat → Bool) (W : Nat) : List Bool := (List.range e).map fun i => s (W - i)

theorem map_range_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.1 hi)

/-- A ranking certificate through (width, wall window, edge window): strict decrease along every
surviving double step of every finitely supported start of width `W`. -/
def RankCert (w e : Nat) (R : Nat → List Bool → List Bool → Nat) : Prop :=
  ∀ (s : Nat → Bool) (W : Nat), 1 ≤ W → s W = true → (∀ k, W < k → s k = false) → Survives s →
    R (W + 2) (wallW w (fun k => zrow s 2 k)) (edgeW e (fun k => zrow s 2 k) (W + 2)) <
      R W (wallW w s) (edgeW e s W)

theorem wall_iter {n : Nat} (hn : n % 2 = 1) (w j : Nat) (h : 2 * j + w ≤ n + 1) :
    wallW w (iter (trunc n) j) = wallW w stripe := by
  unfold wallW iter
  exact map_range_congr fun i hi => trunc_agree hn _ _ (by omega)

theorem edge_iter (n0 m e j : Nat) (he : e ≤ n0) :
    edgeW e (iter (trunc (n0 + 2 * m)) j) (n0 + 2 * m + 2 * j) = edgeW e (iter (trunc n0) j) (n0 + 2 * j) := by
  unfold edgeW iter
  apply map_range_congr
  intro i hi
  rw [show n0 + 2 * m + 2 * j - i = (n0 + 2 * j - i) + 2 * m by omega]
  exact zrow_translate (L := trunc n0) (L' := trunc (n0 + 2 * m)) (d := 2 * m) (a := 1) (by omega)
    (fun k _ => trunc_shift n0 m k) (2 * j) (n0 + 2 * j - i) (by omega)

/-- **B2.** No function of (width, wall window of any size `w`, edge window of any size `e`) is a
ranking function certifying termination of the constrained ZBL from all finite starts. -/
theorem no_local_ranking (w e : Nat) (R : Nat → List Bool → List Bool → Nat) : ¬ RankCert w e R := by
  intro hR
  let n0 := 2 * e + 1
  have hn0 : n0 % 2 = 1 := by omega
  let E : Nat → List Bool := fun j => edgeW e (iter (trunc n0) j) (n0 + 2 * j)
  obtain ⟨j1, j2, hlt, -, hE⟩ := pigeonhole e E (fun j => by simp [E, edgeW])
  let S := wallW w stripe
  let N0 := 2 * j2 + w + 2
  have stepR : ∀ m, N0 ≤ m → ∀ j, j < j2 →
      R (n0 + 2 * m + 2 * (j + 1)) S (E (j + 1)) < R (n0 + 2 * m + 2 * j) S (E j) := by
    intro m hm j hj
    have hn : (n0 + 2 * m) % 2 = 1 := by omega
    have hw := zrow_edge (L := trunc (n0 + 2 * m)) (m := n0 + 2 * m) (by omega)
      (trunc_width hn).1 (trunc_width hn).2 (2 * j)
    have hstep := hR (iter (trunc (n0 + 2 * m)) j) (n0 + 2 * m + 2 * j) (by omega) hw.1 hw.2
      (iter_survives hn (by omega))
    have hit : (fun k => zrow (iter (trunc (n0 + 2 * m)) j) 2 k) = iter (trunc (n0 + 2 * m)) (j + 1) := by
      funext k; rw [iter_zrow, show 2 * j + 2 = 2 * (j + 1) by omega]; rfl
    rw [hit, wall_iter hn w (j + 1) (by omega), wall_iter hn w j (by omega),
      show n0 + 2 * m + 2 * j + 2 = n0 + 2 * m + 2 * (j + 1) by omega, edge_iter n0 m e (j + 1) (by omega),
      edge_iter n0 m e j (by omega)] at hstep
    exact hstep
  have chain : ∀ m, N0 ≤ m → ∀ i, i ≤ j2 - j1 →
      R (n0 + 2 * m + 2 * (j1 + i)) S (E (j1 + i)) + i ≤ R (n0 + 2 * m + 2 * j1) S (E j1) := by
    intro m hm i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have h := stepR m hm (j1 + i) (by omega)
      rw [show j1 + (i + 1) = j1 + i + 1 by omega]
      omega
  let P := j2 - j1
  have hP : 1 ≤ P := by omega
  let f : Nat → Nat := fun M => R M S (E j1)
  have period : ∀ m, N0 ≤ m → f (n0 + 2 * m + 2 * j1 + 2 * P) + P ≤ f (n0 + 2 * m + 2 * j1) := by
    intro m hm
    have h := chain m hm P (Nat.le_refl _)
    rw [show j1 + P = j2 by omega, ← hE, show n0 + 2 * m + 2 * j2 = n0 + 2 * m + 2 * j1 + 2 * P by omega] at h
    exact h
  let B := n0 + 2 * N0 + 2 * j1
  have descent : ∀ k, f (B + 2 * (k * P)) + k * P ≤ f B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have h := period (N0 + k * P) (by omega)
      have e2 : n0 + 2 * (N0 + k * P) + 2 * j1 = B + 2 * (k * P) := by omega
      have e3 : B + 2 * ((k + 1) * P) = B + 2 * (k * P) + 2 * P := by rw [e1]; omega
      rw [e2] at h
      rw [e3, e1]
      omega
  have := descent (f B + 1)
  have hk : f B + 1 ≤ (f B + 1) * P := Nat.le_mul_of_pos_right _ hP
  omega

/-! ### Barrier B6: no finite automaton reading from the edge -/

/-- A deterministic finite automaton on `Bool` with states in `Nat`. -/
structure DFA where
  δ : Nat → Bool → Nat
  F : Nat → Bool

def dfaRun (A : DFA) : Nat → List Bool → Nat
  | q, [] => q
  | q, b :: w => dfaRun A (A.δ q b) w

/-- The length of the longest accepted prefix (`-1` if none). -/
def maxAcc (A : DFA) : Nat → List Bool → Int
  | q, [] => if A.F q then 0 else -1
  | q, b :: w => if 0 ≤ maxAcc A (A.δ q b) w then maxAcc A (A.δ q b) w + 1 else (if A.F q then 0 else -1)

theorem dfaRun_append (A : DFA) : ∀ (q : Nat) (u v : List Bool), dfaRun A q (u ++ v) = dfaRun A (dfaRun A q u) v
  | _, [], _ => rfl
  | q, b :: u, v => dfaRun_append A (A.δ q b) u v

theorem maxAcc_nil (A : DFA) (q : Nat) : maxAcc A q [] = if A.F q then 0 else -1 := rfl
theorem maxAcc_cons (A : DFA) (q : Nat) (b : Bool) (w : List Bool) :
    maxAcc A q (b :: w) = if 0 ≤ maxAcc A (A.δ q b) w then maxAcc A (A.δ q b) w + 1
      else (if A.F q then 0 else -1) := rfl

theorem maxAcc_ge (A : DFA) : ∀ (q : Nat) (w : List Bool), -1 ≤ maxAcc A q w
  | q, [] => by rw [maxAcc_nil]; split <;> omega
  | q, b :: w => by
    rw [maxAcc_cons]
    have := maxAcc_ge A (A.δ q b) w
    split
    · omega
    · split <;> omega

theorem maxAcc_le (A : DFA) : ∀ (q : Nat) (w : List Bool), maxAcc A q w ≤ w.length
  | q, [] => by rw [maxAcc_nil]; split <;> simp
  | q, b :: w => by
    rw [maxAcc_cons]
    have := maxAcc_le A (A.δ q b) w
    simp only [List.length_cons]
    split
    · omega
    · split <;> omega

theorem maxAcc_neg (A : DFA) (q : Nat) (w : List Bool) (h : maxAcc A q w < 0) :
    A.F q = false ∧ maxAcc A q w = -1 := by
  cases w with
  | nil =>
    rw [maxAcc_nil] at h ⊢
    cases hq : A.F q <;> simp_all
  | cons b w =>
    rw [maxAcc_cons] at h ⊢
    have := maxAcc_ge A (A.δ q b) w
    by_cases hr : 0 ≤ maxAcc A (A.δ q b) w
    · simp only [hr, ite_true] at h; omega
    · simp only [hr, ite_false] at h ⊢
      cases hq : A.F q <;> simp_all

theorem maxAcc_append (A : DFA) : ∀ (q : Nat) (u v : List Bool),
    maxAcc A q (u ++ v) = if 0 ≤ maxAcc A (dfaRun A q u) v then (u.length : Int) + maxAcc A (dfaRun A q u) v
      else maxAcc A q u
  | q, [], v => by
    simp only [List.nil_append, dfaRun, List.length_nil]
    by_cases h : 0 ≤ maxAcc A q v
    · simp [h]
    · simp only [h, ite_false]
      have := maxAcc_neg A q v (by omega)
      rw [this.2, maxAcc_nil, this.1]; rfl
  | q, b :: u, v => by
    simp only [List.cons_append, dfaRun, List.length_cons]
    rw [maxAcc_cons, maxAcc_append A (A.δ q b) u v, maxAcc_cons]
    by_cases h : 0 ≤ maxAcc A (dfaRun A (A.δ q b) u) v
    · have : 0 ≤ (u.length : Int) + maxAcc A (dfaRun A (A.δ q b) u) v := by omega
      simp only [h, ite_true, this]
      push_cast
      omega
    · simp only [h, ite_false]

/-- If the state after reading `u` accepts, the longest accepted prefix of `u ++ v` has length at
least `|u|`. -/
theorem maxAcc_ge_of_acc (A : DFA) (q : Nat) (u v : List Bool) (h : A.F (dfaRun A q u) = true) :
    (u.length : Int) ≤ maxAcc A q (u ++ v) := by
  have key : ∀ (q : Nat) (u : List Bool), A.F (dfaRun A q u) = true → (u.length : Int) ≤ maxAcc A q u := by
    intro q u
    induction u generalizing q with
    | nil => intro h; simp only [dfaRun] at h; rw [maxAcc_nil, h]; simp
    | cons b u ih =>
      intro h
      simp only [dfaRun] at h
      have := ih (A.δ q b) h
      rw [maxAcc_cons]
      simp only [List.length_cons]
      have h0 : 0 ≤ maxAcc A (A.δ q b) u := by omega
      simp only [h0, ite_true]
      push_cast
      omega
  rw [maxAcc_append]
  by_cases h' : 0 ≤ maxAcc A (dfaRun A q u) v
  · simp only [h', ite_true]; omega
  · simp only [h', ite_false]; exact key q u h

/-- The word `(01)^k`. -/
def altWord : Nat → List Bool
  | 0 => []
  | k + 1 => false :: true :: altWord k

theorem altWord_length (k : Nat) : (altWord k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [altWord, ih]; omega

theorem altWord_add : ∀ a b, altWord (a + b) = altWord a ++ altWord b
  | 0, b => by simp [altWord]
  | a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp [altWord, altWord_add a b]

def pairStep (A : DFA) (q : Nat) : Nat := A.δ (A.δ q false) true

def iterP (A : DFA) : Nat → Nat → Nat
  | 0, q => q
  | k + 1, q => iterP A k (pairStep A q)

theorem iterP_add (A : DFA) : ∀ a b q, iterP A (a + b) q = iterP A b (iterP A a q)
  | 0, b, q => by simp [iterP]
  | a + 1, b, q => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iterP]
    exact iterP_add A a b (pairStep A q)

theorem dfaRun_altWord (A : DFA) : ∀ k q, dfaRun A q (altWord k) = iterP A k q
  | 0, q => rfl
  | k + 1, q => by simp only [altWord, dfaRun, iterP]; exact dfaRun_altWord A k _

/-- No acceptance from some point on: the longest accepted prefix of `(01)^k` is empty. -/
theorem maxAcc_altWord_dead (A : DFA) (q : Nat)
    (hdead : ∀ i, A.F (iterP A i q) = false ∧ A.F (A.δ (iterP A i q) false) = false) :
    ∀ k, maxAcc A q (altWord k) = -1 := by
  intro k
  induction k generalizing q with
  | zero =>
    have h0 := (hdead 0).1
    simp only [iterP] at h0
    rw [show altWord 0 = [] from rfl, maxAcc_nil, h0]; rfl
  | succ k ih =>
    have hq : ∀ i, A.F (iterP A i (pairStep A q)) = false ∧
        A.F (A.δ (iterP A i (pairStep A q)) false) = false :=
      fun i => hdead (i + 1)
    have h1 := ih (pairStep A q) hq
    have hf0 := (hdead 0).1
    have hf1 := (hdead 0).2
    simp only [iterP] at hf0 hf1
    rw [show altWord (k + 1) = false :: true :: altWord k from rfl, maxAcc_cons, maxAcc_cons]
    simp only [pairStep] at h1
    rw [h1]
    simp [hf0, hf1]

/-- The configuration read from its edge: depths `W, W - 1, …, 1`. -/
def edgeWord (s : Nat → Bool) (W : Nat) : List Bool := (List.range W).map fun i => s (W - i)

/-- An edge-DFA ranking certificate. -/
def CertE (A : DFA) : Prop :=
  ∀ (s : Nat → Bool) (W : Nat), 1 ≤ W → s W = true → (∀ k, W < k → s k = false) → Survives s →
    maxAcc A 0 (edgeWord (fun k => zrow s 2 k) (W + 2)) < maxAcc A 0 (edgeWord s W)

/-- Chain of decreases along the truncated-stripe run. -/
theorem edge_chain {A : DFA} (hA : CertE A) {n : Nat} (hn : n % 2 = 1) :
    ∀ j d, 2 * (j + d) ≤ n - 1 →
      maxAcc A 0 (edgeWord (iter (trunc n) (j + d)) (n + 2 * (j + d))) + d ≤
        maxAcc A 0 (edgeWord (iter (trunc n) j) (n + 2 * j)) := by
  intro j d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have hw := zrow_edge (L := trunc n) (m := n) (by omega) (trunc_width hn).1 (trunc_width hn).2
      (2 * (j + d))
    have hstep := hA (iter (trunc n) (j + d)) (n + 2 * (j + d)) (by omega) hw.1 hw.2
      (iter_survives hn (by omega))
    have hit : (fun k => zrow (iter (trunc n) (j + d)) 2 k) = iter (trunc n) (j + (d + 1)) := by
      funext k; rw [iter_zrow, show 2 * (j + d) + 2 = 2 * (j + (d + 1)) by omega]; rfl
    rw [hit, show n + 2 * (j + d) + 2 = n + 2 * (j + (d + 1)) by omega] at hstep
    push_cast
    omega

theorem range_add_map (a b : Nat) (f : Nat → Bool) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun i => f (a + i)) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem stripe_part (n j : Nat) (hn : n % 2 = 1) (hj : 2 * j ≤ n + 1) :
    (List.range (n + 1 - 2 * j)).map (fun i => stripe (n + 1 - 2 * j - i)) = altWord ((n + 1 - 2 * j) / 2) := by
  have key : ∀ k, (List.range (2 * k)).map (fun i => stripe (2 * k - i)) = altWord k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, range_add_map]
      have h1 : (List.range 2).map (fun i => stripe (2 + 2 * k - i)) = [false, true] := by
        simp [List.range, List.range.loop, stripe]
      rw [h1]
      have h2 : (List.range (2 * k)).map (fun i => stripe (2 + 2 * k - (2 + i))) =
          (List.range (2 * k)).map (fun i => stripe (2 * k - i)) := by
        apply List.map_congr_left; intro i _; congr 1; omega
      rw [h2, ih]; rfl
  have he : n + 1 - 2 * j = 2 * ((n + 1 - 2 * j) / 2) := by omega
  rw [he, key, ← he]

theorem edge_split {n : Nat} (hn : n % 2 = 1) (j : Nat) (hj1 : 1 ≤ j) (hj : 4 * j ≤ n) :
    edgeWord (iter (trunc n) j) (n + 2 * j) =
      (List.range (4 * j - 1)).map (fun i => zrow (trunc n) (2 * j) (n + 2 * j - i)) ++
        altWord ((n + 1 - 2 * j) / 2) := by
  unfold edgeWord iter
  rw [show n + 2 * j = (4 * j - 1) + (n + 1 - 2 * j) by omega, range_add_map,
    ← show n + 2 * j = (4 * j - 1) + (n + 1 - 2 * j) by omega]
  congr 1
  rw [← stripe_part n j hn (by omega)]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [show n + 2 * j - (4 * j - 1 + i) = n + 1 - 2 * j - i by omega]
  exact trunc_agree hn _ _ (by omega)

theorem Z_shift (n0 m j : Nat) (hj : 4 * j ≤ n0) :
    (List.range (4 * j - 1)).map (fun i => zrow (trunc (n0 + 2 * m)) (2 * j) (n0 + 2 * m + 2 * j - i)) =
      (List.range (4 * j - 1)).map (fun i => zrow (trunc n0) (2 * j) (n0 + 2 * j - i)) := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [show n0 + 2 * m + 2 * j - i = (n0 + 2 * j - i) + 2 * m by omega]
  exact zrow_translate (L := trunc n0) (L' := trunc (n0 + 2 * m)) (d := 2 * m) (a := 1) (by omega)
    (fun k _ => trunc_shift n0 m k) (2 * j) (n0 + 2 * j - i) (by omega)

/-- One-hot encoding (for the list pigeonhole principle). -/
def oneHot (N v : Nat) : List Bool := (List.range N).map fun k => k == v

theorem oneHot_inj {N v w : Nat} (hv : v < N) (h : oneHot N v = oneHot N w) : v = w := by
  have : (oneHot N v)[v]? = (oneHot N w)[v]? := by rw [h]
  simp [oneHot, hv] at this
  omega

theorem last_index (k i π : Nat) (hπ : 1 ≤ π) (hik : i + 1 ≤ k) :
    ∃ t, i + t * π ≤ k - 1 ∧ k - 1 < i + t * π + π := by
  refine ⟨(k - 1 - i) / π, ?_, ?_⟩
  · have := Nat.div_mul_le_self (k - 1 - i) π; omega
  · have := Nat.lt_div_mul_add (a := k - 1 - i) (b := π) (by omega); omega

/-- **B6.** No DFA reading the configuration from its edge defines a ranking function. -/
theorem no_edge_dfa_ranking (A : DFA) (N : Nat) (hN : 0 < N) (hδ : ∀ q b, A.δ q b < N) : ¬ CertE A := by
  intro hA
  let B := 2 ^ N
  have hB : 1 ≤ B := Nat.one_le_two_pow
  let j := B + 1
  let n0 := 4 * j + 1
  have hn0 : n0 % 2 = 1 := by omega
  let Zw := (List.range (4 * j - 1)).map (fun i => zrow (trunc n0) (2 * j) (n0 + 2 * j - i))
  have hZlen : Zw.length = 4 * j - 1 := by simp [Zw]
  let q := dfaRun A 0 Zw
  have hq : q < N := by
    show dfaRun A 0 Zw < N
    have : ∀ (p : Nat) (w : List Bool), p < N → dfaRun A p w < N := by
      intro p w
      induction w generalizing p with
      | nil => intro h; exact h
      | cons b w ih => intro _; exact ih _ (hδ p b)
    exact this 0 Zw hN
  have hiter : ∀ i, iterP A i q < N := by
    intro i
    induction i with
    | zero => exact hq
    | succ i ih =>
      rw [show i + 1 = i + 1 from rfl, iterP_add A i 1]
      exact hδ _ _
  obtain ⟨i1, i2, hlt, hle, heq⟩ := pigeonhole N (fun i => oneHot N (iterP A i q)) (fun i => by simp [oneHot])
  have hcyc : iterP A i1 q = iterP A i2 q := oneHot_inj (hiter i1) heq
  let π := i2 - i1
  have hper : ∀ t r, iterP A (i1 + t * π + r) q = iterP A (i1 + r) q := by
    intro t
    induction t with
    | zero => intro r; simp
    | succ t ih =>
      intro r
      rw [show i1 + (t + 1) * π + r = i2 + (t * π + r) by rw [Nat.succ_mul]; omega, iterP_add A i2,
        ← hcyc, ← iterP_add A i1, show i1 + (t * π + r) = i1 + t * π + r by omega, ih]
  let m := 10 * j + 4 * B + 10
  let n := n0 + 2 * m
  have hn : n % 2 = 1 := by omega
  let k := (n + 1 - 2 * j) / 2
  have hj_def : j = B + 1 := rfl
  have hn0_def : n0 = 4 * j + 1 := rfl
  have hm_def : m = 10 * j + 4 * B + 10 := rfl
  have hn_def : n = n0 + 2 * m := rfl
  have hB_def : B = 2 ^ N := rfl
  have hk2 : 2 * k = n + 1 - 2 * j := by omega
  have hsplit : edgeWord (iter (trunc n) j) (n + 2 * j) = Zw ++ altWord k := by
    rw [edge_split hn j (by omega) (by omega)]
    congr 1
    exact Z_shift n0 m j (by omega)
  have hup : maxAcc A 0 (edgeWord (iter (trunc n) j) (n + 2 * j)) + j ≤ n := by
    have h := edge_chain hA hn 0 j (by omega)
    simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h
    have hl := maxAcc_le A 0 (edgeWord (iter (trunc n) 0) n)
    have hlen : (edgeWord (iter (trunc n) 0) n).length = n := by simp [edgeWord]
    rw [hlen] at hl
    omega
  have hlow : ((n - 1) / 2 - j : Nat) - 1 ≤ maxAcc A 0 (edgeWord (iter (trunc n) j) (n + 2 * j)) := by
    have h := edge_chain hA hn j ((n - 1) / 2 - j) (by omega)
    have hg := maxAcc_ge A 0 (edgeWord (iter (trunc n) (j + ((n - 1) / 2 - j))) (n + 2 * (j + ((n - 1) / 2 - j))))
    omega
  rw [hsplit, maxAcc_append] at hup hlow
  rw [show dfaRun A 0 Zw = q from rfl] at hup hlow
  by_cases hacc : ∃ i, i1 ≤ i ∧ i < i2 ∧ (A.F (iterP A i q) = true ∨ A.F (A.δ (iterP A i q) false) = true)
  · obtain ⟨i, hi1, hi2, hF⟩ := hacc
    have hπ : 1 ≤ π := by omega
    obtain ⟨t, hi'k, hi'k2⟩ := last_index k i π hπ (by omega)
    let i' := i + t * π
    have hstate : iterP A i' q = iterP A i q := by
      have := hper t (i - i1)
      rw [show i1 + t * π + (i - i1) = i' by omega, show i1 + (i - i1) = i by omega] at this
      exact this
    have hlow' : (2 * i' : Int) ≤ maxAcc A q (altWord k) := by
      have hsp : altWord k = altWord i' ++ (false :: true :: altWord (k - 1 - i')) := by
        have hh : altWord (i' + (k - 1 - i' + 1)) = altWord i' ++ (false :: true :: altWord (k - 1 - i')) :=
          altWord_add _ _
        rw [show i' + (k - 1 - i' + 1) = k by omega] at hh
        exact hh
      rcases hF with hF | hF
      · rw [hsp]
        have := maxAcc_ge_of_acc A q (altWord i') (false :: true :: altWord (k - 1 - i'))
          (by rw [dfaRun_altWord, hstate]; exact hF)
        rw [altWord_length] at this
        push_cast at this ⊢
        omega
      · rw [hsp, show altWord i' ++ (false :: true :: altWord (k - 1 - i')) =
          (altWord i' ++ [false]) ++ (true :: altWord (k - 1 - i')) by simp]
        have := maxAcc_ge_of_acc A q (altWord i' ++ [false]) (true :: altWord (k - 1 - i'))
          (by rw [dfaRun_append, dfaRun_altWord, hstate]; exact hF)
        simp only [List.length_append, altWord_length, List.length_singleton] at this
        push_cast at this ⊢
        omega
    have h0 : 0 ≤ maxAcc A q (altWord k) := by omega
    simp only [h0, ite_true, hZlen] at hup
    have : (j : Int) * 3 ≤ 2 * B + 1 := by
      push_cast at hup
      omega
    omega
  · have hdead : ∀ i, A.F (iterP A (i1 + i) q) = false ∧ A.F (A.δ (iterP A (i1 + i) q) false) = false := by
      intro i
      have hr := hper (i / π) (i % π)
      have hπ : 1 ≤ π := by omega
      rw [show i1 + i / π * π + i % π = i1 + i by
        have := Nat.div_add_mod i π
        rw [Nat.mul_comm] at this
        omega] at hr
      rw [hr]
      have hm : i % π < π := Nat.mod_lt _ (by omega)
      constructor
      · cases h : A.F (iterP A (i1 + i % π) q)
        · rfl
        · exact absurd ⟨i1 + i % π, by omega, by omega, Or.inl h⟩ hacc
      · cases h : A.F (A.δ (iterP A (i1 + i % π) q) false)
        · rfl
        · exact absurd ⟨i1 + i % π, by omega, by omega, Or.inr h⟩ hacc
    have hsp : altWord k = altWord i1 ++ altWord (k - i1) := by rw [← altWord_add]; congr 1; omega
    have hdead' : maxAcc A (iterP A i1 q) (altWord (k - i1)) = -1 := by
      apply maxAcc_altWord_dead
      intro i
      rw [← iterP_add]
      exact hdead i
    have hsmall : maxAcc A q (altWord k) ≤ 2 * i1 := by
      rw [hsp, maxAcc_append, dfaRun_altWord, hdead']
      simp only [show ¬ ((0 : Int) ≤ -1) by omega, ite_false]
      have := maxAcc_le A q (altWord i1)
      rw [altWord_length] at this
      push_cast at this ⊢
      omega
    have hZ := maxAcc_le A 0 Zw
    rw [hZlen] at hZ
    have hi1B : i1 ≤ B := by omega
    by_cases h0 : 0 ≤ maxAcc A q (altWord k)
    · simp only [h0, ite_true, hZlen] at hlow
      push_cast at hlow
      omega
    · simp only [h0, ite_false] at hlow
      push_cast at hlow
      omega

/-! ### The two-sided barrier -/

open Rule30Realization (evol)

theorem evol_succ (x : Int → Bool) (t : Nat) (p : Int) :
    evol x (t + 1) p = rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) := rfl

theorem evol_restart (x : Int → Bool) (a : Nat) :
    ∀ b p, evol (fun p => evol x a p) b p = evol x (a + b) p := by
  intro b
  induction b with
  | zero => intro p; rfl
  | succ b ih =>
    intro p
    rw [show a + (b + 1) = (a + b) + 1 by omega, evol_succ, evol_succ, ih, ih, ih]

theorem evol_shift_all {x x' : Int → Bool} {d : Int} (h : ∀ p, x' (p + d) = x p) :
    ∀ t p, evol x' t (p + d) = evol x t p := by
  intro t
  induction t with
  | zero => intro p; exact h p
  | succ t ih =>
    intro p
    rw [evol_succ, evol_succ, show p + d - 1 = (p - 1) + d by omega,
      show p + d + 1 = (p + 1) + d by omega, ih, ih, ih]

/-- Locality with translation, region bounded above. -/
theorem evol_local_le {x x' : Int → Bool} {d b : Int} (h : ∀ p, p ≤ b → x' (p + d) = x p) :
    ∀ (t : Nat) p, p + t ≤ b → evol x' t (p + d) = evol x t p := by
  intro t
  induction t with
  | zero => intro p hp; exact h p (by omega)
  | succ t ih =>
    intro p hp
    rw [evol_succ, evol_succ, show p + d - 1 = (p - 1) + d by omega,
      show p + d + 1 = (p + 1) + d by omega,
      ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]

/-- Locality with translation, region bounded below. -/
theorem evol_local_ge {x x' : Int → Bool} {d a : Int} (h : ∀ p, a ≤ p → x' (p + d) = x p) :
    ∀ (t : Nat) p, a + t ≤ p → evol x' t (p + d) = evol x t p := by
  intro t
  induction t with
  | zero => intro p hp; exact h p (by omega)
  | succ t ih =>
    intro p hp
    rw [evol_succ, evol_succ, show p + d - 1 = (p - 1) + d by omega,
      show p + d + 1 = (p + 1) + d by omega,
      ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]

/-- Locality in a window. -/
theorem evol_local {x x' : Int → Bool} {a b : Int} (h : ∀ p, a ≤ p → p ≤ b → x' p = x p) :
    ∀ (t : Nat) p, a + t ≤ p → p + t ≤ b → evol x' t p = evol x t p := by
  intro t
  induction t with
  | zero => intro p h1 h2; exact h p (by omega) (by omega)
  | succ t ih =>
    intro p h1 h2
    rw [evol_succ, evol_succ, ih (p - 1) (by omega) (by omega), ih p (by omega) (by omega),
      ih (p + 1) (by omega) (by omega)]

/-- The leftmost black cell moves left by one per step. -/
theorem left_edge {x : Int → Bool} {lo : Int} (h1 : x lo = true) (h0 : ∀ p, p < lo → x p = false) :
    ∀ t : Nat, evol x t (lo - t) = true ∧ ∀ p, p < lo - t → evol x t p = false := by
  intro t
  induction t with
  | zero => exact ⟨by simpa [evol] using h1, fun p hp => h0 p (by omega)⟩
  | succ t ih =>
    refine ⟨?_, fun p hp => ?_⟩
    · rw [evol_succ, ih.2 _ (by omega), ih.2 _ (by omega), show lo - ↑(t + 1) + 1 = lo - ↑t by omega, ih.1]
      rfl
    · rw [evol_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]; rfl

/-- The rightmost black cell moves right by one per step. -/
theorem right_edge {x : Int → Bool} {hi : Int} (h1 : x hi = true) (h0 : ∀ p, hi < p → x p = false) :
    ∀ t : Nat, evol x t (hi + t) = true ∧ ∀ p, hi + t < p → evol x t p = false := by
  intro t
  induction t with
  | zero => exact ⟨by simpa [evol] using h1, fun p hp => h0 p (by omega)⟩
  | succ t ih =>
    refine ⟨?_, fun p hp => ?_⟩
    · rw [evol_succ, show hi + ↑(t + 1) - 1 = hi + t by omega, ih.1, ih.2 _ (by omega),
        ih.2 _ (by omega)]
      rfl
    · rw [evol_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]; rfl

/-- The spatially `7`-periodic configuration, black exactly at `p ≡ 6 mod 7`. -/
def c7 (p : Int) : Bool := decide ((p + 1) % 7 = 0)

theorem c7_shift (p k : Int) : c7 (p + 7 * k) = c7 p := by
  unfold c7
  have : (p + 7 * k + 1) % 7 = (p + 1) % 7 := by omega
  rw [this]

theorem evol_c7_shift (t : Nat) (p k : Int) : evol c7 t (p + 7 * k) = evol c7 t p :=
  evol_shift_all (fun p => c7_shift p k) t p

theorem evol_c7_four (p : Int) : evol c7 4 p = c7 p := by
  have hp : p = p % 7 + 7 * (p / 7) := by omega
  rw [hp, evol_c7_shift, c7_shift]
  have hr : p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 := by
    omega
  rcases hr with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem evol_c7_period (t : Nat) (p : Int) : evol c7 (t + 4) p = evol c7 t p := by
  have h4 : (fun p => evol c7 4 p) = c7 := funext evol_c7_four
  rw [show t + 4 = 4 + t by omega, ← evol_restart, h4]

theorem evol_c7_period_mul (t k : Nat) (p : Int) : evol c7 (t + 4 * k) p = evol c7 t p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [show t + 4 * (k + 1) = (t + 4 * k) + 4 by omega, evol_c7_period, ih]

/-- **Column `0` of `c7` alternates.** -/
theorem c7_center (t : Nat) : evol c7 (t + 1) 0 = !evol c7 t 0 := by
  have ht : t = t % 4 + 4 * (t / 4) := by omega
  rw [ht, show t % 4 + 4 * (t / 4) + 1 = (t % 4 + 1) + 4 * (t / 4) by omega, evol_c7_period_mul,
    evol_c7_period_mul]
  have hr : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hr with h | h | h | h <;> rw [h] <;> decide

/-- The truncation of `c7` to `[-(7 N + 1), 7 N + 6]`. -/
def c7cut (N : Nat) (p : Int) : Bool :=
  c7 p && decide (-(7 * (N : Int) + 1) ≤ p) && decide (p ≤ 7 * (N : Int) + 6)

theorem c7cut_lo (N : Nat) : c7cut N (-(7 * (N : Int) + 1)) = true := by
  unfold c7cut c7
  have : (-(7 * (N : Int) + 1) + 1) % 7 = 0 := by omega
  simp [this] <;> omega

theorem c7cut_hi (N : Nat) : c7cut N (7 * (N : Int) + 6) = true := by
  unfold c7cut c7
  have : (7 * (N : Int) + 6 + 1) % 7 = 0 := by omega
  simp [this] <;> omega

theorem c7cut_below (N : Nat) (p : Int) (hp : p < -(7 * (N : Int) + 1)) : c7cut N p = false := by
  unfold c7cut
  have : ¬ (-(7 * (N : Int) + 1) ≤ p) := by omega
  simp [this]

theorem c7cut_above (N : Nat) (p : Int) (hp : 7 * (N : Int) + 6 < p) : c7cut N p = false := by
  unfold c7cut
  have : ¬ (p ≤ 7 * (N : Int) + 6) := by omega
  simp [this]

theorem c7cut_agree (N : Nat) (t : Nat) (p : Int) (h1 : -(7 * (N : Int) + 1) + t ≤ p)
    (h2 : p + t ≤ 7 * (N : Int) + 6) : evol (c7cut N) t p = evol c7 t p := by
  apply evol_local (a := -(7 * (N : Int) + 1)) (b := 7 * (N : Int) + 6) _ t p h1 h2
  intro q hq1 hq2
  unfold c7cut
  simp [hq1, hq2]

theorem c7cut_eq (N : Nat) (p : Int) :
    c7cut N p = if -(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6 then c7 p else false := by
  unfold c7cut
  by_cases h1 : -(7 * (N : Int) + 1) ≤ p <;> by_cases h2 : p ≤ 7 * (N : Int) + 6 <;> simp [h1, h2]

/-- Near the left end, the truncations are translates of each other. -/
theorem c7cut_left_shift (N m : Nat) (p : Int) (hp : p ≤ 7 * (N : Int) + 6) :
    c7cut (N + m) (p + (-(7 * (m : Int)))) = c7cut N p := by
  rw [c7cut_eq, c7cut_eq, show p + -(7 * (m : Int)) = p + 7 * (-(m : Int)) by omega, c7_shift]
  have e1 : (-(7 * ((N + m : Nat) : Int) + 1) ≤ p + 7 * (-(m : Int)) ∧
      p + 7 * (-(m : Int)) ≤ 7 * ((N + m : Nat) : Int) + 6) ↔
      (-(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6) := by push_cast; omega
  by_cases h : -(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6
  · rw [ite_eq_left h, ite_eq_left (e1.2 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (e1.1 h'))]

theorem c7cut_right_shift (N m : Nat) (p : Int) (hp : -(7 * (N : Int) + 1) ≤ p) :
    c7cut (N + m) (p + 7 * (m : Int)) = c7cut N p := by
  rw [c7cut_eq, c7cut_eq, c7_shift]
  have e1 : (-(7 * ((N + m : Nat) : Int) + 1) ≤ p + 7 * (m : Int) ∧
      p + 7 * (m : Int) ≤ 7 * ((N + m : Nat) : Int) + 6) ↔
      (-(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6) := by push_cast; omega
  by_cases h : -(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6
  · rw [ite_eq_left h, ite_eq_left (e1.2 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (e1.1 h'))]

/-- Center window, left-edge window and right-edge window. -/
def centerWin (w : Nat) (x : Int → Bool) : List Bool :=
  (List.range (2 * w + 1)).map fun (i : Nat) => x ((i : Int) - (w : Int))
def leftWin (e : Nat) (x : Int → Bool) (lo : Int) : List Bool :=
  (List.range e).map fun (i : Nat) => x (lo + (i : Int))
def rightWin (e : Nat) (x : Int → Bool) (hi : Int) : List Bool :=
  (List.range e).map fun (i : Nat) => x (hi - (i : Int))

/-- A ranking certificate through (leftmost black position, rightmost black position, center
window, left-edge window, right-edge window): strict decrease at every step where the center
column flips. -/
def JointCert (w e : Nat) (R : Int → Int → List Bool → List Bool → List Bool → Nat) : Prop :=
  ∀ (x : Int → Bool) (lo hi : Int), x lo = true → x hi = true → (∀ p, p < lo → x p = false) →
    (∀ p, hi < p → x p = false) → evol x 1 0 = !evol x 0 0 →
    R (lo - 1) (hi + 1) (centerWin w (fun p => evol x 1 p)) (leftWin e (fun p => evol x 1 p) (lo - 1))
        (rightWin e (fun p => evol x 1 p) (hi + 1)) <
      R lo hi (centerWin w x) (leftWin e x lo) (rightWin e x hi)

/-- Left-edge windows of the truncations do not depend on `N`. -/
theorem leftWin_indep (e N m t : Nat) (he : e ≤ 14 * N + 7) :
    leftWin e (fun p => evol (c7cut (N + m)) t p) (-(7 * ((N + m : Nat) : Int) + 1) - t) =
      leftWin e (fun p => evol (c7cut N) t p) (-(7 * (N : Int) + 1) - t) := by
  unfold leftWin
  apply map_range_congr
  intro i hi
  have := evol_local_le (x := c7cut N) (x' := c7cut (N + m)) (d := -(7 * (m : Int)))
    (b := 7 * (N : Int) + 6) (fun p hp => c7cut_left_shift N m p hp) t (-(7 * (N : Int) + 1) - t + i)
    (by omega)
  rw [show -(7 * (N : Int) + 1) - ↑t + ↑i + -(7 * (m : Int)) = -(7 * ((N + m : Nat) : Int) + 1) - ↑t + ↑i by
    push_cast; omega] at this
  exact this

/-- Right-edge windows of the truncations do not depend on `N`. -/
theorem rightWin_indep (e N m t : Nat) (he : e ≤ 14 * N + 7) :
    rightWin e (fun p => evol (c7cut (N + m)) t p) (7 * ((N + m : Nat) : Int) + 6 + t) =
      rightWin e (fun p => evol (c7cut N) t p) (7 * (N : Int) + 6 + t) := by
  unfold rightWin
  apply map_range_congr
  intro i hi
  have := evol_local_ge (x := c7cut N) (x' := c7cut (N + m)) (d := 7 * (m : Int))
    (a := -(7 * (N : Int) + 1)) (fun p hp => c7cut_right_shift N m p hp) t (7 * (N : Int) + 6 + t - i)
    (by omega)
  rw [show 7 * (N : Int) + 6 + ↑t - ↑i + 7 * (m : Int) = 7 * ((N + m : Nat) : Int) + 6 + ↑t - ↑i by
    push_cast; omega] at this
  exact this

/-- Center windows of the truncations follow the periodic configuration while the light cone
allows. -/
theorem centerWin_agree (w N t : Nat) (h : t + w ≤ 7 * N + 1) :
    centerWin w (fun p => evol (c7cut N) t p) = centerWin w (fun p => evol c7 t p) := by
  unfold centerWin
  apply map_range_congr
  intro i hi
  exact c7cut_agree N t _ (by omega) (by omega)

/-- The ranked quantity along the run of `c7cut N`. -/
def jointRank (w e : Nat) (R : Int → Int → List Bool → List Bool → List Bool → Nat) (N t : Nat) : Nat :=
  R (-(7 * (N : Int) + 1) - t) (7 * (N : Int) + 6 + t) (centerWin w (fun p => evol (c7cut N) t p))
    (leftWin e (fun p => evol (c7cut N) t p) (-(7 * (N : Int) + 1) - t))
    (rightWin e (fun p => evol (c7cut N) t p) (7 * (N : Int) + 6 + t))

theorem jointRank_step {w e : Nat} {R : Int → Int → List Bool → List Bool → List Bool → Nat}
    (hR : JointCert w e R) (N t : Nat) (ht : t + 1 ≤ 7 * N + 1) :
    jointRank w e R N (t + 1) < jointRank w e R N t := by
  have hl := left_edge (x := c7cut N) (lo := -(7 * (N : Int) + 1)) (c7cut_lo N)
    (fun p hp => c7cut_below N p hp) t
  have hr := right_edge (x := c7cut N) (hi := 7 * (N : Int) + 6) (c7cut_hi N)
    (fun p hp => c7cut_above N p hp) t
  have halt : evol (fun p => evol (c7cut N) t p) 1 0 = !evol (fun p => evol (c7cut N) t p) 0 0 := by
    simp only [evol_restart, Nat.add_zero]
    rw [c7cut_agree N (t + 1) 0 (by omega) (by omega), c7cut_agree N t 0 (by omega) (by omega)]
    exact c7_center t
  have h := hR (fun p => evol (c7cut N) t p) (-(7 * (N : Int) + 1) - t) (7 * (N : Int) + 6 + t)
    hl.1 hr.1 hl.2 hr.2 halt
  have hfun : (fun p => evol (fun p => evol (c7cut N) t p) 1 p) = (fun p => evol (c7cut N) (t + 1) p) := by
    funext p; rw [evol_restart]
  rw [hfun, show -(7 * (N : Int) + 1) - ↑t - 1 = -(7 * (N : Int) + 1) - ↑(t + 1) by push_cast; omega,
    show 7 * (N : Int) + 6 + ↑t + 1 = 7 * (N : Int) + 6 + ↑(t + 1) by push_cast; omega] at h
  exact h

theorem jointRank_chain {w e : Nat} {R : Int → Int → List Bool → List Bool → List Bool → Nat}
    (hR : JointCert w e R) (N t : Nat) :
    ∀ d, t + d ≤ 7 * N + 1 → jointRank w e R N (t + d) + d ≤ jointRank w e R N t := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := jointRank_step hR N (t + d) (by omega)
    rw [show t + (d + 1) = t + d + 1 by omega]
    omega

/-- **Two-sided barrier.** No ranking function through (leftmost and rightmost black positions,
center window, left-edge window, right-edge window) decreases at every flip of the center column of
every finite configuration. -/
theorem no_joint_local_ranking (w e : Nat) (R : Int → Int → List Bool → List Bool → List Bool → Nat) :
    ¬ JointCert w e R := by
  intro hR
  let N0 := e + 1
  have hN0 : N0 = e + 1 := rfl
  let a : Nat → List Bool := fun i =>
    leftWin e (fun p => evol (c7cut N0) (28 * i) p) (-(7 * (N0 : Int) + 1) - (28 * i : Nat)) ++
      rightWin e (fun p => evol (c7cut N0) (28 * i) p) (7 * (N0 : Int) + 6 + (28 * i : Nat))
  obtain ⟨i1, i2, hlt, -, ha⟩ := pigeonhole (e + e) a (fun i => by simp [a, leftWin, rightWin])
  have hlen : ∀ i, (leftWin e (fun p => evol (c7cut N0) (28 * i) p)
      (-(7 * (N0 : Int) + 1) - (28 * i : Nat))).length = e :=
    fun i => by simp [leftWin]
  have hsplit := List.append_inj ha (by rw [hlen, hlen])
  let t1 := 28 * i1
  let Δ := i2 - i1
  have ht2 : 28 * i2 = t1 + 28 * Δ := by omega
  have key : ∀ m, 28 * i2 + w ≤ 7 * (N0 + m) + 1 →
      jointRank w e R (N0 + m) (28 * i2) = jointRank w e R (N0 + m + 4 * Δ) t1 := by
    intro m hm
    unfold jointRank
    have e1 : -(7 * ((N0 + m : Nat) : Int) + 1) - ((28 * i2 : Nat) : Int) =
        -(7 * ((N0 + m + 4 * Δ : Nat) : Int) + 1) - (t1 : Int) := by
      rw [ht2]; push_cast; omega
    have e2 : 7 * ((N0 + m : Nat) : Int) + 6 + ((28 * i2 : Nat) : Int) =
        7 * ((N0 + m + 4 * Δ : Nat) : Int) + 6 + (t1 : Int) := by
      rw [ht2]; push_cast; omega
    have ecw : centerWin w (fun p => evol (c7cut (N0 + m)) (28 * i2) p) =
        centerWin w (fun p => evol (c7cut (N0 + m + 4 * Δ)) t1 p) := by
      rw [centerWin_agree w (N0 + m) (28 * i2) hm, centerWin_agree w (N0 + m + 4 * Δ) t1 (by omega)]
      have : (fun p => evol c7 (28 * i2) p) = (fun p => evol c7 t1 p) := by
        funext p; rw [ht2, show t1 + 28 * Δ = t1 + 4 * (7 * Δ) by omega, evol_c7_period_mul]
      rw [this]
    have ele : leftWin e (fun p => evol (c7cut (N0 + m)) (28 * i2) p)
        (-(7 * ((N0 + m : Nat) : Int) + 1) - ((28 * i2 : Nat) : Int)) =
        leftWin e (fun p => evol (c7cut (N0 + m + 4 * Δ)) t1 p)
          (-(7 * ((N0 + m + 4 * Δ : Nat) : Int) + 1) - (t1 : Int)) := by
      rw [leftWin_indep e N0 m (28 * i2) (by omega), show N0 + m + 4 * Δ = N0 + (m + 4 * Δ) by omega,
        leftWin_indep e N0 (m + 4 * Δ) t1 (by omega)]
      exact hsplit.1.symm
    have ere : rightWin e (fun p => evol (c7cut (N0 + m)) (28 * i2) p)
        (7 * ((N0 + m : Nat) : Int) + 6 + ((28 * i2 : Nat) : Int)) =
        rightWin e (fun p => evol (c7cut (N0 + m + 4 * Δ)) t1 p)
          (7 * ((N0 + m + 4 * Δ : Nat) : Int) + 6 + (t1 : Int)) := by
      rw [rightWin_indep e N0 m (28 * i2) (by omega), show N0 + m + 4 * Δ = N0 + (m + 4 * Δ) by omega,
        rightWin_indep e N0 (m + 4 * Δ) t1 (by omega)]
      exact hsplit.2.symm
    rw [ecw, ele, ere, e1, e2]
  let M0 := 28 * i2 + w
  let f : Nat → Nat := fun m => jointRank w e R (N0 + m) t1
  have period : ∀ m, M0 ≤ m → f (m + 4 * Δ) + 28 * Δ ≤ f m := by
    intro m hm
    have hc := jointRank_chain hR (N0 + m) t1 (28 * Δ) (by omega)
    rw [← ht2, key m (by omega), show N0 + m + 4 * Δ = N0 + (m + 4 * Δ) by omega] at hc
    exact hc
  have descent : ∀ k, f (M0 + k * (4 * Δ)) + k * (28 * Δ) ≤ f M0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := period (M0 + k * (4 * Δ)) (by omega)
      rw [show M0 + k * (4 * Δ) + 4 * Δ = M0 + (k + 1) * (4 * Δ) by rw [Nat.succ_mul k (4 * Δ)]; omega] at h
      rw [Nat.succ_mul k (28 * Δ)]
      omega
  have := descent (f M0 + 1)
  have hΔ : 1 ≤ 28 * Δ := by omega
  have : f M0 + 1 ≤ (f M0 + 1) * (28 * Δ) := Nat.le_mul_of_pos_right _ hΔ
  omega

end Rule30ZeroBoundaryBarriers
end Ruliology.CellularAutomata
