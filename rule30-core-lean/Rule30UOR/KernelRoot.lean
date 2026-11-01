module
public import Rule30UOR.Antidiagonal
public import Rule30UOR.Scale
public import Rule30UOR.Fixed
public import Rule30UOR.KitConstructive
public import Rule30UOR.RightPeriods
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The kernel root: the left cone is Duhamel at start `0`, and the Mahler coefficients of the right words

The bivariate specialization of the left light cone is the kernel method for the rule-60
linearization of rule 30 (`x (p−1) ⊕ x p` plus the run-end source). In Lean it is an identity
already in the repository, read at start `0`:

* **The lens is `Scale.duhamel` at `t0 = 0`.** The rule-60 transport of the seed is white left of
  the edge and black at `0` at every age (`Lpow_seed`). So the left cone is the window response at
  the center (`leftCone_eq_window60`), every column `p < 0` is its own window response
  (`cell_left_eq_window60`), and the cone from column `0` is column `−1` (`coneZero_eq_cell`,
  `coneZero_eq_window60`). The light-cone frame of `Antidiagonal` and the Witt/window frame of
  `Scale` are one identity.
* **The increment law is the local rule at column `0`** (`center_increment_eq_rule`). Its corollary
  is Jen's two-column theorem at columns `0` and `−1`: under a center period the cone from column `0`
  has no eventual period at all, for every period and from every start
  (`not_eventuallyPeriodic_coneZero`, `not_coneZeroPeriodic_any`; constructive Jen).
* **The identity is the column-0 equation of `Fixed.Phi`** with column `+1` left free
  (`fixed_iff_column_zero`): its only input from outside the left half is `Rh c t 1` on the white
  times of `c`. Nothing about the right half enters, so the identity cannot close Problem 1.
* **Mahler coefficients mod 2** (`mahlerCoeff f k = ⊕_{i ≤ k} C(k, i) f(i)`, the iterated forward
  difference at `0`, `mahlerCoeff_eq_diffPow`). Newton's inversion (`mahler_inversion`); a word has
  period `2^m` exactly when its Mahler coefficients vanish from `2^m` on
  (`period_iff_mahler_vanish`); an explicit failure of the period `2^m` at `s` gives a nonzero
  coefficient in `[2^m, s + 2^m]` (`mahler_degree_of_witness`); a right word that is not
  `2^m`-periodic has a nonzero coefficient in `[2^m, 2^j)` (`towerWord_mahler_degree`).
* **The tower in Mahler coordinates.** The prefix parity shifts the Mahler coefficients by one
  (`mahlerCoeff_prefix_succ`), so the word `k + 2` has the OR-word's coefficients shifted
  (`wordMahler_succ_succ`). Under a period `2^e` of the OR-word, Jen's doubling bit is the top Mahler
  coefficient of the word above, and every coefficient beyond `2^e` vanishes
  (`wordMahler_doubling`, `wordMahler_above_doubling`): at a doubling the Mahler degree is exactly
  `2^e`. The center is the Mahler sum of the word `t` read at `t` (`center_eq_mahler`).
* **Mahler valuation.** The word `j` is white before `j / 2` (`towerWord_white`), so its Mahler
  coefficients vanish below `⌈j/2⌉` (`wordMahler_white`) and the coefficient at `⌈j/2⌉` is the left
  edge, black (`wordMahler_even`, `wordMahler_odd`). Diagonal `j` lives in the Mahler band
  `[⌈j/2⌉, 2^(e_j))`.
-/

@[expose] public section

namespace Rule30UOR.KernelRoot

open Rule30UOR.Core Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Band Rule30UOR.Antidiagonal

/-! ## (A) The lens is Duhamel at start `0` -/

/-- The rule-60 transport of the seed is white left of the edge and black at `0` at every age. -/
theorem Lpow_seed : ∀ n : Nat, (∀ p : Int, p < 0 → Rule30UOR.Scale.Lpow n (cell 0) p = false) ∧
    Rule30UOR.Scale.Lpow n (cell 0) 0 = true
  | 0 => ⟨fun p hp => by
      show cell 0 p = false
      rw [Rule30UOR.Scale.cell_zero_eq]
      exact decide_eq_false (by cfomega),
    by
      show cell 0 0 = true
      rw [Rule30UOR.Scale.cell_zero_eq]
      rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := Lpow_seed n
    refine ⟨fun p hp => ?_, ?_⟩
    · show xor (Rule30UOR.Scale.Lpow n (cell 0) (p - 1)) (Rule30UOR.Scale.Lpow n (cell 0) p) = false
      rw [h1 (p - 1) (by cfomega), h1 p hp]
      rfl
    · show xor (Rule30UOR.Scale.Lpow n (cell 0) (0 - 1)) (Rule30UOR.Scale.Lpow n (cell 0) 0) = true
      rw [h1 (0 - 1) (by cfomega), h2]
      rfl

/-- The position `−(k + 1)`, left of the edge. -/
def leftPos (k : Nat) : Int := Int.negSucc k

theorem leftPos_neg (k : Nat) : leftPos k < 0 := Int.negSucc_lt_zero k

/-- The seed's transport is white at every position left of the edge. -/
theorem seed_transport_left (n k : Nat) : Rule30UOR.Scale.Lpow n (cell 0) (leftPos k) = false :=
  (Lpow_seed n).1 (leftPos k) (leftPos_neg k)

/-- The seed's transport is black at the center at every age. -/
theorem seed_transport_zero (n : Nat) : Rule30UOR.Scale.Lpow n (cell 0) 0 = true := (Lpow_seed n).2

/-- **The center is the complement of the window response from start `0`.** -/
theorem center_eq_not_window60 (t : Nat) : center t = !(window60 0 t 0) := by
  have h := Rule30UOR.Scale.duhamel 0 t 0
  rw [Nat.zero_add, (Lpow_seed t).2] at h
  show cell t 0 = _
  rw [h]
  cases window60 0 t 0 <;> rfl

/-- **The left light cone is the window response at the center**: the light-cone frame and the
window frame are one identity. -/
theorem leftCone_eq_window60 (t : Nat) : leftCone t = window60 0 t 0 := by
  rcases t with _ | _ | t
  · rfl
  · rfl
  · apply not_inj_aux
    rw [← center_eq_leftCone (t + 2) (by cfomega), center_eq_not_window60]

/-- **Every column left of the edge is its own window response from start `0`.** -/
theorem cell_left_eq_window60 (t : Nat) (p : Int) (hp : p < 0) : cell t p = window60 0 t p := by
  have h := Rule30UOR.Scale.duhamel 0 t p
  rw [Nat.zero_add, (Lpow_seed t).1 p hp] at h
  rw [h]
  cases window60 0 t p <;> rfl

/-- The same at the named positions `−(k + 1)`. -/
theorem cell_neg_eq_window60 (t k : Nat) : cell t (leftPos k) = window60 0 t (leftPos k) :=
  cell_left_eq_window60 t (leftPos k) (leftPos_neg k)

/-! ## (B) The increment law is the local rule at column `0` -/

theorem center_succ_rule (t : Nat) : center (t + 1) = rule (cell t (-1)) (center t) (cell t 1) := by
  show rule (cell t (LexLeanRuntime.subtract 0 1)) (cell t 0) (cell t (LexLeanRuntime.subtract 0 (-1))) = _
  rw [Rule30UOR.Scale.sub_one, Rule30UOR.Scale.sub_neg_one, show (0 : Int) - 1 = -1 by cfomega,
    show (0 : Int) + 1 = 1 by cfomega]
  rfl

theorem rule_increment_aux (a b c z : Bool) (h : bxor (rule a b c) b = bxor (c && !b) z) : z = a := by
  revert h
  cases a <;> cases b <;> cases c <;> cases z <;> decide

/-- **The cone from column `0` is column `−1`.** -/
theorem coneZero_eq_cell (t : Nat) : coneZero t = cell t (-1) := by
  have h := center_increment_all t
  rw [center_succ_rule] at h
  unfold maskedColumn at h
  exact rule_increment_aux _ _ _ _ h

/-- The cone from column `0` is the window response at column `−1`. -/
theorem coneZero_eq_window60 (t : Nat) : coneZero t = window60 0 t (-1) := by
  rw [coneZero_eq_cell]
  exact cell_left_eq_window60 t (-1) (by cfomega)

/-- **The increment law is the rule at column `0`**: the center's change is the masked column plus
column `−1`. -/
theorem center_increment_eq_rule (t : Nat) :
    bxor (center (t + 1)) (center t) = bxor (maskedColumn t) (cell t (-1)) := by
  rw [← coneZero_eq_cell]
  exact center_increment_all t

/-! ## (C) Jen's two-column theorem at columns `0` and `−1` -/

/-- **Under a center period the cone from column `0` has no eventual period**, for every period
and from every start: it is column `−1`, and Jen's theorem (constructive form) forbids two
eventually periodic columns. -/
theorem not_eventuallyPeriodic_coneZero {T P : Nat} (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic coneZero := by
  rintro ⟨S, Q, hQ, hz⟩
  apply Rule30UOR.KitConstructive.jen 0 (-1) (by cfomega)
  refine ⟨⟨T, P, hP, fun t ht => ?_⟩, ⟨S, Q, hQ, fun t ht => ?_⟩⟩
  · show Ruliology.CellularAutomata.Rule30Jen.cell (t + P) 0 = Ruliology.CellularAutomata.Rule30Jen.cell t 0
    rw [← Rule30UOR.Scale.cell_eq_kit, ← Rule30UOR.Scale.cell_eq_kit]
    exact hc t ht
  · show Ruliology.CellularAutomata.Rule30Jen.cell (t + Q) (-1) =
      Ruliology.CellularAutomata.Rule30Jen.cell t (-1)
    rw [← Rule30UOR.Scale.cell_eq_kit, ← Rule30UOR.Scale.cell_eq_kit, ← coneZero_eq_cell,
      ← coneZero_eq_cell]
    exact hz t ht

/-- First-order form: under a center period `P` from `T`, the cone from column `0` has no period
`Q > 0` from any start `S`. Supersedes `Antidiagonal.not_coneZeroPeriodic_from` (`Q = P`). -/
theorem not_coneZeroPeriodic_any (T P S Q : Nat) (hP : 0 < P) (hQ : 0 < Q)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) : ¬ ConeZeroPeriodic S Q :=
  fun hz => not_eventuallyPeriodic_coneZero hP hc ⟨S, Q, hQ, hz⟩

/-! ## (D) The identity is the column-0 equation of the recombination -/

theorem column_zero_aux (x b l r : Bool) :
    x = Ruliology.CellularAutomata.Rule30Jen.rule l b r ↔ bxor x b = bxor (r && !b) l := by
  cases x <;> cases b <;> cases l <;> cases r <;> decide

/-- **One-half invariance**: a column is a fixed point of `Phi` exactly when it satisfies the
column-`0` increment law with its own driven halves, column `+1` of the right half left free. -/
theorem fixed_iff_column_zero (c : Nat → Bool) :
    (∀ t, c (t + 1) = Rule30UOR.Fixed.Phi c t) ↔
      ∀ t, bxor (c (t + 1)) (c t) =
        bxor (Rule30UOR.Fixed.Rh c t 1 && !(c t)) (Rule30UOR.Fixed.Lh c t (-1)) :=
  ⟨fun h t => (column_zero_aux (c (t + 1)) (c t) (Rule30UOR.Fixed.Lh c t (-1))
      (Rule30UOR.Fixed.Rh c t 1)).1 (h t),
    fun h t => (column_zero_aux (c (t + 1)) (c t) (Rule30UOR.Fixed.Lh c t (-1))
      (Rule30UOR.Fixed.Rh c t 1)).2 (h t)⟩

/-! ## (E) Mahler coefficients mod 2 -/

/-- The Mahler coefficient of `f` at `k`, mod 2: `⊕_{i ≤ k} C(k, i) f(i)`. -/
def mahlerCoeff (f : Nat → Bool) (k : Nat) : Bool := xorBelow (fun i => pascalParity k i && f i) (k + 1)

/-- The iterated forward difference. -/
def diffPow : Nat → (Nat → Bool) → Nat → Bool
  | 0, f => f
  | k + 1, f => fun n => bxor (diffPow k f n) (diffPow k f (n + 1))

/-- Pascal's rule on a binomial sum. -/
theorem pascalSum_succ (n : Nat) (g : Nat → Bool) :
    xorBelow (fun a => pascalParity (n + 1) a && g a) (n + 2) =
      bxor (xorBelow (fun a => pascalParity n a && g a) (n + 1))
        (xorBelow (fun a => pascalParity n a && g (a + 1)) (n + 1)) := by
  have h1 : xorBelow (fun a => pascalParity (n + 1) a && g a) (n + 2) =
      bxor (pascalParity (n + 1) 0 && g 0)
        (xorBelow (fun m => pascalParity (n + 1) (m + 1) && g (m + 1)) (n + 1)) :=
    xorBelow_front _ (n + 1)
  have h2 : xorBelow (fun a => pascalParity n a && g a) (n + 1) =
      bxor (pascalParity n 0 && g 0) (xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n) :=
    xorBelow_front _ n
  have h3 : xorBelow (fun m => pascalParity (n + 1) (m + 1) && g (m + 1)) (n + 1) =
      bxor (xorBelow (fun m => pascalParity n m && g (m + 1)) (n + 1))
        (xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) (n + 1)) := by
    rw [← xorBelow_bxor]
    exact xorBelow_congr _ _ (n + 1) (fun m _ => by
      show (pascalParity (n + 1) (m + 1) && g (m + 1)) =
        bxor (pascalParity n m && g (m + 1)) (pascalParity n (m + 1) && g (m + 1))
      rw [pascalParity_succ, cone_and_bxor])
  have h4 : xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) (n + 1) =
      xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n := by
    show bxor (xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n)
      (pascalParity n (n + 1) && g (n + 1)) = _
    rw [pascalParity_gt n (n + 1) (by cfomega), Bool.false_and, cone_bxor_false_right]
  rw [h1, h2, h3, h4, pascalParity_zero_right, pascalParity_zero_right]
  cases g 0 <;> cases xorBelow (fun m => pascalParity n m && g (m + 1)) (n + 1) <;>
    cases xorBelow (fun m => pascalParity n (m + 1) && g (m + 1)) n <;> rfl

/-- The iterated difference composes. -/
theorem diffPow_add (a b : Nat) (f : Nat → Bool) : diffPow (a + b) f = diffPow a (diffPow b f) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by cfomega]
    show (fun n => bxor (diffPow (a + b) f n) (diffPow (a + b) f (n + 1))) =
      (fun n => bxor (diffPow a (diffPow b f) n) (diffPow a (diffPow b f) (n + 1)))
    rw [ih]

/-- **The iterated difference is the binomial sum**: `Δ^k f (n) = ⊕_{i ≤ k} C(k, i) f(n + i)`. -/
theorem diffPow_eq_sum (f : Nat → Bool) :
    ∀ k n, diffPow k f n = xorBelow (fun i => pascalParity k i && f (n + i)) (k + 1)
  | 0, n => by
    show f n = bxor false (pascalParity 0 0 && f (n + 0))
    rw [pascalParity_zero_right, Nat.add_zero]
    cases f n <;> rfl
  | k + 1, n => by
    have h : xorBelow (fun a => pascalParity (k + 1) a && f (n + a)) (k + 2) =
        bxor (xorBelow (fun a => pascalParity k a && f (n + a)) (k + 1))
          (xorBelow (fun a => pascalParity k a && f (n + (a + 1))) (k + 1)) :=
      pascalSum_succ k (fun i => f (n + i))
    have e : xorBelow (fun i => pascalParity k i && f (n + 1 + i)) (k + 1) =
        xorBelow (fun a => pascalParity k a && f (n + (a + 1))) (k + 1) :=
      xorBelow_congr _ _ (k + 1) (fun i _ => by rw [show n + 1 + i = n + (i + 1) by cfomega])
    show bxor (diffPow k f n) (diffPow k f (n + 1)) =
      xorBelow (fun i => pascalParity (k + 1) i && f (n + i)) (k + 2)
    rw [diffPow_eq_sum f k n, diffPow_eq_sum f k (n + 1), e, h]

/-- The Mahler coefficient is the iterated difference at `0`. -/
theorem mahlerCoeff_eq_diffPow (f : Nat → Bool) (k : Nat) : mahlerCoeff f k = diffPow k f 0 := by
  rw [diffPow_eq_sum]
  exact xorBelow_congr _ _ (k + 1) (fun i _ => by rw [Nat.zero_add])

/-- **Newton's forward formula mod 2**: `f(n + s) = ⊕_{k ≤ s} C(s, k) Δ^k f (n)`. -/
theorem newton (f : Nat → Bool) :
    ∀ s n, f (n + s) = xorBelow (fun k => pascalParity s k && diffPow k f n) (s + 1)
  | 0, n => by
    show f (n + 0) = bxor false (pascalParity 0 0 && f n)
    rw [pascalParity_zero_right, Nat.add_zero]
    cases f n <;> rfl
  | s + 1, n => by
    rw [show n + (s + 1) = (n + 1) + s by cfomega, newton f s (n + 1)]
    have h : xorBelow (fun a => pascalParity (s + 1) a && diffPow a f n) (s + 2) =
        bxor (xorBelow (fun a => pascalParity s a && diffPow a f n) (s + 1))
          (xorBelow (fun a => pascalParity s a && diffPow (a + 1) f n) (s + 1)) :=
      pascalSum_succ s (fun k => diffPow k f n)
    have e : xorBelow (fun a => pascalParity s a && diffPow (a + 1) f n) (s + 1) =
        bxor (xorBelow (fun a => pascalParity s a && diffPow a f n) (s + 1))
          (xorBelow (fun a => pascalParity s a && diffPow a f (n + 1)) (s + 1)) := by
      rw [← xorBelow_bxor]
      exact xorBelow_congr _ _ (s + 1) (fun a _ => by
        show (pascalParity s a && bxor (diffPow a f n) (diffPow a f (n + 1))) =
          bxor (pascalParity s a && diffPow a f n) (pascalParity s a && diffPow a f (n + 1))
        cases pascalParity s a <;> cases diffPow a f n <;> cases diffPow a f (n + 1) <;> rfl)
    show _ = xorBelow (fun k => pascalParity (s + 1) k && diffPow k f n) (s + 2)
    rw [h, e]
    cases xorBelow (fun a => pascalParity s a && diffPow a f n) (s + 1) <;>
      cases xorBelow (fun a => pascalParity s a && diffPow a f (n + 1)) (s + 1) <;> rfl

/-- **Mahler inversion mod 2**: `f(s) = ⊕_{k ≤ s} C(s, k) β_k`. -/
theorem mahler_inversion (f : Nat → Bool) (s : Nat) :
    f s = xorBelow (fun k => pascalParity s k && mahlerCoeff f k) (s + 1) := by
  have h := newton f s 0
  rw [Nat.zero_add] at h
  rw [h]
  exact xorBelow_congr _ _ (s + 1) (fun k _ => by rw [mahlerCoeff_eq_diffPow])

/-- A shift by `2^m` is decided by the Mahler coefficients in `[2^m, s + 2^m]`. -/
theorem shift_of_mahler_vanish (f : Nat → Bool) (m s : Nat)
    (h : ∀ k, twopow m ≤ k → k ≤ s + twopow m → mahlerCoeff f k = false) :
    f (s + twopow m) = f s := by
  have hA : f (s + twopow m) = xorBelow (fun k => pascalParity s k && mahlerCoeff f k) (twopow m) := by
    rw [mahler_inversion f (s + twopow m),
      xorBelow_of_vanish (fun k => pascalParity (s + twopow m) k && mahlerCoeff f k) (twopow m)
        (s + twopow m + 1)
        (fun k hk1 hk2 => by
          show (pascalParity (s + twopow m) k && mahlerCoeff f k) = false
          rw [h k hk1 (by cfomega), Bool.and_false])
        (s + twopow m + 1) (by cfomega) (Nat.le_refl _)]
    exact xorBelow_congr _ _ (twopow m) (fun k hk => by
      show (pascalParity (s + twopow m) k && mahlerCoeff f k) = (pascalParity s k && mahlerCoeff f k)
      have hp := pascalParity_add_twopow_mul m s k 1 hk
      rw [Nat.mul_one] at hp
      rw [hp])
  have hB : f s = xorBelow (fun k => pascalParity s k && mahlerCoeff f k) (twopow m) := by
    rw [mahler_inversion f s]
    have e1 := xorBelow_of_vanish (fun k => pascalParity s k && mahlerCoeff f k) (s + 1)
      (s + twopow m + 1)
      (fun k hk1 _ => by
        show (pascalParity s k && mahlerCoeff f k) = false
        rw [pascalParity_gt s k (by cfomega), Bool.false_and])
      (s + twopow m + 1) (by cfomega) (Nat.le_refl _)
    have e2 := xorBelow_of_vanish (fun k => pascalParity s k && mahlerCoeff f k) (twopow m)
      (s + twopow m + 1)
      (fun k hk1 hk2 => by
        show (pascalParity s k && mahlerCoeff f k) = false
        rw [h k hk1 (by cfomega), Bool.and_false])
      (s + twopow m + 1) (by cfomega) (Nat.le_refl _)
    exact e1.symm.trans e2
  rw [hA, hB]

/-- **Vanishing Mahler coefficients from `2^m` on give the period `2^m`.** -/
theorem period_of_mahler_vanish (f : Nat → Bool) (m : Nat)
    (h : ∀ k, twopow m ≤ k → mahlerCoeff f k = false) : ∀ s, f (s + twopow m) = f s :=
  fun s => shift_of_mahler_vanish f m s (fun k hk _ => h k hk)

/-- Frobenius for the difference: `Δ^(2^e) f (n) = f(n) ⊕ f(n + 2^e)`. -/
theorem diffPow_twopow : ∀ (e : Nat) (f : Nat → Bool) (n : Nat),
    diffPow (twopow e) f n = bxor (f n) (f (n + twopow e))
  | 0, _, _ => rfl
  | e + 1, f, n => by
    rw [twopow_succ, diffPow_add, diffPow_twopow e (diffPow (twopow e) f) n, diffPow_twopow e f n,
      diffPow_twopow e f (n + twopow e), Nat.add_assoc]
    cases f n <;> cases f (n + twopow e) <;> cases f (n + (twopow e + twopow e)) <;> rfl

/-- A constant has vanishing differences. -/
theorem diffPow_const (b : Bool) : ∀ k n, diffPow (k + 1) (fun _ => b) n = false
  | 0, _ => by
    show bxor b b = false
    cases b <;> rfl
  | k + 1, n => by
    show bxor (diffPow (k + 1) (fun _ => b) n) (diffPow (k + 1) (fun _ => b) (n + 1)) = false
    rw [diffPow_const b k n, diffPow_const b k (n + 1)]
    rfl

/-- **The period `2^n` kills the Mahler coefficients from `2^n` on.** -/
theorem mahler_vanish_of_period (f : Nat → Bool) (n : Nat)
    (h : ∀ s, f (s + twopow n) = f s) : ∀ k, twopow n ≤ k → mahlerCoeff f k = false := by
  intro k hk
  have e : diffPow (twopow n) f = fun _ => false := funext (fun x => by
    rw [diffPow_twopow, h x]
    cases f x <;> rfl)
  rcases Nat.lt_or_ge (twopow n) k with hlt | hle
  · rw [mahlerCoeff_eq_diffPow, show k = (k - twopow n - 1 + 1) + twopow n by cfomega, diffPow_add, e]
    exact diffPow_const false (k - twopow n - 1) 0
  · rw [mahlerCoeff_eq_diffPow, show k = twopow n by cfomega, e]

/-- **Periods `2^m` are exactly the vanishing of the Mahler coefficients from `2^m` on.** -/
theorem period_iff_mahler_vanish (f : Nat → Bool) (m : Nat) :
    (∀ s, f (s + twopow m) = f s) ↔ ∀ k, twopow m ≤ k → mahlerCoeff f k = false :=
  ⟨mahler_vanish_of_period f m, period_of_mahler_vanish f m⟩

/-- A bounded search on a Boolean sequence, decided by recursion. -/
theorem bool_search (g : Nat → Bool) (a : Nat) :
    ∀ b, (∃ k, a ≤ k ∧ k < b ∧ g k = true) ∨ (∀ k, a ≤ k → k < b → g k = false)
  | 0 => Or.inr (fun k _ hk => absurd hk (Nat.not_lt_zero k))
  | b + 1 => by
    rcases bool_search g a b with ⟨k, h1, h2, h3⟩ | hno
    · exact Or.inl ⟨k, h1, by cfomega, h3⟩
    · cases hg : g b with
      | true =>
        rcases Nat.lt_or_ge b a with hba | hab
        · exact Or.inr (fun k hk1 hk2 => hno k hk1 (by cfomega))
        · exact Or.inl ⟨b, hab, by cfomega, hg⟩
      | false =>
        exact Or.inr (fun k hk1 hk2 => by
          rcases Nat.lt_or_ge k b with hkb | hkb
          · exact hno k hk1 hkb
          · rw [show k = b by cfomega]
            exact hg)

/-- **Constructive degree bound**: an explicit failure of the shift by `2^m` at `s` gives a
nonzero Mahler coefficient in `[2^m, s + 2^m]`. -/
theorem mahler_degree_of_witness (f : Nat → Bool) (m s : Nat) (hs : f (s + twopow m) ≠ f s) :
    ∃ k, twopow m ≤ k ∧ k ≤ s + twopow m ∧ mahlerCoeff f k = true := by
  rcases bool_search (mahlerCoeff f) (twopow m) (s + twopow m + 1) with ⟨k, h1, h2, h3⟩ | hno
  · exact ⟨k, h1, by cfomega, h3⟩
  · exact absurd (shift_of_mahler_vanish f m s (fun k hk1 hk2 => hno k hk1 (by cfomega))) hs

/-! ## The right words in Mahler coordinates -/

/-- The Mahler coefficient of the right word `j` at `k`. -/
def wordMahler (j k : Nat) : Bool := mahlerCoeff (towerWord j) k

/-- The word `j` has a nonzero Mahler coefficient in `[2^m, 2^j)`. -/
def WordMahlerAbove (j m : Nat) : Prop := ∃ k, twopow m ≤ k ∧ k < twopow j ∧ wordMahler j k = true

/-- The Mahler coefficients of the word `j` vanish from `2^m` on. -/
def WordMahlerVanish (j m : Nat) : Prop := ∀ k, twopow m ≤ k → wordMahler j k = false

/-- **A right word has period `2^m` exactly when its Mahler coefficients vanish from `2^m` on.** -/
theorem wordPeriodic_iff_mahler (j m : Nat) :
    Rule30UOR.RightPeriods.WordPeriodic j (twopow m) ↔ WordMahlerVanish j m :=
  period_iff_mahler_vanish (towerWord j) m

/-- The Mahler coefficients of the word `j` vanish from `2^j` on. -/
theorem wordMahler_vanish_jen (j : Nat) : WordMahlerVanish j j :=
  mahler_vanish_of_period (towerWord j) j (towerWord_add_twopow j)

/-- **Mahler degree of the right words**: a word that is not `2^m`-periodic has a nonzero Mahler
coefficient in `[2^m, 2^j)`. With minimal period `2^e`, the Mahler degree lies in
`[2^(e−1), 2^e)`. -/
theorem towerWord_mahler_degree (j m : Nat)
    (hmin : ¬ Rule30UOR.RightPeriods.WordPeriodic j (twopow m)) : WordMahlerAbove j m := by
  rcases bool_search (wordMahler j) (twopow m) (twopow j) with ⟨k, h1, h2, h3⟩ | hno
  · exact ⟨k, h1, h2, h3⟩
  · exact absurd ((wordPeriodic_iff_mahler j m).2 (fun k hk => by
      rcases Nat.lt_or_ge k (twopow j) with hkj | hkj
      · exact hno k hk hkj
      · exact wordMahler_vanish_jen j k hkj)) hmin

/-- **The prefix parity shifts the Mahler coefficients by one place.** -/
theorem mahlerCoeff_prefix_succ (g : Nat → Bool) (i : Nat) :
    mahlerCoeff (xorBelow g) (i + 1) = mahlerCoeff g i := by
  have e : diffPow 1 (xorBelow g) = g := funext (fun n => by
    show bxor (xorBelow g n) (bxor (xorBelow g n) (g n)) = g n
    cases xorBelow g n <;> cases g n <;> rfl)
  rw [mahlerCoeff_eq_diffPow, mahlerCoeff_eq_diffPow, diffPow_add, e]

theorem mahlerCoeff_prefix_zero (g : Nat → Bool) : mahlerCoeff (xorBelow g) 0 = false := by
  rw [mahlerCoeff_eq_diffPow]
  rfl

/-- **The tower in Mahler coordinates**: the word `k + 2` carries the OR-word's Mahler coefficients
one place up. -/
theorem wordMahler_succ_succ (k i : Nat) : wordMahler (k + 2) (i + 1) = mahlerCoeff (orWord k) i := by
  have e : towerWord (k + 2) = xorBelow (orWord k) := funext (towerWord_eq_prefix k)
  unfold wordMahler
  rw [e, mahlerCoeff_prefix_succ]

theorem wordMahler_succ_zero (j : Nat) : wordMahler (j + 1) 0 = false := by
  unfold wordMahler
  rw [mahlerCoeff_eq_diffPow]
  exact towerWord_succ_zero j

/-- Under a period `2^e` of the OR-word, the `2^e`-th difference of the word above is its
doubling bit. -/
theorem diffPow_doubling (k e : Nat) (h : Rule30UOR.RightPeriods.OrPeriodic k (twopow e)) :
    diffPow (twopow e) (towerWord (k + 2)) = fun _ => towerWord (k + 2) (twopow e) :=
  funext (fun x => by
    rw [diffPow_twopow, Rule30UOR.RightPeriods.towerWord_shift k (twopow e) h x]
    cases towerWord (k + 2) x <;> cases towerWord (k + 2) (twopow e) <;> rfl)

/-- **Jen's doubling bit is the top Mahler coefficient**: under a period `2^e` of the OR-word, the
Mahler coefficient of the word above at `2^e` is its doubling bit. -/
theorem wordMahler_doubling (k e : Nat) (h : Rule30UOR.RightPeriods.OrPeriodic k (twopow e)) :
    wordMahler (k + 2) (twopow e) = towerWord (k + 2) (twopow e) := by
  unfold wordMahler
  rw [mahlerCoeff_eq_diffPow, diffPow_doubling k e h]

/-- Under a period `2^e` of the OR-word, every Mahler coefficient of the word above beyond `2^e`
vanishes: at a doubling the Mahler degree is exactly `2^e`. -/
theorem wordMahler_above_doubling (k e n : Nat) (h : Rule30UOR.RightPeriods.OrPeriodic k (twopow e))
    (hn : twopow e < n) : wordMahler (k + 2) n = false := by
  unfold wordMahler
  rw [mahlerCoeff_eq_diffPow, show n = (n - twopow e - 1 + 1) + twopow e by cfomega, diffPow_add,
    diffPow_doubling k e h]
  exact diffPow_const _ (n - twopow e - 1) 0

/-- **The center is the Mahler sum of the word `t` read at `t`**: `center t = ⊕_{k ≤ t} C(t, k) β^(t)_k`. -/
theorem center_eq_mahler (t : Nat) :
    center t = xorBelow (fun k => pascalParity t k && wordMahler t k) (t + 1) := by
  rw [center_eq_towerWord]
  exact mahler_inversion (towerWord t) t

/-! ## The Mahler valuation of the right words -/

/-- Every right word starts white: `W_j(s) = 0` for `2s < j` (the left edge seen from the tower). -/
theorem towerWord_white (j s : Nat) (h : s + s < j) : towerWord j s = false := by
  have hs : s < twopow j :=
    Nat.lt_of_lt_of_le (by cfomega : s < j) (Nat.le_of_lt (Rule30UOR.Interfaces.twopow_gt_self j))
  unfold towerWord
  rw [Nat.mod_eq_of_lt hs, ← Rule30UOR.Ledger.cell_eq_rdiag s j ((s : Int) - (j : Int)) rfl]
  exact Rule30UOR.Scale.cell_left_white s _ (by cfomega)

/-- Inside its first period the word `j` is the cell on the diagonal `j`. -/
private theorem towerWord_cell (j s : Nat) (hs : s < twopow j) (p : Int) (hp : (s : Int) - (j : Int) = p) :
    towerWord j s = cell s p := by
  unfold towerWord
  rw [Nat.mod_eq_of_lt hs, Rule30UOR.Ledger.cell_eq_rdiag s j p hp]

/-- The Mahler coefficients of the word `j` vanish below `j / 2`. -/
theorem wordMahler_white (j k : Nat) (h : k + k < j) : wordMahler j k = false := by
  unfold wordMahler mahlerCoeff
  exact (xorBelow_congr _ (fun _ => false) (k + 1) (fun i hi => by
    show (pascalParity k i && towerWord j i) = false
    rw [towerWord_white j i (by cfomega), Bool.and_false])).trans (xorBelow_false _)

/-- The first Mahler coefficient after a white prefix is the word's first value. -/
theorem wordMahler_first (j k : Nat) (h : ∀ i, i < k → towerWord j i = false) :
    wordMahler j k = towerWord j k := by
  unfold wordMahler mahlerCoeff
  show bxor (xorBelow (fun i => pascalParity k i && towerWord j i) k) (pascalParity k k && towerWord j k) = _
  rw [(xorBelow_congr _ (fun _ => false) k (fun i hi => by
    show (pascalParity k i && towerWord j i) = false
    rw [h i hi, Bool.and_false])).trans (xorBelow_false _), pascalParity_self]
  cases towerWord j k <;> rfl

private theorem cell_left_edge_core (t : Nat) : cell t (-(t : Int)) = true := by
  rw [Rule30UOR.Scale.cell_eq_kit]
  exact Ruliology.CellularAutomata.Rule30Jen.cell_left_edge t

private theorem cell_left_edge_next (t : Nat) : cell (t + 1) (-(t : Int)) = true := by
  show rule (cell t (LexLeanRuntime.subtract (-(t : Int)) 1)) (cell t (-(t : Int)))
    (cell t (LexLeanRuntime.subtract (-(t : Int)) (-1))) = true
  rw [Rule30UOR.Scale.sub_one, Rule30UOR.Scale.cell_left_white t _ (by cfomega), cell_left_edge_core t]
  rfl

/-- **The Mahler valuation of the word `2a` is `a`**: the coefficient at `a` is the left edge. -/
theorem wordMahler_even (a : Nat) : wordMahler (a + a) a = true := by
  rw [wordMahler_first (a + a) a (fun i hi => towerWord_white (a + a) i (by cfomega)),
    towerWord_cell (a + a) a (by have := Rule30UOR.Interfaces.twopow_gt_self (a + a); cfomega) (-(a : Int))
      (by cfomega)]
  exact cell_left_edge_core a

/-- **The Mahler valuation of the word `2a + 1` is `a + 1`**: the coefficient is the cell next to
the left edge. -/
theorem wordMahler_odd (a : Nat) : wordMahler (a + a + 1) (a + 1) = true := by
  rw [wordMahler_first (a + a + 1) (a + 1) (fun i hi => towerWord_white (a + a + 1) i (by cfomega)),
    towerWord_cell (a + a + 1) (a + 1) (by have := Rule30UOR.Interfaces.twopow_gt_self (a + a + 1); cfomega)
      (-(a : Int)) (by cfomega)]
  exact cell_left_edge_next a

end Rule30UOR.KernelRoot
