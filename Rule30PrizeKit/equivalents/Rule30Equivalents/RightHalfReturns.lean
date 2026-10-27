module

public import Rule30Equivalents.ShiftOrbit
public import Rule30Equivalents.LimitPoints
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-!
# The right half returns to its start only finitely often

Theorem 4.5 of J. Kopra, *Rapid left expansivity, a commonality between Wolfram's Rule 30 and
powers of p/q*, for rule 30. Run rule 30 from a configuration `x` with a leftmost black cell,
possibly with infinitely many black cells to its right. Then the right half of row `t`, its cells
`p ≥ 0`, equals that of `x` for only finitely many `t` (`finite_returns`). For the single seed
this is `LimitPoints.half_cell_eq_zero_iff`.

* `eventuallyPeriodic_of_return` (Kopra's Lemma 4.3): one return at a time `t ≥ 1` makes the
  right half of `x` eventually periodic. After the return, row `n` agrees with row `n mod t` from
  cell `n` on (`evol_mod_of_return`), so far to the right every two adjacent columns repeat with
  period `t` for a long time. Rule 30 is left-permutive: two adjacent columns at times `0, …, K`
  determine the `K` cells to their left at time `0` (`eq_left_of_eq_columns`). So the right half
  of `x` has at most `4^t` factors of length `4^t`, and Morse–Hedlund makes it eventually periodic.
* `periodic_rows` (Kopra's Lemma 4.4): if rows `0` and `t` are `P`-periodic from a cell `c` on, so
  is every row in between, by the same reconstruction run leftward from the light cone.
* With infinitely many returns every row is `P`-periodic from some cell on, and then the columns
  there repeat with the period of a return. Two adjacent periodic columns contradict Jen's theorem
  for configurations with a leftmost black cell (`Rule30FiniteConfigs.not_adjacent`).
-/

@[expose] public section

namespace Rule30Equivalents.RightHalfReturns

open Ruliology.CellularAutomata Rule30Jen Rule30Realization Rule30ZeroBoundaryBarriers

variable {x : ℤ → Bool}

/-- After a return at time `t`, row `t + j` agrees with row `j` from cell `j` on. -/
theorem evol_add_of_return {t : ℕ} (hr : ∀ p : ℤ, 0 ≤ p → evol x t p = x p) (j : ℕ) {q : ℤ}
    (hq : (j : ℤ) ≤ q) : evol x (t + j) q = evol x j q := by
  rw [← evol_restart]
  have := evol_local_ge (x := x) (x' := fun p => evol x t p) (d := 0) (a := 0)
    (fun p hp => by rw [add_zero]; exact hr p hp) j q (by omega)
  simpa using this

/-- After a return at time `t ≥ 1`, row `n` agrees with row `n mod t` from cell `n` on. -/
theorem evol_mod_of_return {t : ℕ} (hr : ∀ p : ℤ, 0 ≤ p → evol x t p = x p) (ht : 0 < t) :
    ∀ n : ℕ, ∀ q : ℤ, (n : ℤ) ≤ q → evol x n q = evol x (n % t) q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hq
    by_cases hn : n < t
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨k, rfl⟩ : ∃ k, n = t + k := ⟨n - t, by omega⟩
      rw [evol_add_of_return hr k (by omega), Nat.add_mod_left, ih k (by omega) q (by omega)]

/-- Rule 30 is left-permutive (`Rule30FiniteConfigs.evol_left`): if the columns `i, i + 1` of
`evol x` and `i', i' + 1` of `evol x'` agree at times `0, …, n`, then so do the columns `k` cells to
their left at times `0, …, n − k`. -/
theorem eq_left_of_eq_columns {x' : ℤ → Bool} {i i' : ℤ} {n : ℕ}
    (h : ∀ s ≤ n, evol x s i = evol x' s i' ∧ evol x s (i + 1) = evol x' s (i' + 1)) :
    ∀ k ≤ n, ∀ s ≤ n - k, evol x s (i - k) = evol x' s (i' - k) ∧
      evol x s (i - k + 1) = evol x' s (i' - k + 1)
  | 0 => fun _ s hs => by simpa using h s (by omega)
  | k + 1 => fun hk s hs => by
    have ih := eq_left_of_eq_columns h k (by omega)
    have e : ∀ j : ℤ, j - ((k + 1 : ℕ) : ℤ) = j - k - 1 := fun j => by push_cast; omega
    have e' : ∀ j : ℤ, j - ((k + 1 : ℕ) : ℤ) + 1 = j - k := fun j => by push_cast; omega
    rw [e', e', e, e, Rule30FiniteConfigs.evol_left x, Rule30FiniteConfigs.evol_left x',
      (ih (s + 1) (by omega)).1, (ih s (by omega)).1, (ih s (by omega)).2]
    exact ⟨rfl, rfl⟩

/-- **Kopra's Lemma 4.3 for rule 30.** A return of the right half at a time `t ≥ 1` makes the
right half of `x` eventually periodic. -/
theorem eventuallyPeriodic_of_return {t : ℕ} (ht : 0 < t)
    (hr : ∀ p : ℤ, 0 ≤ p → evol x t p = x p) : EventuallyPeriodic fun n : ℕ => x n := by
  rw [ShiftOrbit.eventuallyPeriodic_iff_exists_ncard_factors_le]
  refine ⟨4 ^ t, ?_⟩
  set K := 4 ^ t with hK
  -- the columns `i + K, i + K + 1` at times `0, …, t - 1`
  set τ : ℕ → Fin t → Bool × Bool :=
    fun i s => (evol x s ((i + K : ℕ) : ℤ), evol x s ((i + K : ℕ) + 1 : ℤ)) with hτ
  -- the factor of length `K` at `i`
  set g : ℕ → Fin K → Bool := fun i j => x ((i + j : ℕ) : ℤ) with hg
  have key : ∀ i i', τ i = τ i' → g i = g i' := by
    intro i i' he
    -- the two pairs of columns agree at all times `≤ K`
    have hcol : ∀ s ≤ K, evol x s ((i + K : ℕ) : ℤ) = evol x s ((i' + K : ℕ) : ℤ) ∧
        evol x s ((i + K : ℕ) + 1 : ℤ) = evol x s ((i' + K : ℕ) + 1 : ℤ) := by
      intro s hs
      have h1 := congrFun he ⟨s % t, Nat.mod_lt _ ht⟩
      simp only [hτ, Prod.mk.injEq] at h1
      rw [evol_mod_of_return hr ht s ((i + K : ℕ) : ℤ) (by push_cast; omega),
        evol_mod_of_return hr ht s ((i' + K : ℕ) : ℤ) (by push_cast; omega),
        evol_mod_of_return hr ht s (((i + K : ℕ) : ℤ) + 1) (by push_cast; omega),
        evol_mod_of_return hr ht s (((i' + K : ℕ) : ℤ) + 1) (by push_cast; omega)]
      exact h1
    funext j
    have hj := j.2
    have := (eq_left_of_eq_columns hcol (K - j) (by omega) 0 (by omega)).1
    rw [show ((i + K : ℕ) : ℤ) - ((K - j : ℕ) : ℤ) = ((i + j : ℕ) : ℤ) by push_cast; omega,
      show ((i' + K : ℕ) : ℤ) - ((K - j : ℕ) : ℤ) = ((i' + j : ℕ) : ℤ) by push_cast; omega]
      at this
    exact this
  have hsub : ShiftOrbit.factors (fun n : ℕ => x n) K ⊆
      Set.range fun u : Fin t → Bool × Bool => g (Function.invFun τ u) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨τ i, key _ _ (Function.invFun_eq ⟨i, rfl⟩)⟩
  calc (ShiftOrbit.factors (fun n : ℕ => x n) K).ncard
      ≤ (Set.range fun u : Fin t → Bool × Bool => g (Function.invFun τ u)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set (Fin t → Bool × Bool)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le (Set.toFinite _)
    _ = K := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod,
          Fintype.card_bool, Fintype.card_fin]

/-- **Kopra's Lemma 4.4 for rule 30.** If rows `0` and `t` are `P`-periodic from cell `c` on, so
is every row in between. -/
theorem periodic_rows {t P : ℕ} {c : ℤ} (h0 : ∀ q, c ≤ q → x (q + P) = x q)
    (ht : ∀ q, c ≤ q → evol x t (q + P) = evol x t q) :
    ∀ j ≤ t, ∀ q, c ≤ q → evol x j (q + P) = evol x j q := by
  have key : ∀ n : ℕ, ∀ j ≤ t, ∀ q, c ≤ q → c + t ≤ q + n → evol x j (q + P) = evol x j q := by
    intro n
    induction n with
    | zero =>
      -- far right, every row inherits the period of row `0`
      intro j _ q _ hq
      exact evol_local_ge (x := x) (x' := x) (d := P) (a := c) h0 j q (by omega)
    | succ n ih =>
      intro j hj q hc hq
      by_cases hjt : j = t
      · subst hjt
        exact ht q hc
      · have e1 := Rule30FiniteConfigs.evol_left x j (q + 1)
        have e2 := Rule30FiniteConfigs.evol_left x j (q + 1 + P)
        rw [show q + 1 - 1 = q by omega] at e1
        rw [show q + 1 + (P : ℤ) - 1 = q + P by omega] at e2
        rw [e1, e2, ih (j + 1) (by omega) (q + 1) (by omega) (by omega),
          ih j (by omega) (q + 1) (by omega) (by omega),
          show q + 1 + (P : ℤ) + 1 = q + 1 + 1 + P by omega,
          ih j (by omega) (q + 1 + 1) (by omega) (by omega)]
  exact fun j hj q hq => key t j hj q hq (by omega)

/-- **Kopra's Theorem 4.5 for rule 30.** From a configuration with a leftmost black cell, the
right half of row `t` equals that of row `0` for only finitely many `t`. -/
theorem finite_returns {lo : ℤ} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) :
    {t | LimitPoints.half (evol x) t = LimitPoints.half (evol x) 0}.Finite := by
  have hset : {t | LimitPoints.half (evol x) t = LimitPoints.half (evol x) 0} =
      {t : ℕ | ∀ p : ℤ, 0 ≤ p → evol x t p = x p} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h p hp
      have : evol x t (p.toNat : ℤ) = evol x 0 (p.toNat : ℤ) := congrFun h p.toNat
      rwa [Int.toNat_of_nonneg hp] at this
    · intro h
      funext p
      exact h p (by omega)
  rw [hset]
  by_contra hinf
  -- a return at a time `t₀ ≥ 1`
  obtain ⟨t₀, ht₀, ht₀pos⟩ := Set.Infinite.exists_gt hinf 0
  have hr₀ : ∀ p : ℤ, 0 ≤ p → evol x t₀ p = x p := ht₀
  obtain ⟨T, P, hP, hper⟩ := eventuallyPeriodic_of_return ht₀pos hr₀
  have hx : ∀ q : ℤ, (T : ℤ) ≤ q → x (q + P) = x q := by
    intro q hq
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
    have := hper n (by omega)
    simpa using this
  -- every row is `P`-periodic from cell `T` on
  have hrow : ∀ j : ℕ, ∀ q : ℤ, (T : ℤ) ≤ q → evol x j (q + P) = evol x j q := by
    intro j q hq
    obtain ⟨t, ht, hjt⟩ := Set.Infinite.exists_gt hinf j
    have hr : ∀ p : ℤ, 0 ≤ p → evol x t p = x p := ht
    refine periodic_rows (t := t) hx (fun q hq => ?_) j hjt.le q hq
    rw [hr (q + P) (by omega), hr q (by omega), hx q hq]
  have hshift : ∀ (k m : ℕ) (i : ℤ), (T : ℤ) ≤ i →
      evol x k (i + ((m * P : ℕ) : ℤ)) = evol x k i := by
    intro k m
    induction m with
    | zero => intro i _; simp
    | succ m ih =>
      intro i hi
      rw [Nat.add_mul, Nat.one_mul, Nat.cast_add, ← add_assoc,
        hrow k (i + ((m * P : ℕ) : ℤ)) (by have := Nat.zero_le (m * P); omega), ih i hi]
  -- the columns from `T` on repeat with period `t₀`
  have hcol : ∀ i : ℤ, (T : ℤ) ≤ i → ∀ j : ℕ, evol x (j + t₀) i = evol x j i := by
    intro i hi j
    have hjP : (j : ℤ) ≤ i + ((j * P : ℕ) : ℤ) := by
      have : (j : ℤ) ≤ ((j * P : ℕ) : ℤ) := by exact_mod_cast Nat.le_mul_of_pos_right j hP
      omega
    rw [← hshift (j + t₀) j i hi, ← hshift j j i hi, Nat.add_comm j t₀,
      evol_add_of_return hr₀ j hjP]
  exact Rule30FiniteConfigs.not_adjacent hlo hzero (T : ℤ)
    ⟨0, t₀, ht₀pos, fun j _ => hcol T le_rfl j⟩
    ⟨0, t₀, ht₀pos, fun j _ => hcol (T + 1) (by omega) j⟩

end Rule30Equivalents.RightHalfReturns
