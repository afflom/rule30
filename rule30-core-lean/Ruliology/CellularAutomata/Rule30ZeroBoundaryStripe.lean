module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Rule 30, zero-boundary left half: epochs, stripe stability and stripe absorption

The ZBL (`Rule30ZeroBoundary.zrow`) has the stripe `…10101` (black exactly at the odd depths) as a
fixed point, and a constrained history (column `-1` black at the even steps) is organized by its
deviations from the stripe.

**Epochs: the first deviation.**
* `first_defect_step`, `first_defect_run`, `first_defect_hits`: the first deviation from the
  stripe moves one depth toward the wall per step; a deviation at depth `d` turns depth `1` white
  at time `d - 1`.
* `first_defect_even`, `first_defect_parity`: in a constrained history the first deviation of the
  row at time `t` is at a depth `d` with `t + d` even.
* `free_bit`, `free_bit_iff`, `reset_config`, `epoch_col1`, `epoch_survives_iff`, `after_reset`: the
  free bit after a black depth-`1` cell is white exactly when the first deviation is at depth `2`;
  an epoch of even length `d` produces free bits `1, …, 1, 0`.
* `first_defect_phase`: **for rule 30 itself**, under an alternating center (black first from `T`),
  at every time `u ≥ T` the first deviation of the left half from `…10101` is at an even depth
  exactly when the center is black at `u` (phase-free form).

**Stripe stability: the last deviation.**
* `agrees_step`, `agrees_step_odd`, `agrees_two_steps`, `agrees_run_even`: a row equal to the stripe
  from depth `L` on stays so at the even times (the last deviation never moves outward over two
  steps), and from an odd depth on at all times (`stripe_confined`).
* `agrees_pre`, `agrees_pre_run`: a preimage of a stripe-tailed row is stripe-tailed (from depth
  `L + 4`), so backward orbits stay stripe-tailed; `finite_never_stripe`, `col1_true_stripe`,
  `col1_not_eventually_true`.

**Stripe absorption.**
* `stripe_absorb`: a row that agrees with the stripe from an odd depth on becomes exactly the
  stripe after finitely many steps (the front moves in by two depths within `9` steps, a kernel
  check over `2 ^ 12` contents, `front_check`; short strips by `small_check`). Hence
  `stripe_tail_free_eventually_one`.
* `stripe2_absorb`, `stripe2_tail_free_eventually_zero`: the even-phase stripe absorbs everything
  except depth `1`, which ends up alternating.
* `Theta_eventually_stripe_iff`: **the constrained start `Theta f` is eventually the stripe iff the
  free bits `f` are eventually `1`.**
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripe

open Rule30Jen Rule30Prize Rule30ZeroBoundary

/-! ### The first deviation from the stripe: epochs -/

theorem zrow_zero_stripe {x : Nat → Bool} {d : Nat} (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) :
    ∀ j, j < d → zrow x 0 j = stripe j := by
  intro j hj
  cases j with
  | zero => rfl
  | succ j => exact hag (j + 1) (by omega) hj

/-- If `x` agrees with the stripe at depths `1, …, d - 1` and deviates at depth `d ≥ 2`, then the
next row agrees with it at depths `1, …, d - 2` and deviates at depth `d - 1`. -/
theorem first_defect_step (x : Nat → Bool) (d : Nat) (hd : 2 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) (hne : x d ≠ stripe d) :
    (∀ k, 1 ≤ k → k < d - 1 → zrow x 1 k = stripe k) ∧ zrow x 1 (d - 1) ≠ stripe (d - 1) := by
  have hj := zrow_zero_stripe hag
  constructor
  · intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, hj (j + 2) (by omega), hj (j + 1) (by omega), hj j (by omega), ← stripe_step]
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
    have hs : stripe (j + 2) = !stripe (j + 1) := stripe_succ (j + 1)
    have hx : zrow x 0 (j + 2) = x (j + 2) := rfl
    rw [show j + 2 - 1 = j + 1 by omega, zrow_succ, hj (j + 1) (by omega), hj j (by omega),
      stripe_or, hx]
    rw [hs] at hne
    revert hne
    cases x (j + 2) <;> cases stripe (j + 1) <;> simp

/-- The first deviation travels to depth `1` at speed one. -/
theorem first_defect_run (x : Nat → Bool) (d : Nat)
    (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) (hne : x d ≠ stripe d) :
    ∀ i, i + 1 ≤ d → (∀ k, 1 ≤ k → k < d - i → zrow x i k = stripe k) ∧
      zrow x i (d - i) ≠ stripe (d - i) := by
  intro i
  induction i with
  | zero =>
    intro hd
    refine ⟨fun k hk1 hk2 => ?_, ?_⟩
    · rw [zrow_zero_of_pos x hk1]; exact hag k hk1 (by omega)
    · rw [Nat.sub_zero, zrow_zero_of_pos x (by omega)]; exact hne
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    have := first_defect_step (zrow x i) (d - i) (by omega) h1 h2
    refine ⟨fun k hk1 hk2 => ?_, ?_⟩
    · have e := this.1 k hk1 (by omega)
      rwa [← zrow_shift] at e
    · have e := this.2
      rwa [← zrow_shift, show d - i - 1 = d - (i + 1) by omega] at e

/-- A deviation at depth `d ≥ 1` turns depth `1` white at time `d - 1`. -/
theorem first_defect_hits (x : Nat → Bool) (d : Nat) (hd : 1 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) (hne : x d ≠ stripe d) : zrow x (d - 1) 1 = false := by
  have := (first_defect_run x d hag hne (d - 1) (by omega)).2
  rw [show d - (d - 1) = 1 by omega] at this
  revert this; cases zrow x (d - 1) 1 <;> simp [stripe]

/-- The constraint up to time `N`: depth `1` is black at every even time `≤ N`. -/
def Constrained (x : Nat → Bool) (N : Nat) : Prop := ∀ j, 2 * j ≤ N → zrow x (2 * j) 1 = true

/-- In a constrained history the first deviation from the stripe (if reached by time `N`) is at an
even depth. -/
theorem first_defect_even (x : Nat → Bool) (N d : Nat) (hd : 1 ≤ d) (hdN : d ≤ N + 1)
    (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) (hne : x d ≠ stripe d) (hc : Constrained x N) :
    d % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · exact h
  · exfalso
    have h1 := first_defect_hits x d hd hag hne
    have h2 := hc ((d - 1) / 2) (by omega)
    rw [show 2 * ((d - 1) / 2) = d - 1 by omega, h1] at h2
    cases h2

/-- **Parity of the first deviation.** In a history constrained up to time `N`, the first
deviation of the row at time `t` from the stripe is at a depth `d` with `t + d` even (when
`t + d ≤ N + 1`). -/
theorem first_defect_parity (x : Nat → Bool) (N t d : Nat) (hd : 1 ≤ d) (hdN : t + d ≤ N + 1)
    (hag : ∀ k, 1 ≤ k → k < d → zrow x t k = stripe k) (hne : zrow x t d ≠ stripe d)
    (hc : Constrained x N) : (t + d) % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (t + d) with h | h
  · exact h
  · exfalso
    have h1 := first_defect_hits (zrow x t) d hd hag hne
    rw [← zrow_shift, show t + (d - 1) = t + d - 1 by omega] at h1
    have h2 := hc ((t + d - 1) / 2) (by omega)
    rw [show 2 * ((t + d - 1) / 2) = t + d - 1 by omega, h1] at h2
    cases h2

/-- The free bit after a black depth-`1` cell is the complement of depth `2`. -/
theorem free_bit (x : Nat → Bool) (h1 : x 1 = true) : zrow x 1 1 = !x 2 := by
  show xor (x 2) (x 1 || false) = !x 2
  rw [h1]; cases x 2 <;> rfl

/-- The free bit after a black depth-`1` cell is white exactly when the first deviation from the
stripe is at depth `2`. -/
theorem free_bit_iff (x : Nat → Bool) (h1 : x 1 = true) :
    zrow x 1 1 = false ↔ ((∀ k, 1 ≤ k → k < 2 → x k = stripe k) ∧ x 2 ≠ stripe 2) := by
  rw [free_bit x h1]
  constructor
  · intro h
    refine ⟨fun k hk1 hk2 => ?_, ?_⟩
    · obtain rfl : k = 1 := by omega
      rw [h1]; rfl
    · revert h; cases x 2 <;> simp [stripe]
  · rintro ⟨_, h⟩
    revert h; cases x 2 <;> simp [stripe]

/-- **Configuration at a reset.** If depth `1` is white and the next row first deviates from the
stripe at depth `d ≥ 2`, the row is `0, 1, stripe 3, …, stripe d`, deviating at depth `d + 1`. -/
theorem reset_config (x : Nat → Bool) (h1 : x 1 = false) (d : Nat) (hd : 2 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → zrow x 1 k = stripe k) (hne : zrow x 1 d ≠ stripe d) :
    x 2 = true ∧ (∀ k, 3 ≤ k → k ≤ d → x k = stripe k) ∧ x (d + 1) ≠ stripe (d + 1) := by
  have inv : ∀ j, x (j + 2) = xor (zrow x 1 (j + 1)) (zrow x 0 (j + 1) || zrow x 0 j) :=
    fun j => zrow_inv x 0 j
  have h2 : x 2 = true := by
    rw [inv 0, hag 1 (by omega) (by omega)]
    show xor (stripe 1) (x 1 || false) = true
    rw [h1]; rfl
  have mid : ∀ k, 3 ≤ k → k ≤ d → x k = stripe k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk3 hkd
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [inv j, hag (j + 1) (by omega) (by omega)]
      have hor : (zrow x 0 (j + 1) || zrow x 0 j) = true := by
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          show (x 2 || x 1) = true
          rw [h2]; rfl
        · rcases Nat.lt_or_ge j 3 with hj3 | hj3
          · obtain rfl : j = 2 := by omega
            show (x 3 || x 2) = true
            rw [h2, Bool.or_true]
          · rw [zrow_zero_of_pos x (by omega), zrow_zero_of_pos x (by omega),
              ih (j + 1) (by omega) (by omega) (by omega), ih j (by omega) (by omega) (by omega),
              stripe_or]
      rw [hor, show j + 2 = (j + 1) + 1 by omega, stripe_succ (j + 1)]
      cases stripe (j + 1) <;> rfl
  refine ⟨h2, mid, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 by omega, inv j]
  have hor : (zrow x 0 (j + 1) || zrow x 0 j) = true := by
    rcases Nat.lt_or_ge j 2 with hj | hj
    · obtain rfl : j = 1 := by omega
      show (x 2 || x 1) = true
      rw [h2]; rfl
    · rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · obtain rfl : j = 2 := by omega
        show (x 3 || x 2) = true
        rw [h2, Bool.or_true]
      · rw [zrow_zero_of_pos x (by omega), zrow_zero_of_pos x (by omega),
          mid (j + 1) (by omega) (by omega), mid j (by omega) (by omega), stripe_or]
  rw [hor, show j + 2 = (j + 1) + 1 by omega, stripe_succ (j + 1)]
  intro h; apply hne
  revert h; cases zrow x 1 (j + 1) <;> cases stripe (j + 1) <;> simp

/-- **Epoch.** A first deviation at depth `d` at time `a` keeps depth `1` black at times
`a, …, a + d - 2` and turns it white at `a + d - 1`; the triangle
`{t ≥ a, k ≥ 1, k + t < a + d}` is pure stripe. -/
theorem epoch_col1 (x : Nat → Bool) (a d : Nat) (hd : 1 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → zrow x a k = stripe k) (hne : zrow x a d ≠ stripe d) :
    (∀ t k, a ≤ t → 1 ≤ k → k + t < a + d → zrow x t k = stripe k) ∧
    (∀ i, i + 1 < d → zrow x (a + i) 1 = true) ∧ zrow x (a + d - 1) 1 = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro t k hat hk1 hkt
    have := (first_defect_run (zrow x a) d hag hne (t - a) (by omega)).1 k hk1 (by omega)
    rwa [← zrow_shift, show a + (t - a) = t by omega] at this
  · intro i hi
    have := (first_defect_run (zrow x a) d hag hne i (by omega)).1 1 (Nat.le_refl 1) (by omega)
    rwa [← zrow_shift] at this
  · have := first_defect_hits (zrow x a) d hd hag hne
    rwa [← zrow_shift, show a + (d - 1) = a + d - 1 by omega] at this

/-- An epoch starting at an even time `a` (first deviation at depth `d`) satisfies the constraint
at all its even times iff `d` is even; if `d` is odd it ends with depth `1` white at the even time
`a + d - 1`. -/
theorem epoch_survives_iff (x : Nat → Bool) (a d : Nat) (ha : a % 2 = 0) (hd : 1 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → zrow x a k = stripe k) (hne : zrow x a d ≠ stripe d) :
    ((∀ j, a ≤ 2 * j → 2 * j ≤ a + d - 1 → zrow x (2 * j) 1 = true) ↔ d % 2 = 0) ∧
    (d % 2 = 1 → (a + d - 1) % 2 = 0 ∧ zrow x (a + d - 1) 1 = false) ∧
    (d % 2 = 0 → (a + d - 1) % 2 = 1 ∧ (a + d) % 2 = 0) := by
  obtain ⟨_, h1, h2⟩ := epoch_col1 x a d hd hag hne
  refine ⟨⟨?_, ?_⟩, fun hodd => ⟨by omega, h2⟩, fun hev => ⟨by omega, by omega⟩⟩
  · intro h
    rcases Nat.mod_two_eq_zero_or_one d with hd2 | hd2
    · exact hd2
    · exfalso
      have := h ((a + d - 1) / 2) (by omega) (by omega)
      rw [show 2 * ((a + d - 1) / 2) = a + d - 1 by omega, h2] at this
      cases this
  · intro hd2 j hj1 hj2
    have := h1 (2 * j - a) (by omega)
    rwa [show a + (2 * j - a) = 2 * j by omega] at this

/-- **After a reset.** If depth `1` is white at an odd time `τ`, the history is constrained through
time `τ + d` and the first deviation at `τ + 1` is at depth `d`, then `d` is even, the free bits at
`τ + 2, τ + 4, …, τ + d - 2` are black and the free bit at `τ + d` is white. -/
theorem after_reset (x : Nat → Bool) (N τ d : Nat) (hτ : τ % 2 = 1) (hd : 1 ≤ d)
    (hN : τ + d ≤ N) (hc : Constrained x N)
    (hag : ∀ k, 1 ≤ k → k < d → zrow x (τ + 1) k = stripe k) (hne : zrow x (τ + 1) d ≠ stripe d) :
    d % 2 = 0 ∧ 2 ≤ d ∧ (∀ i, 1 ≤ i → i < d / 2 → zrow x (τ + 2 * i) 1 = true) ∧
      zrow x (τ + d) 1 = false := by
  have hpar := first_defect_parity x N (τ + 1) d hd (by omega) hag hne hc
  have hdev : d % 2 = 0 := by omega
  obtain ⟨_, h1, h2⟩ := epoch_col1 x (τ + 1) d hd hag hne
  refine ⟨hdev, by omega, fun i hi1 hi2 => ?_, ?_⟩
  · have := h1 (2 * i - 1) (by omega)
    rwa [show τ + 1 + (2 * i - 1) = τ + 2 * i by omega] at this
  · rwa [show τ + 1 + d - 1 = τ + d by omega] at h2

/-! ### Stripe stability: the last deviation from the stripe -/

/-- `x` equals the stripe from depth `L` on. -/
def AgreesFrom (x : Nat → Bool) (L : Nat) : Prop := ∀ k, L ≤ k → x k = stripe k

theorem agrees_step (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom x L) :
    AgreesFrom (zrow x 1) (L + 1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [zrow_succ, zrow_zero_of_pos x (by omega), zrow_zero_of_pos x (by omega),
    zrow_zero_of_pos x (k := j) (by omega), h (j + 2) (by omega), h (j + 1) (by omega),
    h j (by omega), ← stripe_step]

theorem agrees_step_odd (x : Nat → Bool) (L : Nat) (hL : L % 2 = 1) (h : AgreesFrom x L) :
    AgreesFrom (zrow x 1) L := by
  intro k hk
  rcases Nat.lt_or_eq_of_le hk with hk | hk
  · exact agrees_step x L (by omega) h k (by omega)
  · subst hk
    obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
    rw [zrow_succ, zrow_zero_of_pos x (by omega), zrow_zero_of_pos x (by omega),
      h (j + 2) (by omega), h (j + 1) (by omega), stripe_odd (k := j + 1) hL,
      show j + 2 = (j + 1) + 1 by omega, stripe_succ (j + 1), stripe_odd (k := j + 1) hL]
    rfl

theorem agrees_step_odd_defect (x : Nat → Bool) (L : Nat) (hL : L % 2 = 1) (hL3 : 3 ≤ L)
    (h : AgreesFrom x L) (hne : x (L - 1) ≠ stripe (L - 1)) : AgreesFrom (zrow x 1) (L - 1) := by
  intro k hk
  rcases Nat.lt_or_eq_of_le hk with hk | hk
  · exact agrees_step_odd x L hL h k (by omega)
  · subst hk
    obtain ⟨j, rfl⟩ : ∃ j, L = j + 2 := ⟨L - 2, by omega⟩
    have hev : (j + 1) % 2 = 0 := by omega
    have hx : x (j + 1) = true := by
      rw [show j + 2 - 1 = j + 1 by omega, stripe_even hev] at hne
      revert hne; cases x (j + 1) <;> simp
    rw [show j + 2 - 1 = j + 1 by omega, zrow_succ, zrow_zero_of_pos x (by omega),
      zrow_zero_of_pos x (k := j + 1) (by omega), h (j + 2) (by omega), hx,
      stripe_odd (k := j + 2) hL, stripe_even hev]
    rfl

theorem step_even_defect (x : Nat → Bool) (L : Nat) (hL : L % 2 = 0) (hL2 : 2 ≤ L)
    (h : AgreesFrom x L) (hne : x (L - 1) ≠ stripe (L - 1)) : zrow x 1 L ≠ stripe L := by
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  have hodd : j % 2 = 1 := by omega
  have hx : x j = false := by
    rw [show j + 1 - 1 = j by omega, stripe_odd hodd] at hne
    revert hne; cases x j <;> simp
  rw [zrow_succ, zrow_zero_of_pos x (by omega), zrow_zero_of_pos x (by omega),
    zrow_zero_of_pos x (k := j) (by omega), h (j + 2) (by omega), h (j + 1) (by omega), hx,
    stripe_even hL, stripe_odd (k := j + 2) (by omega)]
  simp

/-- **The last deviation from the stripe never moves outward over two steps.** -/
theorem agrees_two_steps (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom x L) :
    AgreesFrom (zrow x 2) L := by
  have e2 : ∀ k, zrow x 2 k = zrow (zrow x 1) 1 k := fun k => zrow_shift x 1 1 k
  intro k hk
  rw [e2]
  revert k
  rcases Nat.mod_two_eq_zero_or_one L with he | ho
  · by_cases hd : x (L - 1) = stripe (L - 1)
    · have h' : AgreesFrom x (L - 1) := by
        intro k hk
        rcases Nat.lt_or_eq_of_le hk with hk | hk
        · exact h k (by omega)
        · subst hk; exact hd
      have h1 := agrees_step_odd x (L - 1) (by omega) h'
      have h2 := agrees_step (zrow x 1) (L - 1) (by omega) h1
      rw [show L - 1 + 1 = L by omega] at h2
      exact h2
    · have h1 := agrees_step x L hL h
      have h2 := step_even_defect x L he (by omega) h hd
      have h3 := agrees_step_odd_defect (zrow x 1) (L + 1) (by omega) (by omega) h1
        (by rw [show L + 1 - 1 = L by omega]; exact h2)
      rw [show L + 1 - 1 = L by omega] at h3
      exact h3
  · exact agrees_step_odd (zrow x 1) L ho (agrees_step_odd x L ho h)

theorem agrees_run_even (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom x L) (t : Nat) :
    AgreesFrom (zrow x (2 * t)) L := by
  induction t with
  | zero =>
    intro k hk
    rw [Nat.mul_zero, zrow_zero_of_pos x (by omega)]; exact h k hk
  | succ t ih =>
    intro k hk
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, zrow_shift]
    exact agrees_two_steps _ L hL ih k hk

/-- **Preimages of stripe-tailed rows.** If the next row equals the stripe from depth `L ≥ 1` on,
the row equals the stripe from depth `L + 4` on. -/
theorem agrees_pre (y : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom (zrow y 1) L) :
    AgreesFrom y (L + 4) := by
  let z := zrow y 0
  have hrec : ∀ k, L ≤ k + 1 → z (k + 2) = xor (stripe (k + 1)) (z (k + 1) || z k) := by
    intro k hk; rw [show z (k + 2) = zrow y 0 (k + 2) from rfl, zrow_inv y 0 k, h (k + 1) hk]
  have prop : ∀ m, L ≤ m + 1 → z m = stripe m → z (m + 1) = stripe (m + 1) →
      ∀ i, z (m + i) = stripe (m + i) := by
    intro m hm h0 h1 i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      match i, ih with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | i + 2, ih =>
        rw [show m + (i + 2) = (m + i) + 2 by omega, hrec (m + i) (by omega),
          show m + i + 1 = m + (i + 1) by omega, ih (i + 1) (by omega), ih i (by omega),
          show m + (i + 1) = (m + i) + 1 by omega, stripe_or, stripe_succ (m + i + 1),
          stripe_succ (m + i)]
        cases stripe (m + i) <;> rfl
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have e2 : z (L' + 2) = xor (!stripe L') (z (L' + 1) || z L') := by
    rw [hrec L' (by omega), stripe_succ]
  have e3 : z (L' + 3) = xor (stripe L') (z (L' + 2) || z (L' + 1)) := by
    rw [hrec (L' + 1) (by omega), show L' + 1 + 1 = L' + 2 by omega, stripe_add_two]
  have e4 : z (L' + 4) = xor (!stripe L') (z (L' + 3) || z (L' + 2)) := by
    rw [hrec (L' + 2) (by omega), show L' + 2 + 1 = L' + 3 by omega,
      show L' + 3 = (L' + 1) + 2 by omega, stripe_add_two, stripe_succ]
  have e5 : z (L' + 5) = xor (stripe L') (z (L' + 4) || z (L' + 3)) := by
    rw [hrec (L' + 3) (by omega), show L' + 3 + 1 = L' + 4 by omega,
      show L' + 4 = L' + 2 + 2 by omega, stripe_add_two, stripe_add_two]
  have e6 : z (L' + 6) = xor (!stripe L') (z (L' + 5) || z (L' + 4)) := by
    rw [hrec (L' + 4) (by omega), show L' + 4 + 1 = L' + 5 by omega,
      show L' + 5 = (L' + 1) + 2 + 2 by omega, stripe_add_two, stripe_add_two, stripe_succ]
  have s5 : stripe (L' + 5) = !stripe L' := by
    rw [show L' + 5 = (L' + 1) + 2 + 2 by omega, stripe_add_two, stripe_add_two, stripe_succ]
  have s6 : stripe (L' + 6) = stripe L' := by
    rw [show L' + 6 = L' + 2 + 2 + 2 by omega, stripe_add_two, stripe_add_two, stripe_add_two]
  have key : z (L' + 5) = stripe (L' + 5) ∧ z (L' + 6) = stripe (L' + 6) := by
    rw [e6, e5, e4, e3, e2, s5, s6]
    cases stripe L' <;> cases z (L' + 1) <;> cases z L' <;> decide
  intro k hk
  have := prop (L' + 5) (by omega) key.1 key.2 (k - (L' + 5))
  rw [show L' + 5 + (k - (L' + 5)) = k by omega] at this
  rw [← zrow_zero_of_pos y (k := k) (by omega)]
  exact this

/-- **Backward orbits of stripe-tailed rows stay stripe-tailed.** -/
theorem agrees_pre_run (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) :
    ∀ t, AgreesFrom (zrow x t) L → AgreesFrom x (L + 4 * t) := by
  intro t
  induction t generalizing L with
  | zero =>
    intro h k hk
    rw [← zrow_zero_of_pos x (k := k) (by omega)]
    exact h k (by omega)
  | succ t ih =>
    intro h
    have h' : AgreesFrom (zrow (zrow x t) 1) L := fun k hk => by
      rw [← zrow_shift]; exact h k hk
    have := ih (L + 4) (by omega) (agrees_pre (zrow x t) L hL h')
    rwa [show L + 4 + 4 * t = L + 4 * (t + 1) by omega] at this

/-- A finitely supported row never evolves into a stripe-tailed one. -/
theorem finite_never_stripe (x : Nat → Bool) (W : Nat) (hx : ∀ k, W < k → x k = false) (L t : Nat) :
    ¬ AgreesFrom (zrow x t) L := by
  intro h
  have h1 := h (2 * (W + L + t) + 1) (by omega)
  rw [zrow_fin hx t _ (by omega), stripe_odd (by omega)] at h1
  cases h1

/-- If depth `1` is black at all times `≥ T`, the row at every time `≥ T` is the stripe. -/
theorem col1_true_stripe (x : Nat → Bool) (T : Nat) (h : ∀ t, T ≤ t → zrow x t 1 = true) :
    ∀ k t, T ≤ t → zrow x t k = stripe k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k, ih with
    | 0, _ => intro t _; rw [zrow_wall]; rfl
    | 1, _ => intro t ht; rw [h t ht]; rfl
    | k + 2, ih =>
      intro t ht
      rw [zrow_inv x t k, ih (k + 1) (by omega) (t + 1) (by omega), ih (k + 1) (by omega) t ht,
        ih k (by omega) t ht, stripe_or, stripe_succ (k + 1), stripe_succ k]
      cases stripe k <;> rfl

/-- For a finitely supported start, column `-1` is not eventually black: the free bits of a
constrained history are not eventually `1`. -/
theorem col1_not_eventually_true (x : Nat → Bool) (hx : FinSupp x) :
    ¬ ∃ T, ∀ t, T ≤ t → zrow x t 1 = true := by
  rintro ⟨T, hT⟩
  obtain ⟨W, hW⟩ := hx
  exact finite_never_stripe x W hW 1 T fun k _ => col1_true_stripe x T hT k T (Nat.le_refl T)

/-- **Stripe confinement.** A row that agrees with the stripe from an odd depth `K` on keeps
agreeing from `K` on. -/
theorem stripe_confined (L : Nat → Bool) (K : Nat) (hK : K % 2 = 1) (h : AgreesFrom L K) :
    ∀ t, AgreesFrom (zrow L t) K := by
  intro t
  induction t with
  | zero => intro k hk; rw [zrow_zero_of_pos L (by omega)]; exact h k hk
  | succ t ih =>
    intro k hk
    rw [zrow_shift L t 1]
    exact agrees_step_odd _ K hK ih k hk

/-- A row that agrees with the stripe from an odd depth on has an eventually periodic column `-1`
(its orbit lives in a finite set). -/
theorem stripe_tail_trace_periodic (L : Nat → Bool) (K : Nat) (hK : K % 2 = 1) (h : AgreesFrom L K) :
    EventuallyPeriodic (fun t => zrow L t 1) := by
  let a : Nat → List Bool := fun m => (List.range K).map (fun k => zrow L m k)
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole K a (fun m => by simp [a])
  have hrow : ∀ k, zrow L m k = zrow L n k := by
    intro k
    rcases Nat.lt_or_ge k K with hk | hk
    · have := congrArg (fun l => l[k]?) he
      simpa [a, hk] using this
    · rw [stripe_confined L K hK h m k hk, stripe_confined L K hK h n k hk]
  refine ⟨m, n - m, by omega, fun t ht => ?_⟩
  show zrow L (t + (n - m)) 1 = zrow L t 1
  rw [show t + (n - m) = n + (t - m) by omega, zrow_shift, show t = m + (t - m) by omega,
    zrow_shift, show m + (t - m) - m = t - m by omega]
  have hfun : zrow L m = zrow L n := funext hrow
  rw [hfun]

/-! ### Stripe absorption -/

/-- Cells `1..n` of a row packed into the bits `1..n` of a natural number. -/
def enc (R : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => enc R n ||| (if R (n + 1) then 1 <<< (n + 1) else 0)

/-- Bits `1..n`. -/
def smask (n : Nat) : Nat := ((1 <<< n) - 1) <<< 1

/-- The strip `1..n` with a white cell at `0` and a black cell at `n + 1`. -/
def sextN (n v : Nat) : Nat := (v &&& smask n) ||| (1 <<< (n + 1))

/-- One ZBL step of the strip `1..n` closed by a black cell at `n + 1`. -/
def bstep (n v : Nat) : Nat :=
  ((sextN n v >>> 1) ^^^ (sextN n v ||| (sextN n v <<< 1))) &&& smask n

def biter (n : Nat) : Nat → Nat → Nat
  | 0, v => v
  | s + 1, v => biter n s (bstep n v)

def frontWithin (n : Nat) : Nat → Nat → Bool
  | 0, v => v.testBit (n - 1) && !v.testBit n
  | f + 1, v => (v.testBit (n - 1) && !v.testBit n) || frontWithin n f (bstep n v)

def reachesStripe (n : Nat) : Nat → Nat → Bool
  | 0, v => v == enc stripe n
  | f + 1, v => v == enc stripe n || reachesStripe n f (bstep n v)

set_option maxRecDepth 100000 in
/-- Local front check: with the stripe from cell `13` on, cells `11, 12` become `1, 0` within
`9` steps, for each of the `2 ^ 12` contents of cells `1..12`. -/
theorem front_check : Rule30StripCertificates.allBelow (fun v => v % 2 == 1 || frontWithin 12 9 v) (2 ^ 13) = true := by
  decide +kernel

/-- Small strips: with the stripe from cell `11` on, every content of cells `1..10` reaches the
stripe within `40` steps. -/
theorem small_check : Rule30StripCertificates.allBelow (fun v => v % 2 == 1 || reachesStripe 10 40 v) (2 ^ 11) = true := by
  decide +kernel

theorem testBit_enc (R : Nat → Bool) :
    ∀ n i, (enc R n).testBit i = (decide (1 ≤ i) && decide (i ≤ n) && R i) := by
  intro n
  induction n with
  | zero =>
    intro i
    simp only [enc, Nat.zero_testBit]
    by_cases h : 1 ≤ i <;> simp [h] <;> omega
  | succ n ih =>
    intro i
    simp only [enc, Nat.testBit_or, ih]
    cases hR : R (n + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.or_false]
      by_cases h1 : i = n + 1
      · subst h1; simp [hR]
      · by_cases h2 : i ≤ n
        · simp [h2, show i ≤ n + 1 by omega]
        · simp [h2, show ¬ i ≤ n + 1 by omega]
    · simp only [↓reduceIte, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h1 : i = n + 1
      · subst h1; simp [hR]
      · by_cases h2 : i ≤ n
        · simp [h2, show i ≤ n + 1 by omega, show n + 1 ≠ i by omega]
        · simp [h2, show ¬ i ≤ n + 1 by omega, show n + 1 ≠ i by omega]

theorem testBit_smask (n i : Nat) : (smask n).testBit i = (decide (1 ≤ i) && decide (i ≤ n)) := by
  unfold smask
  rw [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : 1 ≤ i
  · simp only [show i ≥ 1 from h, decide_true, Bool.true_and]
    by_cases h2 : i ≤ n
    · simp [h2]; omega
    · simp [h2]; omega
  · simp [h]

theorem testBit_sextN (n v i : Nat) :
    (sextN n v).testBit i = ((decide (1 ≤ i) && decide (i ≤ n) && v.testBit i) || decide (i = n + 1)) := by
  unfold sextN
  rw [Nat.testBit_or, Nat.testBit_and, testBit_smask, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = n + 1
  · subst h; simp
  · simp only [h, show ¬ (n + 1 = i) by omega, decide_false, Bool.or_false]
    cases v.testBit i <;> cases decide (1 ≤ i) <;> cases decide (i ≤ n) <;> rfl

theorem testBit_bstep (n v i : Nat) :
    (bstep n v).testBit i = (decide (1 ≤ i) && decide (i ≤ n) &&
      xor ((sextN n v).testBit (i + 1))
        ((sextN n v).testBit i || (decide (1 ≤ i) && (sextN n v).testBit (i - 1)))) := by
  unfold bstep
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_smask, show 1 + i = i + 1 by omega]
  by_cases h : 1 ≤ i
  · simp [show i ≥ 1 from h]; cases decide (i ≤ n) <;> simp
  · simp [h]

/-- The packed strip of a row whose cell `n + 1` is black reads the row correctly on `0..n+1`. -/
theorem sextN_enc (R : Nat → Bool) (n : Nat) (hR : R (n + 1) = true) (h0 : R 0 = false) :
    ∀ j, j ≤ n + 1 → (sextN n (enc R n)).testBit j = R j := by
  intro j hj
  rw [testBit_sextN, testBit_enc]
  by_cases h1 : j = n + 1
  · subst h1; simp [hR]
  · by_cases h2 : j = 0
    · subst h2; simp [h0]
    · simp [show 1 ≤ j by omega, show j ≤ n by omega, h1]

theorem enc_step (R : Nat → Bool) (n t : Nat) (hR : zrow R t (n + 1) = true) :
    enc (zrow R (t + 1)) n = bstep n (enc (zrow R t) n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_enc, testBit_bstep]
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have e := sextN_enc (zrow R t) n hR (zrow_wall R t)
    rw [e (i' + 1 + 1) (by omega), e (i' + 1) (by omega), show i' + 1 - 1 = i' by omega,
      e i' (by omega), zrow_succ]
    simp [show i' + 1 ≤ n by omega]
  · by_cases h1 : 1 ≤ i
    · simp [h1, show ¬ i ≤ n by omega]
    · simp [h1]

theorem enc_congr (R R' : Nat → Bool) (n : Nat) (h : ∀ k, 1 ≤ k → k ≤ n → R k = R' k) :
    enc R n = enc R' n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_enc, testBit_enc]
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · rw [h i hi.1 hi.2]
  · by_cases h1 : 1 ≤ i
    · simp [h1, show ¬ i ≤ n by omega]
    · simp [h1]

theorem biter_enc (R : Nat → Bool) (n : Nat) (hR : ∀ t, zrow R t (n + 1) = true) :
    ∀ s t, biter n s (enc (zrow R t) n) = enc (zrow R (t + s)) n := by
  intro s
  induction s with
  | zero => intro t; rfl
  | succ s ih =>
    intro t
    show biter n s (bstep n (enc (zrow R t) n)) = _
    rw [← enc_step R n t (hR t), ih, show t + 1 + s = t + (s + 1) by omega]

theorem frontWithin_spec (n : Nat) : ∀ f v, frontWithin n f v = true →
    ∃ s, s ≤ f ∧ (biter n s v).testBit (n - 1) = true ∧ (biter n s v).testBit n = false := by
  intro f
  induction f with
  | zero =>
    intro v h
    simp only [frontWithin, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨0, Nat.le_refl 0, h.1, h.2⟩
  | succ f ih =>
    intro v h
    simp only [frontWithin, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact ⟨0, by omega, h.1, h.2⟩
    · obtain ⟨s, hs, h1, h2⟩ := ih _ h
      exact ⟨s + 1, by omega, h1, h2⟩

theorem reachesStripe_spec (n : Nat) : ∀ f v, reachesStripe n f v = true →
    ∃ s, s ≤ f ∧ biter n s v = enc stripe n := by
  intro f
  induction f with
  | zero =>
    intro v h
    simp only [reachesStripe, beq_iff_eq] at h
    exact ⟨0, Nat.le_refl 0, h⟩
  | succ f ih =>
    intro v h
    simp only [reachesStripe, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, h⟩
    · obtain ⟨s, hs, h1⟩ := ih _ h
      exact ⟨s + 1, by omega, h1⟩

theorem enc_lt (R : Nat → Bool) (n : Nat) : enc R n < 2 ^ (n + 1) :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [testBit_enc]; simp [show ¬ i ≤ n by omega]

theorem enc_even (R : Nat → Bool) (n : Nat) : enc R n % 2 = 0 := by
  have h := testBit_enc R n 0
  rw [Nat.testBit_zero] at h
  simp at h
  omega

theorem enc_zrow_zero (R : Nat → Bool) (n : Nat) : enc R n = enc (zrow R 0) n :=
  enc_congr _ _ _ fun _ hk _ => (zrow_zero_of_pos R hk).symm

/-- Base front lemma: the stripe from `13` on gives cells `11, 12 = 1, 0` within `9` steps. -/
theorem front_base (R : Nat → Bool) (h : AgreesFrom R 13) :
    ∃ s, s ≤ 9 ∧ zrow R s 11 = true ∧ zrow R s 12 = false := by
  have hc := stripe_confined R 13 (by decide) h
  have h13 : ∀ t, zrow R t (12 + 1) = true := fun t => hc t 13 (by omega)
  have hv := Rule30StripCertificates.allBelow_spec front_check (enc R 12) (enc_lt R 12)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : frontWithin 12 9 (enc R 12) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, h1, h2⟩ := frontWithin_spec 12 9 _ hv'
  rw [enc_zrow_zero, biter_enc R 12 h13, Nat.zero_add, testBit_enc] at h1 h2
  refine ⟨s, hs, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

/-- **Front lemma.** If a row agrees with the stripe from an odd depth `m ≥ 13` on, then within
`9` steps it agrees with the stripe from `m - 2` on. -/
theorem front_advance (R : Nat → Bool) (m : Nat) (hm : m % 2 = 1) (hm13 : 13 ≤ m)
    (h : AgreesFrom R m) : ∃ s, s ≤ 9 ∧ AgreesFrom (zrow R s) (m - 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = 13 + d := ⟨m - 13, by omega⟩
  have hd : d % 2 = 0 := by omega
  let B : Nat → Bool := fun k => R (k + d)
  have hB : AgreesFrom B 13 := fun k hk => by
    show R (k + d) = stripe k
    rw [h (k + d) (by omega)]; unfold stripe; rw [show (k + d) % 2 = k % 2 by omega]
  obtain ⟨s, hs, h1, h2⟩ := front_base B hB
  have tr := zrow_translate (L := B) (L' := R) (d := d) (a := 1) (by omega) (fun k _ => rfl) s
  have hc := stripe_confined R (13 + d) (by omega) h s
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k (13 + d) with hk' | hk'
  · rcases (show k = 11 + d ∨ k = 12 + d by omega) with rfl | rfl
    · rw [tr 11 (by omega), h1]; unfold stripe; rw [show (11 + d) % 2 = 1 by omega]; rfl
    · rw [tr 12 (by omega), h2]; unfold stripe; rw [show (12 + d) % 2 = 0 by omega]; rfl
  · exact hc k hk'

/-- Base of the descent: the stripe from `11` on reaches the stripe everywhere within `40` steps. -/
theorem small_base (R : Nat → Bool) (h : AgreesFrom R 11) :
    ∃ s, s ≤ 40 ∧ ∀ k, 1 ≤ k → zrow R s k = stripe k := by
  have hc := stripe_confined R 11 (by decide) h
  have h11 : ∀ t, zrow R t (10 + 1) = true := fun t => hc t 11 (by omega)
  have hv := Rule30StripCertificates.allBelow_spec small_check (enc R 10) (enc_lt R 10)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : reachesStripe 10 40 (enc R 10) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, he⟩ := reachesStripe_spec 10 40 _ hv'
  rw [enc_zrow_zero, biter_enc R 10 h11, Nat.zero_add] at he
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 11 with hk' | hk'
  · have := congrArg (fun v => Nat.testBit v k) he
    simp only [testBit_enc] at this
    simpa [hk, show k ≤ 10 by omega] using this
  · exact hc s k hk'

/-- **Stripe absorption.** A ZBL row that agrees with the stripe `…10101` from some odd depth on
becomes exactly the stripe after finitely many steps and stays there. -/
theorem stripe_absorb (R : Nat → Bool) (m : Nat) (hm : m % 2 = 1) (h : AgreesFrom R m) :
    ∃ T, ∀ t, T ≤ t → ∀ k, 1 ≤ k → zrow R t k = stripe k := by
  have desc : ∀ j (R : Nat → Bool), AgreesFrom R (11 + 2 * j) → ∃ T, AgreesFrom (zrow R T) 11 := by
    intro j
    induction j with
    | zero => intro R hR; exact ⟨0, fun k hk => by rw [zrow_zero_of_pos R (by omega)]; exact hR k hk⟩
    | succ j ih =>
      intro R hR
      obtain ⟨s, -, hs⟩ := front_advance R (11 + 2 * (j + 1)) (by omega) (by omega) hR
      obtain ⟨T, hT⟩ := ih (zrow R s) fun k hk => hs k (by omega)
      exact ⟨s + T, fun k hk => by rw [zrow_shift]; exact hT k hk⟩
  obtain ⟨T₁, hT₁⟩ := desc (m / 2) R fun k hk => h k (by omega)
  obtain ⟨s, -, hs⟩ := small_base (zrow R T₁) hT₁
  refine ⟨T₁ + s, fun t ht k hk => ?_⟩
  have hfull : AgreesFrom (zrow R (T₁ + s)) 1 := fun k hk => by rw [zrow_shift]; exact hs k hk
  have := stripe_confined (zrow R (T₁ + s)) 1 (by decide) hfull (t - (T₁ + s)) k hk
  rwa [← zrow_shift, show T₁ + s + (t - (T₁ + s)) = t by omega] at this

/-- A row with a stripe tail has column `-1` eventually black: a constrained row with a stripe tail
has free bits eventually `1`. -/
theorem stripe_tail_free_eventually_one (R : Nat → Bool) (m : Nat) (hm : m % 2 = 1)
    (h : AgreesFrom R m) : ∃ T, ∀ t, T ≤ t → zrow R t 1 = true := by
  obtain ⟨T, hT⟩ := stripe_absorb R m hm h
  exact ⟨T, fun t ht => hT t ht 1 (Nat.le_refl 1)⟩

/-! ### The other stripe phase -/

/-- The stripe black at the even depths. -/
def stripe2 (k : Nat) : Bool := k % 2 == 0

theorem stripe2_fixed (k : Nat) :
    stripe2 (k + 1) = xor (stripe2 (k + 2)) (stripe2 (k + 1) || stripe2 k) := by
  unfold stripe2
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [show (k + 1) % 2 = 1 by omega, show (k + 2) % 2 = 0 by omega, h]; rfl
  · rw [show (k + 1) % 2 = 0 by omega, show (k + 2) % 2 = 1 by omega, h]; rfl

theorem stripe2_confined (L : Nat → Bool) (K : Nat) (hK : K % 2 = 0) (hK2 : 2 ≤ K)
    (h : ∀ k, K ≤ k → L k = stripe2 k) : ∀ t k, K ≤ k → zrow L t k = stripe2 k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [zrow_zero_of_pos L (by omega)]; exact h k hk
  | succ t ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, ih (k' + 2) (by omega), ih (k' + 1) hk]
    rcases Nat.lt_or_ge K (k' + 1) with hlt | hge
    · rw [ih k' (by omega)]; exact (stripe2_fixed k').symm
    · have hKe : k' + 1 = K := by omega
      have hs : stripe2 (k' + 1) = true := by unfold stripe2; rw [hKe, hK]; rfl
      have hs2 : stripe2 (k' + 2) = false := by
        unfold stripe2; rw [show (k' + 2) % 2 = 1 by omega]; rfl
      rw [hs, hs2]; rfl

set_option maxRecDepth 100000 in
/-- Local front check for the even phase: stripe from cell `14` on, cells `12, 13` become `1, 0`
within `9` steps, for each of the `2 ^ 13` contents of cells `1..13`. -/
theorem front_check2 : Rule30StripCertificates.allBelow (fun v => v % 2 == 1 || frontWithin 13 9 v) (2 ^ 14) = true := by
  decide +kernel

def reachesStripe2 (n : Nat) : Nat → Nat → Bool
  | 0, v => v >>> 2 == enc stripe2 n >>> 2
  | f + 1, v => v >>> 2 == enc stripe2 n >>> 2 || reachesStripe2 n f (bstep n v)

set_option maxRecDepth 100000 in
/-- Small strips, even phase: stripe from cell `12` on; every content of cells `1..11` reaches the
stripe on cells `2..11` within `40` steps. -/
theorem small_check2 : Rule30StripCertificates.allBelow (fun v => v % 2 == 1 || reachesStripe2 11 40 v) (2 ^ 12) = true := by
  decide +kernel

theorem reachesStripe2_spec (n : Nat) : ∀ f v, reachesStripe2 n f v = true →
    ∃ s, s ≤ f ∧ biter n s v >>> 2 = enc stripe2 n >>> 2 := by
  intro f
  induction f with
  | zero =>
    intro v h
    simp only [reachesStripe2, beq_iff_eq] at h
    exact ⟨0, Nat.le_refl 0, h⟩
  | succ f ih =>
    intro v h
    simp only [reachesStripe2, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, h⟩
    · obtain ⟨s, hs, h1⟩ := ih _ h
      exact ⟨s + 1, by omega, h1⟩

theorem front_base2 (R : Nat → Bool) (h : ∀ k, 14 ≤ k → R k = stripe2 k) :
    ∃ s, s ≤ 9 ∧ zrow R s 12 = true ∧ zrow R s 13 = false := by
  have hc := stripe2_confined R 14 (by decide) (by decide) h
  have h14 : ∀ t, zrow R t (13 + 1) = true := fun t => hc t 14 (by omega)
  have hv := Rule30StripCertificates.allBelow_spec front_check2 (enc R 13) (enc_lt R 13)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : frontWithin 13 9 (enc R 13) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, h1, h2⟩ := frontWithin_spec 13 9 _ hv'
  rw [enc_zrow_zero, biter_enc R 13 h14, Nat.zero_add, testBit_enc] at h1 h2
  refine ⟨s, hs, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

theorem front_advance2 (R : Nat → Bool) (m : Nat) (hm : m % 2 = 0) (hm14 : 14 ≤ m)
    (h : ∀ k, m ≤ k → R k = stripe2 k) :
    ∃ s, s ≤ 9 ∧ ∀ k, m - 2 ≤ k → zrow R s k = stripe2 k := by
  obtain ⟨d, rfl⟩ : ∃ d, m = 14 + d := ⟨m - 14, by omega⟩
  have hd : d % 2 = 0 := by omega
  let B : Nat → Bool := fun k => R (k + d)
  have hB : ∀ k, 14 ≤ k → B k = stripe2 k := fun k hk => by
    show R (k + d) = stripe2 k
    rw [h (k + d) (by omega)]; unfold stripe2; rw [show (k + d) % 2 = k % 2 by omega]
  obtain ⟨s, hs, h1, h2⟩ := front_base2 B hB
  have tr := zrow_translate (L := B) (L' := R) (d := d) (a := 1) (by omega) (fun k _ => rfl) s
  have hc := stripe2_confined R (14 + d) (by omega) (by omega) h s
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k (14 + d) with hk' | hk'
  · rcases (show k = 12 + d ∨ k = 13 + d by omega) with rfl | rfl
    · rw [tr 12 (by omega), h1]; unfold stripe2; rw [show (12 + d) % 2 = 0 by omega]; rfl
    · rw [tr 13 (by omega), h2]; unfold stripe2; rw [show (13 + d) % 2 = 1 by omega]; rfl
  · exact hc k hk'

theorem small_base2 (R : Nat → Bool) (h : ∀ k, 12 ≤ k → R k = stripe2 k) :
    ∃ s, s ≤ 40 ∧ ∀ k, 2 ≤ k → zrow R s k = stripe2 k := by
  have hc := stripe2_confined R 12 (by decide) (by decide) h
  have h12 : ∀ t, zrow R t (11 + 1) = true := fun t => hc t 12 (by omega)
  have hv := Rule30StripCertificates.allBelow_spec small_check2 (enc R 11) (enc_lt R 11)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : reachesStripe2 11 40 (enc R 11) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, he⟩ := reachesStripe2_spec 11 40 _ hv'
  rw [enc_zrow_zero, biter_enc R 11 h12, Nat.zero_add] at he
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 12 with hk' | hk'
  · have := congrArg (fun v => Nat.testBit v (k - 2)) he
    simp only [Nat.testBit_shiftRight, testBit_enc, show 2 + (k - 2) = k by omega] at this
    simpa [show 1 ≤ k by omega, show k ≤ 11 by omega] using this
  · exact hc s k hk'

/-- **Stripe absorption, even phase.** A row that agrees with the even-phase stripe from some depth
on agrees with it at every depth `k ≥ 2` after finitely many steps; depth `1` then alternates. -/
theorem stripe2_absorb (R : Nat → Bool) (m : Nat) (hm : m % 2 = 0) (h : ∀ k, m ≤ k → R k = stripe2 k) :
    ∃ T, ∀ t, T ≤ t → (∀ k, 2 ≤ k → zrow R t k = stripe2 k) ∧ zrow R (t + 1) 1 = !zrow R t 1 := by
  have desc : ∀ j (R : Nat → Bool), (∀ k, 12 + 2 * j ≤ k → R k = stripe2 k) →
      ∃ T, ∀ k, 12 ≤ k → zrow R T k = stripe2 k := by
    intro j
    induction j with
    | zero => intro R hR; exact ⟨0, fun k hk => by
        rw [zrow_zero_of_pos R (by omega)]; exact hR k hk⟩
    | succ j ih =>
      intro R hR
      obtain ⟨s, -, hs⟩ := front_advance2 R (12 + 2 * (j + 1)) (by omega) (by omega) hR
      obtain ⟨T, hT⟩ := ih (zrow R s) fun k hk => hs k (by omega)
      exact ⟨s + T, fun k hk => by rw [zrow_shift]; exact hT k hk⟩
  obtain ⟨T₁, hT₁⟩ := desc (m / 2) R fun k hk => h k (by omega)
  obtain ⟨s, -, hs⟩ := small_base2 (zrow R T₁) hT₁
  have hfull : ∀ k, 2 ≤ k → zrow R (T₁ + s) k = stripe2 k := fun k hk => by
    rw [zrow_shift]; exact hs k hk
  have hall : ∀ t, T₁ + s ≤ t → ∀ k, 2 ≤ k → zrow R t k = stripe2 k := by
    intro t ht k hk
    have := stripe2_confined (zrow R (T₁ + s)) 2 (by decide) (by decide) hfull (t - (T₁ + s)) k hk
    rwa [← zrow_shift, show T₁ + s + (t - (T₁ + s)) = t by omega] at this
  refine ⟨T₁ + s, fun t ht => ⟨hall t ht, ?_⟩⟩
  have h2 : zrow R t 2 = true := by rw [hall t ht 2 (by omega)]; rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, zrow_succ, h2, zrow_wall]
  cases zrow R t (0 + 1) <;> rfl

/-- A constrained row with an even-phase stripe tail has free bits eventually `0`. -/
theorem stripe2_tail_free_eventually_zero (R : Nat → Bool) (hX : InX R) (m : Nat) (hm : m % 2 = 0)
    (h : ∀ k, m ≤ k → R k = stripe2 k) : ∃ S, ∀ s, S ≤ s → zrow R (2 * s + 1) 1 = false := by
  obtain ⟨T, hT⟩ := stripe2_absorb R m hm h
  refine ⟨T, fun s hs => ?_⟩
  rw [(hT (2 * s) (by omega)).2, hX s]
  rfl

/-! ### The constrained start is eventually the stripe iff the free bits are eventually `1` -/

/-- The constrained start with all free bits `1` is the stripe. -/
theorem Theta_true : Theta (fun _ => true) = stripe := by
  have e := Theta_unique (L := stripe) (f := fun _ => true) (fun s => by rw [zrow_stripe]; rfl)
    (fun s => by rw [zrow_stripe]; rfl)
  rw [zrow_zero_self rfl] at e
  exact e.symm

/-- Running a constrained start for `2 S` steps shifts its free bits by `S`. -/
theorem zrow_Theta_even (f : Nat → Bool) : ∀ S, zrow (Theta f) (2 * S) = Theta (fun s => f (s + S)) := by
  intro S
  induction S with
  | zero =>
    rw [Nat.mul_zero, zrow_zero_self (Theta_wall f)]
    rfl
  | succ S ih =>
    funext k
    rw [show 2 * (S + 1) = 2 * S + 2 by omega, zrow_shift, ih, two_step_shift]
    congr 1
    funext s
    rw [show s + 1 + S = s + (S + 1) by omega]

/-- **The constrained start is eventually the stripe iff its free bits are eventually `1`.**
(`Theta f` equals `…10101` beyond some depth iff `f s = 1` for all large `s`.) -/
theorem Theta_eventually_stripe_iff (f : Nat → Bool) :
    (∃ m, AgreesFrom (Theta f) m) ↔ ∃ S, ∀ s, S ≤ s → f s = true := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨T, hT⟩ := stripe_tail_free_eventually_one (Theta f) (2 * m + 1) (by omega)
      (fun k hk => hm k (by omega))
    exact ⟨T, fun s hs => by rw [← Theta_free f s]; exact hT _ (by omega)⟩
  · rintro ⟨S, hS⟩
    have hconst : (fun s => f (s + S)) = fun _ => true := funext fun s => hS _ (by omega)
    have hrow : AgreesFrom (zrow (Theta f) (2 * S)) 1 := by
      intro k hk
      rw [zrow_Theta_even, hconst, Theta_true]
    exact ⟨1 + 4 * (2 * S), agrees_pre_run (Theta f) 1 (Nat.le_refl 1) (2 * S) hrow⟩

/-! ### Bridge: the phase of the first deviation in rule 30 -/

/-- **Phase of the first deviation, for rule 30 itself.** If the center column alternates
black-first from `T`, then at every time `u ≥ T` the first depth `d` at which the left half
deviates from the stripe `…10101` is even exactly when the center is black at `u`. -/
theorem first_defect_phase {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) (u d : Nat) (hu : T ≤ u)
    (hd : 1 ≤ d) (hag : ∀ k, 1 ≤ k → k < d → cell u (-(k : Int)) = stripe k)
    (hne : cell u (-(d : Int)) ≠ stripe d) : (d % 2 = 0 ↔ cell u 0 = true) := by
  have hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
    intro t ht
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
    · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
      rw [(h j).2]; cases cell (T + 2 * j) 0 <;> rfl
    · show (cell (T + 2 * j + 1) 0 && cell (T + 2 * j + 1 + 1) 0) = false
      rw [(h j).2]; rfl
  have hz := left_half_is_zbl hw
  have hc : Constrained (leftRow T) (u - T + d) := by
    intro j _
    rw [hz (2 * j) 1 (Nat.le_refl 1)]
    exact Rule30PeriodTwo.m1_even h j
  have hp := first_defect_parity (leftRow T) (u - T + d) (u - T) d hd (by omega)
    (fun k hk1 hk2 => by rw [hz _ k hk1, show T + (u - T) = u by omega]; exact hag k hk1 hk2)
    (by rw [hz _ d hd, show T + (u - T) = u by omega]; exact hne) hc
  obtain ⟨j, rfl | rfl⟩ : ∃ j, u = T + 2 * j ∨ u = T + 2 * j + 1 := ⟨(u - T) / 2, by omega⟩
  · rw [(h j).1]; constructor
    · intro _; rfl
    · intro _; omega
  · rw [(h j).2]; constructor
    · intro hd2; exfalso; omega
    · intro h'; cases h'

end Rule30ZeroBoundaryStripe
end Ruliology.CellularAutomata
