module

public import Ruliology.CellularAutomata.Rule30ZeroBoundarySmall

/-!
# The front window of a stripe prefix

Let `x` be a start of the zero-boundary left half (`Rule30ZeroBoundary.zrow`) that agrees with the
stripe `…10101` (`stripe`, black at the odd depths) at the depths `1, …, d - 1`. Then at time
`t < d` the row is still the stripe at the depths `< d - t`, and the window of `K` cells at the
depths `d - t, …, d - t + K - 1` evolves on its own: one step of the ZBL maps the window at time
`t` to the window at time `t + 1` (`win_step`, packed as `fstep`). The window reaches depth `1` at
time `d - 1`; from then on the cell at depth `1` at time `d - 1 + s` only depends on the window
(for `s < K`, light cone).

So the orbit of `(window, parity of the front depth)` decides when depth `1` turns white at an
even time. Since the window map is a bijection on `K`-bit windows, the orbit is periodic, and a
finite certificate (the orbit length `lam` and checkpoints along the orbit) covers every arrival
time `d - 1` at once (`front_sound`).

* `stripe_below`, `win_step`, `win_orb`: the window evolves on its own up to the arrival time.
* `seg`, `seg_sound`, `PathOK`, `Cycle`, `orb_mod`: checked orbit segments and periodic orbits.
* `sig_sound`, `front_sound`: a checked cycle bounds the death time of every such start.
* `row3`, `devB`, `family_of_class`: the family `S[1..m] · b₀ b₁ b₂ · 0^∞` reduces to its class
  data; `Rule30ZeroBoundaryStripeFamily` finishes it with the cycles of
  `Rule30Certificates.ZeroBoundaryStripeCycles0` – `ZeroBoundaryStripeCycles2`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeFront

open Rule30ZeroBoundary Rule30ZeroBoundarySmall

/-! ## Kernel-side definitions -/

/-- One front step on a `K`-bit window `W` (bit `i` = depth `f + i`, stripe below `f`), with
`fp = f % 2`: the new window holds the depths `f - 1, …` one step later. -/
def fstep (K W fp : Nat) : Nat :=
  Nat.land (Nat.xor W (Nat.lor (Nat.lor (Nat.shiftLeft W 1) (Nat.sub 1 fp))
      (Nat.lor (Nat.lor (Nat.shiftLeft W 2) (Nat.shiftLeft (Nat.sub 1 fp) 1)) fp)))
    (Nat.sub (Nat.pow 2 K) 1)

/-- The front step on (window, parity). -/
def fS (K : Nat) (s : Nat × Nat) : Nat × Nat := (fstep K s.1 s.2, 1 - s.2)

/-- `t` front steps. -/
def orb (K : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | t + 1, s => fS K (orb K t s)

/-- One ZBL step on a packed row (raw primitives; equal to `Rule30ZeroBoundarySmall.pstep`). -/
def pstepN (x : Nat) : Nat := Nat.xor (Nat.shiftRight x 1) (Nat.lor x (Nat.shiftLeft x 1))

/-- `a && b` through the recursor. -/
noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

/-- `sig fuel r x`: running the packed row `x` from time `r`, depth `1` is white at an even time
within `fuel` rows. -/
noncomputable def sig (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih r x => Bool.rec (ih (Nat.add r 1) (pstepN x)) true
      (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0))) fuel

/-- A segment of `fuel` front steps from orbit index `r` and state `(W, fp)` to `(Wb, pb)`,
checking `sig (S + 1)` at the indices of parity `q`. -/
noncomputable def seg (K S q Wb pb : Nat) (fuel : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ W fp => band (Nat.beq W Wb) (Nat.beq fp pb))
    (fun _ ih r W fp => band (Bool.rec true (sig (Nat.add S 1) r W) (Nat.beq (Nat.mod r 2) q))
      (ih (Nat.add r 1) (fstep K W fp) (Nat.sub 1 fp))) fuel

/-! ## The orbit -/

theorem orb_succ' (K : Nat) : ∀ t s, orb K (t + 1) s = orb K t (fS K s) := by
  intro t
  induction t with
  | zero => intro s; rfl
  | succ t ih => intro s; show fS K (orb K (t + 1) s) = fS K (orb K t (fS K s)); rw [ih]

theorem orb_add (K : Nat) (a : Nat) : ∀ b s, orb K (a + b) s = orb K b (orb K a s) := by
  intro b
  induction b with
  | zero => intro s; rfl
  | succ b ih => intro s; show fS K (orb K (a + b) s) = fS K (orb K b (orb K a s)); rw [ih]

/-- A checked path: `len` steps from `s` to `s'`, and `sig (S + 1)` holds at the orbit indices
`r + j` of parity `q`. -/
def PathOK (K S q r : Nat) (s s' : Nat × Nat) (len : Nat) : Prop :=
  orb K len s = s' ∧ ∀ j, j < len → (r + j) % 2 = q → sig (S + 1) (r + j) (orb K j s).1 = true

theorem path_append {K S q r a b : Nat} {s s' s'' : Nat × Nat} (h1 : PathOK K S q r s s' a)
    (h2 : PathOK K S q (r + a) s' s'' b) : PathOK K S q r s s'' (a + b) := by
  refine ⟨by rw [orb_add, h1.1, h2.1], fun j hj hq => ?_⟩
  rcases Nat.lt_or_ge j a with h | h
  · exact h1.2 j h hq
  · obtain ⟨i, rfl⟩ : ∃ i, j = a + i := ⟨j - a, by omega⟩
    rw [orb_add, h1.1, show r + (a + i) = r + a + i by omega]
    exact h2.2 i (by omega) (by rw [show r + a + i = r + (a + i) by omega]; exact hq)

theorem seg_sound (K S q Wb pb : Nat) : ∀ fuel r W fp,
    seg K S q Wb pb fuel r W fp = true → PathOK K S q r (W, fp) (Wb, pb) fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro r W fp h
    have h' : band (Nat.beq W Wb) (Nat.beq fp pb) = true := h
    cases h1 : Nat.beq W Wb <;> cases h2 : Nat.beq fp pb <;> rw [h1, h2] at h' <;>
      try exact absurd h' (by decide)
    rw [Nat.beq_eq] at h1 h2
    subst h1 h2
    exact ⟨rfl, fun j hj => absurd hj (by omega)⟩
  | succ fuel ih =>
    intro r W fp h
    have h' : band (Bool.rec true (sig (Nat.add S 1) r W) (Nat.beq (Nat.mod r 2) q))
        (seg K S q Wb pb fuel (Nat.add r 1) (fstep K W fp) (Nat.sub 1 fp)) = true := h
    cases h1 : Bool.rec (motive := fun _ => Bool) true (sig (Nat.add S 1) r W)
        (Nat.beq (Nat.mod r 2) q) <;> rw [h1] at h'
    · exact absurd h' Bool.false_ne_true
    · have hrest := ih (r + 1) (fstep K W fp) (1 - fp) h'
      refine ⟨by rw [orb_succ']; exact hrest.1, fun j hj hq => ?_⟩
      cases j with
      | zero =>
        have hb : Nat.beq (Nat.mod r 2) q = true := by rw [Nat.beq_eq]; exact hq
        rw [hb] at h1
        exact h1
      | succ j =>
        rw [orb_succ', show r + (j + 1) = r + 1 + j by omega]
        exact hrest.2 j (by omega) (by rw [show r + 1 + j = r + (j + 1) by omega]; exact hq)

/-- A periodic orbit with the `sig` checks at every index of parity `1 - p0`. -/
def Cycle (K S W0 p0 lam : Nat) : Prop :=
  lam % 2 = 0 ∧ 0 < lam ∧ PathOK K S (1 - p0) 0 (W0, p0) (W0, p0) lam

theorem orb_mul (K lam : Nat) (s : Nat × Nat) (h : orb K lam s = s) : ∀ j, orb K (lam * j) s = s := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.mul_succ, orb_add, ih, h]

theorem orb_mod (K lam : Nat) (s : Nat × Nat) (h : orb K lam s = s) (t : Nat) :
    orb K t s = orb K (t % lam) s := by
  conv => lhs; rw [← Nat.div_add_mod t lam]
  rw [orb_add, orb_mul K lam s h]

/-! ## `sig` -/

theorem pstepN_eq (x : Nat) : pstepN x = pstep x := rfl

theorem sig_sound : ∀ fuel r x, sig fuel r x = true →
    ∃ s, s < fuel ∧ (r + s) % 2 = 0 ∧ prun x s % 2 = 0 := by
  intro fuel
  induction fuel with
  | zero => intro r x h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro r x h
    have h' : Bool.rec (motive := fun _ => Bool) (sig fuel (Nat.add r 1) (pstepN x)) true
        (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0)) = true := h
    cases h1 : Nat.beq (Nat.mod r 2) 0 <;> cases h2 : Nat.beq (Nat.mod x 2) 0 <;>
      rw [h1, h2] at h'
    · obtain ⟨s, hs, h3, h4⟩ := ih (r + 1) (pstep x) h'
      exact ⟨s + 1, by omega, by rw [show r + (s + 1) = r + 1 + s by omega]; exact h3,
        by rw [prun_succ]; exact h4⟩
    · obtain ⟨s, hs, h3, h4⟩ := ih (r + 1) (pstep x) h'
      exact ⟨s + 1, by omega, by rw [show r + (s + 1) = r + 1 + s by omega]; exact h3,
        by rw [prun_succ]; exact h4⟩
    · obtain ⟨s, hs, h3, h4⟩ := ih (r + 1) (pstep x) h'
      exact ⟨s + 1, by omega, by rw [show r + (s + 1) = r + 1 + s by omega]; exact h3,
        by rw [prun_succ]; exact h4⟩
    · rw [Nat.beq_eq] at h1 h2
      exact ⟨0, by omega, h1, h2⟩

/-! ## Packing -/

/-- `f 0, …, f (K - 1)` as the bits of a number. -/
def pk (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => pk f m ||| (if f m then 2 ^ m else 0)

theorem testBit_pk (f : Nat → Bool) : ∀ m s, (pk f m).testBit s = (decide (s < m) && f s) := by
  intro m
  induction m with
  | zero => intro s; simp [pk]
  | succ m ih =>
    intro s
    simp only [pk, Nat.testBit_or, ih]
    by_cases h : s = m
    · subst h
      cases f s <;> simp
    · cases hf : f m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.or_false]
        by_cases h2 : s < m
        · simp [h2, show s < m + 1 by omega]
        · simp [h2, show ¬ s < m + 1 by omega]
      · simp only [↓reduceIte, Nat.testBit_two_pow]
        by_cases h2 : s < m
        · simp [h2, show s < m + 1 by omega, show m ≠ s by omega]
        · simp [h2, show ¬ s < m + 1 by omega, show m ≠ s by omega]

theorem pk_congr (f g : Nat → Bool) (K : Nat) (h : ∀ i, i < K → f i = g i) : pk f K = pk g K := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pk, testBit_pk]
  by_cases hi : i < K
  · rw [h i hi]
  · simp [hi]

/-! ## The window -/

/-- Below the front the row is the stripe. -/
theorem stripe_below (x : Nat → Bool) (d : Nat) (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) :
    ∀ t k, k + t < d → zrow x t k = stripe k := by
  intro t k hk
  rw [zrow_light_cone (L' := stripe) t k (fun i h1 h2 => hag i h1 (by omega)), zrow_stripe]

/-- The window at time `t`: depths `d - t, …, d - t + K - 1`. -/
def win (x : Nat → Bool) (d K t : Nat) : Nat := pk (fun i => zrow x t (d - t + i)) K

theorem testBit_fstep (K W fp i : Nat) (hfp : fp < 2) :
    (fstep K W fp).testBit i = (decide (i < K) && xor (W.testBit i)
      ((if i = 0 then decide (fp = 0) else W.testBit (i - 1)) ||
        (if i = 0 then decide (fp = 1) else if i = 1 then decide (fp = 0) else W.testBit (i - 2)))) := by
  show ((W ^^^ (((W <<< 1) ||| (1 - fp)) ||| (((W <<< 2) ||| ((1 - fp) <<< 1)) ||| fp)))
    &&& (2 ^ K - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_xor, Nat.testBit_or,
    Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft]
  rw [Bool.and_comm]
  congr 1
  have h11 : (1 : Nat).testBit 1 = false := by decide
  have h10 : (1 : Nat).testBit 0 = true := by decide
  rcases (show fp = 0 ∨ fp = 1 by omega) with rfl | rfl
  · rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · simp [h10]
    · simp [h10]
    · simp [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≥ 1 by omega, show i ≥ 2 by omega,
        Nat.testBit_lt_two_pow (show (1 : Nat) < 2 ^ (i - 1) from Nat.one_lt_two_pow (by omega)),
        Nat.testBit_lt_two_pow (show (1 : Nat) < 2 ^ i from Nat.one_lt_two_pow (by omega))]
  · rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · simp [h10]
    · simp [h11]
    · simp [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≥ 1 by omega, show i ≥ 2 by omega,
        Nat.testBit_lt_two_pow (show (1 : Nat) < 2 ^ i from Nat.one_lt_two_pow (by omega))]

theorem stripe_pred (c : Nat) (hc : 1 ≤ c) : stripe (c - 1) = decide (c % 2 = 0) := by
  unfold stripe
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · simp [h, show (c - 1) % 2 = 1 by omega]
  · simp [h, show (c - 1) % 2 = 0 by omega]

theorem stripe_pred2 (c : Nat) (hc : 2 ≤ c) : stripe (c - 2) = decide (c % 2 = 1) := by
  unfold stripe
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · simp [h, show (c - 2) % 2 = 0 by omega]
  · simp [h, show (c - 2) % 2 = 1 by omega]

/-- **The window evolves on its own.** -/
theorem win_step (x : Nat → Bool) (d K t : Nat) (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k)
    (ht : t + 2 ≤ d) : win x d K (t + 1) = fstep K (win x d K t) ((d - t) % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fstep K _ _ i (Nat.mod_lt _ (by omega))]
  unfold win
  rw [testBit_pk]
  by_cases hi : i < K
  · simp only [hi, decide_true, Bool.true_and]
    have hsb := stripe_below x d hag t
    -- the ZBL step at depth `d - t - 1 + i`
    have e : zrow x (t + 1) (d - (t + 1) + i) =
        xor (zrow x t (d - t + i)) (zrow x t (d - t - 1 + i) || zrow x t (d - t - 2 + i)) := by
      obtain ⟨j, hj⟩ : ∃ j, d - (t + 1) + i = j + 1 := ⟨d - (t + 1) + i - 1, by omega⟩
      rw [hj, zrow_succ, show j + 2 = d - t + i by omega, show j + 1 = d - t - 1 + i by omega,
        show j = d - t - 2 + i by omega]
    have hW : ∀ j, j < K → (pk (fun i => zrow x t (d - t + i)) K).testBit j = zrow x t (d - t + j) :=
      fun j hj => by rw [testBit_pk]; simp [hj]
    rw [e]
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h2
    · rw [hW 0 hi, ite_eq_left rfl, ite_eq_left rfl]
      simp only [Nat.add_zero]
      rw [hsb (d - t - 1) (by omega), hsb (d - t - 2) (by omega),
        stripe_pred (d - t) (by omega), stripe_pred2 (d - t) (by omega)]
    · rw [hW 1 hi, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, hW 0 (by omega),
        show d - t - 1 + 1 = d - t + 0 by omega, show d - t - 2 + 1 = d - t - 1 by omega,
        hsb (d - t - 1) (by omega), stripe_pred (d - t) (by omega)]
    · rw [hW i hi, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        hW (i - 1) (by omega), hW (i - 2) (by omega),
        show d - t - 1 + i = d - t + (i - 1) by omega, show d - t - 2 + i = d - t + (i - 2) by omega]
  · simp [hi]

/-- **The orbit of the window.** Up to the arrival time `d - 1`, the window and the parity of the
front depth are the orbit of the start window. -/
theorem win_orb (x : Nat → Bool) (d K : Nat) (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) :
    ∀ t, t + 1 ≤ d → orb K t (win x d K 0, d % 2) = (win x d K t, (d - t) % 2) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    show fS K (orb K t (win x d K 0, d % 2)) = _
    rw [ih (by omega)]
    show (fstep K (win x d K t) ((d - t) % 2), 1 - (d - t) % 2) = _
    rw [← win_step x d K t hag (by omega), show 1 - (d - t) % 2 = (d - (t + 1)) % 2 by omega]

theorem win_zero (x : Nat → Bool) (d K : Nat) (hd : 1 ≤ d) :
    win x d K 0 = pk (fun i => x (d + i)) K := by
  unfold win
  apply pk_congr
  intro i _
  rw [Nat.sub_zero, zrow_zero_of_pos x (by omega)]

/-- **Soundness of a front certificate.** If `x` is the stripe at the depths `1, …, d - 1` and the
orbit of its start window `(pk (x (d + ·)) K, d % 2)` is a checked cycle, then depth `1` is white
at some even time `d - 1 + s` with `s ≤ S`. -/
theorem front_sound (x : Nat → Bool) (d K S lam : Nat) (hd : 1 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) (hSK : S + 1 ≤ K)
    (hcyc : Cycle K S (pk (fun i => x (d + i)) K) (d % 2) lam) :
    ∃ s, s ≤ S ∧ (d - 1 + s) % 2 = 0 ∧ zrow x (d - 1 + s) 1 = false := by
  obtain ⟨hlam2, hlam0, hper, hsig⟩ := hcyc
  have ho := win_orb x d K hag (d - 1) (by omega)
  rw [win_zero x d K hd, show d - (d - 1) = 1 by omega] at ho
  rw [orb_mod K lam _ hper] at ho
  have hr := hsig ((d - 1) % lam) (Nat.mod_lt _ hlam0) (by
    rw [Nat.zero_add]
    have : (d - 1) % lam % 2 = (d - 1) % 2 := by
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hlam2)]
    rw [this]; omega)
  rw [Nat.zero_add, ho] at hr
  obtain ⟨s, hs, hpar, hprun⟩ := sig_sound _ _ _ hr
  refine ⟨s, by omega, ?_, ?_⟩
  · have : (d - 1) % lam % 2 = (d - 1) % 2 := by
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hlam2)]
    omega
  · -- light cone: the row at time `d - 1` agrees with the window at depths `1, …, K`
    rw [zrow_shift, zrow_light_cone (L' := toFun (win x d K (d - 1))) s 1 (fun i h1 h2 => by
      simp only [toFun, show i ≠ 0 by omega, ite_false]
      unfold win
      rw [testBit_pk, show d - (d - 1) + (i - 1) = i by omega]
      simp [show i - 1 < K by omega]), run_toFun]
    simp only [toFun, ite_false, Nat.sub_self, show (1 : Nat) ≠ 0 by omega]
    rw [Nat.testBit_zero]
    simp [hprun]

/-! ## The family `S[1..m] · b₀ b₁ b₂ · 0^∞` -/

/-- The word `b₀ b₁ b₂` followed by white. -/
def vget (b0 b1 b2 : Bool) (i : Nat) : Bool :=
  if i = 0 then b0 else if i = 1 then b1 else if i = 2 then b2 else false

/-- The start `S[1..m] · b₀ b₁ b₂ · 0^∞`: the stripe at depths `1, …, m`, then `b₀, b₁, b₂` at depths
`m + 1, m + 2, m + 3`, white beyond. -/
def row3 (m : Nat) (b0 b1 b2 : Bool) (k : Nat) : Bool :=
  if k ≤ m then stripe k else vget b0 b1 b2 (k - m - 1)

/-- The class data: the first deviation is at offset `δ` (for `m` of parity `q`). -/
def devB (q δ : Nat) (b0 b1 b2 : Bool) : Bool :=
  (List.range δ).all (fun j => j == 0 || vget b0 b1 b2 (j - 1) == stripe (q + j)) &&
    vget b0 b1 b2 (δ - 1) != stripe (q + δ)

theorem stripe_add_mod (m q j : Nat) (hq : m % 2 = q) : stripe (m + j) = stripe (q + j) := by
  unfold stripe
  rw [show (m + j) % 2 = (q + j) % 2 by omega]

/-- **The family reduces to the class data.** -/
theorem family_of_class (m q δ lam : Nat) (b0 b1 b2 : Bool) (hq : m % 2 = q) (hδ : 1 ≤ δ)
    (hdev : devB q δ b0 b1 b2 = true)
    (hcyc : Cycle 32 31 (pk (fun i => vget b0 b1 b2 (δ - 1 + i)) 32) ((q + δ) % 2) lam) :
    (∀ k, 1 ≤ k → k < m + δ → row3 m b0 b1 b2 k = stripe k) ∧
      row3 m b0 b1 b2 (m + δ) ≠ stripe (m + δ) ∧
      ∃ t, t ≤ m + δ - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row3 m b0 b1 b2) t 1 = false := by
  simp only [devB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hdev
  obtain ⟨hall, hne⟩ := hdev
  have hag : ∀ k, 1 ≤ k → k < m + δ → row3 m b0 b1 b2 k = stripe k := by
    intro k hk1 hk2
    unfold row3
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
    · rw [ite_eq_right hkm]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      rw [stripe_add_mod m q j hq, show m + j - m - 1 = j - 1 by omega]
      rcases hall j (by omega) with h | h
      · omega
      · exact h
  refine ⟨hag, ?_, ?_⟩
  · unfold row3
    rw [ite_eq_right (by omega), show m + δ - m - 1 = δ - 1 by omega, stripe_add_mod m q δ hq]
    exact hne
  · have hw : pk (fun i => row3 m b0 b1 b2 (m + δ + i)) 32 = pk (fun i => vget b0 b1 b2 (δ - 1 + i)) 32 :=
      pk_congr _ _ _ fun i _ => by
        unfold row3; rw [ite_eq_right (by omega), show m + δ + i - m - 1 = δ - 1 + i by omega]
    have hp : (m + δ) % 2 = (q + δ) % 2 := by omega
    rw [← hw, ← hp] at hcyc
    obtain ⟨s, hs, he, hz⟩ := front_sound (row3 m b0 b1 b2) (m + δ) 32 31 lam (by omega) hag
      (by omega) hcyc
    exact ⟨m + δ - 1 + s, by omega, he, hz⟩

end Rule30ZeroBoundaryStripeFront
end Ruliology.CellularAutomata
