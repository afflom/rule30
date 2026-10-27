module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# `Q01` for all starts of bounded width: a bit-sliced certificate checker

The zero-boundary left half (`Rule30ZeroBoundary.zrow`) is reconstructed sideways from its
boundary column `y t = zrow L t 1` (`Rule30ZeroBoundary.recon`). The cells with `depth + time = k`
form the anti-diagonal `k`; listed by depth, the anti-diagonal `k` is
`[recon y 1 (k-1), recon y 2 (k-2), …, recon y k 0]` (`AD y k 0 k`), and the anti-diagonal `k + 1`
is a running xor over the anti-diagonals `k` and `k - 1`, started from `y k` (`scanN`). Its last
entry is the start `L (k + 1) = recon y (k + 1) 0`.

A start supported at depths `1, …, W` that keeps column `-1` black at the even times is fixed by
its free bits `y 1, y 3, …`: the free bits `y (2 s + 1)` with `2 s + 2 ≤ W` are arbitrary and every
later free bit is forced by `L (k + 1) = 0`. The checker runs `2 ^ n` choices of the first `n` free
bits at once, one choice per bit position ("lane") of each natural number, so every step is a
bitwise operation on big numbers that the kernel evaluates with GMP. The chunk index `c` fixes the
remaining arbitrary free bits. A lane dies when some `L (k + 1)` with `W < k + 1` is black at an
even level `k`.

* `check W K n c`: every lane of chunk `c` dies within `K` levels.
* `q01_of_checks`: if `check W K n c` holds for every chunk `c`, then every start supported at
  depths `≤ W` has a white cell at depth `1` at some even time `< K`.
* `q01_of_chunks`: the same from a combined range certificate `ChunksOK`.

`Rule30ZeroBoundaryWidth52` runs the checker at width `52`: all `256` chunks pass with `97` levels.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryLanes

open Rule30ZeroBoundary

/-! ## The kernel computation -/

/-- Running xor over one anti-diagonal: `v_{i+1} = v_i xor (a_i or b_i)`. Returns the list of
`v_1, v_2, …` and the last value. Written with the recursor and raw `Nat` primitives so that the
kernel evaluates it quickly. -/
noncomputable def scanN : Nat → List Nat → List Nat → List Nat × Nat := fun acc as =>
  List.rec (motive := fun _ => Nat → List Nat → List Nat × Nat)
    (fun acc _ => ([], acc))
    (fun a _ ih acc bs =>
      let v := Nat.xor acc (Nat.lor a (List.headD bs 0))
      let r := ih v (List.tail bs)
      (v :: r.1, r.2))
    as acc

/-- xor every entry with `t`. -/
noncomputable def mapX (t : Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => Nat.xor t a :: ih)

/-- Doubling a bit pattern `m` times. -/
def dbl : Nat → Nat → Nat → Nat
  | 0, B, _ => B
  | m + 1, B, len => dbl m (Nat.lor B (Nat.shiftLeft B len)) (Nat.add len len)

/-- The lane pattern for free bit `s` among `2 ^ n` lanes: bit `p` is bit `s` of `p`. -/
def pat (n s : Nat) : Nat :=
  dbl (n - (s + 1)) (Nat.shiftLeft (Nat.sub (Nat.pow 2 (Nat.pow 2 s)) 1) (Nat.pow 2 s))
    (Nat.pow 2 (s + 1))

/-- The free bit number `s` in every lane: from the lane pattern, or from the chunk index. -/
def yFree (n c ALL : Nat) (pats : List Nat) (s : Nat) : Nat :=
  if s < n then pats.getD s 0 else if c.testBit (s - n) then ALL else 0

/-- One level: the new anti-diagonal `k + 1` and its last entry (all lanes). Even level: `y k = 1`.
Odd level with `k + 1 ≤ W`: free bit. Odd level with `W < k + 1`: the bit that makes
`L (k + 1) = 0`. -/
noncomputable def stepR (W n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) :
    List Nat × Nat :=
  Bool.rec
    (Bool.rec
      (let r := scanN 0 R (0 :: Rm); (r.2 :: mapX r.2 r.1, r.2))
      (let y := yFree n c ALL pats (Nat.div k 2); let r := scanN y R (0 :: Rm); (y :: r.1, r.2))
      (Nat.ble (Nat.add k 1) W))
    (let r := scanN ALL R (0 :: Rm); (ALL :: r.1, r.2))
    (Nat.beq (Nat.mod k 2) 0)

/-- `a && b` through the recursor. -/
noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

/-- Run `fuel` levels from level `k` (anti-diagonals `R = k`, `Rm = k - 1`); `alive` holds the
lanes that have not died. Succeeds when no lane is alive at the end. -/
noncomputable def run (W n c ALL : Nat) (pats : List Nat) (fuel : Nat) :
    Nat → List Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Nat → Bool)
    (fun _ _ _ alive => Nat.beq alive 0)
    (fun _ ih k R Rm alive =>
      let st := stepR W n c ALL pats k R Rm
      ih (Nat.add k 1) st.1 R
        (Bool.rec alive (Nat.land alive (Nat.xor ALL st.2))
          (band (Nat.beq (Nat.mod k 2) 0) (Nat.blt W (Nat.add k 1)))))
    fuel

/-- The check for chunk `c`: `2 ^ n` lanes, `K` levels, starts supported at depths `≤ W`. -/
noncomputable def check (W K n c : Nat) : Bool :=
  run W n c (2 ^ 2 ^ n - 1) ((List.range n).map (pat n)) K 0 [] [] (2 ^ 2 ^ n - 1)

/-! ## Equations -/

theorem scanN_nil (acc : Nat) (bs : List Nat) : scanN acc [] bs = ([], acc) := rfl

theorem scanN_cons (acc a : Nat) (as bs : List Nat) :
    scanN acc (a :: as) bs =
      ((acc ^^^ (a ||| bs.headD 0)) :: (scanN (acc ^^^ (a ||| bs.headD 0)) as bs.tail).1,
        (scanN (acc ^^^ (a ||| bs.headD 0)) as bs.tail).2) := rfl

theorem mapX_nil (t : Nat) : mapX t [] = [] := rfl

theorem mapX_cons (t a : Nat) (as : List Nat) : mapX t (a :: as) = (t ^^^ a) :: mapX t as := rfl

theorem mapX_mapX (a b : Nat) : ∀ l : List Nat, mapX a (mapX b l) = mapX (a ^^^ b) l
  | [] => rfl
  | x :: l => by rw [mapX_cons, mapX_cons, mapX_cons, mapX_mapX a b l, Nat.xor_assoc]

/-- Linearity of the running xor in its start value. -/
theorem scanN_lin : ∀ (as bs : List Nat) (acc : Nat),
    scanN acc as bs = (mapX acc (scanN 0 as bs).1, acc ^^^ (scanN 0 as bs).2)
  | [], bs, acc => by rw [scanN_nil, scanN_nil, mapX_nil, Nat.xor_zero]
  | a :: as, bs, acc => by
    rw [scanN_cons, scanN_cons, scanN_lin as bs.tail (acc ^^^ (a ||| bs.headD 0)),
      scanN_lin as bs.tail (0 ^^^ (a ||| bs.headD 0)), mapX_cons, mapX_mapX, Nat.zero_xor,
      Nat.xor_assoc]

theorem run_zero (W n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) (alive : Nat) :
    run W n c ALL pats 0 k R Rm alive = Nat.beq alive 0 := rfl

theorem run_succ (W n c ALL : Nat) (pats : List Nat) (f k : Nat) (R Rm : List Nat) (alive : Nat) :
    run W n c ALL pats (f + 1) k R Rm alive =
      run W n c ALL pats f (k + 1) (stepR W n c ALL pats k R Rm).1 R
        (Bool.rec alive (alive &&& (ALL ^^^ (stepR W n c ALL pats k R Rm).2))
          (band (Nat.beq (k % 2) 0) (Nat.blt W (k + 1)))) := rfl

theorem stepR_even (W n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : k % 2 = 0) :
    stepR W n c ALL pats k R Rm =
      (ALL :: (scanN ALL R (0 :: Rm)).1, (scanN ALL R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod k 2) 0 = true := by rw [Nat.beq_eq]; exact h
  unfold stepR; rw [hb]

theorem stepR_free (W n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : k % 2 = 1) (hW : k + 1 ≤ W) :
    stepR W n c ALL pats k R Rm =
      (yFree n c ALL pats (k / 2) :: (scanN (yFree n c ALL pats (k / 2)) R (0 :: Rm)).1,
        (scanN (yFree n c ALL pats (k / 2)) R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod k 2) 0 = false := by
    cases hq : Nat.beq (Nat.mod k 2) 0
    · rfl
    · rw [Nat.beq_eq] at hq; exact absurd hq (by show ¬ k % 2 = 0; omega)
  have hb2 : Nat.ble (Nat.add k 1) W = true := by rw [Nat.ble_eq]; exact hW
  unfold stepR; rw [hb, hb2]; rfl

theorem stepR_forced (W n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : k % 2 = 1) (hW : W < k + 1) :
    stepR W n c ALL pats k R Rm =
      ((scanN 0 R (0 :: Rm)).2 :: mapX (scanN 0 R (0 :: Rm)).2 (scanN 0 R (0 :: Rm)).1,
        (scanN 0 R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod k 2) 0 = false := by
    cases hq : Nat.beq (Nat.mod k 2) 0
    · rfl
    · rw [Nat.beq_eq] at hq; exact absurd hq (by show ¬ k % 2 = 0; omega)
  have hb2 : Nat.ble (Nat.add k 1) W = false := by
    cases hq : Nat.ble (Nat.add k 1) W
    · rfl
    · rw [Nat.ble_eq] at hq; exact absurd hq (by show ¬ k + 1 ≤ W; omega)
  unfold stepR; rw [hb, hb2]

/-! ## Anti-diagonals of the reconstruction -/

/-- `AD y k i n`: the entries `i, …, i + n - 1` of anti-diagonal `k` listed by depth; entry `i` is
the cell at depth `i + 1` and time `k - 1 - i`. -/
def AD (y : Nat → Bool) (k : Nat) : Nat → Nat → List Bool
  | _, 0 => []
  | i, n + 1 => recon y (i + 1) (k - 1 - i) :: AD y k (i + 1) n

theorem AD_getD (y : Nat → Bool) (k : Nat) :
    ∀ n i j, j < n → (AD y k i n).getD j false = recon y (i + j + 1) (k - 1 - i - j) := by
  intro n
  induction n with
  | zero => intro i j hj; omega
  | succ n ih =>
    intro i j hj
    cases j with
    | zero => simp [AD]
    | succ j =>
      show (AD y k (i + 1) n).getD j false = _
      rw [ih (i + 1) j (by omega), show i + 1 + j + 1 = i + (j + 1) + 1 by omega,
        show k - 1 - (i + 1) - j = k - 1 - i - (j + 1) by omega]

theorem recon_zero' (y : Nat → Bool) (t : Nat) : recon y 0 t = false := by rw [recon]

theorem recon_one' (y : Nat → Bool) (t : Nat) : recon y 1 t = y t := by rw [recon]

theorem getD_tail (l : List Nat) (j : Nat) : l.tail.getD j 0 = l.getD (j + 1) 0 := by
  cases l with
  | nil => rfl
  | cons a l => rfl

theorem headD_eq (l : List Nat) : l.headD 0 = l.getD 0 0 := by
  cases l with
  | nil => rfl
  | cons a l => rfl

theorem getD_testBit (l : List Nat) (p : Nat) :
    ∀ j, (l.getD j 0).testBit p = (l.map (fun v => v.testBit p)).getD j false := by
  induction l with
  | nil => intro j; simp
  | cons a l ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j => rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ, ih]

/-- **Lane semantics of the running xor.** If lane `p` of `as` is the depth range `i + 1, …` of
anti-diagonal `k`, lane `p` of `bs` the matching range of anti-diagonal `k - 1` shifted by one
depth, and lane `p` of `acc` the cell at depth `i + 1` and time `k - i`, then lane `p` of the
output is the matching range of anti-diagonal `k + 1`, and the last value is the cell at depth
`i + n + 1` and time `k - i - n`. -/
theorem scanN_AD (y : Nat → Bool) (k p : Nat) : ∀ (n i : Nat) (as bs : List Nat) (acc : Nat),
    i + n ≤ k →
    as.map (fun v => v.testBit p) = AD y k i n →
    (∀ j, j < n → (bs.getD j 0).testBit p = recon y (i + j) (k - 1 - i - j)) →
    acc.testBit p = recon y (i + 1) (k - i) →
    (scanN acc as bs).1.map (fun v => v.testBit p) = AD y (k + 1) (i + 1) n ∧
      (scanN acc as bs).2.testBit p = recon y (i + n + 1) (k - i - n) := by
  intro n
  induction n with
  | zero =>
    intro i as bs acc _ has _ hacc
    cases as with
    | nil => exact ⟨rfl, by rw [scanN_nil]; exact hacc⟩
    | cons a as => simp [AD] at has
  | succ n ih =>
    intro i as bs acc hk has hbs hacc
    cases as with
    | nil => simp [AD] at has
    | cons a as =>
      rw [List.map_cons] at has
      simp only [AD, List.cons.injEq] at has
      obtain ⟨ha, has⟩ := has
      have hb0 := hbs 0 (by omega)
      rw [Nat.add_zero, Nat.sub_zero] at hb0
      have hv : (acc ^^^ (a ||| bs.headD 0)).testBit p = recon y (i + 1 + 1) (k - (i + 1)) := by
        rw [show k - (i + 1) = k - 1 - i by omega, show i + 1 + 1 = i + 2 from rfl, recon_two,
          show k - 1 - i + 1 = k - i by omega, Nat.testBit_xor, Nat.testBit_or, hacc, ha,
          headD_eq, hb0]
      have := ih (i + 1) as bs.tail (acc ^^^ (a ||| bs.headD 0)) (by omega) has
        (fun j hj => by
          rw [getD_tail, hbs (j + 1) (by omega), show i + (j + 1) = i + 1 + j by omega,
            show k - 1 - i - (j + 1) = k - 1 - (i + 1) - j by omega]) hv
      rw [scanN_cons]
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, this.1]
        simp only [AD]
        rw [hv, show k + 1 - 1 - (i + 1) = k - (i + 1) by omega]
      · rw [this.2, show i + 1 + n + 1 = i + (n + 1) + 1 by omega,
          show k - (i + 1) - n = k - i - (n + 1) by omega]

/-- **One level, one lane.** -/
theorem level (y : Nat → Bool) (p k : Nat) (R Rm : List Nat) (Y : Nat)
    (hR : R.map (fun v => v.testBit p) = AD y k 0 k)
    (hRm : Rm.map (fun v => v.testBit p) = AD y (k - 1) 0 (k - 1))
    (hY : Y.testBit p = y k) :
    (Y :: (scanN Y R (0 :: Rm)).1).map (fun v => v.testBit p) = AD y (k + 1) 0 (k + 1) ∧
      (scanN Y R (0 :: Rm)).2.testBit p = recon y (k + 1) 0 := by
  have h := scanN_AD y k p k 0 R (0 :: Rm) Y (by omega) hR
    (fun j hj => by
      cases j with
      | zero =>
        rw [show ((0 :: Rm).getD 0 0) = 0 from rfl, Nat.zero_testBit, Nat.zero_add, recon_zero']
      | succ j =>
        show (Rm.getD j 0).testBit p = _
        rw [getD_testBit, hRm, AD_getD y (k - 1) (k - 1) 0 j (by omega)]
        rw [show 0 + j + 1 = 0 + (j + 1) by omega,
          show k - 1 - 1 - 0 - j = k - 1 - 0 - (j + 1) by omega])
    (by rw [hY, Nat.zero_add, Nat.sub_zero, recon_one'])
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, h.1, hY]
    simp only [AD]
    rw [Nat.zero_add, show k + 1 - 1 - 0 = k by omega, recon_one']
  · rw [h.2, show 0 + k + 1 = k + 1 by omega, show k - 0 - k = 0 by omega]

/-! ## Lane patterns -/

theorem testBit_low_block (s q : Nat) (hq : q < 2 ^ (s + 1)) :
    q.testBit s = decide (2 ^ s ≤ q) := by
  by_cases h : 2 ^ s ≤ q
  · obtain ⟨r, rfl⟩ : ∃ r, q = 2 ^ s + r := ⟨q - 2 ^ s, by omega⟩
    have hr : r < 2 ^ s := by rw [Nat.pow_succ] at hq; omega
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
    simp
  · rw [Nat.testBit_lt_two_pow (by omega)]
    simp [h]

theorem dbl_spec (s : Nat) : ∀ (m B j : Nat), s < j →
    (∀ q, B.testBit q = (decide (q < 2 ^ j) && q.testBit s)) →
    ∀ q, (dbl m B (2 ^ j)).testBit q = (decide (q < 2 ^ (j + m)) && q.testBit s) := by
  intro m
  induction m with
  | zero => intro B j _ hB q; exact hB q
  | succ m ih =>
    intro B j hsj hB q
    show (dbl m (B ||| (B <<< 2 ^ j)) (2 ^ j + 2 ^ j)).testBit q = _
    rw [show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by rw [Nat.pow_succ]; omega,
      ih (B ||| (B <<< 2 ^ j)) (j + 1) (by omega) ?_ q, show j + 1 + m = j + (m + 1) by omega]
    intro q
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, hB, hB]
    have h2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
    by_cases h1 : q < 2 ^ j
    · simp [h1, show q < 2 ^ (j + 1) by omega, show ¬ q ≥ 2 ^ j by omega]
    · by_cases h3 : q < 2 ^ (j + 1)
      · obtain ⟨r, rfl⟩ : ∃ r, q = 2 ^ j + r := ⟨q - 2 ^ j, by omega⟩
        have hr : r < 2 ^ j := by omega
        simp [h1, h3, hr, Nat.testBit_two_pow_add_gt hsj]
      · simp [h1, h3, show ¬ q - 2 ^ j < 2 ^ j by omega]

/-- **The lane pattern**: bit `p` of `pat n s` is bit `s` of `p`. -/
theorem pat_spec (n s p : Nat) (hs : s < n) (hp : p < 2 ^ n) : (pat n s).testBit p = p.testBit s := by
  have base : ∀ q, (Nat.shiftLeft (Nat.sub (Nat.pow 2 (Nat.pow 2 s)) 1) (Nat.pow 2 s)).testBit q =
      (decide (q < 2 ^ (s + 1)) && q.testBit s) := by
    intro q
    show ((2 ^ 2 ^ s - 1) <<< 2 ^ s).testBit q = _
    rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    have h2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [Nat.pow_succ]; omega
    by_cases hq : q < 2 ^ (s + 1)
    · rw [testBit_low_block s q hq]
      by_cases h : 2 ^ s ≤ q
      · simp [h, hq, show q - 2 ^ s < 2 ^ s by omega]
      · simp [h, hq]
    · simp [hq, show ¬ q - 2 ^ s < 2 ^ s by omega]
  have := dbl_spec s (n - (s + 1)) _ (s + 1) (by omega) base p
  unfold pat
  rw [show Nat.pow 2 (s + 1) = 2 ^ (s + 1) from rfl, this,
    show s + 1 + (n - (s + 1)) = n by omega]
  simp [hp]

theorem pats_getD (n s : Nat) (hs : s < n) : ((List.range n).map (pat n)).getD s 0 = pat n s := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]
  rfl

/-! ## Packing free bits -/

/-- The first `m` values of `f` as the bits of a number. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => pack f m ||| (if f m then 2 ^ m else 0)

theorem testBit_pack (f : Nat → Bool) : ∀ m s, (pack f m).testBit s = (decide (s < m) && f s) := by
  intro m
  induction m with
  | zero => intro s; simp [pack]
  | succ m ih =>
    intro s
    simp only [pack, Nat.testBit_or, ih]
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

theorem pack_lt (f : Nat → Bool) (m : Nat) : pack f m < 2 ^ m :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [testBit_pack]; simp; omega

/-! ## Soundness -/

/-- **Soundness of `run` for one lane.** Lane `p` follows a boundary column `y` that is black at
the even times, matches the free bits of the lane, and comes from a start that is white beyond
depth `W`. Then the lane never dies, so `run` cannot succeed. -/
theorem run_sound (W n c ALL : Nat) (pats : List Nat) (y : Nat → Bool) (p : Nat)
    (hALL : ALL.testBit p = true)
    (hfree : ∀ t, t % 2 = 1 → t + 1 ≤ W → (yFree n c ALL pats (t / 2)).testBit p = y t)
    (hwid : ∀ d, W < d → recon y d 0 = false) :
    ∀ fuel k R Rm alive,
      run W n c ALL pats fuel k R Rm alive = true →
      (∀ t, k ≤ t → t < k + fuel → t % 2 = 0 → y t = true) →
      R.map (fun v => v.testBit p) = AD y k 0 k →
      Rm.map (fun v => v.testBit p) = AD y (k - 1) 0 (k - 1) →
      alive.testBit p = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro k R Rm alive hrun _ _ _ halive
    rw [run_zero, Nat.beq_eq] at hrun
    rw [hrun, Nat.zero_testBit] at halive
    exact absurd halive (by decide)
  | succ fuel ih =>
    intro k R Rm alive hrun heven hR hRm halive
    rw [run_succ] at hrun
    have heven' : ∀ t, k + 1 ≤ t → t < k + 1 + fuel → t % 2 = 0 → y t = true :=
      fun t h1 h2 h3 => heven t (by omega) (by omega) h3
    have hRm' : R.map (fun v => v.testBit p) = AD y (k + 1 - 1) 0 (k + 1 - 1) := by
      rw [show k + 1 - 1 = k by omega]; exact hR
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · -- even level
      rw [stepR_even W n c ALL pats k R Rm hk] at hrun
      have hY : ALL.testBit p = y k := by rw [hALL, heven k (by omega) (by omega) hk]
      have hl := level y p k R Rm ALL hR hRm hY
      refine ih (k + 1) _ R _ hrun heven' hl.1 hRm' ?_
      have hb : Nat.beq (k % 2) 0 = true := by rw [Nat.beq_eq]; exact hk
      rw [hb]
      by_cases hW : W < k + 1
      · have hb2 : Nat.blt W (k + 1) = true := by rw [Nat.blt_eq]; exact hW
        rw [hb2]
        show (alive &&& (ALL ^^^ (scanN ALL R (0 :: Rm)).2)).testBit p = true
        rw [Nat.testBit_and, Nat.testBit_xor, hl.2, hwid (k + 1) hW, hALL, halive]
        rfl
      · have hb2 : Nat.blt W (k + 1) = false := by
          cases hq : Nat.blt W (k + 1)
          · rfl
          · rw [Nat.blt_eq] at hq; exact absurd hq hW
        rw [hb2]
        exact halive
    · -- odd level
      have hb : Nat.beq (k % 2) 0 = false := by
        cases hq : Nat.beq (k % 2) 0
        · rfl
        · rw [Nat.beq_eq] at hq; omega
      by_cases hW : k + 1 ≤ W
      · -- free bit
        rw [stepR_free W n c ALL pats k R Rm hk hW] at hrun
        have hl := level y p k R Rm _ hR hRm (hfree k hk hW)
        refine ih (k + 1) _ R _ hrun heven' hl.1 hRm' ?_
        rw [hb]
        exact halive
      · -- forced bit
        rw [stepR_forced W n c ALL pats k R Rm hk (by omega)] at hrun
        -- the forced value is the true `y k`
        let Y' : Nat := if y k then 2 ^ p else 0
        have hY' : Y'.testBit p = y k := by
          show (if y k then 2 ^ p else 0).testBit p = y k
          cases y k
          · simp
          · simp
        have hl' := level y p k R Rm Y' hR hRm hY'
        rw [hwid (k + 1) (by omega), scanN_lin, Nat.testBit_xor, hY'] at hl'
        have hT : (scanN 0 R (0 :: Rm)).2.testBit p = y k := by
          have h2 := hl'.2
          revert h2
          cases y k <;> cases (scanN 0 R (0 :: Rm)).2.testBit p <;> simp
        have hl := level y p k R Rm (scanN 0 R (0 :: Rm)).2 hR hRm hT
        rw [scanN_lin R (0 :: Rm) (scanN 0 R (0 :: Rm)).2] at hl
        refine ih (k + 1) _ R _ hrun heven' hl.1 hRm' ?_
        rw [hb]
        exact halive

/-- **Soundness of the chunked check.** If every chunk passes, then every start supported at
depths `≤ W` has a white cell at depth `1` at some even time `< K`. -/
theorem q01_of_checks (W K n : Nat) (hn : n ≤ W / 2)
    (hc : ∀ c, c < 2 ^ (W / 2 - n) → check W K n c = true)
    (x : Nat → Bool) (hx : ∀ k, W < k → x k = false) :
    ∃ t, t < K ∧ t % 2 = 0 ∧ zrow x t 1 = false := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ t, t < K → t % 2 = 0 → zrow x t 1 = true := by
    intro t ht he
    cases hz : zrow x t 1
    · exact absurd ⟨t, ht, he, hz⟩ hne
    · rfl
  let y : Nat → Bool := fun t => zrow x t 1
  let p := pack (fun s => y (2 * s + 1)) n
  let c := pack (fun s => y (2 * (n + s) + 1)) (W / 2 - n)
  have hcheck := hc c (pack_lt _ _)
  have hp : p < 2 ^ n := pack_lt _ _
  have hALL : (2 ^ 2 ^ n - 1).testBit p = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  refine run_sound W n c (2 ^ 2 ^ n - 1) ((List.range n).map (pat n)) y p hALL ?_ ?_ K 0 [] []
    (2 ^ 2 ^ n - 1) hcheck (fun t _ ht he => hall t (by omega) he) rfl rfl hALL
  · intro t ht htW
    obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    rw [show (2 * s + 1) / 2 = s by omega]
    unfold yFree
    by_cases hs : s < n
    · rw [ite_eq_left hs, pats_getD n s hs, pat_spec n s p hs hp, testBit_pack]
      simp [hs]
    · rw [ite_eq_right hs, testBit_pack]
      have hsn : s - n < W / 2 - n := by omega
      have hyy : y (2 * (n + (s - n)) + 1) = y (2 * s + 1) := by
        rw [show n + (s - n) = s by omega]
      simp only [hsn, decide_true, Bool.true_and, hyy]
      cases y (2 * s + 1)
      · simp
      · simpa using hALL
  · intro d hd
    have e := history_eq_recon x d 0
    rw [zrow_zero_of_pos x (by omega), hx d hd] at e
    exact e.symm

/-! ## Combining chunks -/

/-- The chunks `lo, …, lo + cnt - 1` pass. -/
def ChunksOK (W K n lo cnt : Nat) : Prop := ∀ c, lo ≤ c → c < lo + cnt → check W K n c = true

theorem chunksOK_one {W K n c : Nat} (h : check W K n c = true) : ChunksOK W K n c 1 :=
  fun c' h1 h2 => by rw [show c' = c by omega]; exact h

theorem chunksOK_append {W K n lo a b : Nat} (h1 : ChunksOK W K n lo a)
    (h2 : ChunksOK W K n (lo + a) b) : ChunksOK W K n lo (a + b) := fun c hc1 hc2 => by
  rcases Nat.lt_or_ge c (lo + a) with h | h
  · exact h1 c hc1 h
  · exact h2 c h (by omega)

/-- `q01_of_checks` from a combined chunk certificate. -/
theorem q01_of_chunks (W K n : Nat) (hn : n ≤ W / 2) (h : ChunksOK W K n 0 (2 ^ (W / 2 - n)))
    (x : Nat → Bool) (hx : ∀ k, W < k → x k = false) :
    ∃ t, t < K ∧ t % 2 = 0 ∧ zrow x t 1 = false :=
  q01_of_checks W K n hn (fun c hc => h c (Nat.zero_le c) (by omega)) x hx

end Rule30ZeroBoundaryLanes
end Ruliology.CellularAutomata
