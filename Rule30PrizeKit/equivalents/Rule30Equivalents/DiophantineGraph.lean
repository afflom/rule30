module

public import Rule30Equivalents.IntegerRows
public import Mathlib.NumberTheory.Dioph
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Bitwise

/-!
# The graph of the center column is Diophantine

There is a polynomial equation in `n`, `y` and further unknowns that has a
solution exactly when `y = c(n)`. So Problem 1, a `Π⁰₂` sentence, is a `∀∃` sentence about
polynomial equations. The proof does not need the DPRM theorem. It uses Matiyasevich's
exponentiation (`Dioph.pow_dioph`) and Mathlib's `Dioph` closure properties.

* Bits through binomial coefficients: the bits of `x` are bits of `y` iff `C(y, x)` is odd (Lucas;
  `sub_iff_odd_choose`), and `C(n, k) = ⌊(u + 1)ⁿ / uᵏ⌋ mod u` for `u = 2ⁿ + 1` (`choose_eq`), so
  bit inclusion is Diophantine (`dioph_sub`).
* `z = x ∨ y` iff `x ⊆ z`, `y ⊆ z` and `z − x ⊆ y` (`or_iff`). `z = x ⊕ y` iff
  `z + x + y = 2 (x ∨ y)` (`xor_iff`), from the half adder `x + y = (x ⊕ y) + 2 (x ∧ y)`. So one rule
  30 step `Φ(x) = x ⊕ (2x ∨ 4x)` is Diophantine (`Φ_iff`).
* The whole history up to time `n` is one number `H` with blocks of width `w = 2n + 4`: block `t` is
  row `a(t)` of rule 30 as an integer (`IntegerRows`). The conditions `H mod 2^w = 1` and
  `⌊H / 2^w⌋ = Φ(H mod 2^{nw})` force these blocks by induction (`mod_eq_blocks`), because rows stay
  below `2^{2t+1}` and so `Φ` acts block by block (`Φ_blocks`). Then `c(n)` is bit `nw + n` of `H`
  (`center_iff`).
* `center_diophFn`.

Sources: Y. Matiyasevich, *Enumerable sets are Diophantine*, Soviet Math. Dokl. 11 (1970) 354–358;
M. Davis, *Hilbert's tenth problem is unsolvable*, Amer. Math. Monthly 80 (1973) 233–269;
É. Lucas (1878); E. Kummer (1852).
-/

@[expose] public section

namespace Rule30Equivalents.DiophantineGraph

open Finset Ruliology.CellularAutomata

/-! ### Bitwise arithmetic -/

/-- **The half adder**: `x + y = (x ⊕ y) + 2 (x ∧ y)`. -/
theorem add_eq_xor_add_two_mul_and : ∀ x y : ℕ, x + y = (x ^^^ y) + 2 * (x &&& y) := by
  intro x
  induction x using Nat.binaryRec with
  | zero => intro y; simp
  | bit a m ih =>
    intro y
    rw [← Nat.bit_bodd_div2 y, Nat.xor_bit, Nat.land_bit, Nat.bit_val, Nat.bit_val, Nat.bit_val,
      Nat.bit_val]
    have := ih y.div2
    cases a <;> cases y.bodd <;> simp <;> omega

/-- Bit inclusion: every bit of `x` is a bit of `y`. -/
def Sub (x y : ℕ) : Prop := ∀ i, x.testBit i → y.testBit i

theorem sub_xor_of_sub {x z : ℕ} (h : Sub x z) : z - x = z ^^^ x := by
  have hand : x &&& (z ^^^ x) = 0 := Nat.eq_of_testBit_eq fun i => by
    have := h i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases hx : x.testBit i <;> cases hz : z.testBit i <;> simp_all
  have hxor : x ^^^ (z ^^^ x) = z := by rw [Nat.xor_comm z x, ← Nat.xor_assoc, Nat.xor_self,
    Nat.zero_xor]
  have := add_eq_xor_add_two_mul_and x (z ^^^ x)
  rw [hand, hxor, mul_zero, add_zero] at this
  omega

theorem or_iff (x y z : ℕ) : z = x ||| y ↔ Sub x z ∧ Sub y z ∧ Sub (z - x) y := by
  constructor
  · rintro rfl
    refine ⟨fun i h => by simp [h], fun i h => by simp [h], ?_⟩
    rw [sub_xor_of_sub fun i h => by simp [h]]
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_or]
    cases x.testBit i <;> cases y.testBit i <;> simp
  · rintro ⟨hx, hy, hz⟩
    rw [sub_xor_of_sub hx] at hz
    refine Nat.eq_of_testBit_eq fun i => ?_
    have h1 := hx i
    have h2 := hy i
    have h3 := hz i
    simp only [Nat.testBit_xor, Nat.testBit_or] at h3 ⊢
    cases hxi : x.testBit i <;> cases hyi : y.testBit i <;> cases hzi : z.testBit i <;> simp_all

theorem xor_iff (x y z : ℕ) : z = x ^^^ y ↔ z + x + y = 2 * (x ||| y) := by
  have hor : x ||| y = (x ^^^ y) + (x &&& y) := by
    have hd : (x ^^^ y) &&& (x &&& y) = 0 := Nat.eq_of_testBit_eq fun i => by
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases x.testBit i <;> cases y.testBit i <;> rfl
    have := add_eq_xor_add_two_mul_and (x ^^^ y) (x &&& y)
    rw [hd, mul_zero, add_zero] at this
    rw [this]
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> rfl
  have hadd := add_eq_xor_add_two_mul_and x y
  constructor
  · rintro rfl; omega
  · intro h; omega

/-! ### One rule 30 step -/

/-- One step of rule 30 on integer rows: `Φ(x) = x ⊕ (2x ∨ 4x)`. -/
def Φ (x : ℕ) : ℕ := x ^^^ ((2 * x) ||| (4 * x))

theorem Φ_iff (x y : ℕ) : y = Φ x ↔ ∃ s o, Sub (2 * x) s ∧ Sub (4 * x) s ∧ Sub (s - 2 * x) (4 * x) ∧
    Sub x o ∧ Sub s o ∧ Sub (o - x) s ∧ y + x + s = 2 * o := by
  constructor
  · rintro rfl
    refine ⟨_, _, ((or_iff _ _ _).1 rfl).1, ((or_iff _ _ _).1 rfl).2.1, ((or_iff _ _ _).1 rfl).2.2,
      ((or_iff x ((2 * x) ||| (4 * x)) _).1 rfl).1, ((or_iff x ((2 * x) ||| (4 * x)) _).1 rfl).2.1,
      ((or_iff x ((2 * x) ||| (4 * x)) _).1 rfl).2.2, (xor_iff _ _ _).1 rfl⟩
  · rintro ⟨s, o, h1, h2, h3, h4, h5, h6, h7⟩
    obtain rfl := (or_iff _ _ s).2 ⟨h1, h2, h3⟩
    obtain rfl := (or_iff _ _ o).2 ⟨h4, h5, h6⟩
    exact (xor_iff _ _ _).2 h7

theorem testBit_Φ (x k : ℕ) : (Φ x).testBit k = (x.testBit k ^^
    ((decide (1 ≤ k) && x.testBit (k - 1)) || (decide (2 ≤ k) && x.testBit (k - 2)))) := by
  simp only [Φ, Nat.testBit_xor, Nat.testBit_or, IntegerRows.testBit_two_mul,
    IntegerRows.testBit_four_mul]

theorem Φ_lt {x k : ℕ} (h : x < 2 ^ k) : Φ x < 2 ^ (k + 2) := by
  have h1 : x < 2 ^ (k + 2) := h.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 2 * x < 2 ^ (k + 2) := by rw [pow_add]; omega
  have h4 : 4 * x < 2 ^ (k + 2) := by rw [pow_add]; omega
  exact Nat.xor_lt_two_pow h1 (Nat.or_lt_two_pow h2 h4)

theorem Φ_zero : Φ 0 = 0 := rfl

/-- `Φ` is causal: the low `m` bits of `Φ x` depend only on the low `m` bits of `x`. -/
theorem Φ_mod (x m : ℕ) : Φ x % 2 ^ m = Φ (x % 2 ^ m) % 2 ^ m := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_mod_two_pow, testBit_Φ]
  by_cases hi : i < m
  · simp [hi, show i - 1 < m by omega, show i - 2 < m by omega]
  · simp [hi]

theorem a_lt (t : ℕ) : IntegerRows.a t < 2 ^ (2 * t + 1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have := Φ_lt ih
    rwa [show 2 * t + 1 + 2 = 2 * (t + 1) + 1 by ring] at this

theorem a_succ (t : ℕ) : IntegerRows.a (t + 1) = Φ (IntegerRows.a t) := rfl

/-! ### Blocks -/

/-- `blocks w f k = ∑_{s<k} f s · 2^{s w}`: `k` blocks of width `w`. -/
def blocks (w : ℕ) : (ℕ → ℕ) → ℕ → ℕ
  | _, 0 => 0
  | f, k + 1 => f 0 + 2 ^ w * blocks w (fun s => f (s + 1)) k

theorem blocks_lt {w : ℕ} : ∀ (k : ℕ) (f : ℕ → ℕ), (∀ s, s < k → f s < 2 ^ w) →
    blocks w f k < 2 ^ (k * w)
  | 0, _, _ => by simp [blocks]
  | k + 1, f, hf => by
    have ih := blocks_lt k (fun s => f (s + 1)) fun s hs => hf _ (by omega)
    have h0 := hf 0 (by omega)
    rw [blocks, show (k + 1) * w = w + k * w by ring, pow_add]
    calc f 0 + 2 ^ w * blocks w (fun s => f (s + 1)) k
        < 2 ^ w + 2 ^ w * blocks w (fun s => f (s + 1)) k := by omega
      _ = 2 ^ w * (blocks w (fun s => f (s + 1)) k + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (k * w) := Nat.mul_le_mul_left _ ih

theorem testBit_blocks {w : ℕ} : ∀ (k : ℕ) (f : ℕ → ℕ), (∀ s, s < k → f s < 2 ^ w) →
    ∀ t j, j < w → (blocks w f k).testBit (t * w + j) = (decide (t < k) && (f t).testBit j)
  | 0, _, _, t, j, _ => by simp [blocks]
  | k + 1, f, hf, t, j, hj => by
    have h0 := hf 0 (by omega)
    rw [blocks, add_comm, Nat.testBit_two_pow_mul_add _ h0]
    cases t with
    | zero => simp [hj]
    | succ t =>
      rw [ite_eq_right (by nlinarith), show (t + 1) * w + j - w = t * w + j by
        rw [Nat.succ_mul]; omega, testBit_blocks k _ (fun s hs => hf _ (by omega)) t j hj]
      simp

theorem blocks_mod {w : ℕ} (hw : 0 < w) {m : ℕ} {f : ℕ → ℕ} (hf : ∀ s, s < m → f s < 2 ^ w)
    {k : ℕ} (hk : k ≤ m) : blocks w f m % 2 ^ (k * w) = blocks w f k := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_mod_two_pow, ← Nat.div_add_mod i w, mul_comm w,
    testBit_blocks m f hf _ _ (Nat.mod_lt _ hw),
    testBit_blocks k f (fun s hs => hf s (by omega)) _ _ (Nat.mod_lt _ hw)]
  by_cases hik : i / w < k
  · have : i / w * w + i % w < k * w := by
      have := Nat.mod_lt i hw
      nlinarith
    simp [this, hik, show i / w < m by omega]
  · have : ¬ i / w * w + i % w < k * w := by
      have := Nat.div_add_mod i w
      intro h
      exact hik ((Nat.div_lt_iff_lt_mul hw).2 (by rw [mul_comm w] at this; omega))
    simp [this, hik]

/-- `Φ` acts block by block when the top two bits of each block are clear. -/
theorem Φ_add {w x y : ℕ} (hw : 2 ≤ w) (hx : x < 2 ^ (w - 2)) :
    Φ (x + 2 ^ w * y) = Φ x + 2 ^ w * Φ y := by
  have hx' : x < 2 ^ w := hx.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hΦ : Φ x < 2 ^ w := by
    have := Φ_lt hx
    rwa [show w - 2 + 2 = w by omega] at this
  have hb : ∀ i, w - 2 ≤ i → x.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (hx.trans_le (Nat.pow_le_pow_right (by norm_num) hi))
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [add_comm (Φ x), Nat.testBit_two_pow_mul_add _ hΦ, testBit_Φ, add_comm x,
    Nat.testBit_two_pow_mul_add _ hx']
  by_cases hi : i < w
  · rw [ite_eq_left hi, testBit_Φ, Nat.testBit_two_pow_mul_add _ hx',
      Nat.testBit_two_pow_mul_add _ hx', ite_eq_left hi,
      ite_eq_left (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right hi, ite_eq_right hi, testBit_Φ, Nat.testBit_two_pow_mul_add _ hx',
      Nat.testBit_two_pow_mul_add _ hx']
    by_cases h1 : i - 1 < w
    · have hi' : i = w := by omega
      subst hi'
      rw [ite_eq_left h1, ite_eq_left (by omega), hb _ (by omega), hb _ (by omega)]
      simp
    · by_cases h2 : i - 2 < w
      · have hi' : i = w + 1 := by omega
        subst hi'
        rw [ite_eq_right h1, ite_eq_left h2, hb _ (by omega)]
        simp [show w + 1 - w = 1 by omega]
      · rw [ite_eq_right h1, ite_eq_right h2]
        simp only [show i - 1 - w = i - w - 1 by omega, show i - 2 - w = i - w - 2 by omega]
        simp [show 1 ≤ i by omega, show 2 ≤ i by omega, show 1 ≤ i - w by omega,
          show 2 ≤ i - w by omega]

theorem Φ_blocks {w : ℕ} (hw : 2 ≤ w) (k : ℕ) : ∀ (f : ℕ → ℕ), (∀ s, s < k → f s < 2 ^ (w - 2)) →
    Φ (blocks w f k) = blocks w (fun s => Φ (f s)) k := by
  induction k with
  | zero => intro _ _; rw [blocks, blocks, Φ_zero]
  | succ k ih =>
    intro f hf
    rw [blocks, blocks, Φ_add hw (hf 0 (by omega)), ih _ fun s hs => hf _ (by omega)]

/-! ### The history of rule 30 as one number -/

theorem a_lt_block {n w : ℕ} (hw : w = 2 * n + 4) {s : ℕ} (hs : s ≤ n) :
    IntegerRows.a s < 2 ^ (w - 2) :=
  (a_lt s).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Under the two block conditions, the low `k + 1` blocks of `H` are the first rows of rule 30. -/
theorem mod_eq_blocks {n w H : ℕ} (hw : w = 2 * n + 4) (h1 : H % 2 ^ w = 1)
    (h2 : H / 2 ^ w = Φ (H % 2 ^ (n * w))) :
    ∀ k, k ≤ n + 1 → H % 2 ^ (k * w) = blocks w IntegerRows.a k := by
  intro k
  induction k with
  | zero => intro _; simp [blocks, Nat.mod_one]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hbl : ∀ s, s < k → IntegerRows.a s < 2 ^ (w - 2) := fun s hs => a_lt_block hw (by omega)
    have hbl' : ∀ s, s < k → IntegerRows.a (s + 1) < 2 ^ w := fun s hs =>
      (a_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show (k + 1) * w = w + k * w by ring, pow_add, Nat.mod_mul, h1, h2, Φ_mod,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.mul_le_mul_right w (by omega))), ih,
      Φ_blocks (by omega) k _ hbl,
      Nat.mod_eq_of_lt (blocks_lt k (fun s => Φ (IntegerRows.a s)) hbl'), blocks]
    rfl

/-- **The center column through the history number**. -/
theorem center_iff (n y : ℕ) : (if Rule30Prize.center n then 1 else 0) = y ↔
    ∃ H, H % 2 ^ (2 * n + 4) = 1 ∧ H / 2 ^ (2 * n + 4) = Φ (H % 2 ^ (n * (2 * n + 4))) ∧
      y = H / 2 ^ (n * (2 * n + 4) + n) % 2 := by
  set w := 2 * n + 4 with hw
  have hbit : ∀ H, H % 2 ^ w = 1 → H / 2 ^ w = Φ (H % 2 ^ (n * w)) →
      H / 2 ^ (n * w + n) % 2 = if Rule30Prize.center n then 1 else 0 := fun H h1 h2 => by
    have hm := mod_eq_blocks hw h1 h2 (n + 1) le_rfl
    have hlt : ∀ s, s < n + 1 → IntegerRows.a s < 2 ^ w := fun s hs =>
      (a_lt s).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hb : H.testBit (n * w + n) = Rule30Prize.center n := by
      have := congrArg (fun z => z.testBit (n * w + n)) hm
      simp only [Nat.testBit_mod_two_pow] at this
      rw [testBit_blocks (n + 1) _ hlt n n (by omega)] at this
      simp only [show n * w + n < (n + 1) * w by rw [Nat.succ_mul]; omega,
        show n < n + 1 by omega, decide_true, Bool.true_and] at this
      rw [this, ← IntegerRows.center_eq_testBit]
    rw [← hb, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (H / 2 ^ (n * w + n)) with h | h <;> simp [h]
  constructor
  · rintro rfl
    have hlt : ∀ s, s < n + 1 → IntegerRows.a s < 2 ^ w := fun s hs =>
      (a_lt s).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1 : blocks w IntegerRows.a (n + 1) % 2 ^ w = 1 := by
      rw [blocks, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlt 0 (by omega))]
      rfl
    have h2 : blocks w IntegerRows.a (n + 1) / 2 ^ w =
        Φ (blocks w IntegerRows.a (n + 1) % 2 ^ (n * w)) := by
      rw [blocks_mod (by omega) hlt (Nat.le_succ n), Φ_blocks (by omega) n _
        (fun s hs => a_lt_block hw (by omega)), blocks, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (hlt 0 (by omega)), zero_add]
      rfl
    exact ⟨_, h1, h2, (hbit _ h1 h2).symm⟩
  · rintro ⟨H, h1, h2, rfl⟩
    exact (hbit H h1 h2).symm

/-! ### Bits through binomial coefficients -/

theorem sub_iff_mod_div (x y : ℕ) : Sub x y ↔ (x % 2 = 1 → y % 2 = 1) ∧ Sub (x / 2) (y / 2) := by
  constructor
  · intro h
    refine ⟨fun hx => ?_, fun j hj => ?_⟩
    · have := h 0 (by simp [Nat.testBit_zero, hx])
      simpa [Nat.testBit_zero] using this
    · have := h (j + 1) (by rwa [Nat.testBit_add_one])
      rwa [Nat.testBit_add_one] at this
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero =>
      simp only [Nat.testBit_zero, decide_eq_true_eq] at hi ⊢
      exact h0 hi
    | succ j =>
      rw [Nat.testBit_add_one] at hi ⊢
      exact h1 j hi

/-- **Lucas mod 2**: the bits of `x` are bits of `y` iff `C(y, x)` is odd. -/
theorem sub_iff_odd_choose : ∀ y x : ℕ, Sub x y ↔ Odd (y.choose x) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · constructor
      · intro h
        have hx : x = 0 := Nat.eq_of_testBit_eq fun i => by
          have := h i
          simp only [Nat.zero_testBit] at this ⊢
          cases hxi : x.testBit i <;> simp_all
        subst hx
        simp
      · intro h
        rcases Nat.eq_zero_or_pos x with rfl | hx
        · intro i hi
          simp at hi
        · rw [Nat.choose_eq_zero_of_lt hx] at h
          exact absurd h (by decide)
    · have hl : y.choose x % 2 = ((y % 2).choose (x % 2) * (y / 2).choose (x / 2)) % 2 :=
        @Choose.choose_modEq_choose_mod_mul_choose_div_nat y x 2 ⟨Nat.prime_two⟩
      rw [Nat.odd_iff, hl, ← Nat.odd_iff, Nat.odd_mul, ← ih (y / 2) (Nat.div_lt_self hy (by norm_num)),
        sub_iff_mod_div]
      refine and_congr_left fun _ => ?_
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
        rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [hx, hy]

/-- Digits in base `u`. -/
theorem digit_extract {u : ℕ} (hu : 0 < u) : ∀ (N : ℕ) (d : ℕ → ℕ), (∀ i, d i < u) → ∀ k,
    (∑ i ∈ range N, d i * u ^ i) / u ^ k % u = if k < N then d k else 0 := by
  intro N
  induction N with
  | zero => intro d _ k; simp
  | succ N ih =>
    intro d hd k
    rw [Finset.sum_range_succ']
    have hS : ∑ i ∈ range N, d (i + 1) * u ^ (i + 1) + d 0 * u ^ 0 =
        d 0 + u * ∑ i ∈ range N, d (i + 1) * u ^ i := by
      rw [pow_zero, mul_one, add_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hS]
    cases k with
    | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
    | succ k =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hu,
        Nat.div_eq_of_lt (hd 0), zero_add, ih (fun i => d (i + 1)) (fun i => hd _) k]
      simp

/-- `C(n, k)` is digit `k` of `(u + 1)ⁿ` in base `u = 2ⁿ + 1`. -/
theorem choose_eq (n k : ℕ) : n.choose k = (2 ^ n + 2) ^ n / (2 ^ n + 1) ^ k % (2 ^ n + 1) := by
  have hpow : (2 ^ n + 2) ^ n = ∑ i ∈ range (n + 1), n.choose i * (2 ^ n + 1) ^ i := by
    rw [show 2 ^ n + 2 = (2 ^ n + 1) + 1 by ring, add_pow]
    exact Finset.sum_congr rfl fun i _ => by simp only [Nat.cast_id]; ring
  rw [hpow, digit_extract (by positivity) (n + 1) (fun i => n.choose i)
    (fun i => (Nat.choose_le_two_pow n i).trans_lt (by omega)) k]
  split_ifs with hk
  · rfl
  · exact Nat.choose_eq_zero_of_lt (by omega)

theorem choose_diophFn {α : Type} {f g : (α → ℕ) → ℕ} (df : Dioph.DiophFn f)
    (dg : Dioph.DiophFn g) : Dioph.DiophFn fun v => (f v).choose (g v) := by
  have h2 : Dioph.DiophFn fun v : α → ℕ => 2 ^ f v := Dioph.pow_dioph (Dioph.const_dioph 2) df
  have hu : Dioph.DiophFn fun v : α → ℕ => 2 ^ f v + 1 := Dioph.add_dioph h2 (Dioph.const_dioph 1)
  have hu2 : Dioph.DiophFn fun v : α → ℕ => 2 ^ f v + 2 := Dioph.add_dioph h2 (Dioph.const_dioph 2)
  have h : Dioph.DiophFn fun v : α → ℕ => (2 ^ f v + 2) ^ f v / (2 ^ f v + 1) ^ g v % (2 ^ f v + 1) :=
    Dioph.mod_dioph (Dioph.div_dioph (Dioph.pow_dioph hu2 df) (Dioph.pow_dioph hu dg)) hu
  convert h using 1
  funext v
  exact choose_eq (f v) (g v)

/-- Bit inclusion is Diophantine. -/
theorem sub_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : Dioph.DiophFn f) (dg : Dioph.DiophFn g) :
    Dioph {v | Sub (f v) (g v)} := by
  have h : Dioph {v : α → ℕ | (g v).choose (f v) % 2 = 1} :=
    Dioph.eq_dioph (Dioph.mod_dioph (choose_diophFn dg df) (Dioph.const_dioph 2)) (Dioph.const_dioph 1)
  refine Dioph.ext h fun v => ?_
  simp only [Set.mem_ofPred_eq]
  rw [sub_iff_odd_choose, Nat.odd_iff]

/-! ### The graph of the center column -/

/-- **The graph of the center column is Diophantine**: `y = c(n)` iff a fixed
polynomial equation in `n`, `y` and further unknowns has a solution. -/
theorem center_diophFn :
    Dioph.DiophFn fun v : Fin 1 → ℕ => if Rule30Prize.center (v 0) then 1 else 0 := by
  have dn : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ => u (.inl (some 0)) :=
    Dioph.proj_dioph _
  have dy : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ => u (.inl none) := Dioph.proj_dioph _
  have dH : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ => u (.inr 0) := Dioph.proj_dioph _
  have ds : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ => u (.inr 1) := Dioph.proj_dioph _
  have dO : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ => u (.inr 2) := Dioph.proj_dioph _
  have dw : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ => 2 * u (.inl (some 0)) + 4 :=
    Dioph.add_dioph (Dioph.mul_dioph (Dioph.const_dioph 2) dn) (Dioph.const_dioph 4)
  have dpw : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ =>
      2 ^ (2 * u (.inl (some 0)) + 4) := Dioph.pow_dioph (Dioph.const_dioph 2) dw
  have dL : Dioph.DiophFn fun u : Option (Fin 1) ⊕ Fin 3 → ℕ =>
      u (.inr 0) % 2 ^ (u (.inl (some 0)) * (2 * u (.inl (some 0)) + 4)) :=
    Dioph.mod_dioph dH (Dioph.pow_dioph (Dioph.const_dioph 2) (Dioph.mul_dioph dn dw))
  have dQ := Dioph.div_dioph dH dpw
  have d2L := Dioph.mul_dioph (Dioph.const_dioph 2) dL
  have d4L := Dioph.mul_dioph (Dioph.const_dioph 4) dL
  have c1 := Dioph.eq_dioph (Dioph.mod_dioph dH dpw) (Dioph.const_dioph 1)
  have c2 := sub_dioph d2L ds
  have c3 := sub_dioph d4L ds
  have c4 := sub_dioph (Dioph.sub_dioph ds d2L) d4L
  have c5 := sub_dioph dL dO
  have c6 := sub_dioph ds dO
  have c7 := sub_dioph (Dioph.sub_dioph dO dL) ds
  have c8 := Dioph.eq_dioph (Dioph.add_dioph (Dioph.add_dioph dQ dL) ds)
    (Dioph.mul_dioph (Dioph.const_dioph 2) dO)
  have c9 := Dioph.eq_dioph dy (Dioph.mod_dioph (Dioph.div_dioph dH (Dioph.pow_dioph
    (Dioph.const_dioph 2) (Dioph.add_dioph (Dioph.mul_dioph dn dw) dn))) (Dioph.const_dioph 2))
  have hT := Dioph.ex_dioph (c1.inter (c2.inter (c3.inter (c4.inter (c5.inter (c6.inter
    (c7.inter (c8.inter c9))))))))
  refine Dioph.ext hT fun v => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Function.const_apply, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply]
  refine Iff.trans ?_ (center_iff _ _).symm
  constructor
  · rintro ⟨x, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨x 0, h1, (Φ_iff _ _).2 ⟨x 1, x 2, h2, h3, h4, h5, h6, h7, h8⟩, h9⟩
  · rintro ⟨H, h1, h2, h9⟩
    obtain ⟨s, o, h2, h3, h4, h5, h6, h7, h8⟩ := (Φ_iff _ _).1 h2
    exact ⟨![H, s, o], h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **Problem 1 as a `∀∃` sentence about one polynomial equation**: there is a polynomial `p` with
integer coefficients such that `p(n, y, x) = 0` has a solution `x` exactly when `y = c(n)`, and then
Problem 1 says that for all `T` and `P ≥ 1` some `t ≥ T` has `c(t + P) ≠ c(t)`, witnessed by
solutions. -/
theorem problem1_iff_forall_exists_poly : ∃ (β : Type) (p : Poly (Option (Fin 1) ⊕ β)),
    (∀ n y, (if Rule30Prize.center n then 1 else 0) = y ↔
      ∃ x, p (Sum.elim (Option.elim' y fun _ => n) x) = 0) ∧
    (Rule30Prize.Problem1 ↔ ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ ∃ x x' : β → ℕ,
      (p (Sum.elim (Option.elim' 1 fun _ => t + P) x) = 0 ∧
        p (Sum.elim (Option.elim' 0 fun _ => t) x') = 0) ∨
      (p (Sum.elim (Option.elim' 0 fun _ => t + P) x) = 0 ∧
        p (Sum.elim (Option.elim' 1 fun _ => t) x') = 0)) := by
  obtain ⟨β, p, hp⟩ := center_diophFn
  have hG : ∀ n y, (if Rule30Prize.center n then 1 else 0) = y ↔
      ∃ x, p (Sum.elim (Option.elim' y fun _ => n) x) = 0 := fun n y => by
    rw [← hp]
    rfl
  refine ⟨β, p, hG, ?_⟩
  have h1 : ∀ n, Rule30Prize.center n = true ↔ ∃ x, p (Sum.elim (Option.elim' 1 fun _ => n) x) = 0 :=
    fun n => by rw [← hG]; cases Rule30Prize.center n <;> simp
  have h0 : ∀ n, Rule30Prize.center n = false ↔ ∃ x, p (Sum.elim (Option.elim' 0 fun _ => n) x) = 0 :=
    fun n => by rw [← hG]; cases Rule30Prize.center n <;> simp
  unfold Rule30Prize.Problem1 Rule30Jen.EventuallyPeriodic
  push Not
  refine forall_congr' fun T => forall_congr' fun P => imp_congr_right fun _ =>
    exists_congr fun t => and_congr_right fun _ => ?_
  constructor
  · intro h
    rcases hc : Rule30Prize.center (t + P) <;> rcases hc' : Rule30Prize.center t
    · exact absurd (hc.trans hc'.symm) h
    · obtain ⟨x, hx⟩ := (h0 _).1 hc
      obtain ⟨x', hx'⟩ := (h1 _).1 hc'
      exact ⟨x, x', Or.inr ⟨hx, hx'⟩⟩
    · obtain ⟨x, hx⟩ := (h1 _).1 hc
      obtain ⟨x', hx'⟩ := (h0 _).1 hc'
      exact ⟨x, x', Or.inl ⟨hx, hx'⟩⟩
    · exact absurd (hc.trans hc'.symm) h
  · rintro ⟨x, x', (⟨hx, hx'⟩ | ⟨hx, hx'⟩)⟩
    · rw [(h1 _).2 ⟨x, hx⟩, (h0 _).2 ⟨x', hx'⟩]; simp
    · rw [(h0 _).2 ⟨x, hx⟩, (h1 _).2 ⟨x', hx'⟩]; simp

end Rule30Equivalents.DiophantineGraph
