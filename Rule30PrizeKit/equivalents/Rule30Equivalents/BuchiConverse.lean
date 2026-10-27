module

public import Rule30Equivalents.BuchiArithmetic
public import Mathlib.Basic.Finite.Sum

/-!
# `k`-automatic sets are definable in Büchi arithmetic

`BuchiArithmetic` proves that a set
definable in `(ℕ, 0, 1, +, V_k)` is `k`-automatic. This file proves the converse, completing the
Büchi–Bruyère theorem for sets of naturals (`definable_iff_isAutomatic`): non-definability in
`(ℕ, +, V_k)` is exactly "not `k`-automatic".

The formula reads the base-`k` digits of `n`, least significant first, through the automaton whose
states are the `k`-kernel of `f` (`run`): reading the digit `d` moves from `g` to `m ↦ g(km + d)`,
and after `L` digits with `n < kᴸ` the state `g` has `g(0) = f(n)`.

* `digit_iff`, `pow_dvd_iff`, `isPow_iff`: the digit of `x` at the position `y = kᵉ` is `j` iff
  `x = a + j y + b` with `a < y` and `k y ∣ b`, and `k y ∣ b` iff `b = 0` or `k y ≤ V_k b`. So
  "`y` is a power of `k`" and "the digit of `x` at `y` is `j`" are definable (`definable_pow`,
  `definable_digit`), using Mathlib's definable functions for `+` and `V_k`.
* The run is coded by one number `X_g` per state `g`, with digit `1` at the positions `kⁱ` where
  the run is in `g`: `X_{f}` has digit `1` at `1`; if `X_g` has digit `1` at `y < Y` and `n` has
  digit `d` there, then `X_{δ(g, d)}` has digit `1` at `k y`; and at the last position `Y > n`
  no state with output `0` is marked. Such numbers exist iff `f(n) = 1` (`mem_body_iff`).
-/

@[expose] public section

namespace Rule30Equivalents.BuchiConverse

open FirstOrder Language Structure Set BuchiArithmetic Automatic

variable {k : ℕ}

/-! ### Powers and digits -/

theorem vk_one (hk : 2 ≤ k) : vk k 1 = 1 :=
  vk_of_not_dvd one_pos fun h => by have := Nat.le_of_dvd one_pos h; omega

theorem vk_pow (hk : 2 ≤ k) (e : ℕ) : vk k (k ^ e) = k ^ e := by
  have := vk_pow_mul hk e 1
  rwa [mul_one, vk_one hk, mul_one] at this

/-- For `x > 0`, `V_k x` is a power of `k` dividing `x`. -/
theorem vk_spec (hk : 2 ≤ k) : ∀ x, 0 < x → ∃ e, vk k x = k ^ e ∧ k ^ e ∣ x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    by_cases hdvd : k ∣ x
    · obtain ⟨y, rfl⟩ := hdvd
      have hy : 0 < y := Nat.pos_of_mul_pos_left hx
      obtain ⟨e, he, hdv⟩ := ih y (by nlinarith) hy
      refine ⟨e + 1, by rw [vk_mul hk, he, pow_succ, mul_comm], ?_⟩
      rw [pow_succ, mul_comm]
      exact Nat.mul_dvd_mul_left k hdv
    · exact ⟨0, by rw [vk_of_not_dvd hx hdvd, pow_zero], by simp⟩

theorem isPow_iff (hk : 2 ≤ k) {y : ℕ} : (∃ e, y = k ^ e) ↔ 1 ≤ y ∧ vk k y = y := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨Nat.one_le_pow _ _ (by omega), vk_pow hk e⟩
  · rintro ⟨hy, hv⟩
    obtain ⟨e, he, -⟩ := vk_spec hk y hy
    exact ⟨e, by rw [← hv, he]⟩

/-- `kᵉ ∣ b` iff `b = 0` or `kᵉ ≤ V_k b`. -/
theorem pow_dvd_iff (hk : 2 ≤ k) (e b : ℕ) : k ^ e ∣ b ↔ b = 0 ∨ k ^ e ≤ vk k b := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Or.inl rfl
    · right
      obtain ⟨m, rfl⟩ := h
      have hm : 0 < m := Nat.pos_of_mul_pos_left hb
      rw [vk_pow_mul hk]
      obtain ⟨e', he', -⟩ := vk_spec hk m hm
      rw [he']
      exact Nat.le_mul_of_pos_right _ (by positivity)
  · rintro (rfl | h)
    · exact dvd_zero _
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [vk_zero] at h
        have := Nat.one_le_pow e k (by omega)
        omega
      obtain ⟨e', he', hdv⟩ := vk_spec hk b hb
      rw [he'] at h
      exact (pow_dvd_pow k ((Nat.pow_le_pow_iff_right (by omega)).1 h)).trans hdv

/-- The digit of `x` at the position `kᵉ` is `j < k` iff `x = a + j kᵉ + b` with `a < kᵉ` and
`k^(e+1) ∣ b`. -/
theorem digit_iff (hk : 2 ≤ k) (e x j : ℕ) (hj : j < k) :
    x / k ^ e % k = j ↔ ∃ a b, x = a + j * k ^ e + b ∧ a < k ^ e ∧ k ^ (e + 1) ∣ b := by
  have hpos : 0 < k ^ e := by positivity
  constructor
  · intro h
    refine ⟨x % k ^ e, k ^ (e + 1) * (x / k ^ e / k), ?_, Nat.mod_lt _ hpos, dvd_mul_right _ _⟩
    have h1 := Nat.mod_add_div x (k ^ e)
    have h2 := Nat.mod_add_div (x / k ^ e) k
    rw [h] at h2
    calc x = x % k ^ e + k ^ e * (x / k ^ e) := h1.symm
      _ = x % k ^ e + k ^ e * (j + k * (x / k ^ e / k)) := by rw [h2]
      _ = _ := by rw [pow_succ]; ring
  · rintro ⟨a, b, rfl, ha, ⟨m, rfl⟩⟩
    have : (a + j * k ^ e + k ^ (e + 1) * m) / k ^ e = j + k * m := by
      rw [show a + j * k ^ e + k ^ (e + 1) * m = a + k ^ e * (j + k * m) by rw [pow_succ]; ring,
        Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, zero_add]
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem sum_lt (hk : 2 ≤ k) (b : ℕ → ℕ) (hb : ∀ j, b j < k) :
    ∀ m, ∑ j ∈ Finset.range m, b j * k ^ j < k ^ m
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := sum_lt hk b hb m
    have : b m * k ^ m ≤ (k - 1) * k ^ m := Nat.mul_le_mul_right _ (by have := hb m; omega)
    have : (k - 1) * k ^ m + k ^ m = k ^ m * k := by
      rw [mul_comm (k ^ m) k]; rw [← Nat.succ_mul]; congr 1; omega
    omega

/-- The digits of `∑_{j < m} b_j kʲ`, with all `b_j < k`, are the `b_j`. -/
theorem digit_sum (hk : 2 ≤ k) (b : ℕ → ℕ) (hb : ∀ j, b j < k) :
    ∀ m i, (∑ j ∈ Finset.range m, b j * k ^ j) / k ^ i % k = if i < m then b i else 0
  | 0, i => by simp
  | m + 1, i => by
    have hpos : ∀ e, 0 < k ^ e := fun e => by positivity
    have ih := digit_sum hk b hb m i
    have hlt := sum_lt hk b hb m
    rw [Finset.sum_range_succ]
    rcases lt_trichotomy i m with him | rfl | him
    · rw [ite_eq_left (by omega)]
      rw [ite_eq_left him] at ih
      obtain ⟨d, rfl⟩ : ∃ d, m = i + 1 + d := ⟨m - (i + 1), by omega⟩
      rw [show b (i + 1 + d) * k ^ (i + 1 + d) = k ^ i * (k * (b (i + 1 + d) * k ^ d)) by
          rw [pow_add, pow_add, pow_one]; ring,
        Nat.add_mul_div_left _ _ (hpos i), Nat.add_mul_mod_self_left, ih]
    · rw [ite_eq_left (by omega), mul_comm, Nat.add_mul_div_left _ _ (hpos i), Nat.div_eq_of_lt hlt,
        zero_add, Nat.mod_eq_of_lt (hb i)]
    · rw [ite_eq_right (by omega), Nat.div_eq_of_lt, Nat.zero_mod]
      calc ∑ j ∈ Finset.range m, b j * k ^ j + b m * k ^ m
          = ∑ j ∈ Finset.range (m + 1), b j * k ^ j := (Finset.sum_range_succ _ _).symm
        _ < k ^ (m + 1) := sum_lt hk b hb (m + 1)
        _ ≤ k ^ i := Nat.pow_le_pow_right (by omega) (by omega)

/-! ### The kernel automaton -/

section Run

variable (f : ℕ → Bool) (hk : 2 ≤ k)

/-- The states: the `k`-kernel of `f`. -/
abbrev State (f : ℕ → Bool) (k : ℕ) := ↥(kernel k f)

/-- The start state `f`. -/
def start : State f k := ⟨f, self_mem_kernel k f⟩

/-- Reading the digit `d < k`. -/
def step (g : State f k) (d : Fin k) : State f k :=
  ⟨fun m => g.1 (k * m + d), mem_kernel_step g.2 d.2⟩

/-- The state after the `i` lowest digits of `n`. -/
def run (n i : ℕ) : State f k :=
  ⟨fun m => f (k ^ i * m + n % k ^ i), ⟨i, n % k ^ i, Nat.mod_lt _ (pow_pos (by omega) i), rfl⟩⟩

theorem run_zero (n : ℕ) : run f hk n 0 = start f := by
  apply Subtype.ext
  funext m
  simp [run, start, Nat.mod_one]

/-- The digit of `n` at `kⁱ`. -/
def digitAt (n i : ℕ) : Fin k := ⟨n / k ^ i % k, Nat.mod_lt _ (by omega)⟩

theorem run_succ (n i : ℕ) : run f hk n (i + 1) = step f (run f hk n i) (digitAt hk n i) := by
  apply Subtype.ext
  funext m
  simp only [run, step, digitAt]
  congr 1
  rw [Nat.mod_pow_succ, pow_succ]
  ring

theorem run_out {n i : ℕ} (hn : n < k ^ i) : (run f hk n i).1 0 = f n := by
  simp [run, Nat.mod_eq_of_lt hn]

/-- The digit of `x` at the position `y` is `j`, and `y` is a power of `k`. -/
def Dig (k x y j : ℕ) : Prop := (∃ e, y = k ^ e) ∧ x / y % k = j

/-- The run conditions on `n`, the codes `X g` of the states, and the last position `Y`. -/
def Good (n : ℕ) (X : State f k → ℕ) (Y : ℕ) : Prop :=
  (∃ e, Y = k ^ e) ∧ n < Y ∧ Dig k (X (start f)) 1 1 ∧
  (∀ y, (∃ e, y = k ^ e) ∧ y < Y → ∀ p : State f k × Fin k,
    Dig k (X p.1) y 1 → Dig k n y p.2 → Dig k (X (step f p.1 p.2)) (k * y) 1) ∧
  (∀ g : State f k, g.1 0 = false → ¬ Dig k (X g) Y 1)

include hk in
/-- **The run conditions decide `f`.** -/
theorem exists_good_iff (n : ℕ) :
    (∃ (X : State f k → ℕ) (Y : ℕ), Good f n X Y) ↔ f n = true := by
  classical
  have hk1 : 1 < k := by omega
  constructor
  · rintro ⟨X, Y, ⟨L, rfl⟩, hnY, hstart, htrans, hout⟩
    have key : ∀ i ≤ L, Dig k (X (run f hk n i)) (k ^ i) 1 := by
      intro i
      induction i with
      | zero =>
        intro _
        rw [run_zero, pow_zero]
        exact hstart
      | succ i ih =>
        intro hi
        have h1 := htrans (k ^ i) ⟨⟨i, rfl⟩, Nat.pow_lt_pow_right hk1 (by omega)⟩
          (run f hk n i, digitAt hk n i) (ih (by omega)) ⟨⟨i, rfl⟩, rfl⟩
        rw [← run_succ, ← pow_succ'] at h1
        exact h1
    have hL := key L le_rfl
    have : (run f hk n L).1 0 ≠ false := fun h => hout _ h hL
    rw [← run_out f hk hnY]
    simpa using this
  · intro hfn
    set L := n with hL
    have hnL : n < k ^ L := Nat.lt_pow_self hk1
    -- the codes: digit `1` at `kⁱ`, `i ≤ L`, where the run is in `g`
    set X : State f k → ℕ := fun g =>
      ∑ i ∈ Finset.range (L + 1), (if run f hk n i = g then 1 else 0) * k ^ i with hX
    have hdig : ∀ g i, X g / k ^ i % k = if i < L + 1 ∧ run f hk n i = g then 1 else 0 := by
      intro g i
      rw [hX]
      dsimp only
      rw [digit_sum hk _ (fun j => by split_ifs <;> omega)]
      split_ifs <;> tauto
    have hDig : ∀ g i, Dig k (X g) (k ^ i) 1 ↔ i ≤ L ∧ run f hk n i = g := by
      intro g i
      constructor
      · rintro ⟨-, h⟩
        rw [hdig] at h
        split_ifs at h with h'
        · exact ⟨by omega, h'.2⟩
      · rintro ⟨hi, hg⟩
        exact ⟨⟨i, rfl⟩, by rw [hdig, ite_eq_left ⟨by omega, hg⟩]⟩
    refine ⟨X, k ^ L, ⟨L, rfl⟩, hnL, ?_, ?_, ?_⟩
    · show Dig k (X (start f)) (k ^ 0) 1
      rw [hDig]
      exact ⟨by omega, run_zero f hk n⟩
    · rintro y ⟨⟨i, rfl⟩, hy⟩ p hp hd
      have hiL : i < L := (Nat.pow_lt_pow_iff_right hk1).1 hy
      obtain ⟨-, hg⟩ := (hDig p.1 i).1 hp
      have hd' : p.2 = digitAt hk n i := Fin.ext (by rw [digitAt]; exact hd.2.symm)
      rw [← pow_succ', hDig, ← hg, hd', ← run_succ]
      exact ⟨by omega, rfl⟩
    · intro g hg hd
      obtain ⟨-, hrun⟩ := (hDig g L).1 hd
      rw [← hrun, run_out f hk hnL] at hg
      rw [hg] at hfn
      exact Bool.false_ne_true hfn

end Run

/-! ### Definable sets and functions of `(ℕ, 0, 1, +, V_k)` -/

/-- Definable in `(ℕ, 0, 1, +, V_k)` without parameters. -/
abbrev BDef (k : ℕ) {α : Type} (s : Set (α → ℕ)) : Prop := (∅ : Set ℕ).Definable (buchi k) s

/-- A function definable in `(ℕ, 0, 1, +, V_k)` without parameters. -/
abbrev BFun (k : ℕ) {α : Type} (f : (α → ℕ) → ℕ) : Prop :=
  (∅ : Set ℕ).DefinableFun (buchi k) f

theorem bfun_var {α : Type} (i : α) : BFun k fun v : α → ℕ => v i :=
  (buchi k).definableFun_var i

theorem bfun_add {α : Type} {f g : (α → ℕ) → ℕ} (hf : BFun k f) (hg : BFun k g) :
    BFun k fun v => f v + g v := by
  have hmap : (∅ : Set ℕ).DefinableMap (buchi k) fun v => ![f v, g v] := by
    simp [DefinableMap, Fin.forall_fin_two, hf, hg]
  exact DefinableFun.comp hmap (DefinableFun.fun_symbol (L := buchi k) (M := ℕ) BuchiFunc.add)

theorem bfun_vk {α : Type} {f : (α → ℕ) → ℕ} (hf : BFun k f) : BFun k fun v => vk k (f v) := by
  have hmap : (∅ : Set ℕ).DefinableMap (buchi k) fun v => ![f v] := by
    simp [DefinableMap, hf]
  exact DefinableFun.comp hmap (DefinableFun.fun_symbol (L := buchi k) (M := ℕ) BuchiFunc.v)

theorem bfun_const {α : Type} : ∀ n : ℕ, BFun k fun _ : α → ℕ => n
  | 0 => by
    have hmap : (∅ : Set ℕ).DefinableMap (buchi k) fun _ : α → ℕ => (![] : Fin 0 → ℕ) :=
      fun i => i.elim0
    exact DefinableFun.comp hmap (DefinableFun.fun_symbol (L := buchi k) (M := ℕ) BuchiFunc.zero)
  | n + 1 => by
    have hmap : (∅ : Set ℕ).DefinableMap (buchi k) fun _ : α → ℕ => (![] : Fin 0 → ℕ) :=
      fun i => i.elim0
    exact bfun_add (bfun_const n)
      (DefinableFun.comp hmap (DefinableFun.fun_symbol (L := buchi k) (M := ℕ) BuchiFunc.one))

theorem bfun_mul {α : Type} {f : (α → ℕ) → ℕ} (hf : BFun k f) : ∀ m : ℕ, BFun k fun v => m * f v
  | 0 => by simpa using bfun_const (k := k) (α := α) 0
  | m + 1 => by
    have e : (fun v => (m + 1) * f v) = fun v => m * f v + f v := funext fun v => by ring
    rw [e]
    exact bfun_add (bfun_mul hf m) hf

theorem bfun_comp_inl {α β : Type} [Finite α] {f : (α → ℕ) → ℕ} (hf : BFun k f) :
    BFun k fun w : α ⊕ β → ℕ => f (w ∘ Sum.inl) :=
  DefinableFun.comp (fun i => bfun_var (Sum.inl i)) hf

theorem bdef_eq {α : Type} {f g : (α → ℕ) → ℕ} (hf : BFun k f) (hg : BFun k g) :
    BDef k {v | f v = g v} :=
  hf.ofPred_eq hg

theorem bdef_le {α : Type} [Finite α] {f g : (α → ℕ) → ℕ} (hf : BFun k f) (hg : BFun k g) :
    BDef k {v | f v ≤ g v} := by
  have h : BDef k {w : α ⊕ Unit → ℕ | f (w ∘ Sum.inl) + w (Sum.inr ()) = g (w ∘ Sum.inl)} :=
    bdef_eq (bfun_add (bfun_comp_inl hf) (bfun_var _)) (bfun_comp_inl hg)
  convert h.exists_of_finite using 1
  ext v
  simp only [Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
  constructor
  · intro hle
    exact ⟨fun _ => g v - f v, Nat.add_sub_of_le hle⟩
  · rintro ⟨u, hu⟩
    omega

theorem bdef_lt {α : Type} [Finite α] {f g : (α → ℕ) → ℕ} (hf : BFun k f) (hg : BFun k g) :
    BDef k {v | f v < g v} := by
  exact bdef_le (bfun_add hf (bfun_const 1)) hg

/-- "`g v` is a power of `k`" is definable. -/
theorem bdef_pow (hk : 2 ≤ k) {α : Type} [Finite α] {g : (α → ℕ) → ℕ} (hg : BFun k g) :
    BDef k {v | ∃ e, g v = k ^ e} := by
  have : {v | ∃ e, g v = k ^ e} = {v | 1 ≤ g v} ∩ {v | vk k (g v) = g v} := by
    ext v
    exact isPow_iff hk
  rw [this]
  exact (bdef_le (bfun_const 1) hg).inter (bdef_eq (bfun_vk hg) hg)

/-- "The digit of `f v` at the position `g v`, a power of `k`, is `j`" is definable. -/
theorem bdef_digit (hk : 2 ≤ k) {α : Type} [Finite α] {j : ℕ} (hj : j < k)
    {f g : (α → ℕ) → ℕ} (hf : BFun k f) (hg : BFun k g) :
    BDef k {v | Dig k (f v) (g v) j} := by
  have hF : BFun k fun w : α ⊕ Fin 2 → ℕ => f (w ∘ Sum.inl) := bfun_comp_inl hf
  have hG : BFun k fun w : α ⊕ Fin 2 → ℕ => g (w ∘ Sum.inl) := bfun_comp_inl hg
  have hS : BDef k ({w : α ⊕ Fin 2 → ℕ |
      f (w ∘ Sum.inl) = w (Sum.inr 0) + j * g (w ∘ Sum.inl) + w (Sum.inr 1)} ∩
      {w | w (Sum.inr 0) < g (w ∘ Sum.inl)} ∩
      ({w | w (Sum.inr 1) = 0} ∪ {w | k * g (w ∘ Sum.inl) ≤ vk k (w (Sum.inr 1))})) :=
    ((bdef_eq hF (bfun_add (bfun_add (bfun_var _) (bfun_mul hG j)) (bfun_var _))).inter
      (bdef_lt (bfun_var _) hG)).inter
      ((bdef_eq (bfun_var _) (bfun_const 0)).union (bdef_le (bfun_mul hG k) (bfun_vk (bfun_var _))))
  convert (bdef_pow hk hg).inter hS.exists_of_finite using 1
  ext v
  simp only [Dig, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Sum.elim_comp_inl,
    Sum.elim_inr]
  constructor
  · rintro ⟨⟨e, he⟩, hd⟩
    refine ⟨⟨e, he⟩, ?_⟩
    rw [he] at hd
    obtain ⟨a, b, hab, ha, hb⟩ := (digit_iff hk e (f v) j hj).1 hd
    refine ⟨![a, b], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [he, ← pow_succ']
    exact ⟨⟨hab, ha⟩, (pow_dvd_iff hk (e + 1) b).1 hb⟩
  · rintro ⟨⟨e, he⟩, u, ⟨hab, ha⟩, hb⟩
    refine ⟨⟨e, he⟩, ?_⟩
    rw [he] at hab ha hb ⊢
    rw [← pow_succ'] at hb
    exact (digit_iff hk e (f v) j hj).2 ⟨u 0, u 1, hab, ha, (pow_dvd_iff hk (e + 1) _).2 hb⟩

/-! ### Automatic sets are definable -/

/-- **`k`-automatic ⟹ definable in `(ℕ, 0, 1, +, V_k)`**, without parameters: the run of the
kernel automaton is coded by one number per state. -/
theorem definable_of_isAutomatic (hk : 2 ≤ k) {f : ℕ → Bool} (hf : IsAutomatic k f) :
    (∅ : Set ℕ).Definable₁ (buchi k) {t | f t = true} := by
  classical
  have : Finite (State f k) := hf.to_subtype
  have h1k : 1 < k := by omega
  -- the transition condition, with the position `y` as an extra variable
  have hT : BDef k {w : (Fin 1 ⊕ (State f k ⊕ Unit)) ⊕ Unit → ℕ |
      (∃ e, w (Sum.inr ()) = k ^ e) ∧ w (Sum.inr ()) < w (Sum.inl (Sum.inr (Sum.inr ()))) →
      ∀ p : State f k × Fin k, Dig k (w (Sum.inl (Sum.inr (Sum.inl p.1)))) (w (Sum.inr ())) 1 →
        Dig k (w (Sum.inl (Sum.inl 0))) (w (Sum.inr ())) p.2 →
        Dig k (w (Sum.inl (Sum.inr (Sum.inl (step f p.1 p.2))))) (k * w (Sum.inr ())) 1} := by
    have e : {w : (Fin 1 ⊕ (State f k ⊕ Unit)) ⊕ Unit → ℕ |
        (∃ e, w (Sum.inr ()) = k ^ e) ∧ w (Sum.inr ()) < w (Sum.inl (Sum.inr (Sum.inr ()))) →
        ∀ p : State f k × Fin k, Dig k (w (Sum.inl (Sum.inr (Sum.inl p.1)))) (w (Sum.inr ())) 1 →
          Dig k (w (Sum.inl (Sum.inl 0))) (w (Sum.inr ())) p.2 →
          Dig k (w (Sum.inl (Sum.inr (Sum.inl (step f p.1 p.2))))) (k * w (Sum.inr ())) 1} =
        ({w | ∃ e, w (Sum.inr ()) = k ^ e} ∩
          {w | w (Sum.inr ()) < w (Sum.inl (Sum.inr (Sum.inr ())))})ᶜ ∪
        ⋂ p : State f k × Fin k,
          ({w | Dig k (w (Sum.inl (Sum.inr (Sum.inl p.1)))) (w (Sum.inr ())) 1}ᶜ ∪
            {w | Dig k (w (Sum.inl (Sum.inl 0))) (w (Sum.inr ())) p.2}ᶜ ∪
            {w | Dig k (w (Sum.inl (Sum.inr (Sum.inl (step f p.1 p.2)))))
              (k * w (Sum.inr ())) 1}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
        Set.mem_iInter, imp_iff_not_or, or_assoc]
    rw [e]
    refine (((bdef_pow hk (bfun_var _)).inter (bdef_lt (bfun_var _) (bfun_var _))).compl).union
      (definable_iInter_of_finite fun p => ?_)
    exact (((bdef_digit hk h1k (bfun_var _) (bfun_var _)).compl).union
      ((bdef_digit hk p.2.isLt (bfun_var _) (bfun_var _)).compl)).union
      (bdef_digit hk h1k (bfun_var _) (bfun_mul (bfun_var _) k))
  -- the output condition
  have hO : BDef k {v : Fin 1 ⊕ (State f k ⊕ Unit) → ℕ | ∀ g : State f k, g.1 0 = false →
      ¬ Dig k (v (Sum.inr (Sum.inl g))) (v (Sum.inr (Sum.inr ()))) 1} := by
    rw [Set.ofPred_forall]
    refine definable_iInter_of_finite fun g => ?_
    by_cases hg : g.1 0 = false
    · simp only [hg, true_implies]
      exact (bdef_digit hk h1k (bfun_var _) (bfun_var _)).compl
    · have : {x : Fin 1 ⊕ (State f k ⊕ Unit) → ℕ | g.1 0 = false →
          ¬ Dig k (x (Sum.inr (Sum.inl g))) (x (Sum.inr (Sum.inr ()))) 1} = Set.univ := by
        ext x
        simp [hg]
      rw [this]
      exact Set.definable_univ
  -- the run conditions
  have hgood : BDef k {v : Fin 1 ⊕ (State f k ⊕ Unit) → ℕ | Good f (v (Sum.inl 0))
      (fun g => v (Sum.inr (Sum.inl g))) (v (Sum.inr (Sum.inr ())))} := by
    have hA4 : BDef k {v : Fin 1 ⊕ (State f k ⊕ Unit) → ℕ | ∀ y,
        (∃ e, y = k ^ e) ∧ y < v (Sum.inr (Sum.inr ())) → ∀ p : State f k × Fin k,
          Dig k (v (Sum.inr (Sum.inl p.1))) y 1 → Dig k (v (Sum.inl 0)) y p.2 →
          Dig k (v (Sum.inr (Sum.inl (step f p.1 p.2)))) (k * y) 1} := by
      convert hT.forall_of_finite using 1
      ext v
      simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
      constructor
      · intro h u
        exact h (u ())
      · intro h y
        exact h fun _ => y
    have hY := bfun_var (k := k) (Sum.inr (Sum.inr ()) : Fin 1 ⊕ (State f k ⊕ Unit))
    have hn := bfun_var (k := k) (Sum.inl 0 : Fin 1 ⊕ (State f k ⊕ Unit))
    have hX0 := bfun_var (k := k) (Sum.inr (Sum.inl (start f)) : Fin 1 ⊕ (State f k ⊕ Unit))
    convert ((((bdef_pow hk hY).inter (bdef_lt hn hY)).inter
      (bdef_digit hk h1k hX0 (bfun_const 1))).inter hA4).inter hO using 1
    ext v
    simp only [Good, start, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  unfold Set.Definable₁
  convert hgood.exists_of_finite using 1
  ext x
  simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
  rw [← exists_good_iff f hk (x 0)]
  constructor
  · rintro ⟨X, Y, h⟩
    exact ⟨Sum.elim X fun _ => Y, h⟩
  · rintro ⟨u, h⟩
    exact ⟨fun g => u (Sum.inl g), u (Sum.inr ()), h⟩

/-- **The Büchi–Bruyère theorem** for sets of naturals: `{t | f t}` is definable in
`(ℕ, 0, 1, +, V_k)`, with any parameters, iff `f` is `k`-automatic. -/
theorem definable_iff_isAutomatic (hk : 2 ≤ k) (A : Set ℕ) (f : ℕ → Bool) :
    A.Definable₁ (buchi k) {t | f t = true} ↔ IsAutomatic k f :=
  ⟨isAutomatic_of_definable hk, fun h =>
    Set.Definable.mono (definable_of_isAutomatic hk h) (Set.empty_subset A)⟩

/-- **The ladder of logics, rung `(ℕ, +, V_k)`**: the black times of rule 30 are not definable in
`(ℕ, 0, 1, +, V_k)` iff the center column is not `k`-automatic. -/
theorem not_definable_iff_not_isAutomatic (hk : 2 ≤ k) (A : Set ℕ) :
    ¬ A.Definable₁ (buchi k) {t | c t = true} ↔ ¬ IsAutomatic k c :=
  (definable_iff_isAutomatic hk A c).not

end Rule30Equivalents.BuchiConverse
