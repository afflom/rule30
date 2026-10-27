module

public import Rule30Equivalents.OneTapeGap

/-!
# Monadic second-order logic over `(ℕ, <)`

A set `S ⊆ ℕ` is definable in monadic second-order logic over
`(ℕ, <)` iff it is eventually periodic (a consequence of Büchi's theorem). So Problem 1 holds iff
the set of black times of the center column is not MSO-definable
(`problem1_iff_not_msoDefinable`).

The proof does not go through Büchi automata (and their complementation). It is the composition
method with types defined semantically:
* `MSO`, `MSO.Holds`: formulas with first-order variables `x i` and set variables `X j`, named by
  natural numbers, and their truth in `(ℕ, <)`. `MSODefinable S`: some formula holds exactly when
  its first-order variables are `n ∈ S`.
* `MSO.toMSO0`: the standard translation into a logic with set variables only, where a first-order
  variable becomes a singleton (`MSO.holds_iff_toMSO0`).
* `tp m k ρ`: the `k`-type of an assignment `ρ` of the set variables below `m`: its atomic facts,
  and for each variable the set of `(k − 1)`-types of its modifications. Types take values in a
  finite type (`finiteTy`), and assignments of equal `k`-type satisfy the same formulas of depth
  at most `k` (`holds_iff_of_tp_eq`).
* `tp_shift`: putting one more position in front of `ℕ` (`shift`) maps equal types to equal types.
  The assignments for the inputs `n` and `n + 1` differ by such a shift, so their types are
  eventually periodic, and so is `S`.
* `periodicFormula`: an eventually periodic set is defined by "every family of sets that starts at
  `0` and follows the counting automaton puts `x` in an accepting set".
-/

@[expose] public section

namespace Rule30Equivalents.MonadicLogic

open Ruliology.CellularAutomata OneTapeGap

/-- Formulas of monadic second-order logic over `(ℕ, <)`: first-order variables `x i` range over
`ℕ` and set variables `X j` over subsets of `ℕ`; both are named by natural numbers. -/
inductive MSO : Type
  /-- `x i < x j` -/
  | lt (i j : ℕ)
  /-- `x i ∈ X j` -/
  | mem (i j : ℕ)
  | not (φ : MSO)
  | and (φ ψ : MSO)
  /-- `∃ x i, φ` -/
  | ex (i : ℕ) (φ : MSO)
  /-- `∃ X j, φ` -/
  | exSet (j : ℕ) (φ : MSO)

namespace MSO

/-- Truth in `(ℕ, <)`, under an assignment `v` of the first-order variables and `V` of the set
variables. -/
def Holds : MSO → (ℕ → ℕ) → (ℕ → Set ℕ) → Prop
  | lt i j, v, _ => v i < v j
  | mem i j, v, V => v i ∈ V j
  | not φ, v, V => ¬ φ.Holds v V
  | and φ ψ, v, V => φ.Holds v V ∧ ψ.Holds v V
  | ex i φ, v, V => ∃ n, φ.Holds (Function.update v i n) V
  | exSet j φ, v, V => ∃ A, φ.Holds v (Function.update V j A)

end MSO

/-- `S` is definable in MSO over `(ℕ, <)`: some formula holds exactly when all its first-order
variables are `n ∈ S` (only one of them need occur free) and its set variables are empty. -/
def MSODefinable (S : Set ℕ) : Prop :=
  ∃ φ : MSO, ∀ n, n ∈ S ↔ φ.Holds (fun _ => n) (fun _ => ∅)

/-! ### Set variables only -/

/-- Monadic logic over `(ℕ, <)` with set variables only. -/
inductive MSO0 : Type
  /-- `X i = ∅` -/
  | empty (i : ℕ)
  /-- `X i` is a singleton -/
  | sing (i : ℕ)
  /-- `X i ⊆ X j` -/
  | sub (i j : ℕ)
  /-- every element of `X i` is below every element of `X j` -/
  | less (i j : ℕ)
  | not (φ : MSO0)
  | and (φ ψ : MSO0)
  /-- `∃ X i, φ` -/
  | ex (i : ℕ) (φ : MSO0)

namespace MSO0

/-- Truth under an assignment `ρ` of the set variables. -/
def Holds : MSO0 → (ℕ → Set ℕ) → Prop
  | empty i, ρ => ρ i = ∅
  | sing i, ρ => ∃ n, ρ i = {n}
  | sub i j, ρ => ρ i ⊆ ρ j
  | less i j, ρ => ∀ p ∈ ρ i, ∀ q ∈ ρ j, p < q
  | not φ, ρ => ¬ φ.Holds ρ
  | and φ ψ, ρ => φ.Holds ρ ∧ ψ.Holds ρ
  | ex i φ, ρ => ∃ A, φ.Holds (Function.update ρ i A)

/-- Quantifier depth. -/
def depth : MSO0 → ℕ
  | not φ => φ.depth
  | and φ ψ => max φ.depth ψ.depth
  | ex _ φ => φ.depth + 1
  | _ => 0

/-- All variables are below `m`. -/
def Bounded (m : ℕ) : MSO0 → Prop
  | empty i => i < m
  | sing i => i < m
  | sub i j => i < m ∧ j < m
  | less i j => i < m ∧ j < m
  | not φ => φ.Bounded m
  | and φ ψ => φ.Bounded m ∧ ψ.Bounded m
  | ex i φ => i < m ∧ φ.Bounded m

theorem Bounded.mono {m m' : ℕ} (h : m ≤ m') : ∀ (φ : MSO0), φ.Bounded m → φ.Bounded m'
  | empty _, hb => lt_of_lt_of_le hb h
  | sing _, hb => lt_of_lt_of_le hb h
  | sub _ _, hb => ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2 h⟩
  | less _ _, hb => ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2 h⟩
  | not φ, hb => Bounded.mono h φ hb
  | and φ ψ, hb => ⟨Bounded.mono h φ hb.1, Bounded.mono h ψ hb.2⟩
  | ex _ φ, hb => ⟨lt_of_lt_of_le hb.1 h, Bounded.mono h φ hb.2⟩

theorem exists_bounded : ∀ φ : MSO0, ∃ m, φ.Bounded m
  | empty i => ⟨i + 1, by simp [Bounded]⟩
  | sing i => ⟨i + 1, by simp [Bounded]⟩
  | sub i j => ⟨max i j + 1, by simp only [Bounded]; omega⟩
  | less i j => ⟨max i j + 1, by simp only [Bounded]; omega⟩
  | not φ => φ.exists_bounded
  | and φ ψ => by
    obtain ⟨m₁, h₁⟩ := φ.exists_bounded
    obtain ⟨m₂, h₂⟩ := ψ.exists_bounded
    exact ⟨max m₁ m₂, Bounded.mono (le_max_left _ _) φ h₁, Bounded.mono (le_max_right _ _) ψ h₂⟩
  | ex i φ => by
    obtain ⟨m, h⟩ := φ.exists_bounded
    exact ⟨max m (i + 1), by omega, Bounded.mono (le_max_left _ _) φ h⟩

end MSO0

/-- The standard translation: the first-order variable `x i` becomes the set variable `X (2i)`,
a singleton, and the set variable `X j` becomes `X (2j + 1)`. -/
def MSO.toMSO0 : MSO → MSO0
  | .lt i j => .less (2 * i) (2 * j)
  | .mem i j => .sub (2 * i) (2 * j + 1)
  | .not φ => .not φ.toMSO0
  | .and φ ψ => .and φ.toMSO0 ψ.toMSO0
  | .ex i φ => .ex (2 * i) (.and (.sing (2 * i)) φ.toMSO0)
  | .exSet j φ => .ex (2 * j + 1) φ.toMSO0

/-- The set assignment that encodes `v` and `V`. -/
def enc (v : ℕ → ℕ) (V : ℕ → Set ℕ) (k : ℕ) : Set ℕ :=
  if k % 2 = 0 then {v (k / 2)} else V (k / 2)

theorem enc_even (v : ℕ → ℕ) (V : ℕ → Set ℕ) (i : ℕ) : enc v V (2 * i) = {v i} := by
  simp [enc]

theorem enc_odd (v : ℕ → ℕ) (V : ℕ → Set ℕ) (j : ℕ) : enc v V (2 * j + 1) = V j := by
  simp only [enc]
  rw [ite_eq_right (by omega)]
  congr 1
  omega

theorem enc_update_fo (v : ℕ → ℕ) (V : ℕ → Set ℕ) (i n : ℕ) :
    enc (Function.update v i n) V = Function.update (enc v V) (2 * i) {n} := by
  funext k
  by_cases hk : k = 2 * i
  · subst hk
    rw [Function.update_self, enc_even, Function.update_self]
  · rw [Function.update_of_ne hk]
    simp only [enc]
    split_ifs with h
    · rw [Function.update_of_ne (by omega)]
    · rfl

theorem enc_update_so (v : ℕ → ℕ) (V : ℕ → Set ℕ) (j : ℕ) (A : Set ℕ) :
    enc v (Function.update V j A) = Function.update (enc v V) (2 * j + 1) A := by
  funext k
  by_cases hk : k = 2 * j + 1
  · subst hk
    rw [Function.update_self, enc_odd, Function.update_self]
  · rw [Function.update_of_ne hk]
    simp only [enc]
    split_ifs with h
    · rfl
    · rw [Function.update_of_ne (by omega)]

theorem MSO.holds_iff_toMSO0 : ∀ (φ : MSO) (v : ℕ → ℕ) (V : ℕ → Set ℕ),
    φ.Holds v V ↔ φ.toMSO0.Holds (enc v V)
  | .lt i j, v, V => by
    simp only [MSO.Holds, MSO.toMSO0, MSO0.Holds, enc_even, Set.mem_singleton_iff, forall_eq]
  | .mem i j, v, V => by
    simp only [MSO.Holds, MSO.toMSO0, MSO0.Holds, enc_even, enc_odd, Set.singleton_subset_iff]
  | .not φ, v, V => by
    simp only [MSO.Holds, MSO.toMSO0, MSO0.Holds, φ.holds_iff_toMSO0 v V]
  | .and φ ψ, v, V => by
    simp only [MSO.Holds, MSO.toMSO0, MSO0.Holds, φ.holds_iff_toMSO0 v V, ψ.holds_iff_toMSO0 v V]
  | .ex i φ, v, V => by
    simp only [MSO.Holds, MSO.toMSO0, MSO0.Holds]
    constructor
    · rintro ⟨n, h⟩
      refine ⟨{n}, ⟨n, Function.update_self _ _ _⟩, ?_⟩
      rw [← enc_update_fo, ← φ.holds_iff_toMSO0]
      exact h
    · rintro ⟨A, ⟨n, hn⟩, h⟩
      rw [Function.update_self] at hn
      subst hn
      refine ⟨n, ?_⟩
      rw [φ.holds_iff_toMSO0, enc_update_fo]
      exact h
  | .exSet j φ, v, V => by
    simp only [MSO.Holds, MSO.toMSO0, MSO0.Holds]
    constructor
    · rintro ⟨A, h⟩
      exact ⟨A, by rw [← enc_update_so, ← φ.holds_iff_toMSO0]; exact h⟩
    · rintro ⟨A, h⟩
      exact ⟨A, by rw [φ.holds_iff_toMSO0, enc_update_so]; exact h⟩

/-! ### Types -/

/-- The kinds of atomic formulas. -/
inductive AtomKind
  | empty
  | sing
  | sub
  | less
  deriving DecidableEq

instance : Fintype AtomKind where
  elems := {.empty, .sing, .sub, .less}
  complete x := by cases x <;> simp

/-- Atomic formulas over the variables below `m`. -/
abbrev Atom (m : ℕ) := AtomKind × Fin m × Fin m

/-- Truth of an atomic formula. -/
def Atom.Holds {m : ℕ} (a : Atom m) (ρ : ℕ → Set ℕ) : Prop :=
  match a.1 with
  | .empty => ρ a.2.1 = ∅
  | .sing => ∃ n, ρ a.2.1 = {n}
  | .sub => ρ a.2.1 ⊆ ρ a.2.2
  | .less => ∀ p ∈ ρ a.2.1, ∀ q ∈ ρ a.2.2, p < q

/-- The values of `k`-types over the variables below `m`. -/
def Ty (m : ℕ) : ℕ → Type
  | 0 => Set (Atom m)
  | k + 1 => Set (Atom m) × Set (Fin m × Ty m k)

instance finiteTy (m : ℕ) : ∀ k, Finite (Ty m k)
  | 0 => inferInstanceAs (Finite (Set (Atom m)))
  | k + 1 => by
    have := finiteTy m k
    exact inferInstanceAs (Finite (Set (Atom m) × Set (Fin m × Ty m k)))

/-- The atomic facts of `ρ`. -/
def atoms (m : ℕ) (ρ : ℕ → Set ℕ) : Set (Atom m) := {a | a.Holds ρ}

/-- The `k`-type of `ρ`: its atomic facts and, for `k > 0`, for each variable the set of
`(k − 1)`-types of the assignments that change that variable. -/
def tp (m : ℕ) : (k : ℕ) → (ℕ → Set ℕ) → Ty m k
  | 0, ρ => atoms m ρ
  | k + 1, ρ => (atoms m ρ, {p | ∃ A, p.2 = tp m k (Function.update ρ (p.1 : ℕ) A)})

theorem atoms_eq_of_tp_eq {m : ℕ} : ∀ {k : ℕ} {ρ ρ' : ℕ → Set ℕ}, tp m k ρ = tp m k ρ' →
    atoms m ρ = atoms m ρ'
  | 0, _, _, h => h
  | _ + 1, _, _, h => congrArg Prod.fst h

theorem tp_eq_of_succ {m : ℕ} : ∀ {k : ℕ} {ρ ρ' : ℕ → Set ℕ}, tp m (k + 1) ρ = tp m (k + 1) ρ' →
    tp m k ρ = tp m k ρ'
  | 0, _, _, h => congrArg Prod.fst h
  | k + 1, ρ, ρ', h => by
    have h1 : atoms m ρ = atoms m ρ' := congrArg Prod.fst h
    have h2 : {p : Fin m × Ty m (k + 1) | ∃ A, p.2 = tp m (k + 1) (Function.update ρ p.1 A)} =
        {p | ∃ A, p.2 = tp m (k + 1) (Function.update ρ' p.1 A)} := congrArg Prod.snd h
    show (atoms m ρ, {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ p.1 A)}) =
      (atoms m ρ', {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ' p.1 A)})
    refine Prod.ext h1 (Set.ext fun p => ⟨fun ⟨A, hA⟩ => ?_, fun ⟨A, hA⟩ => ?_⟩)
    · have hm : (p.1, tp m (k + 1) (Function.update ρ p.1 A)) ∈
          {p : Fin m × Ty m (k + 1) | ∃ A, p.2 = tp m (k + 1) (Function.update ρ p.1 A)} :=
        ⟨A, rfl⟩
      rw [h2] at hm
      obtain ⟨A', hA'⟩ := hm
      exact ⟨A', hA.trans (tp_eq_of_succ hA')⟩
    · have hm : (p.1, tp m (k + 1) (Function.update ρ' p.1 A)) ∈
          {p : Fin m × Ty m (k + 1) | ∃ A, p.2 = tp m (k + 1) (Function.update ρ' p.1 A)} :=
        ⟨A, rfl⟩
      rw [← h2] at hm
      obtain ⟨A', hA'⟩ := hm
      exact ⟨A', hA.trans (tp_eq_of_succ hA')⟩

theorem atom_iff {m : ℕ} {ρ ρ' : ℕ → Set ℕ} (h : atoms m ρ = atoms m ρ') (a : Atom m) :
    a.Holds ρ ↔ a.Holds ρ' := by
  have := congrArg (a ∈ ·) h
  simpa [atoms] using this

/-- **Types decide formulas.** Assignments with the same `k`-type satisfy the same formulas of
depth at most `k`. -/
theorem holds_iff_of_tp_eq {m : ℕ} : ∀ (φ : MSO0) {k : ℕ}, φ.Bounded m → φ.depth ≤ k →
    ∀ {ρ ρ' : ℕ → Set ℕ}, tp m k ρ = tp m k ρ' → (φ.Holds ρ ↔ φ.Holds ρ')
  | .empty i, _, hb, _, _, _, h => atom_iff (atoms_eq_of_tp_eq h) (.empty, ⟨i, hb⟩, ⟨i, hb⟩)
  | .sing i, _, hb, _, _, _, h => atom_iff (atoms_eq_of_tp_eq h) (.sing, ⟨i, hb⟩, ⟨i, hb⟩)
  | .sub i j, _, hb, _, _, _, h => atom_iff (atoms_eq_of_tp_eq h) (.sub, ⟨i, hb.1⟩, ⟨j, hb.2⟩)
  | .less i j, _, hb, _, _, _, h => atom_iff (atoms_eq_of_tp_eq h) (.less, ⟨i, hb.1⟩, ⟨j, hb.2⟩)
  | .not φ, _, hb, hd, _, _, h => not_congr (holds_iff_of_tp_eq φ hb hd h)
  | .and φ ψ, _, hb, hd, _, _, h =>
    and_congr (holds_iff_of_tp_eq φ hb.1 (le_trans (le_max_left _ _) hd) h)
      (holds_iff_of_tp_eq ψ hb.2 (le_trans (le_max_right _ _) hd) h)
  | .ex i φ, k, hb, hd, ρ, ρ', h => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [MSO0.depth] at hd; omega⟩
    have hd' : φ.depth ≤ k := by simp only [MSO0.depth] at hd; omega
    have h2 : {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ p.1 A)} =
        {p | ∃ A, p.2 = tp m k (Function.update ρ' p.1 A)} := congrArg Prod.snd h
    simp only [MSO0.Holds]
    constructor
    · rintro ⟨A, hA⟩
      have hm : ((⟨i, hb.1⟩ : Fin m), tp m k (Function.update ρ i A)) ∈
          {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ p.1 A)} := ⟨A, rfl⟩
      rw [h2] at hm
      obtain ⟨A', hA'⟩ := hm
      exact ⟨A', (holds_iff_of_tp_eq φ hb.2 hd' hA').1 hA⟩
    · rintro ⟨A, hA⟩
      have hm : ((⟨i, hb.1⟩ : Fin m), tp m k (Function.update ρ' i A)) ∈
          {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ' p.1 A)} := ⟨A, rfl⟩
      rw [← h2] at hm
      obtain ⟨A', hA'⟩ := hm
      exact ⟨A', (holds_iff_of_tp_eq φ hb.2 hd' hA').1 hA⟩

/-! ### One more position in front -/

/-- Put one more position in front of `ℕ`: it belongs to `X i` iff `a i`, and the old positions
move up by one. -/
def shift (a : ℕ → Bool) (ρ : ℕ → Set ℕ) (i : ℕ) : Set ℕ :=
  {p | Nat.casesOn p (a i = true) fun q => q ∈ ρ i}

@[simp] theorem zero_mem_shift {a : ℕ → Bool} {ρ : ℕ → Set ℕ} {i : ℕ} :
    0 ∈ shift a ρ i ↔ a i = true := Iff.rfl

@[simp] theorem succ_mem_shift {a : ℕ → Bool} {ρ : ℕ → Set ℕ} {i q : ℕ} :
    q + 1 ∈ shift a ρ i ↔ q ∈ ρ i := Iff.rfl

theorem shift_eq_empty {a : ℕ → Bool} {ρ : ℕ → Set ℕ} {i : ℕ} :
    shift a ρ i = ∅ ↔ a i = false ∧ ρ i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun q hq => h (q + 1) (by simpa using hq)⟩
  · rintro ⟨ha, hρ⟩ p hp
    cases p with
    | zero => simp [ha] at hp
    | succ q => exact hρ q (by simpa using hp)

theorem shift_sing {a : ℕ → Bool} {ρ : ℕ → Set ℕ} {i : ℕ} :
    (∃ n, shift a ρ i = {n}) ↔ (a i = true ∧ ρ i = ∅) ∨ (a i = false ∧ ∃ n, ρ i = {n}) := by
  constructor
  · rintro ⟨n, hn⟩
    have hmem : ∀ p, p ∈ shift a ρ i ↔ p = n := fun p => by rw [hn]; rfl
    cases n with
    | zero =>
      refine Or.inl ⟨(hmem 0).2 rfl, Set.eq_empty_iff_forall_notMem.2 fun q hq => ?_⟩
      have := (hmem (q + 1)).1 (by simpa using hq)
      omega
    | succ n =>
      refine Or.inr ⟨?_, n, Set.ext fun q => ?_⟩
      · cases ha : a i
        · rfl
        · have := (hmem 0).1 (by simpa using ha)
          omega
      · rw [Set.mem_singleton_iff, ← succ_mem_shift (a := a), hmem]
        omega
  · rintro (⟨ha, hρ⟩ | ⟨ha, n, hn⟩)
    · refine ⟨0, Set.ext fun p => ?_⟩
      cases p with
      | zero => simpa using ha
      | succ q => simp [hρ]
    · refine ⟨n + 1, Set.ext fun p => ?_⟩
      cases p with
      | zero => simp [ha]
      | succ q => simp [hn]

theorem shift_subset {a : ℕ → Bool} {ρ : ℕ → Set ℕ} {i j : ℕ} :
    shift a ρ i ⊆ shift a ρ j ↔ (a i = true → a j = true) ∧ ρ i ⊆ ρ j := by
  constructor
  · intro h
    exact ⟨fun ha => h (show 0 ∈ shift a ρ i from ha),
      fun q hq => h (show q + 1 ∈ shift a ρ i from hq)⟩
  · rintro ⟨ha, hρ⟩ p hp
    cases p with
    | zero => exact ha hp
    | succ q => exact hρ hp

theorem shift_less {a : ℕ → Bool} {ρ : ℕ → Set ℕ} {i j : ℕ} :
    (∀ p ∈ shift a ρ i, ∀ q ∈ shift a ρ j, p < q) ↔
      ¬ (a i = true ∧ a j = true) ∧ ¬ (a j = true ∧ ρ i ≠ ∅) ∧ ∀ p ∈ ρ i, ∀ q ∈ ρ j, p < q := by
  constructor
  · intro h
    refine ⟨fun ⟨hi, hj⟩ => absurd (h 0 hi 0 hj) (lt_irrefl 0), fun ⟨hj, hne⟩ => ?_,
      fun p hp q hq => Nat.succ_lt_succ_iff.1 (h (p + 1) hp (q + 1) hq)⟩
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact absurd (h (p + 1) hp 0 hj) (Nat.not_lt_zero _)
  · rintro ⟨h1, h2, h3⟩ p hp q hq
    cases p with
    | zero =>
      cases q with
      | zero => exact absurd ⟨hp, hq⟩ h1
      | succ q => exact Nat.succ_pos q
    | succ p =>
      cases q with
      | zero => exact absurd ⟨hq, Set.nonempty_iff_ne_empty.1 ⟨p, hp⟩⟩ h2
      | succ q => exact Nat.succ_lt_succ (h3 p hp q hq)

/-- The atomic facts after a shift depend only on the new position and the atomic facts before. -/
theorem atoms_shift {m : ℕ} (a : ℕ → Bool) {ρ ρ' : ℕ → Set ℕ} (h : atoms m ρ = atoms m ρ') :
    atoms m (shift a ρ) = atoms m (shift a ρ') := by
  have hat := atom_iff h
  ext ⟨k, i, j⟩
  have he : ∀ i : Fin m, ρ i = ∅ ↔ ρ' i = ∅ := fun i => hat (.empty, i, i)
  have hs : ∀ i : Fin m, (∃ n, ρ i = {n}) ↔ ∃ n, ρ' i = {n} := fun i => hat (.sing, i, i)
  have hsub : ρ i ⊆ ρ j ↔ ρ' i ⊆ ρ' j := hat (.sub, i, j)
  have hl : (∀ p ∈ ρ i, ∀ q ∈ ρ j, p < q) ↔ ∀ p ∈ ρ' i, ∀ q ∈ ρ' j, p < q := hat (.less, i, j)
  show Atom.Holds (k, i, j) (shift a ρ) ↔ Atom.Holds (k, i, j) (shift a ρ')
  cases k <;> simp only [Atom.Holds]
  · rw [shift_eq_empty, shift_eq_empty, he]
  · rw [shift_sing, shift_sing, he, hs]
  · rw [shift_subset, shift_subset, hsub]
  · rw [shift_less, shift_less, ne_eq, ne_eq, he, hl]

open Classical in
theorem update_shift (a : ℕ → Bool) (ρ : ℕ → Set ℕ) (i : ℕ) (A : Set ℕ) :
    Function.update (shift a ρ) i A =
      shift (Function.update a i (decide (0 ∈ A))) (Function.update ρ i {q | q + 1 ∈ A}) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    ext p
    cases p with
    | zero => simp
    | succ q => simp
  · rw [Function.update_of_ne hj]
    ext p
    cases p with
    | zero => simp [Function.update_of_ne hj]
    | succ q => simp [Function.update_of_ne hj]

open Classical in
theorem shift_update (a : ℕ → Bool) (ρ : ℕ → Set ℕ) (i : ℕ) (b : Bool) (B : Set ℕ) :
    shift (Function.update a i b) (Function.update ρ i B) =
      Function.update (shift a ρ) i {p | Nat.casesOn p (b = true) fun q => q ∈ B} := by
  rw [update_shift]
  congr 2
  cases b <;> simp

open Classical in
/-- **Shifting respects types.** -/
theorem tp_shift {m : ℕ} : ∀ (k : ℕ) (a : ℕ → Bool) {ρ ρ' : ℕ → Set ℕ}, tp m k ρ = tp m k ρ' →
    tp m k (shift a ρ) = tp m k (shift a ρ')
  | 0, a, _, _, h => atoms_shift a h
  | k + 1, a, ρ, ρ', h => by
    have h1 : atoms m ρ = atoms m ρ' := congrArg Prod.fst h
    have h2 : {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ p.1 A)} =
        {p | ∃ A, p.2 = tp m k (Function.update ρ' p.1 A)} := congrArg Prod.snd h
    show (atoms m (shift a ρ),
        {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update (shift a ρ) p.1 A)}) =
      (atoms m (shift a ρ'),
        {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update (shift a ρ') p.1 A)})
    refine Prod.ext (atoms_shift a h1) (Set.ext fun p => ⟨fun ⟨A, hA⟩ => ?_, fun ⟨A, hA⟩ => ?_⟩)
    · have hm : (p.1, tp m k (Function.update ρ p.1 {q | q + 1 ∈ A})) ∈
          {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ p.1 A)} := ⟨_, rfl⟩
      rw [h2] at hm
      obtain ⟨B, hB⟩ := hm
      refine ⟨{p | Nat.casesOn p (decide (0 ∈ A) = true) fun q => q ∈ B}, ?_⟩
      rw [hA, update_shift, ← shift_update, tp_shift k _ hB]
    · have hm : (p.1, tp m k (Function.update ρ' p.1 {q | q + 1 ∈ A})) ∈
          {p : Fin m × Ty m k | ∃ A, p.2 = tp m k (Function.update ρ' p.1 A)} := ⟨_, rfl⟩
      rw [← h2] at hm
      obtain ⟨B, hB⟩ := hm
      refine ⟨{p | Nat.casesOn p (decide (0 ∈ A) = true) fun q => q ∈ B}, ?_⟩
      rw [hA, update_shift, ← shift_update, tp_shift k _ hB]

/-- **Eventual periodicity.** If the assignments `ρ n` arise from each other by shifts, then the
truth of a formula is eventually periodic in `n`: the types of the `ρ n` take finitely many
values, and equal types stay equal under shifts. -/
theorem holds_eventually_periodic {m : ℕ} (ψ : MSO0) (hψ : ψ.Bounded m) (ρ : ℕ → ℕ → Set ℕ)
    (hρ : ∀ n, ρ (n + 1) = shift (fun _ => false) (ρ n)) :
    ∃ N P, 0 < P ∧ ∀ n, N ≤ n → (ψ.Holds (ρ (n + P)) ↔ ψ.Holds (ρ n)) := by
  obtain ⟨n₁, n₂, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun n => tp m ψ.depth (ρ n)
  have key : ∀ n₁ n₂, n₁ < n₂ → tp m ψ.depth (ρ n₁) = tp m ψ.depth (ρ n₂) →
      ∃ N P, 0 < P ∧ ∀ n, N ≤ n → (ψ.Holds (ρ (n + P)) ↔ ψ.Holds (ρ n)) := by
    intro n₁ n₂ hlt heq
    have hall : ∀ j, tp m ψ.depth (ρ (n₁ + j)) = tp m ψ.depth (ρ (n₂ + j)) := by
      intro j
      induction j with
      | zero => exact heq
      | succ j ih =>
        rw [← add_assoc, ← add_assoc, hρ, hρ]
        exact tp_shift _ _ ih
    refine ⟨n₁, n₂ - n₁, by omega, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = n₁ + j := ⟨n - n₁, by omega⟩
    rw [show n₁ + j + (n₂ - n₁) = n₂ + j by omega]
    exact (holds_iff_of_tp_eq ψ hψ le_rfl (hall j)).symm
  rcases lt_or_gt_of_ne hne with h | h
  · exact key n₁ n₂ h heq
  · exact key n₂ n₁ h heq.symm

/-- **MSO-definable sets are eventually periodic.** -/
theorem eventuallyPeriodic_of_msoDefinable {f : ℕ → Bool} (h : MSODefinable {t | f t = true}) :
    EventuallyPeriodic f := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨m, hm⟩ := φ.toMSO0.exists_bounded
  have hρ : ∀ n, enc (fun _ => n + 1) (fun _ => ∅) =
      shift (fun _ => false) (enc (fun _ => n) (fun _ => ∅)) := by
    intro n
    funext k
    ext p
    cases p with
    | zero => simp [enc]
    | succ q => simp only [succ_mem_shift, enc]; split_ifs <;> simp
  obtain ⟨N, P, hP, hNP⟩ := holds_eventually_periodic φ.toMSO0 hm
    (fun n => enc (fun _ => n) (fun _ => ∅)) hρ
  refine ⟨N, P, hP, fun t ht => ?_⟩
  have h1 := hφ (t + P)
  have h2 := hφ t
  rw [MSO.holds_iff_toMSO0] at h1 h2
  have h3 := hNP t ht
  simp only [Set.mem_ofPred_eq] at h1 h2
  rw [Bool.eq_iff_iff, h1, h2]
  exact h3

/-! ### Defining an eventually periodic set -/

namespace MSO

/-- A formula that always holds. -/
def top : MSO := not (lt 0 0)

def or (φ ψ : MSO) : MSO := not (and (not φ) (not ψ))

def imp (φ ψ : MSO) : MSO := not (and φ (not ψ))

/-- `∀ x i, φ` -/
def all (i : ℕ) (φ : MSO) : MSO := not (ex i (not φ))

/-- `∀ X j, φ` -/
def allSet (j : ℕ) (φ : MSO) : MSO := not (exSet j (not φ))

def bigAnd : List MSO → MSO
  | [] => top
  | φ :: l => and φ (bigAnd l)

def bigOr : List MSO → MSO
  | [] => not top
  | φ :: l => or φ (bigOr l)

/-- `∀ X j₁, …, ∀ X jₖ, φ` -/
def allSets : List ℕ → MSO → MSO
  | [], φ => φ
  | j :: l, φ => allSet j (allSets l φ)

variable {v : ℕ → ℕ} {V : ℕ → Set ℕ}

@[simp] theorem holds_top : top.Holds v V := lt_irrefl (v 0)

@[simp] theorem holds_or {φ ψ : MSO} : (or φ ψ).Holds v V ↔ φ.Holds v V ∨ ψ.Holds v V := by
  simp only [or, Holds]
  tauto

@[simp] theorem holds_imp {φ ψ : MSO} : (imp φ ψ).Holds v V ↔ (φ.Holds v V → ψ.Holds v V) := by
  simp only [imp, Holds]
  tauto

@[simp] theorem holds_all {i : ℕ} {φ : MSO} :
    (all i φ).Holds v V ↔ ∀ n, φ.Holds (Function.update v i n) V := by
  simp [all, Holds]

@[simp] theorem holds_allSet {j : ℕ} {φ : MSO} :
    (allSet j φ).Holds v V ↔ ∀ A, φ.Holds v (Function.update V j A) := by
  simp [allSet, Holds]

theorem holds_bigAnd : ∀ {l : List MSO}, (bigAnd l).Holds v V ↔ ∀ φ ∈ l, φ.Holds v V
  | [] => by simp [bigAnd]
  | φ :: l => by simp [bigAnd, Holds, holds_bigAnd]

theorem holds_bigOr : ∀ {l : List MSO}, (bigOr l).Holds v V ↔ ∃ φ ∈ l, φ.Holds v V
  | [] => by simp [bigOr, Holds]
  | φ :: l => by simp [bigOr, holds_bigOr]

theorem holds_allSets {φ : MSO} : ∀ {l : List ℕ} {V : ℕ → Set ℕ},
    (allSets l φ).Holds v V ↔ ∀ V' : ℕ → Set ℕ, (∀ j, j ∉ l → V' j = V j) → φ.Holds v V'
  | [], V => by
    simp only [allSets, List.not_mem_nil, not_false_eq_true, forall_const]
    exact ⟨fun h V' hV' => (funext hV' : V' = V) ▸ h, fun h => h V fun _ => rfl⟩
  | j :: l, V => by
    simp only [allSets, holds_allSet, holds_allSets, List.mem_cons, not_or]
    constructor
    · intro h V' hV'
      refine h (V' j) V' fun j' hj' => ?_
      by_cases hjj : j' = j
      · subst hjj
        rw [Function.update_self]
      · rw [Function.update_of_ne hjj]
        exact hV' j' ⟨hjj, hj'⟩
    · intro h A V' hV'
      refine h V' fun j' ⟨hjj, hj'⟩ => ?_
      rw [hV' j' hj', Function.update_of_ne hjj]

end MSO

/-- `x 1` and `x 2` are consecutive. -/
def succ12 : MSO := .and (.lt 1 2) (.not (.ex 3 (.and (.lt 1 3) (.lt 3 2))))

/-- The body of `periodicFormula`: if `X 0` contains `0` and the sets `X s` follow the counting
automaton (`y ∈ X s` gives `y + 1 ∈ X (wrap s)`), then `x 0` lies in some `X s` with `f s`. -/
def periodicBody (f : ℕ → Bool) (N P : ℕ) : MSO :=
  MSO.imp
    (.and
      (MSO.all 1 (MSO.imp (.not (.ex 3 (.lt 3 1))) (.mem 1 0)))
      (MSO.all 1 (MSO.all 2 (MSO.imp succ12 (MSO.bigAnd ((List.range (N + P)).map fun s =>
        MSO.imp (.mem 1 s) (.mem 2 (wrap N P s))))))))
    (MSO.bigOr (((List.range (N + P)).filter fun s => f s).map fun s => .mem 0 s))

/-- The formula that defines `{t | f t}` for an eventually periodic `f`: the body, for all set
variables below `N + P`. -/
def periodicFormula (f : ℕ → Bool) (N P : ℕ) : MSO :=
  MSO.allSets (List.range (N + P)) (periodicBody f N P)

theorem holds_periodicBody {f : ℕ → Bool} {N P n : ℕ} (V : ℕ → Set ℕ) :
    (periodicBody f N P).Holds (fun _ => n) V ↔
      ((0 ∈ V 0 ∧ ∀ y s, s < N + P → y ∈ V s → y + 1 ∈ V (wrap N P s)) →
        ∃ s, s < N + P ∧ f s = true ∧ n ∈ V s) := by
  simp only [periodicBody, succ12, MSO.holds_imp, MSO.holds_all, MSO.holds_bigAnd,
    MSO.holds_bigOr, MSO.Holds, List.forall_mem_map, Function.update_apply]
  simp only [List.mem_map, List.mem_range, List.mem_filter, exists_exists_and_eq_and, MSO.Holds,
    show (1 : ℕ) ≠ 3 by norm_num, show (1 : ℕ) ≠ 2 by norm_num, show (2 : ℕ) ≠ 3 by norm_num,
    ite_false, ite_true]
  have hinit : (∀ y : ℕ, (¬ ∃ w, w < y) → y ∈ V 0) ↔ 0 ∈ V 0 := by
    constructor
    · intro h
      exact h 0 fun ⟨w, hw⟩ => Nat.not_lt_zero w hw
    · intro h y hy
      obtain rfl : y = 0 := by
        by_contra hne
        exact hy ⟨0, Nat.pos_of_ne_zero hne⟩
      exact h
  have hstep : (∀ y z : ℕ, (y < z ∧ ¬ ∃ w, y < w ∧ w < z) → ∀ s, s < N + P → y ∈ V s →
      z ∈ V (wrap N P s)) ↔ ∀ y s, s < N + P → y ∈ V s → y + 1 ∈ V (wrap N P s) := by
    constructor
    · intro h y s hs hy
      exact h y (y + 1) ⟨Nat.lt_succ_self y, fun ⟨w, h1, h2⟩ => by omega⟩ s hs hy
    · intro h y z ⟨hyz, hno⟩ s hs hy
      obtain rfl : z = y + 1 := by
        by_contra hne
        exact hno ⟨y + 1, by omega, by omega⟩
      exact h y s hs hy
  constructor
  · intro h ⟨h0, hs⟩
    obtain ⟨a, ⟨ha, hfa⟩, hn⟩ := h ⟨hinit.2 h0, hstep.2 hs⟩
    exact ⟨a, ha, hfa, hn⟩
  · intro h ⟨h0, hs⟩
    obtain ⟨a, ha, hfa, hn⟩ := h ⟨hinit.1 h0, hstep.1 hs⟩
    exact ⟨a, ⟨ha, hfa⟩, hn⟩

theorem holds_periodicFormula {f : ℕ → Bool} {N P : ℕ} (hP : 0 < P)
    (hf : ∀ t, N ≤ t → f (t + P) = f t) (n : ℕ) :
    (periodicFormula f N P).Holds (fun _ => n) (fun _ => ∅) ↔ f n = true := by
  rw [periodicFormula, MSO.holds_allSets]
  simp only [List.mem_range, holds_periodicBody]
  constructor
  · intro h
    -- the sets of the counting automaton itself
    obtain ⟨s, hs, hfs, hn⟩ := h (fun j => if j < N + P then {t | (cnt N P hP t : ℕ) = j} else ∅)
      (fun j hj => ite_eq_right hj)
      ⟨by rw [ite_eq_left (by omega)]; rfl, fun y s hs hy => by
        rw [ite_eq_left hs] at hy
        rw [ite_eq_left (wrap_lt hP s)]
        show (cnt N P hP (y + 1) : ℕ) = wrap N P s
        rw [← hy]
        rfl⟩
    rw [ite_eq_left hs] at hn
    rw [← apply_cnt hP hf n, show (cnt N P hP n : ℕ) = s from hn]
    exact hfs
  · intro hfn V _ ⟨h0, hstep⟩
    -- every family that follows the automaton contains its run
    have hrun : ∀ t, t ∈ V (cnt N P hP t) := by
      intro t
      induction t with
      | zero => exact h0
      | succ t ih => exact hstep t _ (cnt N P hP t).2 ih
    exact ⟨cnt N P hP n, (cnt N P hP n).2, by rw [apply_cnt hP hf n]; exact hfn, hrun n⟩

/-- **Eventually periodic sets are MSO-definable.** -/
theorem msoDefinable_of_eventuallyPeriodic {f : ℕ → Bool} (h : EventuallyPeriodic f) :
    MSODefinable {t | f t = true} := by
  obtain ⟨N, P, hP, hf⟩ := h
  exact ⟨periodicFormula f N P, fun n => (holds_periodicFormula hP hf n).symm⟩

/-! ### Problem 1 in monadic second-order logic -/

/-- A set of naturals is MSO-definable over `(ℕ, <)` iff it is eventually periodic. -/
theorem eventuallyPeriodic_iff_msoDefinable (f : ℕ → Bool) :
    EventuallyPeriodic f ↔ MSODefinable {t | f t = true} :=
  ⟨msoDefinable_of_eventuallyPeriodic, eventuallyPeriodic_of_msoDefinable⟩

/-- **Monadic second-order logic.** Problem 1 holds iff the set of black times of the center column is not
definable in monadic second-order logic over `(ℕ, <)`. -/
theorem problem1_iff_not_msoDefinable :
    Rule30Prize.Problem1 ↔ ¬ MSODefinable {t | c t = true} := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_msoDefinable]

end Rule30Equivalents.MonadicLogic
