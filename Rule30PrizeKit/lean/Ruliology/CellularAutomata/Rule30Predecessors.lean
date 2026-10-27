module

/-!
# Rule 30 on a cyclic register: a corrected Feynman theorem

Wolfram, *Random Sequence Generation by Cellular Automata* (1986, pp. 150–151),
reports a result of C. and R. Feynman (private communication) about predecessors under rule 30
on a cyclic register. The paper prints the condition backwards. The corrected statement, checked
by brute force for `N ≤ 20` and proved here for every register length `N ≥ 1`, is:

* every configuration has `0`, `1`, `2` or `3` predecessors;
* exactly `3` iff it is all `1`s and `3 ∣ N` (`predCount_eq_three_iff`);
* exactly `1` iff some cyclic run of `1`s between consecutive `0`s has length `≡ 1 (mod 3)`
  (`predCount_eq_one_iff`). For a single `0`, the run wraps around to that same `0`.
* otherwise `0` or `2`.

`HasPreds y (predCount y)` (`hasPreds`) says `predCount` really counts predecessors: there is a
duplicate-free list of exactly that many registers `x`, consisting of exactly those with
`step x = y`.

**Proof.** Rule 30 is left-permutive: `x_{i-1} = y_i xor (x_i || x_{i+1})`. So `(x_i, x_{i+1})`
determines `(x_{i-1}, x_i)` through the *transfer map* `T y_i`.
- Predecessors of `y` correspond to fixed points of `F y = T y₀ ∘ ⋯ ∘ T y_{N-1}` on the four
  states (`step_eq_iff`).
- `#Fix (f ∘ g) = #Fix (g ∘ f)`, so the count is invariant under rotating the register.
- After rotating to a `0`, `F` is a product of block maps `M a = T 0 ∘ (T 1)^a`, one per run
  `0 1^a`. These depend only on `a % 3`.
- Products containing `M 1` lie in a 14-element set `J` whose members each have exactly one fixed
  point. Products of `M 0` and `M 2` lie in a 10-element set `K` whose members have `0` or `2`.
  These finite facts are checked by `decide`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30

/-! ### Rule 30 on a cyclic register -/

/-- Rule 30: the new cell is `left xor (center || right)`. -/
def rule (l c r : Bool) : Bool := xor l (c || r)

/-- Rule 30 on a segment: a word of length `m + 2` maps to a word of length `m`. -/
def lin : List Bool → List Bool
  | a :: b :: c :: rest => rule a b c :: lin (b :: c :: rest)
  | _ => []

/-- The register `x` with its cyclic neighbours attached: `x_{N-1}, x_0, …, x_{N-1}, x_0`. -/
def ext (x : List Bool) : List Bool := x.getLastD false :: (x ++ [x.headD false])

/-- One step of rule 30 on a cyclic register. Cell `i` sees cells `i - 1`, `i`, `i + 1` mod `N`. -/
def step (x : List Bool) : List Bool := lin (ext x)

example : step [false, false, true, false, false] = [false, true, true, true, false] := by decide

/-! ### Transfer maps -/

/-- A state is a pair of adjacent cells `(x_i, x_{i+1})`. -/
abbrev State := Bool × Bool

/-- From `(x_{i+1}, x_{i+2})` and the output `y_i`, recover `(x_i, x_{i+1})`. -/
def T (b : Bool) (s : State) : State := (xor b (s.1 || s.2), s.1)

/-- `F y = T y₀ ∘ T y₁ ∘ ⋯ ∘ T y_{N-1}`. -/
def F (y : List Bool) (s : State) : State := y.foldr T s

/-- `back y s` is the unique word `w` with `lin w = y` that ends in `s`. -/
def back : List Bool → State → List Bool
  | [], s => [s.1, s.2]
  | b :: y, s =>
    match back y s with
    | p :: q :: rest => xor b (p || q) :: p :: q :: rest
    | w => w

theorem back_shape : ∀ (y : List Bool) (s : State),
    ∃ rest, back y s = (F y s).1 :: (F y s).2 :: rest
  | [], s => ⟨[], rfl⟩
  | b :: y, s => by
    obtain ⟨rest, h⟩ := back_shape y s
    exact ⟨(F y s).2 :: rest, by simp [back, h, F, T]⟩

theorem back_cons (b : Bool) (y : List Bool) (s : State) :
    back (b :: y) s = xor b ((F y s).1 || (F y s).2) :: back y s := by
  obtain ⟨rest, h⟩ := back_shape y s
  simp [back, h]

theorem rule_xor (b p q : Bool) : rule (xor b (p || q)) p q = b := by
  cases b <;> cases p <;> cases q <;> rfl

theorem lin_back : ∀ (y : List Bool) (s : State), lin (back y s) = y
  | [], _ => rfl
  | b :: y, s => by
    obtain ⟨rest, h⟩ := back_shape y s
    rw [back_cons, h]
    simp only [lin]
    rw [← h, lin_back y s, rule_xor]

theorem back_end : ∀ (y : List Bool) (s : State),
    ∃ u, u.length = y.length ∧ back y s = u ++ [s.1, s.2]
  | [], _ => ⟨[], rfl, rfl⟩
  | b :: y, s => by
    obtain ⟨u, hu, h⟩ := back_end y s
    exact ⟨_ :: u, by simp [hu], by rw [back_cons, h]; rfl⟩

/-- A word `u ++ [a, b]` with `lin (u ++ [a, b]) = y` is `back y (a, b)`. -/
theorem eq_back : ∀ (y u : List Bool) (a b : Bool), u.length = y.length →
    lin (u ++ [a, b]) = y → u ++ [a, b] = back y (a, b)
  | [], u, a, b, hu, _ => by
    rw [List.length_eq_zero_iff.1 hu]; rfl
  | c :: y, u, a, b, hu, hl => by
    match u, hu with
    | x :: u₁, hu =>
      have hu₁ : u₁.length = y.length := by simp at hu; omega
      obtain ⟨p, q, rest, hpq⟩ : ∃ p q rest, u₁ ++ [a, b] = p :: q :: rest := by
        cases u₁ with
        | nil => exact ⟨a, b, [], rfl⟩
        | cons p u₂ => cases u₂ with
          | nil => exact ⟨p, a, [b], rfl⟩
          | cons q u₃ => exact ⟨p, q, u₃ ++ [a, b], rfl⟩
      rw [List.cons_append, hpq] at hl
      simp only [lin] at hl
      injection hl with hc hy
      rw [← hpq] at hy
      have ih := eq_back y u₁ a b hu₁ hy
      rw [List.cons_append, ih, back_cons]
      obtain ⟨r, hr⟩ := back_shape y (a, b)
      rw [← ih, hpq] at hr
      injection hr with h1 h2
      injection h2 with h2 _
      congr 1
      rw [← h1, ← h2, ← hc]
      cases x <;> cases p <;> cases q <;> rfl

/-! ### Predecessors are fixed points of the transfer map -/

/-- The predecessor determined by a fixed state `s` of `F y`. -/
def pred (y : List Bool) (s : State) : List Bool := ((back y s).drop 1).take y.length

theorem take_append_pair (u : List Bool) (a b : Bool) : (u ++ [a, b]).take (u.length + 1) = u ++ [a] := by
  induction u with
  | nil => rfl
  | cons c u ih => simp [ih]

/-- For a fixed state `s`, `pred y s` has the right length, its cyclic extension is `back y s`,
and it ends in `s.1` and starts with `s.2`. -/
theorem pred_spec (y : List Bool) (hy : y ≠ []) {s : State} (hfix : F y s = s) :
    (pred y s).length = y.length ∧ ext (pred y s) = back y s ∧
      (pred y s).getLastD false = s.1 ∧ (pred y s).headD false = s.2 := by
  obtain ⟨u, hu, hend⟩ := back_end y s
  obtain ⟨rest, hstart⟩ := back_shape y s
  rw [hfix] at hstart
  obtain ⟨a, u₁, rfl⟩ : ∃ a u₁, u = a :: u₁ := by
    cases u with
    | nil => cases y with
      | nil => exact absurd rfl hy
      | cons _ _ => simp at hu
    | cons a u₁ => exact ⟨a, u₁, rfl⟩
  rw [hend] at hstart
  simp only [List.cons_append] at hstart
  injection hstart with ha hb
  have hu₁ : u₁.length + 1 = y.length := by simpa using hu
  have hpred : pred y s = u₁ ++ [s.1] := by
    rw [pred, hend, ← hu₁]
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero]
    exact take_append_pair u₁ s.1 s.2
  have hhead : (u₁ ++ [s.1]).headD false = s.2 := by
    cases u₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hb
      simp [hb.1]
    | cons c u₂ =>
      simp only [List.cons_append, List.cons.injEq] at hb
      simp [hb.1]
  have hlast : (u₁ ++ [s.1]).getLastD false = s.1 := by
    simp [List.getLastD_eq_getLast?]
  rw [hpred]
  refine ⟨by simp [← hu₁], ?_, hlast, hhead⟩
  rw [hend, ext, hhead, hlast, ha]
  simp

/-- **Transfer theorem.** For a nonempty register `y`, the registers `x` with `step x = y` are
exactly the words `pred y s` for fixed points `s` of `F y`. -/
theorem step_eq_iff (y : List Bool) (hy : y ≠ []) (x : List Bool) :
    (x.length = y.length ∧ step x = y) ↔ ∃ s, F y s = s ∧ x = pred y s := by
  constructor
  · rintro ⟨hl, hs⟩
    obtain ⟨h, t, rfl⟩ : ∃ h t, x = h :: t := by
      cases x with
      | nil => cases y with
        | nil => exact absurd rfl hy
        | cons _ _ => simp at hl
      | cons h t => exact ⟨h, t, rfl⟩
    have hne : (h :: t) ≠ [] := List.cons_ne_nil h t
    have hsplit : (h :: t).dropLast ++ [(h :: t).getLast hne] = h :: t :=
      List.dropLast_concat_getLast hne
    have hext : ext (h :: t) = ((h :: t).getLast hne :: (h :: t).dropLast) ++
        [(h :: t).getLast hne, h] := by
      have e : (h :: t).getLastD false = (h :: t).getLast hne := by
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
      rw [ext, e]
      simp only [List.headD_cons, List.cons_append]
      congr 1
      rw [show (h :: t).dropLast ++ [(h :: t).getLast hne, h] =
          ((h :: t).dropLast ++ [(h :: t).getLast hne]) ++ [h] by simp, hsplit]
      rfl
    have hu : ((h :: t).getLast hne :: (h :: t).dropLast).length = y.length := by
      rw [← hl]; simp
    have hw := eq_back y _ _ h hu (by rw [← hext]; exact hs)
    have hstart : back y ((h :: t).getLast hne, h) = (h :: t).getLast hne :: h :: (t ++ [h]) := by
      rw [← hw, ← hext]; rfl
    refine ⟨((h :: t).getLast hne, h), ?_, ?_⟩
    · obtain ⟨rest, hr⟩ := back_shape y ((h :: t).getLast hne, h)
      rw [hstart] at hr
      injection hr with h1 h2
      injection h2 with h2 _
      exact Prod.ext h1.symm h2.symm
    · rw [pred, hstart, ← hl]
      simp
  · rintro ⟨s, hfix, rfl⟩
    obtain ⟨hlen, hext, -, -⟩ := pred_spec y hy hfix
    exact ⟨hlen, by rw [step, hext, lin_back]⟩

/-! ### Counting predecessors -/

/-- The four states. -/
def states : List State := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_states (s : State) : s ∈ states := by
  rcases s with ⟨_ | _, _ | _⟩ <;> decide

/-- The fixed points of `F y`. -/
def fixedStates (y : List Bool) : List State := states.filter (fun s => F y s == s)

/-- The predecessors of `y`, one for each fixed point of `F y`. -/
def preds (y : List Bool) : List (List Bool) := (fixedStates y).map (pred y)

/-- The number of predecessors of `y`: the number of fixed points of `F y`. -/
def predCount (y : List Bool) : Nat := (fixedStates y).length

/-- `y` has exactly `k` predecessors: a duplicate-free list of `k` registers consisting of
exactly the `x` with `step x = y`. -/
def HasPreds (y : List Bool) (k : Nat) : Prop :=
  ∃ L : List (List Bool), L.Nodup ∧ L.length = k ∧ ∀ x, x ∈ L ↔ (x.length = y.length ∧ step x = y)

/-- Two duplicate-free lists with the same members have the same length. -/
theorem length_eq_of_nodup {l₁ l₂ : List (List Bool)} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.length = l₂.length :=
  (List.perm_iff_count.2 fun a => by rw [h₁.count, h₂.count]; simp only [h a]).length_eq

theorem HasPreds.unique {y : List Bool} {k k' : Nat} (h : HasPreds y k) (h' : HasPreds y k') :
    k = k' := by
  obtain ⟨L, hL, rfl, hm⟩ := h
  obtain ⟨L', hL', rfl, hm'⟩ := h'
  exact length_eq_of_nodup hL hL' fun x => by rw [hm, hm']

theorem nodup_map_of_inj {α β : Type} (f : α → β) : ∀ {l : List α}, l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, hinj => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj f hl.2 fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    exact hl.1 (hinj a (by simp) b (by simp [hb]) hfb.symm ▸ hb)

/-- `predCount y` is the number of predecessors of `y`. -/
theorem hasPreds (y : List Bool) (hy : y ≠ []) : HasPreds y (predCount y) := by
  refine ⟨preds y, ?_, by simp [preds, predCount], ?_⟩
  · -- `pred y` is injective on fixed points: `s` is read off from its first and last cells
    refine nodup_map_of_inj _ (List.Nodup.sublist List.filter_sublist (by decide)) ?_
    intro s hs t ht hst
    simp only [fixedStates, List.mem_filter, beq_iff_eq] at hs ht
    obtain ⟨-, -, hs1, hs2⟩ := pred_spec y hy hs.2
    obtain ⟨-, -, ht1, ht2⟩ := pred_spec y hy ht.2
    rw [hst] at hs1 hs2
    exact Prod.ext (hs1.symm.trans ht1) (hs2.symm.trans ht2)
  · intro x
    rw [step_eq_iff y hy x]
    simp only [preds, fixedStates, List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨s, ⟨-, hs⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨mem_states s, hs⟩, rfl⟩

/-! ### Transfer maps as finite data -/

/-- A map on states, recorded by its values on `(F,F), (F,T), (T,F), (T,T)`. -/
abbrev Fn := State × State × State × State

def Fn.app (f : Fn) : State → State
  | (false, false) => f.1
  | (false, true) => f.2.1
  | (true, false) => f.2.2.1
  | (true, true) => f.2.2.2

def Fn.ofFun (g : State → State) : Fn :=
  (g (false, false), g (false, true), g (true, false), g (true, true))

theorem Fn.app_ofFun (g : State → State) (s : State) : (Fn.ofFun g).app s = g s := by
  rcases s with ⟨_ | _, _ | _⟩ <;> rfl

def Fn.comp (f g : Fn) : Fn := Fn.ofFun (fun s => f.app (g.app s))

theorem Fn.comp_assoc (f g h : Fn) : (f.comp g).comp h = f.comp (g.comp h) := by
  simp [Fn.comp, Fn.app_ofFun]

/-- The number of fixed points. -/
def Fn.fix (f : Fn) : Nat := (states.filter (fun s => f.app s == s)).length

/-- `F y` as finite data. -/
def fn (y : List Bool) : Fn := Fn.ofFun (F y)

theorem predCount_eq (y : List Bool) : predCount y = (fn y).fix := by
  simp [predCount, fixedStates, Fn.fix, fn, Fn.app_ofFun]

theorem fn_append (y z : List Bool) : fn (y ++ z) = (fn y).comp (fn z) := by
  simp only [fn, Fn.comp, Fn.app_ofFun]
  congr 1
  funext s
  simp [F, List.foldr_append]

/-! ### Rotation invariance -/

/-- Rotate a register by one cell. -/
def rot1 : List Bool → List Bool
  | [] => []
  | b :: r => r ++ [b]

/-- Rotate a register by `k` cells. -/
def rotate : List Bool → Nat → List Bool
  | y, 0 => y
  | y, k + 1 => rotate (rot1 y) k

/-- All maps on states. -/
def allFn : List Fn :=
  states.flatMap fun a => states.flatMap fun b => states.flatMap fun c => states.map fun d =>
    (a, b, c, d)

theorem mem_allFn (f : Fn) : f ∈ allFn := by
  obtain ⟨a, b, c, d⟩ := f
  simp only [allFn, List.mem_flatMap, List.mem_map]
  exact ⟨a, mem_states a, b, mem_states b, c, mem_states c, d, mem_states d, rfl⟩

/-- `#Fix (T b ∘ g) = #Fix (g ∘ T b)`, checked over all `g`. -/
theorem fix_comm_T : ∀ b : Bool, ∀ g ∈ allFn, ((fn [b]).comp g).fix = (g.comp (fn [b])).fix := by
  decide +kernel

theorem predCount_rot1 (y : List Bool) : predCount (rot1 y) = predCount y := by
  cases y with
  | nil => rfl
  | cons b r =>
    simp only [rot1, predCount_eq]
    rw [fn_append, show b :: r = [b] ++ r from rfl, fn_append]
    exact (fix_comm_T b (fn r) (mem_allFn _)).symm

theorem predCount_rotate (y : List Bool) (k : Nat) : predCount (rotate y k) = predCount y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [rotate, ih, predCount_rot1]

theorem length_rotate (y : List Bool) (k : Nat) : (rotate y k).length = y.length := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [rotate, ih]
    cases y <;> simp [rot1]

theorem rotate_append (l m : List Bool) : rotate (l ++ m) l.length = m ++ l := by
  induction l generalizing m with
  | nil => simp [rotate]
  | cons c l ih =>
    rw [List.length_cons, rotate, List.cons_append, rot1, List.append_assoc, ih]
    simp

theorem rotate_ne_nil {y : List Bool} (hy : y ≠ []) (k : Nat) : rotate y k ≠ [] := by
  intro h
  have := length_rotate y k
  rw [h] at this
  exact hy (List.length_eq_zero_iff.1 this.symm)

/-! ### Blocks `0 1^a` -/

/-- The register `0 1^{a₁} 0 1^{a₂} ⋯ 0 1^{a_k}`. -/
def blocks : List Nat → List Bool
  | [] => []
  | a :: as => false :: List.replicate a true ++ blocks as

/-- The block map `M a = T 0 ∘ (T 1)^a`. -/
def M (a : Nat) : Fn := fn (false :: List.replicate a true)

theorem fn_blocks_cons (a : Nat) (as : List Nat) :
    fn (blocks (a :: as)) = (M a).comp (fn (blocks as)) := by
  rw [blocks, M, fn_append]

theorem M_add_three (a : Nat) : M (a + 3) = M a := by
  have e : false :: List.replicate (a + 3) true = [false, true, true, true] ++ List.replicate a true := by
    simp [List.replicate_succ]
  have e' : false :: List.replicate a true = [false] ++ List.replicate a true := rfl
  rw [M, M, e, e', fn_append, fn_append]
  congr 1

theorem M_mod (a : Nat) : M a = M (a % 3) := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases h : a < 3
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
      rw [M_add_three, ih b (by omega), Nat.add_mod_right]

/-! ### The finite semigroup facts (checked by `decide`) -/

/-- The 14 products of block maps that contain `M 1`: each has exactly one fixed point. -/
def J : List Fn := [
  ((false, false), (false, false), (false, false), (false, false)),
  ((false, false), (true, false), (false, false), (false, false)),
  ((false, false), (true, true), (false, false), (false, false)),
  ((true, false), (false, false), (true, false), (true, false)),
  ((true, false), (true, false), (true, false), (true, false)),
  ((true, false), (true, false), (true, true), (true, true)),
  ((true, false), (true, true), (true, false), (true, false)),
  ((true, false), (true, true), (true, true), (true, true)),
  ((true, true), (false, false), (true, false), (true, false)),
  ((true, true), (false, false), (true, true), (true, true)),
  ((true, true), (true, false), (true, false), (true, false)),
  ((true, true), (true, false), (true, true), (true, true)),
  ((true, true), (true, true), (true, false), (true, false)),
  ((true, true), (true, true), (true, true), (true, true))]

/-- The 10 products of `M 0` and `M 2`: each has zero or two fixed points. -/
def K : List Fn := [
  ((false, false), (false, false), (true, false), (true, false)),
  ((false, false), (false, false), (true, true), (true, true)),
  ((false, false), (true, false), (true, false), (true, false)),
  ((false, false), (true, false), (true, true), (true, true)),
  ((false, false), (true, true), (true, true), (true, true)),
  ((true, false), (false, false), (false, false), (false, false)),
  ((true, false), (true, false), (false, false), (false, false)),
  ((true, false), (true, true), (false, false), (false, false)),
  ((true, true), (false, false), (false, false), (false, false)),
  ((true, true), (true, true), (false, false), (false, false))]

theorem M1_mem_J : M 1 ∈ J := by decide
theorem M0_mem_K : M 0 ∈ K := by decide
theorem M2_mem_K : M 2 ∈ K := by decide

theorem J_closed_check : J.all (fun g => (J.elem ((M 0).comp g) && J.elem ((M 1).comp g)) &&
    J.elem ((M 2).comp g)) = true := by decide

theorem K_closed_check : K.all (fun g => (K.elem ((M 0).comp g) && K.elem ((M 2).comp g)) &&
    J.elem ((M 1).comp g)) = true := by decide

theorem J_closed : ∀ g ∈ J, (M 0).comp g ∈ J ∧ (M 1).comp g ∈ J ∧ (M 2).comp g ∈ J := by
  intro g hg
  have h := List.all_eq_true.1 J_closed_check g hg
  simp only [Bool.and_eq_true, List.elem_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem K_closed : ∀ g ∈ K, (M 0).comp g ∈ K ∧ (M 2).comp g ∈ K ∧ (M 1).comp g ∈ J := by
  intro g hg
  have h := List.all_eq_true.1 K_closed_check g hg
  simp only [Bool.and_eq_true, List.elem_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
theorem fix_J : ∀ g ∈ J, g.fix = 1 := by decide
theorem fix_K : ∀ g ∈ K, g.fix = 0 ∨ g.fix = 2 := by decide

theorem fn_blocks_single (a : Nat) : fn (blocks [a]) = M a := by
  simp [blocks, M]

theorem mod_three_cases (a : Nat) : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega

/-- Products of block maps with no run `≡ 1 (mod 3)` lie in `K`. -/
theorem fn_blocks_K : ∀ as : List Nat, as ≠ [] → (∀ a ∈ as, a % 3 ≠ 1) → fn (blocks as) ∈ K
  | [], hne, _ => absurd rfl hne
  | [a], _, h => by
    rw [fn_blocks_single, M_mod]
    have ha := h a (by simp)
    rcases mod_three_cases a with h0 | h1 | h2
    · rw [h0]; exact M0_mem_K
    · exact absurd h1 ha
    · rw [h2]; exact M2_mem_K
  | a :: b :: as, _, h => by
    rw [fn_blocks_cons, M_mod]
    have ih := fn_blocks_K (b :: as) (by simp) (fun c hc => h c (by simp [hc]))
    have ha := h a (by simp)
    rcases mod_three_cases a with h0 | h1 | h2
    · rw [h0]; exact (K_closed _ ih).1
    · exact absurd h1 ha
    · rw [h2]; exact (K_closed _ ih).2.1

/-- Products of block maps with a run `≡ 1 (mod 3)` lie in `J`. -/
theorem fn_blocks_J : ∀ as : List Nat, (∃ a ∈ as, a % 3 = 1) → fn (blocks as) ∈ J
  | [], h => by simp at h
  | [a], h => by
    simp only [List.mem_singleton, exists_eq_left] at h
    rw [fn_blocks_single, M_mod, h]
    exact M1_mem_J
  | a :: b :: as, h => by
    rw [fn_blocks_cons, M_mod]
    by_cases hrest : ∃ c ∈ b :: as, c % 3 = 1
    · have ih := fn_blocks_J (b :: as) hrest
      rcases mod_three_cases a with h0 | h1 | h2
      · rw [h0]; exact (J_closed _ ih).1
      · rw [h1]; exact (J_closed _ ih).2.1
      · rw [h2]; exact (J_closed _ ih).2.2
    · have hK := fn_blocks_K (b :: as) (by simp) (fun c hc hc1 => hrest ⟨c, hc, hc1⟩)
      have ha : a % 3 = 1 := by
        obtain ⟨c, hc, hc1⟩ := h
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hc1
        · exact absurd ⟨c, hc, hc1⟩ hrest
      rw [ha]
      exact (K_closed _ hK).2.2

theorem predCount_blocks_one {as : List Nat} (h : ∃ a ∈ as, a % 3 = 1) :
    predCount (blocks as) = 1 := by
  rw [predCount_eq]; exact fix_J _ (fn_blocks_J as h)

theorem predCount_blocks_other {as : List Nat} (hne : as ≠ []) (h : ∀ a ∈ as, a % 3 ≠ 1) :
    predCount (blocks as) = 0 ∨ predCount (blocks as) = 2 := by
  rw [predCount_eq]; exact fix_K _ (fn_blocks_K as hne h)

/-! ### The all-ones register -/

theorem fn_T1_cube : (fn [true, true, true]).comp (fn [true]) = fn [true] := by decide

theorem fn_replicate_add_three (n : Nat) :
    fn (List.replicate (n + 4) true) = fn (List.replicate (n + 1) true) := by
  have e₁ : List.replicate (n + 4) true = [true, true, true] ++ ([true] ++ List.replicate n true) := by
    simp [List.replicate_succ]
  have e₂ : List.replicate (n + 1) true = [true] ++ List.replicate n true := by
    simp [List.replicate_succ]
  rw [e₁, e₂, fn_append, fn_append, ← Fn.comp_assoc, fn_T1_cube]

theorem predCount_replicate_true : ∀ N : Nat, 0 < N →
    predCount (List.replicate N true) = if N % 3 = 0 then 3 else 0
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | n + 4, _ => by
    rw [predCount_eq, fn_replicate_add_three, ← predCount_eq, predCount_replicate_true (n + 1) (by omega)]
    have : (n + 4) % 3 = (n + 1) % 3 := by omega
    rw [this]

/-! ### Every register with a `0` is a rotation of a block register -/

theorem exists_blocks : ∀ r : List Bool, ∃ as : List Nat, as ≠ [] ∧ blocks as = false :: r
  | [] => ⟨[0], by simp, rfl⟩
  | true :: r => by
    obtain ⟨as, hne, h⟩ := exists_blocks r
    match as, hne, h with
    | a :: as', _, h =>
      refine ⟨(a + 1) :: as', by simp, ?_⟩
      simp only [blocks, List.cons_append, List.cons.injEq, true_and] at h ⊢
      simp [List.replicate_succ, h]
  | false :: r => by
    obtain ⟨as, hne, h⟩ := exists_blocks r
    exact ⟨0 :: as, by simp, by simp [blocks, h]⟩

theorem exists_rotate_blocks {y : List Bool} (hf : false ∈ y) :
    ∃ k as, as ≠ [] ∧ rotate y k = blocks as := by
  obtain ⟨l, m, rfl⟩ := List.append_of_mem hf
  obtain ⟨as, hne, h⟩ := exists_blocks (m ++ l)
  exact ⟨l.length, as, hne, by rw [rotate_append, h]; rfl⟩

theorem eq_replicate_of_not_mem {y : List Bool} (hf : false ∉ y) :
    y = List.replicate y.length true := by
  rw [List.eq_replicate_iff]
  refine ⟨rfl, fun b hb => ?_⟩
  cases b
  · exact absurd hb hf
  · rfl

/-! ### Main results -/

/-- Some cyclic run of `1`s between consecutive `0`s has length `≡ 1 (mod 3)`: some rotation
of `y` is `0 1^{a₁} 0 1^{a₂} ⋯ 0 1^{a_k}` with some `aᵢ % 3 = 1`. -/
def HasOneRun (y : List Bool) : Prop := ∃ k as, rotate y k = blocks as ∧ ∃ a ∈ as, a % 3 = 1

theorem predCount_cases (y : List Bool) (hy : y ≠ []) :
    predCount y = 0 ∨ predCount y = 1 ∨ predCount y = 2 ∨ predCount y = 3 := by
  by_cases hf : false ∈ y
  · obtain ⟨k, as, hne, hk⟩ := exists_rotate_blocks hf
    rw [← predCount_rotate y k, hk]
    by_cases hrun : ∃ a ∈ as, a % 3 = 1
    · exact Or.inr (Or.inl (predCount_blocks_one hrun))
    · rcases predCount_blocks_other hne (fun a ha h => hrun ⟨a, ha, h⟩) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
  · rw [eq_replicate_of_not_mem hf,
      predCount_replicate_true _ (List.length_pos_iff.2 hy)]
    split
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl rfl

/-- **Exactly one predecessor** iff some cyclic run of `1`s between `0`s has length
`≡ 1 (mod 3)`. -/
theorem predCount_eq_one_iff (y : List Bool) (hy : y ≠ []) : predCount y = 1 ↔ HasOneRun y := by
  constructor
  · intro h1
    by_cases hf : false ∈ y
    · obtain ⟨k, as, hne, hk⟩ := exists_rotate_blocks hf
      refine ⟨k, as, hk, ?_⟩
      by_cases hrun : ∃ a ∈ as, a % 3 = 1
      · exact hrun
      · have := predCount_blocks_other hne (fun a ha h => hrun ⟨a, ha, h⟩)
        rw [← hk, predCount_rotate] at this
        omega
    · have h3 := predCount_replicate_true y.length (List.length_pos_iff.2 hy)
      rw [← eq_replicate_of_not_mem hf] at h3
      rw [h3] at h1
      split at h1 <;> omega
  · rintro ⟨k, as, hk, hrun⟩
    rw [← predCount_rotate y k, hk, predCount_blocks_one hrun]

/-- **Exactly three predecessors** iff the register is all `1`s and `3 ∣ N`. -/
theorem predCount_eq_three_iff (y : List Bool) (hy : y ≠ []) :
    predCount y = 3 ↔ (y = List.replicate y.length true ∧ y.length % 3 = 0) := by
  by_cases hf : false ∈ y
  · have hne : y ≠ List.replicate y.length true := by
      intro h; rw [h] at hf; simp at hf
    obtain ⟨k, as, hasne, hk⟩ := exists_rotate_blocks hf
    rw [← predCount_rotate y k, hk]
    constructor
    · intro h3
      by_cases hrun : ∃ a ∈ as, a % 3 = 1
      · rw [predCount_blocks_one hrun] at h3; omega
      · rcases predCount_blocks_other hasne (fun a ha h => hrun ⟨a, ha, h⟩) with h | h <;> omega
    · rintro ⟨h, -⟩; exact absurd h hne
  · have hr := eq_replicate_of_not_mem hf
    have h3 := predCount_replicate_true y.length (List.length_pos_iff.2 hy)
    rw [← hr] at h3
    rw [h3]
    constructor
    · intro h; split at h
      · exact ⟨hr, by assumption⟩
      · omega
    · rintro ⟨-, h⟩; rw [ite_eq_left h]

/-- **The corrected Feynman theorem** for rule 30 on a cyclic register of `N ≥ 1` cells.
`predCount y` counts the predecessors of `y` (`hasPreds`). It is `0`, `1`, `2` or `3`; it is `1`
iff some cyclic run of `1`s between `0`s has length `≡ 1 (mod 3)`; and it is `3` iff `y` is all
`1`s with `3 ∣ N`. -/
theorem feynman (y : List Bool) (hy : y ≠ []) :
    HasPreds y (predCount y) ∧
    (predCount y = 0 ∨ predCount y = 1 ∨ predCount y = 2 ∨ predCount y = 3) ∧
    (predCount y = 1 ↔ HasOneRun y) ∧
    (predCount y = 3 ↔ (y = List.replicate y.length true ∧ y.length % 3 = 0)) :=
  ⟨hasPreds y hy, predCount_cases y hy, predCount_eq_one_iff y hy, predCount_eq_three_iff y hy⟩

end Rule30
end Ruliology.CellularAutomata
