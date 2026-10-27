module

public import Rule30Equivalents.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Nat.Log

/-!
# One-tape Turing machines: the `n log n` gap for unary input

**Hennie's theorem** (Trakhtenbrot 1964, Hennie 1965): a
deterministic one-tape Turing machine that decides a language in time `o(n log n)` decides a
regular language. For unary input this means the language is eventually periodic, so Problem 1
holds iff no one-tape machine decides `{1ⁿ : c(n) = 1}` in time `o(n log n)`
(`problem1_iff_no_fast_one_tape_decider`).

* `Machine`, `step`, `run`: a head on a two-way infinite tape, with a transition that writes a
  symbol and moves the head one cell left or right or leaves it; halting states are fixed. The
  states and symbols are arbitrary types, so that `OfflineGap` can reuse everything below. `TM`
  is the textbook one-tape machine: a `Machine` with finitely many states and tape symbols.
  `DecidesInTime M f T`: on input `1ⁿ` the machine has halted by step `T n`, in an accepting
  state iff `f n`.
* `cs X b T`: the crossing sequence of a run `X` at the boundary `b` (between cells `b − 1` and
  `b`) before time `T`, the states just after each crossing.
* `splice`: two halting runs with the same crossing sequence at `b₁` and at `b₂` can be cut there
  and joined. The joined run halts with the crossing sequences of the left run up to `b₁` and of
  the right run from `b₁` on, in the final state of the left run if the crossing sequence has even
  length and of the right run otherwise; it passes through every state of the left run on the
  left and of the right run on the right. The proof is a simulation invariant, `SpliceInv`.
* `DecidesInTime.eventuallyPeriodic_of_finite`: finitely many crossing sequences give eventual
  periodicity. By splicing, the values `f (a + r)` are determined by a finite type of the left
  length `a`, so two left lengths of the same type give a period.
* `DecidesInTime.time_lower_bound`, `DecidesInTime.bounded`: Hennie's counting. In a shortest input
  with a crossing sequence longer than `K`, the boundaries on each side of it have distinct crossing
  sequences, or cutting would give a shorter one. Few sequences are short, so the time is at least
  `(n / 4) · log_{q+1} (n / 4)`, which time `o(n log n)` rules out for large `K`.
* `periodicTM`: an eventually periodic `f` is decided in `n + 1` steps.

The proof never uses that the tape alphabet is finite. The space version is in `OfflineGap`.
-/

@[expose] public section

namespace Rule30Equivalents.OneTapeGap

open Ruliology.CellularAutomata

/-- A head move: one cell left, none, or one cell right. -/
inductive Move
  | left
  | stay
  | right

/-- The change of the head position. -/
def Move.shift : Move → ℤ
  | left => -1
  | stay => 0
  | right => 1

theorem Move.shift_cases (m : Move) : m.shift = 1 ∨ m.shift = -1 ∨ m.shift = 0 := by
  cases m <;> simp [Move.shift]

/-- A deterministic machine with one head on a two-way infinite tape, with arbitrary types of
states and symbols. Crossing sequences are studied at this generality: a machine with a read-only
input tape and a work tape is such a machine on its input tape, whose states are the work
configurations. -/
structure Machine where
  /-- States. -/
  Q : Type
  /-- Tape symbols. -/
  Γ : Type
  /-- The blank symbol. -/
  blank : Γ
  /-- The input symbol. -/
  one : Γ
  /-- The start state. -/
  start : Q
  /-- Halting states. -/
  halt : Q → Bool
  /-- Accepting states. -/
  accept : Q → Bool
  /-- New state, written symbol, and head move. -/
  δ : Q → Γ → Q × Γ × Move

/-- A deterministic one-tape Turing machine: finitely many states and tape symbols. -/
structure TM extends Machine where
  [instFintype : Fintype Q]
  [instFintypeΓ : Fintype Γ]

attribute [instance] TM.instFintype TM.instFintypeΓ

/-- A configuration: state, head position, tape. -/
structure Cfg (M : Machine) where
  q : M.Q
  h : ℤ
  tape : ℤ → M.Γ

variable {M : Machine}

theorem Cfg.ext' {x y : Cfg M} (hq : x.q = y.q) (hh : x.h = y.h) (ht : x.tape = y.tape) :
    x = y := by
  cases x; cases y
  simp only at hq hh ht
  subst hq hh ht
  rfl

/-- One step; a halting state stays put. -/
def step (c : Cfg M) : Cfg M :=
  if M.halt c.q then c else
    ⟨(M.δ c.q (c.tape c.h)).1, c.h + (M.δ c.q (c.tape c.h)).2.2.shift,
      Function.update c.tape c.h (M.δ c.q (c.tape c.h)).2.1⟩

/-- The input `1ⁿ` on cells `0, …, n − 1`, with the head on cell `0`. -/
def init (M : Machine) (n : ℕ) : Cfg M :=
  ⟨M.start, 0, fun i => if 0 ≤ i ∧ i < n then M.one else M.blank⟩

/-- The run on input `1ⁿ`. -/
def run (M : Machine) (n t : ℕ) : Cfg M := step^[t] (init M n)

theorem run_succ (n t : ℕ) : run M n (t + 1) = step (run M n t) := by
  rw [run, run, Function.iterate_succ_apply']

theorem step_eq {c : Cfg M} (h : M.halt c.q = false) :
    step c = ⟨(M.δ c.q (c.tape c.h)).1, c.h + (M.δ c.q (c.tape c.h)).2.2.shift,
      Function.update c.tape c.h (M.δ c.q (c.tape c.h)).2.1⟩ := by
  simp [step, h]

theorem step_of_halt {c : Cfg M} (h : M.halt c.q = true) : step c = c := by
  simp [step, h]

theorem step_q_of_not_halt {c : Cfg M} (h : M.halt c.q = false) :
    (step c).q = (M.δ c.q (c.tape c.h)).1 := by simp [step, h]

/-- The head moves at most one cell. -/
theorem step_h (c : Cfg M) : (step c).h = c.h + 1 ∨ (step c).h = c.h - 1 ∨ (step c).h = c.h := by
  unfold step
  split_ifs
  · simp
  · dsimp only
    have := Move.shift_cases (M.δ c.q (c.tape c.h)).2.2
    omega

/-- Only the scanned cell changes. -/
theorem step_tape_of_ne (c : Cfg M) {i : ℤ} (hi : i ≠ c.h) : (step c).tape i = c.tape i := by
  unfold step
  split_ifs <;> simp [Function.update_of_ne hi]

/-- Two configurations with the same state and scanned symbol take the same step: same new state,
same head move, same written symbol. -/
theorem step_congr {x y : Cfg M} (hq : x.q = y.q) (hc : x.tape x.h = y.tape y.h) :
    (step x).q = (step y).q ∧ (step x).h - x.h = (step y).h - y.h ∧
      (step x).tape x.h = (step y).tape y.h := by
  obtain ⟨xq, xh, xt⟩ := x
  obtain ⟨yq, yh, yt⟩ := y
  simp only at hq hc
  subst hq
  unfold step
  simp only [hc]
  split_ifs <;> simp [hc]

/-! ### Runs and crossing sequences -/

/-- `X` is a run: each configuration is the step of the previous one. -/
def IsRun (X : ℕ → Cfg M) : Prop := ∀ t, X (t + 1) = step (X t)

theorem isRun_run (n : ℕ) : IsRun (run M n) := run_succ n

/-! ### Runs on words

The input word `w ∈ α*`, written letter by letter through `enc : α → M.Γ`. -/

/-- The input word `w`, written letter by letter through `enc` on the cells `0, …, |w| - 1`,
blanks elsewhere, with the head on cell `0`. -/
def initW {α : Type*} (M : Machine) (enc : α → M.Γ) (w : List α) : Cfg M :=
  ⟨M.start, 0, fun i => if h : 0 ≤ i ∧ i < w.length then enc (w[i.toNat]'(by omega)) else M.blank⟩

/-- The run on the input `w`. -/
def runW {α : Type*} (M : Machine) (enc : α → M.Γ) (w : List α) (t : ℕ) : Cfg M :=
  step^[t] (initW M enc w)

theorem isRun_runW {α : Type*} (enc : α → M.Γ) (w : List α) : IsRun (runW M enc w) := fun t => by
  simp only [runW, Function.iterate_succ_apply']

theorem runW_zero {α : Type*} (enc : α → M.Γ) (w : List α) :
    runW M enc w 0 = initW M enc w := rfl

/-- The run crosses the boundary `b` (between cells `b − 1` and `b`) at step `t`. -/
def Cross (X : ℕ → Cfg M) (b : ℤ) (t : ℕ) : Prop := ¬ ((X t).h < b ↔ (X (t + 1)).h < b)

instance (X : ℕ → Cfg M) (b : ℤ) (t : ℕ) : Decidable (Cross X b t) := by
  unfold Cross; infer_instance

/-- The crossing sequence of `X` at `b` before time `T`: the states just after each crossing. -/
def cs (X : ℕ → Cfg M) (b : ℤ) (T : ℕ) : List M.Q :=
  ((List.range T).filter fun t => decide (Cross X b t)).map fun t => (X (t + 1)).q

theorem cs_zero (X : ℕ → Cfg M) (b : ℤ) : cs X b 0 = [] := rfl

theorem cs_succ (X : ℕ → Cfg M) (b : ℤ) (T : ℕ) :
    cs X b (T + 1) = cs X b T ++ (if Cross X b T then [(X (T + 1)).q] else []) := by
  unfold cs
  rw [List.range_succ, List.filter_append, List.map_append]
  by_cases h : Cross X b T <;> simp [h]

theorem cs_mono (X : ℕ → Cfg M) (b : ℤ) {T T' : ℕ} (h : T ≤ T') : (cs X b T) <+: (cs X b T') := by
  induction T' with
  | zero => obtain rfl : T = 0 := by omega
            exact List.prefix_refl _
  | succ T' ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [cs_succ]
      exact (ih (by omega)).trans (List.prefix_append _ _)
    · exact List.prefix_refl _

/-- A crossing moves the head from `b − 1` to `b` or back. -/
theorem cross_iff {X : ℕ → Cfg M} (hX : IsRun X) (b : ℤ) (t : ℕ) :
    Cross X b t ↔
      ((X t).h = b - 1 ∧ (X (t + 1)).h = b) ∨ ((X t).h = b ∧ (X (t + 1)).h = b - 1) := by
  unfold Cross
  rw [hX t]
  rcases step_h (X t) with h | h | h <;> rw [h] <;> omega

/-! ### General facts about runs -/

section Runs

variable {X : ℕ → Cfg M} (hX : IsRun X)
include hX

/-- A halted run stays put. -/
theorem eq_of_halt {s t : ℕ} (hs : M.halt (X s).q = true) (hst : s ≤ t) : X t = X s := by
  induction t with
  | zero => obtain rfl : s = 0 := by omega
            rfl
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le hst with h | rfl
    · rw [hX t, ih (by omega), step_of_halt hs]
    · rfl

theorem not_cross_of_halt {s t : ℕ} (hs : M.halt (X s).q = true) (hst : s ≤ t) (b : ℤ) :
    ¬ Cross X b t := by
  unfold Cross
  rw [eq_of_halt hX hs hst, eq_of_halt hX hs (by omega : s ≤ t + 1)]
  simp

omit hX in
/-- **Parity**: started left of `b`, the head is left of `b` iff it has crossed `b` an even number
of times. -/
theorem left_iff_even {b : ℤ} (h0 : (X 0).h < b) (t : ℕ) :
    (X t).h < b ↔ Even (cs X b t).length := by
  induction t with
  | zero => simpa [cs_zero] using h0
  | succ t ih =>
    rw [cs_succ]
    by_cases hc : Cross X b t
    · rw [ite_eq_left hc, List.length_append, List.length_singleton, Nat.even_add_one, ← ih]
      unfold Cross at hc
      tauto
    · rw [ite_eq_right hc, List.append_nil, ← ih]
      unfold Cross at hc
      tauto

omit hX in
theorem cs_eq_of_no_cross {b : ℤ} {s T : ℕ} (hsT : s ≤ T)
    (h : ∀ t, s ≤ t → t < T → ¬ Cross X b t) : cs X b T = cs X b s := by
  induction T with
  | zero => obtain rfl : s = 0 := by omega
            rfl
  | succ T ih =>
    rcases Nat.lt_or_eq_of_le hsT with hlt | rfl
    · rw [cs_succ, ite_eq_right (h T (by omega) (by omega)), List.append_nil,
        ih (by omega) fun t h1 h2 => h t h1 (by omega)]
    · rfl

omit hX in
/-- Without crossings the head stays on its side. -/
theorem side_const {b : ℤ} {s T : ℕ} (hsT : s ≤ T) (h : ∀ t, s ≤ t → t < T → ¬ Cross X b t) :
    ((X T).h < b ↔ (X s).h < b) := by
  induction T with
  | zero => obtain rfl : s = 0 := by omega
            rfl
  | succ T ih =>
    rcases Nat.lt_or_eq_of_le hsT with hlt | rfl
    · have := h T (by omega) (by omega)
      unfold Cross at this
      rw [← ih (by omega) fun t h1 h2 => h t h1 (by omega)]
      tauto
    · rfl

/-- While the head stays left of `b`, the cells from `b` on do not change. -/
theorem frozen_right {b : ℤ} {s T : ℕ} (hsT : s ≤ T) (h : ∀ t, s ≤ t → t < T → (X t).h < b)
    {i : ℤ} (hi : b ≤ i) : (X T).tape i = (X s).tape i := by
  induction T with
  | zero => obtain rfl : s = 0 := by omega
            rfl
  | succ T ih =>
    rcases Nat.lt_or_eq_of_le hsT with hlt | rfl
    · rw [hX T, step_tape_of_ne _ (by have := h T (by omega) (by omega); omega),
        ih (by omega) fun t h1 h2 => h t h1 (by omega)]
    · rfl

/-- While the head stays at `b` or right of it, the cells left of `b` do not change. -/
theorem frozen_left {b : ℤ} {s T : ℕ} (hsT : s ≤ T) (h : ∀ t, s ≤ t → t < T → b ≤ (X t).h)
    {i : ℤ} (hi : i < b) : (X T).tape i = (X s).tape i := by
  induction T with
  | zero => obtain rfl : s = 0 := by omega
            rfl
  | succ T ih =>
    rcases Nat.lt_or_eq_of_le hsT with hlt | rfl
    · rw [hX T, step_tape_of_ne _ (by have := h T (by omega) (by omega); omega),
        ih (by omega) fun t h1 h2 => h t h1 (by omega)]
    · rfl

omit hX in
/-- The next crossing of `b` after time `s`, when there is one before `T`. -/
theorem exists_next_cross {b : ℤ} {s T : ℕ} (hsT : s ≤ T)
    (hlen : (cs X b s).length < (cs X b T).length) :
    ∃ t, s ≤ t ∧ t < T ∧ Cross X b t ∧ ∀ u, s ≤ u → u < t → ¬ Cross X b u := by
  classical
  have hex : ∃ t, s ≤ t ∧ t < T ∧ Cross X b t := by
    by_contra hne
    push Not at hne
    have := cs_eq_of_no_cross hsT fun t h1 h2 => hne t h1 h2
    rw [this] at hlen
    exact lt_irrefl _ hlen
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2,
    fun u hu hut hc => Nat.find_min hex hut ⟨hu, by have := (Nat.find_spec hex).2.1; omega, hc⟩⟩

end Runs

/-- Two prefixes of one list with the same length are equal. -/
theorem eq_of_prefix_of_length_eq {α : Type*} {l₁ l₂ L : List α} (h₁ : l₁ <+: L) (h₂ : l₂ <+: L)
    (h : l₁.length = l₂.length) : l₁ = l₂ :=
  (List.prefix_of_prefix_length_le h₁ h₂ h.le).eq_of_length h

theorem cross_congr {X Y : ℕ → Cfg M} {s t : ℕ} {b b' : ℤ} (h0 : (X s).h - b = (Y t).h - b')
    (h1 : (X (s + 1)).h - b = (Y (t + 1)).h - b') : Cross X b s ↔ Cross Y b' t := by
  unfold Cross
  have e0 : (X s).h < b ↔ (Y t).h < b' := by omega
  have e1 : (X (s + 1)).h < b ↔ (Y (t + 1)).h < b' := by omega
  rw [e0, e1]

theorem cs_succ_congr {X Y : ℕ → Cfg M} {s t : ℕ} {b b' : ℤ} (hcs : cs X b s = cs Y b' t)
    (hcr : Cross X b s ↔ Cross Y b' t) (hq : (X (s + 1)).q = (Y (t + 1)).q) :
    cs X b (s + 1) = cs Y b' (t + 1) := by
  rw [cs_succ, cs_succ, hcs, hq]
  by_cases h : Cross X b s
  · rw [ite_eq_left h, ite_eq_left (hcr.1 h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (hcr.2 h')]

theorem not_cross_of_lt {X : ℕ → Cfg M} {t : ℕ} {b : ℤ} (h0 : (X t).h < b)
    (h1 : (X (t + 1)).h < b) : ¬ Cross X b t := by
  unfold Cross; tauto

theorem not_cross_of_ge {X : ℕ → Cfg M} {t : ℕ} {b : ℤ} (h0 : b ≤ (X t).h)
    (h1 : b ≤ (X (t + 1)).h) : ¬ Cross X b t := by
  unfold Cross; simp only [not_lt.2 h0, not_lt.2 h1]; tauto

/-- If the crossing sequence does not grow between `s` and `T`, nothing crosses in between. -/
theorem no_cross_of_length_eq {X : ℕ → Cfg M} {b : ℤ} {s T : ℕ}
    (hlen : (cs X b T).length = (cs X b s).length) : ∀ t, s ≤ t → t < T → ¬ Cross X b t := by
  intro t hst htT hc
  have h1 := (cs_mono X b hst).length_le
  have h2 := (cs_mono X b (by omega : t + 1 ≤ T)).length_le
  rw [cs_succ, ite_eq_left hc, List.length_append, List.length_singleton] at h2
  omega

theorem lt_of_no_cross {X : ℕ → Cfg M} {b : ℤ} {s t : ℕ} (hst : s ≤ t)
    (h : ∀ u, s ≤ u → u < t → ¬ Cross X b u) (hs : (X s).h < b) : (X t).h < b :=
  (side_const hst h).2 hs

theorem ge_of_no_cross {X : ℕ → Cfg M} {b : ℤ} {s t : ℕ} (hst : s ≤ t)
    (h : ∀ u, s ≤ u → u < t → ¬ Cross X b u) (hs : b ≤ (X s).h) : b ≤ (X t).h :=
  not_lt.1 fun ht => not_lt.2 hs ((side_const hst h).1 ht)

/-! ### Splicing two runs at equal crossing sequences -/

section Splice

variable {X Y Z : ℕ → Cfg M} {b₁ b₂ : ℤ} {TX TY : ℕ}

/-- The invariant of a splice. At time `τ` the run `Z` holds, left of `b₁`, the tape of `X` at
time `l`, and from `b₁` on, the tape of `Y` at time `r` from `b₂` on; its head and state are
those of the run on whose side the head is. -/
structure SpliceInv (X Y Z : ℕ → Cfg M) (b₁ b₂ : ℤ) (TX TY τ l r : ℕ) : Prop where
  csL : ∀ b, b ≤ b₁ → cs Z b τ = cs X b l
  csR : ∀ b, b₁ ≤ b → cs Z b τ = cs Y (b + (b₂ - b₁)) r
  bl : l ≤ TX
  br : r ≤ TY
  prog : τ ≤ l + r ∨ M.halt (Z τ).q = true
  tapeL : ∀ i, i < b₁ → (Z τ).tape i = (X l).tape i
  tapeR : ∀ i, b₁ ≤ i → (Z τ).tape i = (Y r).tape (i + (b₂ - b₁))
  left : (Z τ).h < b₁ → (Z τ).q = (X l).q ∧ (Z τ).h = (X l).h ∧ (Y r).h < b₂
  right : b₁ ≤ (Z τ).h → (Z τ).q = (Y r).q ∧ (Z τ).h + (b₂ - b₁) = (Y r).h ∧ b₁ ≤ (X l).h
  visL : ∀ t, t < l → (X t).h < b₁ → ∃ σ, (Z σ).q = (X t).q
  visR : ∀ t, t < r → b₂ ≤ (Y t).h → ∃ σ, (Z σ).q = (Y t).q

theorem SpliceInv.step_halt {τ l r : ℕ} (hZ : IsRun Z) (I : SpliceInv X Y Z b₁ b₂ TX TY τ l r)
    (hh : M.halt (Z τ).q = true) : SpliceInv X Y Z b₁ b₂ TX TY (τ + 1) l r := by
  have hZ1 : Z (τ + 1) = Z τ := by rw [hZ τ, step_of_halt hh]
  have hcs : ∀ b, cs Z b (τ + 1) = cs Z b τ := fun b => by
    rw [cs_succ, ite_eq_right (by unfold Cross; rw [hZ1]; simp), List.append_nil]
  refine ⟨fun b hb => (hcs b).trans (I.csL b hb), fun b hb => (hcs b).trans (I.csR b hb), I.bl,
    I.br, Or.inr (by rw [hZ1]; exact hh), ?_, ?_, ?_, ?_, I.visL, I.visR⟩ <;> rw [hZ1]
  exacts [I.tapeL, I.tapeR, I.left, I.right]

theorem SpliceInv.step_left {τ l r : ℕ} (hX : IsRun X) (hY : IsRun Y) (hZ : IsRun Z)
    (hXT : M.halt (X TX).q = true) (hC : cs X b₁ TX = cs Y b₂ TY)
    (I : SpliceInv X Y Z b₁ b₂ TX TY τ l r) (hh : M.halt (Z τ).q = false) (hL : (Z τ).h < b₁) :
    ∃ l' r', SpliceInv X Y Z b₁ b₂ TX TY (τ + 1) l' r' := by
  obtain ⟨hq, hpos, hYr⟩ := I.left hL
  have hsc : (Z τ).tape (Z τ).h = (X l).tape (X l).h := by rw [← hpos]; exact I.tapeL _ hL
  obtain ⟨h1, h2, h3⟩ := step_congr hq hsc
  rw [← hZ τ, ← hX l] at h1 h2 h3
  have hXh : (X (l + 1)).h = (Z (τ + 1)).h := by omega
  have hprog : τ ≤ l + r := I.prog.resolve_right (by simp [hh])
  have hlt : l < TX := by
    rcases Nat.lt_or_eq_of_le I.bl with h | h
    · exact h
    · subst h; rw [← hq, hh] at hXT; exact absurd hXT (by simp)
  have hmove := step_h (Z τ)
  rw [← hZ τ] at hmove
  have hb12 : b₁ + (b₂ - b₁) = b₂ := by omega
  have htL : ∀ i, i < b₁ → (Z (τ + 1)).tape i = (X (l + 1)).tape i := by
    intro i hi
    by_cases hiz : i = (Z τ).h
    · rw [hiz, h3, hpos]
    · rw [hZ τ, step_tape_of_ne _ hiz, hX l, step_tape_of_ne _ (by rw [← hpos]; exact hiz)]
      exact I.tapeL i hi
  have hcsL : ∀ b, b ≤ b₁ → cs Z b (τ + 1) = cs X b (l + 1) := fun b hb =>
    cs_succ_congr (I.csL b hb) (cross_congr (by omega) (by omega)) h1
  have hvisL : ∀ t, t < l + 1 → (X t).h < b₁ → ∃ σ, (Z σ).q = (X t).q := fun t ht hxt => by
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 ht) with h | rfl
    · exact I.visL t h hxt
    · exact ⟨τ, hq⟩
  rcases lt_or_ge (Z (τ + 1)).h b₁ with hL' | hR'
  · refine ⟨l + 1, r, hcsL, fun b hb => ?_, hlt, I.br, Or.inl (by omega), htL, fun i hi => ?_,
      fun _ => ⟨h1, hXh.symm, hYr⟩, fun h => absurd h (not_le.2 hL'), hvisL, I.visR⟩
    · rw [cs_succ, ite_eq_right (not_cross_of_lt (by omega) (by omega)), List.append_nil]
      exact I.csR b hb
    · rw [hZ τ, step_tape_of_ne _ (by omega)]
      exact I.tapeR i hi
  · have hz : (Z τ).h = b₁ - 1 := by omega
    have hz' : (Z (τ + 1)).h = b₁ := by omega
    have hcrX : Cross X b₁ l := by unfold Cross; omega
    have hlenX : (cs X b₁ (l + 1)).length = (cs X b₁ l).length + 1 := by
      rw [cs_succ, ite_eq_left hcrX, List.length_append, List.length_singleton]
    have hXY : cs X b₁ l = cs Y b₂ r := by rw [← I.csL b₁ le_rfl, I.csR b₁ le_rfl, hb12]
    have hpreX : cs X b₁ (l + 1) <+: cs Y b₂ TY := by rw [← hC]; exact cs_mono X b₁ hlt
    obtain ⟨r', hr', hr'T, hcrY, hnoY⟩ := exists_next_cross (X := Y) (b := b₂) I.br (by
      rw [← hXY]; have := hpreX.length_le; omega)
    have hYside : ∀ t, r ≤ t → t ≤ r' → (Y t).h < b₂ := fun t ht1 ht2 =>
      lt_of_no_cross ht1 (fun u hu1 hu2 => hnoY u hu1 (by omega)) hYr
    have hYcr := (cross_iff hY b₂ r').1 hcrY
    have hYr'h : (Y r').h = b₂ - 1 ∧ (Y (r' + 1)).h = b₂ := by
      have := hYside r' hr' le_rfl; omega
    have hcsY : cs Y b₂ r' = cs Y b₂ r := cs_eq_of_no_cross hr' hnoY
    have hpreY : cs Y b₂ (r' + 1) <+: cs Y b₂ TY := cs_mono Y b₂ hr'T
    have hlenY : (cs Y b₂ (r' + 1)).length = (cs Y b₂ r).length + 1 := by
      rw [cs_succ, ite_eq_left hcrY, List.length_append, List.length_singleton, hcsY]
    have hXYs : cs X b₁ (l + 1) = cs Y b₂ (r' + 1) :=
      eq_of_prefix_of_length_eq hpreX hpreY (by rw [hlenX, hlenY, hXY])
    have hq' : (X (l + 1)).q = (Y (r' + 1)).q := by
      have := hXYs
      rw [cs_succ, ite_eq_left hcrX, cs_succ, ite_eq_left hcrY, hcsY, hXY] at this
      simpa using this
    refine ⟨l + 1, r' + 1, hcsL, fun b hb => ?_, hlt, hr'T, Or.inl (by omega), htL, fun i hi => ?_,
      fun h => absurd h (by omega), fun _ => ⟨h1.trans hq', by omega, by omega⟩, hvisL,
      fun t ht hyt => ?_⟩
    · have hno : cs Y (b + (b₂ - b₁)) r' = cs Y (b + (b₂ - b₁)) r :=
        cs_eq_of_no_cross hr' fun t ht1 ht2 => not_cross_of_lt
          (by have := hYside t ht1 (by omega); omega)
          (by have := hYside (t + 1) (by omega) (by omega); omega)
      exact cs_succ_congr ((I.csR b hb).trans hno.symm) (cross_congr (by omega) (by omega))
        (h1.trans hq')
    · rw [hZ τ, step_tape_of_ne _ (by omega), I.tapeR i hi]
      exact (frozen_right hY (by omega : r ≤ r' + 1)
        (fun t ht1 ht2 => hYside t ht1 (by omega)) (by omega)).symm
    · rcases lt_or_ge t r with h | h
      · exact I.visR t h hyt
      · exact absurd hyt (not_le.2 (hYside t h (by omega)))

theorem SpliceInv.step_right {τ l r : ℕ} (hX : IsRun X) (hY : IsRun Y) (hZ : IsRun Z)
    (hYT : M.halt (Y TY).q = true) (hC : cs X b₁ TX = cs Y b₂ TY)
    (I : SpliceInv X Y Z b₁ b₂ TX TY τ l r) (hh : M.halt (Z τ).q = false) (hR : b₁ ≤ (Z τ).h) :
    ∃ l' r', SpliceInv X Y Z b₁ b₂ TX TY (τ + 1) l' r' := by
  obtain ⟨hq, hpos, hXl⟩ := I.right hR
  have hsc : (Z τ).tape (Z τ).h = (Y r).tape (Y r).h := by rw [← hpos]; exact I.tapeR _ hR
  obtain ⟨h1, h2, h3⟩ := step_congr hq hsc
  rw [← hZ τ, ← hY r] at h1 h2 h3
  have hYh : (Y (r + 1)).h = (Z (τ + 1)).h + (b₂ - b₁) := by omega
  have hprog : τ ≤ l + r := I.prog.resolve_right (by simp [hh])
  have hlt : r < TY := by
    rcases Nat.lt_or_eq_of_le I.br with h | h
    · exact h
    · subst h; rw [← hq, hh] at hYT; exact absurd hYT (by simp)
  have hmove := step_h (Z τ)
  rw [← hZ τ] at hmove
  have hb12 : b₁ + (b₂ - b₁) = b₂ := by omega
  have htR : ∀ i, b₁ ≤ i → (Z (τ + 1)).tape i = (Y (r + 1)).tape (i + (b₂ - b₁)) := by
    intro i hi
    by_cases hiz : i = (Z τ).h
    · rw [hiz, h3, ← hpos]
    · rw [hZ τ, step_tape_of_ne _ hiz, hY r, step_tape_of_ne _ (by omega)]
      exact I.tapeR i hi
  have hcsR : ∀ b, b₁ ≤ b → cs Z b (τ + 1) = cs Y (b + (b₂ - b₁)) (r + 1) := fun b hb =>
    cs_succ_congr (I.csR b hb) (cross_congr (by omega) (by omega)) h1
  have hvisR : ∀ t, t < r + 1 → b₂ ≤ (Y t).h → ∃ σ, (Z σ).q = (Y t).q := fun t ht hyt => by
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 ht) with h | rfl
    · exact I.visR t h hyt
    · exact ⟨τ, hq⟩
  rcases le_or_gt b₁ (Z (τ + 1)).h with hR' | hL'
  · refine ⟨l, r + 1, fun b hb => ?_, hcsR, I.bl, hlt, Or.inl (by omega), fun i hi => ?_, htR,
      fun h => absurd h (not_lt.2 hR'), fun _ => ⟨h1, hYh.symm, hXl⟩, I.visL, hvisR⟩
    · rw [cs_succ, ite_eq_right (not_cross_of_ge (by omega) (by omega)), List.append_nil]
      exact I.csL b hb
    · rw [hZ τ, step_tape_of_ne _ (by omega)]
      exact I.tapeL i hi
  · have hz : (Z τ).h = b₁ := by omega
    have hz' : (Z (τ + 1)).h = b₁ - 1 := by omega
    have hcrY : Cross Y b₂ r := by unfold Cross; omega
    have hlenY : (cs Y b₂ (r + 1)).length = (cs Y b₂ r).length + 1 := by
      rw [cs_succ, ite_eq_left hcrY, List.length_append, List.length_singleton]
    have hXY : cs X b₁ l = cs Y b₂ r := by rw [← I.csL b₁ le_rfl, I.csR b₁ le_rfl, hb12]
    have hpreY : cs Y b₂ (r + 1) <+: cs X b₁ TX := by rw [hC]; exact cs_mono Y b₂ hlt
    obtain ⟨l', hl', hl'T, hcrX, hnoX⟩ := exists_next_cross (X := X) (b := b₁) I.bl (by
      rw [hXY]; have := hpreY.length_le; omega)
    have hXside : ∀ t, l ≤ t → t ≤ l' → b₁ ≤ (X t).h := fun t ht1 ht2 =>
      ge_of_no_cross ht1 (fun u hu1 hu2 => hnoX u hu1 (by omega)) hXl
    have hXcr := (cross_iff hX b₁ l').1 hcrX
    have hXl'h : (X l').h = b₁ ∧ (X (l' + 1)).h = b₁ - 1 := by
      have := hXside l' hl' le_rfl; omega
    have hcsX : cs X b₁ l' = cs X b₁ l := cs_eq_of_no_cross hl' hnoX
    have hpreX : cs X b₁ (l' + 1) <+: cs X b₁ TX := cs_mono X b₁ hl'T
    have hlenX : (cs X b₁ (l' + 1)).length = (cs X b₁ l).length + 1 := by
      rw [cs_succ, ite_eq_left hcrX, List.length_append, List.length_singleton, hcsX]
    have hXYs : cs X b₁ (l' + 1) = cs Y b₂ (r + 1) :=
      eq_of_prefix_of_length_eq hpreX hpreY (by rw [hlenX, hlenY, hXY])
    have hq' : (X (l' + 1)).q = (Y (r + 1)).q := by
      have := hXYs
      rw [cs_succ, ite_eq_left hcrX, cs_succ, ite_eq_left hcrY, hcsX, hXY] at this
      simpa using this
    refine ⟨l' + 1, r + 1, fun b hb => ?_, hcsR, hl'T, hlt, Or.inl (by omega), fun i hi => ?_, htR,
      fun _ => ⟨h1.trans hq'.symm, by omega, by omega⟩, fun h => absurd h (by omega),
      fun t ht hxt => ?_, hvisR⟩
    · have hno : cs X b l' = cs X b l :=
        cs_eq_of_no_cross hl' fun t ht1 ht2 => not_cross_of_ge
          (by have := hXside t ht1 (by omega); omega)
          (by have := hXside (t + 1) (by omega) (by omega); omega)
      exact cs_succ_congr ((I.csL b hb).trans hno.symm) (cross_congr (by omega) (by omega))
        (h1.trans hq'.symm)
    · rw [hZ τ, step_tape_of_ne _ (by omega), I.tapeL i hi]
      exact (frozen_left hX (by omega : l ≤ l' + 1)
        (fun t ht1 ht2 => hXside t ht1 (by omega)) hi).symm
    · rcases lt_or_ge t l with h | h
      · exact I.visL t h hxt
      · exact absurd hxt (not_lt.2 (hXside t h (by omega)))

theorem SpliceInv.step {τ l r : ℕ} (hX : IsRun X) (hY : IsRun Y) (hZ : IsRun Z)
    (hXT : M.halt (X TX).q = true) (hYT : M.halt (Y TY).q = true)
    (hC : cs X b₁ TX = cs Y b₂ TY) (I : SpliceInv X Y Z b₁ b₂ TX TY τ l r) :
    ∃ l' r', SpliceInv X Y Z b₁ b₂ TX TY (τ + 1) l' r' := by
  cases hh : M.halt (Z τ).q
  · rcases lt_or_ge (Z τ).h b₁ with hL | hR
    · exact I.step_left hX hY hZ hXT hC hh hL
    · exact I.step_right hX hY hZ hYT hC hh hR
  · exact ⟨l, r, I.step_halt hZ hh⟩

/-- **Splicing.** Let the halting runs `X` and `Y` have the same crossing sequence at `b₁` and at
`b₂`. The run `Z` that starts with the left part of `X` (left of `b₁`) and the right part of `Y`
(from `b₂` on, moved to start at `b₁`) halts, with the crossing sequences of `X` up to `b₁` and
those of `Y` from `b₁` on, in the final state of `X` if the crossing sequence has even length and
of `Y` otherwise. -/
theorem splice (hX : IsRun X) (hY : IsRun Y) (hZ : IsRun Z) (hXT : M.halt (X TX).q = true)
    (hYT : M.halt (Y TY).q = true) (hC : cs X b₁ TX = cs Y b₂ TY)
    (hq : (Z 0).q = (X 0).q) (hh : (Z 0).h = (X 0).h) (hz : (Z 0).h < b₁) (hy : (Y 0).h < b₂)
    (htL : ∀ i, i < b₁ → (Z 0).tape i = (X 0).tape i)
    (htR : ∀ i, b₁ ≤ i → (Z 0).tape i = (Y 0).tape (i + (b₂ - b₁))) :
    ∃ T, M.halt (Z T).q = true ∧ (∀ b, b ≤ b₁ → cs Z b T = cs X b TX) ∧
      (∀ b, b₁ ≤ b → cs Z b T = cs Y (b + (b₂ - b₁)) TY) ∧
      (Z T).q = (if Even (cs X b₁ TX).length then (X TX).q else (Y TY).q) ∧
      (∀ t, t ≤ TX → (X t).h < b₁ → ∃ σ, (Z σ).q = (X t).q) ∧
      (∀ t, t ≤ TY → b₂ ≤ (Y t).h → ∃ σ, (Z σ).q = (Y t).q) := by
  have hall : ∀ τ, ∃ l r, SpliceInv X Y Z b₁ b₂ TX TY τ l r := by
    intro τ
    induction τ with
    | zero => exact ⟨0, 0, fun _ _ => rfl, fun _ _ => rfl, Nat.zero_le _, Nat.zero_le _,
        Or.inl le_rfl, htL, htR, fun _ => ⟨hq, hh, hy⟩, fun h => absurd h (not_le.2 hz),
        fun t ht => absurd ht (Nat.not_lt_zero t), fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    | succ τ ih =>
      obtain ⟨l, r, I⟩ := ih
      exact I.step hX hY hZ hXT hYT hC
  obtain ⟨l, r, I⟩ := hall (TX + TY)
  have hb12 : b₁ + (b₂ - b₁) = b₂ := by omega
  have hpar := left_iff_even (X := Z) hz (TX + TY)
  refine ⟨TX + TY, ?_⟩
  rcases lt_or_ge (Z (TX + TY)).h b₁ with hL | hR
  · obtain ⟨hq', -, hYr⟩ := I.left hL
    have hXl : M.halt (X l).q = true := by
      rcases I.prog with hp | hp
      · obtain rfl : l = TX := by have := I.bl; have := I.br; omega
        exact hXT
      · rwa [← hq']
    have hXeq : ∀ b, cs X b TX = cs X b l := fun b =>
      cs_eq_of_no_cross I.bl fun t ht _ => not_cross_of_halt hX hXl ht b
    have hlen : (cs Y b₂ TY).length = (cs Y b₂ r).length := by
      rw [← hC, hXeq, ← I.csL b₁ le_rfl, I.csR b₁ le_rfl, hb12]
    have hno := no_cross_of_length_eq hlen
    have hYeq : ∀ b, b₂ ≤ b → cs Y b TY = cs Y b r := fun b hb =>
      cs_eq_of_no_cross I.br fun t ht1 ht2 => not_cross_of_lt
        (by have := lt_of_no_cross ht1 (fun u hu1 hu2 => hno u hu1 (by omega)) hYr; omega)
        (by have := lt_of_no_cross (by omega : r ≤ t + 1)
              (fun u hu1 hu2 => hno u hu1 (by omega)) hYr; omega)
    refine ⟨by rw [hq']; exact hXl, fun b hb => (I.csL b hb).trans (hXeq b).symm,
      fun b hb => (I.csR b hb).trans (hYeq _ (by omega)).symm, ?_, fun t _ hxt => ?_,
      fun t ht hyt => ?_⟩
    · rw [ite_eq_left (by rw [hXeq, ← I.csL b₁ le_rfl]; exact hpar.1 hL), hq',
        eq_of_halt hX hXl I.bl]
    · rcases lt_or_ge t l with h | h
      · exact I.visL t h hxt
      · exact ⟨TX + TY, by rw [hq', eq_of_halt hX hXl h]⟩
    · rcases lt_or_ge t r with h | h
      · exact I.visR t h hyt
      · exact absurd hyt (not_le.2 (lt_of_no_cross h (fun u hu1 hu2 => hno u hu1 (by omega)) hYr))
  · obtain ⟨hq', -, hXl⟩ := I.right hR
    have hYr : M.halt (Y r).q = true := by
      rcases I.prog with hp | hp
      · obtain rfl : r = TY := by have := I.bl; have := I.br; omega
        exact hYT
      · rwa [← hq']
    have hYeq : ∀ b, cs Y b TY = cs Y b r := fun b =>
      cs_eq_of_no_cross I.br fun t ht _ => not_cross_of_halt hY hYr ht b
    have hlen : (cs X b₁ TX).length = (cs X b₁ l).length := by
      rw [hC, hYeq, ← I.csL b₁ le_rfl, I.csR b₁ le_rfl, hb12]
    have hno := no_cross_of_length_eq hlen
    have hXeq : ∀ b, b ≤ b₁ → cs X b TX = cs X b l := fun b hb =>
      cs_eq_of_no_cross I.bl fun t ht1 ht2 => not_cross_of_ge
        (by have := ge_of_no_cross ht1 (fun u hu1 hu2 => hno u hu1 (by omega)) hXl; omega)
        (by have := ge_of_no_cross (by omega : l ≤ t + 1)
              (fun u hu1 hu2 => hno u hu1 (by omega)) hXl; omega)
    refine ⟨by rw [hq']; exact hYr, fun b hb => (I.csL b hb).trans (hXeq b hb).symm,
      fun b hb => (I.csR b hb).trans (hYeq _).symm, ?_, fun t ht hxt => ?_, fun t _ hyt => ?_⟩
    · rw [ite_eq_right (by
          rw [hXeq b₁ le_rfl, ← I.csL b₁ le_rfl]; exact fun he => not_lt.2 hR (hpar.2 he)),
        hq', eq_of_halt hY hYr I.br]
    · rcases lt_or_ge t l with h | h
      · exact I.visL t h hxt
      · exact absurd hxt (not_lt.2 (ge_of_no_cross h (fun u hu1 hu2 => hno u hu1 (by omega)) hXl))
    · rcases lt_or_ge t r with h | h
      · exact I.visR t h hyt
      · exact ⟨TX + TY, by rw [hq', eq_of_halt hY hYr h]⟩

end Splice

/-- Splicing the runs on `1ⁿ` and `1ᵐ` at the boundaries `a₁` and `a₂` gives the run on
`1^{n'}`, `n' = a₁ + (m − a₂)`. -/
theorem splice_run {n m n' a₁ a₂ TX TY : ℕ} (h₁ : 1 ≤ a₁) (h₁n : a₁ ≤ n) (h₂ : 1 ≤ a₂)
    (h₂m : a₂ ≤ m) (hn' : n' + a₂ = a₁ + m) (hXT : M.halt (run M n TX).q = true)
    (hYT : M.halt (run M m TY).q = true) (hC : cs (run M n) a₁ TX = cs (run M m) a₂ TY) :
    ∃ T, M.halt (run M n' T).q = true ∧
      (∀ b : ℤ, b ≤ a₁ → cs (run M n') b T = cs (run M n) b TX) ∧
      (∀ b : ℤ, a₁ ≤ b → cs (run M n') b T = cs (run M m) (b + ((a₂ : ℤ) - a₁)) TY) ∧
      (run M n' T).q =
        (if Even (cs (run M n) a₁ TX).length then (run M n TX).q else (run M m TY).q) ∧
      (∀ t, t ≤ TX → (run M n t).h < a₁ → ∃ σ, (run M n' σ).q = (run M n t).q) ∧
      (∀ t, t ≤ TY → (a₂ : ℤ) ≤ (run M m t).h → ∃ σ, (run M n' σ).q = (run M m t).q) :=
  splice (isRun_run n) (isRun_run m) (isRun_run n') hXT hYT hC rfl rfl
    (by simp only [run, Function.iterate_zero, id, init]; omega)
    (by simp only [run, Function.iterate_zero, id, init]; omega)
    (fun i hi => by
      simp only [run, Function.iterate_zero, id, init]
      congr 1
      simp only [eq_iff_iff]
      omega)
    (fun i hi => by
      simp only [run, Function.iterate_zero, id, init]
      congr 1
      simp only [eq_iff_iff]
      omega)

theorem cs_eq_of_halt {X : ℕ → Cfg M} (hX : IsRun X) {s s' : ℕ} (hs : M.halt (X s).q = true)
    (hs' : M.halt (X s').q = true) (b : ℤ) : cs X b s = cs X b s' := by
  rcases le_total s s' with h | h
  · exact (cs_eq_of_no_cross h fun t ht _ => not_cross_of_halt hX hs ht b).symm
  · exact cs_eq_of_no_cross h fun t ht _ => not_cross_of_halt hX hs' ht b

theorem eq_of_halt' {X : ℕ → Cfg M} (hX : IsRun X) {s s' : ℕ} (hs : M.halt (X s).q = true)
    (hs' : M.halt (X s').q = true) : X s = X s' := by
  rcases le_total s s' with h | h
  · exact (eq_of_halt hX hs h).symm
  · exact eq_of_halt hX hs' h

theorem length_cs_le (X : ℕ → Cfg M) (b : ℤ) (t : ℕ) : (cs X b t).length ≤ t := by
  unfold cs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-! ### Counting crossings -/

/-- Each step crosses at most one boundary, so the crossing sequences at any set of boundaries
have total length at most the time. -/
theorem sum_length_cs_le {X : ℕ → Cfg M} (hX : IsRun X) (B : Finset ℕ) (t : ℕ) :
    ∑ b ∈ B, (cs X (b : ℤ) t).length ≤ t := by
  classical
  induction t with
  | zero => simp [cs_zero]
  | succ t ih =>
    have h1 : (B.filter fun b : ℕ => Cross X (b : ℤ) t).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro b hb b' hb'
      have := (cross_iff hX b t).1 (Finset.mem_filter.1 hb).2
      have := (cross_iff hX b' t).1 (Finset.mem_filter.1 hb').2
      omega
    have h2 : ∑ b ∈ B, (cs X (b : ℤ) (t + 1)).length =
        ∑ b ∈ B, (cs X (b : ℤ) t).length + (B.filter fun b : ℕ => Cross X (b : ℤ) t).card := by
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [cs_succ]
      split_ifs <;> simp
    omega

/-- At most `(q + 1)^ℓ` distinct words over `q` letters are shorter than `ℓ`. -/
theorem card_short_le {α ι : Type*} [Fintype α] {g : ι → List α} {B : Finset ι}
    (hg : Set.InjOn g B) (ℓ : ℕ) :
    (B.filter fun b => (g b).length < ℓ).card ≤ (Fintype.card α + 1) ^ ℓ := by
  classical
  have : (B.filter fun b => (g b).length < ℓ).card ≤
      (Finset.univ : Finset (Fin ℓ → Option α)).card := by
    refine Finset.card_le_card_of_injOn (fun b i => (g b)[(i : ℕ)]?) (by intro b _; simp) ?_
    intro b hb b' hb' he
    rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
    apply hg hb.1 hb'.1
    apply List.ext_getElem?
    intro i
    by_cases hi : i < ℓ
    · exact congrFun he ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_option] using this

/-- Distinct words: `ℓ` times their number is at most their total length plus `ℓ (q + 1)^ℓ`. -/
theorem le_sum_length {α ι : Type*} [Fintype α] {g : ι → List α} {B : Finset ι}
    (hg : Set.InjOn g B) (ℓ : ℕ) :
    ℓ * B.card ≤ ∑ b ∈ B, (g b).length + ℓ * (Fintype.card α + 1) ^ ℓ := by
  classical
  have h1 := Nat.mul_le_mul_left ℓ (card_short_le hg ℓ)
  have h2 := Finset.card_filter_add_card_filter_not (s := B) (fun b => (g b).length < ℓ)
  have h3 : ℓ * (B.filter fun b => ¬ (g b).length < ℓ).card ≤ ∑ b ∈ B, (g b).length := by
    calc ℓ * (B.filter fun b => ¬ (g b).length < ℓ).card
        = ∑ b ∈ B.filter (fun b => ¬ (g b).length < ℓ), ℓ := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ b ∈ B.filter (fun b => ¬ (g b).length < ℓ), (g b).length :=
          Finset.sum_le_sum fun b hb => not_lt.1 (Finset.mem_filter.1 hb).2
      _ ≤ ∑ b ∈ B, (g b).length := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h4 : ℓ * B.card = ℓ * (B.filter fun b => (g b).length < ℓ).card +
      ℓ * (B.filter fun b => ¬ (g b).length < ℓ).card := by
    rw [← mul_add, h2]
  omega

/-- The arithmetic at the end of Hennie's argument. -/
theorem log_bound {q n ℓ : ℕ} (hq : 1 ≤ q) (hn : 64 ≤ n) (hnq : (q + 1) ^ 4 ≤ n)
    (hℓ : n / 4 < (q + 1) ^ (ℓ + 1)) :
    (n : ℝ) * Real.log n ≤ 32 * Real.log ((q : ℝ) + 1) * (ℓ * ((n / 4 : ℕ) : ℝ)) := by
  have hc : 0 < Real.log ((q : ℝ) + 1) := Real.log_pos (by norm_cast; omega)
  have hA8 : (n : ℝ) ≤ 8 * ((n / 4 : ℕ) : ℝ) := by
    have : n ≤ 8 * (n / 4) := by omega
    exact_mod_cast this
  have hApos : (0 : ℝ) < ((n / 4 : ℕ) : ℝ) := by
    have : 0 < n / 4 := by omega
    exact_mod_cast this
  have h1 : Real.log ((n / 4 : ℕ) : ℝ) < ((ℓ : ℝ) + 1) * Real.log ((q : ℝ) + 1) := by
    have := Real.log_lt_log hApos (show ((n / 4 : ℕ) : ℝ) < ((q : ℝ) + 1) ^ (ℓ + 1) by
      exact_mod_cast hℓ)
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  have h2 : Real.log n - Real.log 8 ≤ Real.log ((n / 4 : ℕ) : ℝ) := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have h3 : 2 * Real.log 8 ≤ Real.log n := by
    have e := Real.log_pow (8 : ℝ) 2
    have := Real.log_le_log (by norm_num) (show (8 : ℝ) ^ 2 ≤ n by norm_num; exact_mod_cast hn)
    push_cast at e
    linarith
  have h4 : 4 * Real.log ((q : ℝ) + 1) ≤ Real.log n := by
    have e := Real.log_pow ((q : ℝ) + 1) 4
    have := Real.log_le_log (by positivity) (show ((q : ℝ) + 1) ^ 4 ≤ n by exact_mod_cast hnq)
    push_cast at e
    linarith
  have h5 : Real.log n ≤ 4 * ℓ * Real.log ((q : ℝ) + 1) := by nlinarith
  calc (n : ℝ) * Real.log n ≤ n * (4 * ℓ * Real.log ((q : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg n)
    _ ≤ (8 * ((n / 4 : ℕ) : ℝ)) * (4 * ℓ * Real.log ((q : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hA8 (by positivity)
    _ = 32 * Real.log ((q : ℝ) + 1) * (ℓ * ((n / 4 : ℕ) : ℝ)) := by ring

/-! ### Deciders -/

/-- `M` decides `f` within time `T`: on input `1ⁿ` it has halted by step `T n`, in an accepting
state iff `f n`. -/
def DecidesInTime (M : Machine) (f : ℕ → Bool) (T : ℕ → ℕ) : Prop :=
  ∀ n, M.halt (run M n (T n)).q = true ∧ M.accept (run M n (T n)).q = f n

section Decider

variable {f : ℕ → Bool} {T : ℕ → ℕ}

/-- Splicing for a decider, in terms of its crossing sequences `cs (run M n) b (T n)`. -/
theorem DecidesInTime.splice (hM : DecidesInTime M f T) {n m n' a₁ a₂ : ℕ} (h₁ : 1 ≤ a₁)
    (h₁n : a₁ ≤ n) (h₂ : 1 ≤ a₂) (h₂m : a₂ ≤ m) (hn' : n' + a₂ = a₁ + m)
    (hC : cs (run M n) a₁ (T n) = cs (run M m) a₂ (T m)) :
    (∀ b : ℤ, b ≤ a₁ → cs (run M n') b (T n') = cs (run M n) b (T n)) ∧
    (∀ b : ℤ, a₁ ≤ b → cs (run M n') b (T n') = cs (run M m) (b + ((a₂ : ℤ) - a₁)) (T m)) ∧
    f n' = if Even (cs (run M n) a₁ (T n)).length then f n else f m := by
  obtain ⟨T', hT', hL, hR, hq, -, -⟩ := splice_run h₁ h₁n h₂ h₂m hn' (hM n).1 (hM m).1 hC
  have heq := cs_eq_of_halt (isRun_run n') hT' (hM n').1
  refine ⟨fun b hb => (heq b).symm.trans (hL b hb), fun b hb => (heq b).symm.trans (hR b hb), ?_⟩
  rw [← (hM n').2, ← eq_of_halt' (isRun_run n') hT' (hM n').1, hq]
  split_ifs
  · exact (hM n).2
  · exact (hM m).2

/-- Splicing for a decider: the spliced run passes through every state of the left run on the left
of `a₁`, and of the right run from `a₂` on. -/
theorem DecidesInTime.splice_visit (hM : DecidesInTime M f T) {n m n' a₁ a₂ : ℕ} (h₁ : 1 ≤ a₁)
    (h₁n : a₁ ≤ n) (h₂ : 1 ≤ a₂) (h₂m : a₂ ≤ m) (hn' : n' + a₂ = a₁ + m)
    (hC : cs (run M n) a₁ (T n) = cs (run M m) a₂ (T m)) :
    (∀ t, t ≤ T n → (run M n t).h < a₁ → ∃ σ, (run M n' σ).q = (run M n t).q) ∧
    (∀ t, t ≤ T m → (a₂ : ℤ) ≤ (run M m t).h → ∃ σ, (run M n' σ).q = (run M m t).q) := by
  obtain ⟨-, -, -, -, -, hvL, hvR⟩ := splice_run h₁ h₁n h₂ h₂m hn' (hM n).1 (hM m).1 hC
  exact ⟨hvL, hvR⟩

/-- **Finitely many crossing sequences give eventual periodicity.** -/
theorem DecidesInTime.eventuallyPeriodic_of_finite (hM : DecidesInTime M f T)
    (hfin : {C | ∃ (n : ℕ) (b : ℤ), cs (run M n) b (T n) = C}.Finite) : EventuallyPeriodic f := by
  classical
  -- `C` occurs at the boundary `a + 1` of inputs whose length exceeds `a` by some `r`
  let occ : ℕ → List M.Q → Prop := fun a C => ∃ r, cs (run M (a + 1 + r)) ((a + 1 : ℕ) : ℤ)
    (T (a + 1 + r)) = C
  -- the type of `a`: which crossing sequences occur, and for even ones, the value of `f`
  let typ : ℕ → {C | ∃ (n : ℕ) (b : ℤ), cs (run M n) b (T n) = C} → Option Bool := fun a C =>
    if h : occ a C.1 then some (if Even C.1.length then f (a + 1 + h.choose) else false) else none
  have : Finite {C | ∃ (n : ℕ) (b : ℤ), cs (run M n) b (T n) = C} := hfin.to_subtype
  -- equal even crossing sequences at the same boundary give equal values
  have heven : ∀ a r r', cs (run M (a + 1 + r)) ((a + 1 : ℕ) : ℤ) (T (a + 1 + r)) =
      cs (run M (a + 1 + r')) ((a + 1 : ℕ) : ℤ) (T (a + 1 + r')) →
      Even (cs (run M (a + 1 + r)) ((a + 1 : ℕ) : ℤ) (T (a + 1 + r))).length →
      f (a + 1 + r') = f (a + 1 + r) := fun a r r' hC he => by
    have := (hM.splice (n := a + 1 + r) (m := a + 1 + r') (n' := a + 1 + r') (a₁ := a + 1)
      (a₂ := a + 1) (by omega) (by omega) (by omega) (by omega) (by omega) hC).2.2
    rwa [ite_eq_left he] at this
  -- the key step: equal types give equal values from `a + 1` and `a' + 1` on
  have key : ∀ a a', typ a = typ a' → ∀ r, f (a' + 1 + r) = f (a + 1 + r) := by
    intro a a' htyp r
    set C := cs (run M (a + 1 + r)) ((a + 1 : ℕ) : ℤ) (T (a + 1 + r)) with hCdef
    have hocc : occ a C := ⟨r, rfl⟩
    have hta := congrFun htyp ⟨C, a + 1 + r, _, rfl⟩
    have hocc' : occ a' C := by
      by_contra hn
      simp only [typ, dite_eq_left hocc, dite_eq_right hn] at hta
      exact absurd hta (by simp)
    have ⟨r', hr'⟩ := hocc'
    have hsp := hM.splice (n := a' + 1 + r') (m := a + 1 + r) (n' := a' + 1 + r)
      (a₁ := a' + 1) (a₂ := a + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hr'.trans hCdef)
    rw [hsp.2.2, hr']
    split_ifs with he
    · simp only [typ, dite_eq_left hocc, dite_eq_left hocc', ite_eq_left he,
        Option.some.injEq] at hta
      rw [heven a' _ r' (hocc'.choose_spec.trans hr'.symm) (by rw [hocc'.choose_spec]; exact he),
        heven a _ r hocc.choose_spec (by rw [hocc.choose_spec]; exact he)]
      exact hta.symm
    · rfl
  obtain ⟨a, a', hne, htyp⟩ := Finite.exists_ne_map_eq_of_infinite typ
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨a + 1, a' - a, by omega, fun t ht => ?_⟩
    obtain ⟨r, rfl⟩ : ∃ r, t = a + 1 + r := ⟨t - (a + 1), by omega⟩
    rw [show a + 1 + r + (a' - a) = a' + 1 + r by omega]
    exact key a a' htyp r
  · refine ⟨a' + 1, a - a', by omega, fun t ht => ?_⟩
    obtain ⟨r, rfl⟩ : ∃ r, t = a' + 1 + r := ⟨t - (a' + 1), by omega⟩
    rw [show a' + 1 + r + (a - a') = a + 1 + r by omega]
    exact key a' a htyp.symm r

/-- **Bounded crossing sequences give eventual periodicity.** -/
theorem DecidesInTime.eventuallyPeriodic_of_bounded [Finite M.Q] (hM : DecidesInTime M f T)
    {K : ℕ} (hK : ∀ n (b : ℤ), (cs (run M n) b (T n)).length ≤ K) : EventuallyPeriodic f :=
  hM.eventuallyPeriodic_of_finite <| (List.finite_length_le M.Q K).subset fun _ ⟨n, b, hC⟩ =>
    hC ▸ hK n b

/-- **Hennie's bound.** Let `1ⁿ` be a shortest input with a crossing sequence longer than `K`, at
`p`. Cutting out the part between two boundaries on the same side of `p` with equal crossing
sequences would give a shorter such input, so the `n` boundaries `1, …, n` have pairwise distinct
crossing sequences on each side of `p`; counting gives `ℓ · (n / 4) ≤ T n` for
`ℓ = log_{q+1} (n / 4)`. -/
theorem DecidesInTime.time_lower_bound [Fintype M.Q] (hM : DecidesInTime M f T) {K n : ℕ} {p : ℤ}
    (hmin : ∀ n' < n, ∀ b : ℤ, (cs (run M n') b (T n')).length ≤ K)
    (hp : K < (cs (run M n) p (T n)).length) :
    Nat.log (Fintype.card M.Q + 1) (n / 4) * (n / 4) ≤ T n := by
  classical
  set g : ℕ → List M.Q := fun b => cs (run M n) (b : ℤ) (T n)
  -- equal crossing sequences on one side of `p` would give a shorter input
  have hdist : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ((j : ℤ) ≤ p ∨ p ≤ i) → g i ≠ g j := by
    intro i j hi hij hjn hside hC
    have hsp := hM.splice (n := n) (m := n) (n' := i + (n - j)) (a₁ := i) (a₂ := j) hi (by omega)
      (by omega) hjn (by omega) hC
    rcases hside with h | h
    · have e := hsp.2.1 (p - ((j : ℤ) - i)) (by omega)
      rw [show p - ((j : ℤ) - i) + ((j : ℤ) - i) = p by ring] at e
      have := hmin (i + (n - j)) (by omega) (p - ((j : ℤ) - i))
      rw [e] at this
      omega
    · have e := hsp.1 p h
      have := hmin (i + (n - j)) (by omega) p
      rw [e] at this
      omega
  set BL := (Finset.Icc 1 n).filter fun b : ℕ => (b : ℤ) ≤ p
  set BR := (Finset.Icc 1 n).filter fun b : ℕ => p ≤ (b : ℤ)
  have hinjL : Set.InjOn g BL := by
    intro i hi j hj he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist i j hi.1.1 h hj.1.2 (Or.inl hj.2) he
    · exact hdist j i hj.1.1 h hi.1.2 (Or.inl hi.2) he.symm
  have hinjR : Set.InjOn g BR := by
    intro i hi j hj he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist i j hi.1.1 h hj.1.2 (Or.inr hi.2) he
    · exact hdist j i hj.1.1 h hi.1.2 (Or.inr hj.2) he.symm
  have hcard : n ≤ BL.card + BR.card := by
    have hsub : Finset.Icc 1 n ⊆ BL ∪ BR := by
      intro b hb
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases le_total (b : ℤ) p with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le BL BR)
    simpa using this
  -- one side has at least `n / 2` boundaries
  obtain ⟨B, hB, hinj⟩ : ∃ B : Finset ℕ, n ≤ 2 * B.card ∧ Set.InjOn g B := by
    rcases le_total BR.card BL.card with h | h
    · exact ⟨BL, by omega, hinjL⟩
    · exact ⟨BR, by omega, hinjR⟩
  set ℓ := Nat.log (Fintype.card M.Q + 1) (n / 4)
  rcases Nat.eq_zero_or_pos (n / 4) with h0 | h0
  · rw [h0, mul_zero]; exact Nat.zero_le _
  have hpow : (Fintype.card M.Q + 1) ^ ℓ ≤ n / 4 := Nat.pow_log_le_self _ h0.ne'
  have h1 := le_sum_length hinj ℓ
  have h2 : ∑ b ∈ B, (g b).length ≤ T n := sum_length_cs_le (isRun_run n) B (T n)
  have h3 : ℓ * (2 * (n / 4)) ≤ ℓ * B.card := Nat.mul_le_mul_left ℓ (by omega)
  have h4 : ℓ * (Fintype.card M.Q + 1) ^ ℓ ≤ ℓ * (n / 4) := Nat.mul_le_mul_left ℓ hpow
  nlinarith

/-- **Hennie: time `o(n log n)` bounds the crossing sequences.** -/
theorem DecidesInTime.bounded [Fintype M.Q] (hM : DecidesInTime M f T)
    (hT : (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ) * Real.log n)) :
    ∃ K, ∀ n (b : ℤ), (cs (run M n) b (T n)).length ≤ K := by
  classical
  by_contra hne
  push Not at hne
  set q := Fintype.card M.Q
  have hq : 1 ≤ q := Fintype.card_pos_iff.2 ⟨M.start⟩
  set c := Real.log ((q : ℝ) + 1)
  have hc : 0 < c := Real.log_pos (by norm_cast; omega)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hT.def (show (0 : ℝ) < 1 / (64 * c) by positivity))
  set N := max N₀ (max 64 ((q + 1) ^ 4))
  set K := ∑ n ∈ Finset.range N, T n
  have hex : ∃ n, ∃ b : ℤ, K < (cs (run M n) b (T n)).length := by
    obtain ⟨n, b, h⟩ := hne K
    exact ⟨n, b, h⟩
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  set n := Nat.find hex
  have hmin : ∀ n' < n, ∀ b : ℤ, (cs (run M n') b (T n')).length ≤ K := fun n' hn' b =>
    not_lt.1 fun h => Nat.find_min hex hn' ⟨b, h⟩
  have hnN : N ≤ n := by
    by_contra h
    push Not at h
    have h1 := length_cs_le (run M n) p (T n)
    have h2 : T n ≤ K :=
      Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 h)
    omega
  have h64 : 64 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
  have hq4 : (q + 1) ^ 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN
  have hbound : (Nat.log (q + 1) (n / 4) : ℝ) * ((n / 4 : ℕ) : ℝ) ≤ T n := by
    exact_mod_cast hM.time_lower_bound hmin hp
  have hℓ := Nat.lt_pow_succ_log_self (show 1 < q + 1 by omega) (n / 4)
  have e1 := log_bound hq h64 hq4 hℓ
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have e2 : (T n : ℝ) ≤ 1 / (64 * c) * ((n : ℝ) * Real.log n) := by
    have := hN₀ n (le_trans (le_max_left _ _) hnN)
    simp only [Real.norm_eq_abs] at this
    rwa [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (mul_nonneg hnpos.le hlogpos.le)] at this
  have e3 : 32 * c * (T n : ℝ) ≤ (n : ℝ) * Real.log n / 2 := by
    calc 32 * c * (T n : ℝ) ≤ 32 * c * (1 / (64 * c) * ((n : ℝ) * Real.log n)) := by gcongr
      _ = (n : ℝ) * Real.log n / 2 := by field_simp; ring
  have e4 : 32 * c * ((Nat.log (q + 1) (n / 4) : ℝ) * ((n / 4 : ℕ) : ℝ)) ≤ 32 * c * (T n : ℝ) := by
    gcongr
  nlinarith [mul_pos hnpos hlogpos]

/-- **Hennie's theorem for unary input.** A one-tape machine that decides `f` in time
`o(n log n)` has bounded crossing sequences, so `f` is eventually periodic. -/
theorem DecidesInTime.eventuallyPeriodic [Fintype M.Q] (hM : DecidesInTime M f T)
    (hT : (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ) * Real.log n)) :
    EventuallyPeriodic f := by
  obtain ⟨K, hK⟩ := hM.bounded hT
  exact hM.eventuallyPeriodic_of_bounded hK

end Decider

/-! ### A linear-time machine for an eventually periodic `f` -/

/-- One more one read: the count goes up, wrapping from `N + P` back to `N`. -/
def wrap (N P s : ℕ) : ℕ := if s + 1 < N + P then s + 1 else N

theorem wrap_lt {N P : ℕ} (hP : 0 < P) (s : ℕ) : wrap N P s < N + P := by
  unfold wrap; split_ifs <;> omega

/-- The count after reading `t` ones. -/
def cnt (N P : ℕ) (hP : 0 < P) : ℕ → Fin (N + P)
  | 0 => ⟨0, by omega⟩
  | t + 1 => ⟨wrap N P (cnt N P hP t), wrap_lt hP _⟩

theorem cnt_spec {N P : ℕ} (hP : 0 < P) (t : ℕ) :
    ∃ k, t = cnt N P hP t + k * P ∧ (0 < k → N ≤ cnt N P hP t) := by
  induction t with
  | zero => exact ⟨0, by simp [cnt], by simp⟩
  | succ t ih =>
    obtain ⟨k, hk, hkN⟩ := ih
    have hlt := (cnt N P hP t).2
    simp only [cnt, wrap]
    split_ifs with h
    · exact ⟨k, by omega, fun hk0 => by have := hkN hk0; omega⟩
    · exact ⟨k + 1, by rw [add_mul, one_mul]; omega, fun _ => le_rfl⟩

theorem apply_cnt {f : ℕ → Bool} {N P : ℕ} (hP : 0 < P) (hf : ∀ t, N ≤ t → f (t + P) = f t)
    (t : ℕ) : f (cnt N P hP t) = f t := by
  obtain ⟨k, hk, hkN⟩ := cnt_spec (N := N) hP t
  have hper : ∀ s, N ≤ s → ∀ j, f (s + j * P) = f s := fun s hs j => by
    induction j with
    | zero => simp
    | succ j ih => rw [add_mul, one_mul, ← add_assoc, hf _ (by omega), ih]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [zero_mul, add_zero] at hk
    rw [← hk]
  · conv_rhs => rw [hk]
    rw [hper _ (hkN hk0)]

/-- The machine that reads `1ⁿ` from left to right, counting with `wrap`, and at the first blank
halts with the answer `f` of the count. -/
def periodicTM (f : ℕ → Bool) (N P : ℕ) (hP : 0 < P) : TM where
  Q := Fin (N + P) ⊕ Bool
  Γ := Bool
  blank := false
  one := true
  start := Sum.inl (cnt N P hP 0)
  halt := Sum.isRight
  accept := Sum.elim (fun _ => false) id
  δ := fun s x => match s, x with
    | Sum.inl s, true => (Sum.inl ⟨wrap N P s, wrap_lt hP s⟩, true, Move.right)
    | Sum.inl s, false => (Sum.inr (f s), false, Move.right)
    | Sum.inr b, x => (Sum.inr b, x, Move.right)

theorem run_periodicTM {f : ℕ → Bool} {N P : ℕ} (hP : 0 < P) {n t : ℕ} (ht : t ≤ n) :
    run (periodicTM f N P hP).toMachine n t =
      ⟨Sum.inl (cnt N P hP t), t, (init (periodicTM f N P hP).toMachine n).tape⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (by omega), step_eq rfl]
    have htape : (init (periodicTM f N P hP).toMachine n).tape (t : ℤ) = true := by
      simp only [init]; rw [ite_eq_left (by omega)]; rfl
    dsimp only
    rw [htape]
    refine (Cfg.mk.injEq ..).mpr ?_
    refine ⟨rfl, by push_cast; rfl, ?_⟩
    exact Function.update_eq_self_iff.2 htape.symm

theorem decidesInTime_periodicTM {f : ℕ → Bool} {N P : ℕ} (hP : 0 < P)
    (hf : ∀ t, N ≤ t → f (t + P) = f t) :
    DecidesInTime (periodicTM f N P hP).toMachine f (· + 1) := by
  intro n
  rw [run_succ, run_periodicTM hP le_rfl, step_eq rfl]
  have htape : (init (periodicTM f N P hP).toMachine n).tape (n : ℤ) = false := by
    simp only [init]; rw [ite_eq_right (by omega)]; rfl
  dsimp only
  rw [htape]
  exact ⟨rfl, apply_cnt hP hf n⟩

theorem isLittleO_succ_mul_log :
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[Filter.atTop] (fun n : ℕ => Real.log n) :=
    Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have h2 : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    push_cast
    linarith
  simpa using h2.mul_isLittleO h1

/-! ### Problem 1 in small time -/

/-- A unary language is decided by a one-tape machine in time `o(n log n)` iff it is eventually
periodic (Hennie–Trakhtenbrot; the fast direction takes `n + 1` steps). -/
theorem eventuallyPeriodic_iff_exists_fast_decider (f : ℕ → Bool) : EventuallyPeriodic f ↔
    ∃ (M : TM) (T : ℕ → ℕ),
      (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ) * Real.log n) ∧
      DecidesInTime M.toMachine f T := by
  constructor
  · rintro ⟨N, P, hP, hf⟩
    exact ⟨periodicTM f N P hP, (· + 1), isLittleO_succ_mul_log, decidesInTime_periodicTM hP hf⟩
  · rintro ⟨M, T, hT, hM⟩
    exact hM.eventuallyPeriodic hT

/-- **Small time.** Problem 1 holds iff no deterministic one-tape Turing machine decides
`L₁ = {1ⁿ : c(n) = 1}` in time `o(n log n)`. -/
theorem problem1_iff_no_fast_one_tape_decider : Rule30Prize.Problem1 ↔
    ¬ ∃ (M : TM) (T : ℕ → ℕ),
      (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ) * Real.log n) ∧
      DecidesInTime M.toMachine c T := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_exists_fast_decider]

end Rule30Equivalents.OneTapeGap
