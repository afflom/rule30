module

public import Rule30Equivalents.OneTapeGap
public import Rule30Equivalents.Automatic
public import Mathlib.Data.Nat.Size
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Ruliology.CellularAutomata.Rule30Problem3

/-!
# Prize Problem 3 implies Problem 1

Wolfram's Problem 3 asks whether computing `c(n)` requires at least `O(n)` computational effort.
Its formal statement quantifies over Turing machines that read `n`. Here it is stated in the
one-tape Turing machine model of `OneTapeGap`, with the binary digits of `n` (least significant
first) as input:
* `Problem3`, the literal reading: no machine computes `c(n)` in time `O(n)`;
* `Problem3Verbal`, the verbal reading "at least of the order of `n`": no machine does it in time
  `o(n)`. The literal reading implies the verbal one (`problem3Verbal_of_problem3`).

`kernelTM` computes a `2`-automatic sequence in `|bin n| + 1 = O(log n)` steps: its states are the
`2`-kernel, and reading the digit `b` moves from `g` to `n ↦ g(2n + b)`. So Problem 3, even in the
verbal reading, implies that `c` is not `2`-automatic (`not_isAutomatic_of_problem3Verbal`), hence
Problem 1 (`problem1_of_problem3Verbal`). This is the chain "Problem 3 ⟹ no polylog-time digit
extraction ⟹ c is not automatic ⟹ Problem 1".

The kit's statements in `Rule30Problem3` use a machine with numbered states and symbols that halts
by a transition. `OfTM.ofTM M zero` runs a machine `M` of this file there, one step slower
(`OfTM.computes_ofTM`). So the kit's statements imply the ones here (`problem3_of_kit`,
`problem3Verbal_of_kit`), and even its model-independent `Problem3Robust` implies that `c` is not
`2`-automatic, hence Problem 1 (`problem1_of_problem3Robust`).
-/

@[expose] public section

namespace Rule30Equivalents.ProblemThree

open Filter Ruliology.CellularAutomata OneTapeGap Automatic

/-- The binary digits of `n`, least significant first, as tape symbols: `M.one` for `1` and `zero`
for `0`. -/
def binWord (M : Machine) (zero : M.Γ) (n : ℕ) : List M.Γ :=
  (List.range n.size).map fun i => if n.testBit i then M.one else zero

/-- `M` computes `f` from the binary digits of `n` within time `T`: on the input `binWord n` it has
halted by step `T n`, in an accepting state iff `f n`. -/
def DecidesBinInTime (M : Machine) (zero : M.Γ) (f : ℕ → Bool) (T : ℕ → ℕ) : Prop :=
  ∀ n, M.halt (runW M id (binWord M zero n) (T n)).q = true ∧
    M.accept (runW M id (binWord M zero n) (T n)).q = f n

/-- **Problem 3**, literally: no one-tape Turing machine computes `c(n)` from the binary digits of
`n` in time `O(n)`. -/
def Problem3 : Prop :=
  ¬ ∃ (M : TM) (zero : M.Γ) (T : ℕ → ℕ),
    (fun n => (T n : ℝ)) =O[atTop] (fun n => (n : ℝ)) ∧ DecidesBinInTime M.toMachine zero c T

/-- **Problem 3**, verbally ("at least of the order of `n`"): no machine does it in time `o(n)`. -/
def Problem3Verbal : Prop :=
  ¬ ∃ (M : TM) (zero : M.Γ) (T : ℕ → ℕ),
    (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧ DecidesBinInTime M.toMachine zero c T

theorem problem3Verbal_of_problem3 (h : Problem3) : Problem3Verbal :=
  fun ⟨M, zero, T, hT, hM⟩ => h ⟨M, zero, T, hT.isBigO, hM⟩

/-! ### Automatic sequences in logarithmic time -/

/-- The low digits: `n mod 2^(t+1)` adds bit `t` to `n mod 2^t`. -/
theorem mod_two_pow_succ' (n t : ℕ) :
    n % 2 ^ (t + 1) = 2 ^ t * (if n.testBit t then 1 else 0) + n % 2 ^ t := by
  rw [pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
  have h2 := Nat.mod_two_eq_zero_or_one (n / 2 ^ t)
  rcases h2 with h2 | h2 <;> simp [h2]
  ring

/-- The machine with the `2`-kernel of `f` as states: reading the digit `b` moves from `g` to
`n ↦ g(2n + b)`, and at the first blank it answers `g 0`. -/
noncomputable def kernelTM (f : ℕ → Bool) (hf : IsAutomatic 2 f) : TM where
  Q := kernel 2 f ⊕ Bool
  Γ := Option Bool
  blank := none
  one := some true
  start := Sum.inl ⟨f, self_mem_kernel 2 f⟩
  halt := Sum.isRight
  accept := Sum.elim (fun _ => false) id
  δ := fun s x => match s, x with
    | Sum.inl g, some b =>
      (Sum.inl ⟨fun m => g.1 (2 * m + if b then 1 else 0),
        mem_kernel_step g.2 (by split <;> omega)⟩,
        some b, Move.right)
    | Sum.inl g, none => (Sum.inr (g.1 0), none, Move.right)
    | Sum.inr a, x => (Sum.inr a, x, Move.right)
  instFintype := by
    haveI := hf.fintype
    infer_instance

theorem mem_kernel_low (f : ℕ → Bool) (n t : ℕ) :
    (fun m => f (2 ^ t * m + n % 2 ^ t)) ∈ kernel 2 f :=
  ⟨t, n % 2 ^ t, Nat.mod_lt _ (by positivity), rfl⟩

theorem run_kernelTM {f : ℕ → Bool} (hf : IsAutomatic 2 f) (n : ℕ) {t : ℕ} (ht : t ≤ n.size) :
    runW (kernelTM f hf).toMachine id (binWord (kernelTM f hf).toMachine (some false) n) t =
      ⟨Sum.inl ⟨fun m => f (2 ^ t * m + n % 2 ^ t), mem_kernel_low f n t⟩, t,
        (initW (kernelTM f hf).toMachine id
          (binWord (kernelTM f hf).toMachine (some false) n)).tape⟩ := by
  induction t with
  | zero =>
    show initW _ id _ = _
    simp only [initW, pow_zero, one_mul, Nat.mod_one, add_zero, Nat.cast_zero]
    rfl
  | succ t ih =>
    rw [(isRun_runW (M := (kernelTM f hf).toMachine) id _) t, ih (by omega), step_eq rfl]
    have htape : (initW (kernelTM f hf).toMachine id
        (binWord (kernelTM f hf).toMachine (some false) n)).tape (t : ℤ) = some (n.testBit t) := by
      simp only [initW, binWord, List.length_map, List.length_range, id]
      erw [dite_eq_left (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, Int.toNat_natCast]
      cases n.testBit t <;> rfl
    refine Cfg.ext' ?_ ?_ ?_
    · dsimp only
      rw [htape]
      show Sum.inl _ = Sum.inl _
      congr 1
      apply Subtype.ext
      funext m
      show f (2 ^ t * (2 * m + if n.testBit t then 1 else 0) + n % 2 ^ t) =
        f (2 ^ (t + 1) * m + n % 2 ^ (t + 1))
      rw [mod_two_pow_succ']
      congr 1
      ring
    · dsimp only
      rw [htape]
      push_cast
      rfl
    · dsimp only
      rw [htape]
      exact Function.update_eq_self_iff.2 htape.symm

/-- **A `2`-automatic sequence is computed in `|bin n| + 1` steps.** -/
theorem decidesBinInTime_kernelTM {f : ℕ → Bool} (hf : IsAutomatic 2 f) :
    DecidesBinInTime (kernelTM f hf).toMachine (some false) f fun n => n.size + 1 := by
  intro n
  rw [(isRun_runW (M := (kernelTM f hf).toMachine) id _) n.size, run_kernelTM hf n le_rfl,
    step_eq rfl]
  have htape : (initW (kernelTM f hf).toMachine id
      (binWord (kernelTM f hf).toMachine (some false) n)).tape (n.size : ℤ) = none := by
    simp only [initW, binWord, List.length_map, List.length_range]
    erw [dite_eq_right (by simp)]
    rfl
  dsimp only
  rw [htape]
  refine ⟨rfl, ?_⟩
  show f (2 ^ n.size * 0 + n % 2 ^ n.size) = f n
  rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (Nat.lt_size_self n)]

/-- `|bin n| + 1 ≤ 2 log n + 2` for `n ≥ 1`, since `2^(|bin n| - 1) ≤ n` and `log 2 > 1/2`. -/
theorem size_succ_le_log {n : ℕ} (hn : 1 ≤ n) : ((n.size + 1 : ℕ) : ℝ) ≤ 2 * Real.log n + 2 := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpow : (2 : ℝ) ^ (n.size - 1) ≤ n := by
    have h1 : 2 ^ (n.size - 1) ≤ n := by
      rcases Nat.eq_zero_or_pos (n.size - 1) with h | h
      · rw [h, pow_zero]; exact hn
      · by_contra hlt
        push Not at hlt
        have := Nat.size_le.2 hlt
        omega
    exact_mod_cast h1
  have hlogn : ((n.size - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hs : 1 ≤ n.size := Nat.size_pos.2 hn
  have : ((n.size + 1 : ℕ) : ℝ) = ((n.size - 1 : ℕ) : ℝ) + 2 := by
    rw [Nat.cast_sub hs]; push_cast; ring
  rw [this]
  nlinarith

/-- `|bin n| + 1 = o(n)`. -/
theorem isLittleO_size :
    (fun n : ℕ => ((n.size + 1 : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hlog : (fun n : ℕ => Real.log n) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hconst : (fun _ : ℕ => (2 : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop (2 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun n : ℕ => 2 * Real.log n + 2) ?_
    ((hlog.const_mul_left 2).add hconst)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul]
  exact size_succ_le_log hn

/-- `(|bin n| + 2)^k ≤ n` from some `n` on: the number of digits grows like `log n`. -/
theorem exists_size_pow_le (k : ℕ) : ∃ N, ∀ n, N ≤ n → (n.size + 1 + 1) ^ k ≤ n := by
  have h1 : (fun n : ℕ => Real.log n ^ k) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((h1.bound (show (0 : ℝ) < 1 / 4 ^ k by positivity)).and (eventually_ge_atTop 8))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hb, h8⟩ := hN n hn
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlog8 : (3 / 2 : ℝ) ≤ Real.log n := by
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 8 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h8)
    have h4 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hsize : ((n.size + 1 + 1 : ℕ) : ℝ) ≤ 4 * Real.log n := by
    have := size_succ_le_log (show 1 ≤ n by omega)
    push_cast at this ⊢
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at hb
  have : (((n.size + 1 + 1) ^ k : ℕ) : ℝ) ≤ n := by
    calc (((n.size + 1 + 1) ^ k : ℕ) : ℝ) = ((n.size + 1 + 1 : ℕ) : ℝ) ^ k := by push_cast; ring
      _ ≤ (4 * Real.log n) ^ k := pow_le_pow_left₀ (by positivity) hsize k
      _ = 4 ^ k * Real.log n ^ k := mul_pow _ _ _
      _ ≤ 4 ^ k * (1 / 4 ^ k * n) := by gcongr
      _ = n := by field_simp
  exact_mod_cast this

/-! ### Problem 3 implies Problem 1 -/

/-- **Problem 3 implies that `c` is not `2`-automatic**, even in the verbal reading. -/
theorem not_isAutomatic_of_problem3Verbal (h : Problem3Verbal) : ¬ IsAutomatic 2 c := fun ha =>
  h ⟨kernelTM c ha, some false, fun n => n.size + 1, isLittleO_size, decidesBinInTime_kernelTM ha⟩

/-- **Problem 3 implies Problem 1**, in the verbal reading. -/
theorem problem1_of_problem3Verbal (h : Problem3Verbal) : Rule30Prize.Problem1 := fun hep =>
  not_isAutomatic_of_problem3Verbal h (isAutomatic_of_eventuallyPeriodic hep le_rfl)

/-- **Problem 3 implies Problem 1**, in the literal reading. -/
theorem problem1_of_problem3 (h : Problem3) : Rule30Prize.Problem1 :=
  problem1_of_problem3Verbal (problem3Verbal_of_problem3 h)

/-! ### The kit's statements -/

namespace OfTM

variable (M : TM) (zero : M.Γ)

/-- The state numbered `p`: `0` is the start state and `i + 1` the `i`-th state. -/
noncomputable def decQ (p : Fin (Fintype.card M.Q + 1)) : M.Q :=
  if h : p.val = 0 then M.start
  else (Fintype.equivFin M.Q).symm ⟨p.val - 1, by have := p.isLt; omega⟩

/-- The number of a state. -/
noncomputable def encQ (q : M.Q) : Fin (Fintype.card M.Q + 1) :=
  ⟨(Fintype.equivFin M.Q q).val + 1, by have := (Fintype.equivFin M.Q q).isLt; omega⟩

/-- The tape symbol numbered `a`: `0`, `1` and `2` are the blank, `zero` and `M.one`, and `i + 3`
is the `i`-th symbol. -/
noncomputable def decΓ (a : Fin (Fintype.card M.Γ + 3)) : M.Γ :=
  if h0 : a.val = 0 then M.blank else if h1 : a.val = 1 then zero else if h2 : a.val = 2 then M.one
  else (Fintype.equivFin M.Γ).symm ⟨a.val - 3, by have := a.isLt; omega⟩

/-- The number of a tape symbol. -/
noncomputable def encΓ (γ : M.Γ) : Fin (Fintype.card M.Γ + 3) :=
  ⟨(Fintype.equivFin M.Γ γ).val + 3, by have := (Fintype.equivFin M.Γ γ).isLt; omega⟩

theorem decQ_encQ (q : M.Q) : decQ M (encQ M q) = q := by
  simp [decQ, encQ]

theorem decΓ_encΓ (γ : M.Γ) : decΓ M zero (encΓ M γ) = γ := by
  simp [decΓ, encΓ]

/-- The same head move in the kit's model. -/
def trMove : Move → Rule30Problem3.Move
  | .left => .left
  | .stay => .stay
  | .right => .right

theorem trMove_apply (m : Move) (h : ℤ) : (trMove m).apply h = h + m.shift := by
  cases m <;> simp only [trMove, Rule30Problem3.Move.apply, Move.shift] <;> omega

/-- The kit's machine that runs `M`, read with the binary digit `0` written as `zero`. In a halting
state of `M` it halts with `M`'s answer. -/
noncomputable def ofTM : Rule30Problem3.Machine where
  q := Fintype.card M.Q
  s := Fintype.card M.Γ
  δ := fun p a =>
    if M.halt (decQ M p) then .inl (M.accept (decQ M p)) else
      .inr (encQ M (M.δ (decQ M p) (decΓ M zero a)).1, encΓ M (M.δ (decQ M p) (decΓ M zero a)).2.1,
        trMove (M.δ (decQ M p) (decΓ M zero a)).2.2)

/-- A configuration of `ofTM M zero` that represents the configuration `x` of `M`. -/
def Sim (c' : Rule30Problem3.Cfg (ofTM M zero)) (x : Cfg M.toMachine) : Prop :=
  decQ M c'.state = x.q ∧ c'.head = x.h ∧ ∀ i, decΓ M zero (c'.tape i) = x.tape i

theorem sim_init (n : ℕ) :
    Sim M zero ((ofTM M zero).init n) (initW M.toMachine id (binWord M.toMachine zero n)) := by
  refine ⟨by simp [Rule30Problem3.Machine.init, decQ, initW], rfl, fun i => ?_⟩
  have key : (0 ≤ i ∧ 2 ^ i.toNat ≤ n) ↔ (0 ≤ i ∧ i < ((binWord M.toMachine zero n).length : ℤ)) := by
    simp only [binWord, List.length_map, List.length_range]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨h0, by have := Nat.lt_size.2 h1; omega⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0, Nat.lt_size.1 (by omega)⟩
  change decΓ M zero (if 0 ≤ i ∧ 2 ^ i.toNat ≤ n then
      (if n.testBit i.toNat then (⟨2, by omega⟩ : Fin (Fintype.card M.Γ + 3)) else ⟨1, by omega⟩)
      else ⟨0, by omega⟩) = (initW M.toMachine id (binWord M.toMachine zero n)).tape i
  simp only [initW]
  by_cases h1 : 0 ≤ i ∧ 2 ^ i.toNat ≤ n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), dite_eq_left_of_eq_true (eq_true (key.1 h1))]
    simp only [binWord, id, List.getElem_map, List.getElem_range]
    by_cases hb : n.testBit i.toNat <;> simp [hb, decΓ]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), dite_eq_right_of_eq_false (eq_false fun h => h1 (key.2 h))]
    simp [decΓ]

theorem sim_step {c' : Rule30Problem3.Cfg (ofTM M zero)} {x : Cfg M.toMachine}
    (h : Sim M zero c' x) (hx : M.halt x.q = false) :
    ∃ c'', c'.step = .inr c'' ∧ Sim M zero c'' (step x) := by
  obtain ⟨hq, hh, ht⟩ := h
  have hread : decΓ M zero (c'.tape c'.head) = x.tape x.h := by rw [ht, hh]
  refine ⟨⟨encQ M (M.δ x.q (x.tape x.h)).1, (trMove (M.δ x.q (x.tape x.h)).2.2).apply c'.head,
    fun i => if i = c'.head then encΓ M (M.δ x.q (x.tape x.h)).2.1 else c'.tape i⟩, ?_, ?_⟩
  · simp [Rule30Problem3.Cfg.step, ofTM, hq, hx, hread]
  · rw [step_eq hx]
    refine ⟨decQ_encQ M _, by rw [trMove_apply, hh], fun i => ?_⟩
    simp only [Function.update_apply]
    by_cases h1 : i = x.h
    · simp [h1, hh, decΓ_encΓ]
    · simp [h1, hh, ht]

theorem sim_halt {c' : Rule30Problem3.Cfg (ofTM M zero)} {x : Cfg M.toMachine}
    (h : Sim M zero c' x) (hx : M.halt x.q = true) : c'.step = .inl (M.accept x.q) := by
  simp [Rule30Problem3.Cfg.step, ofTM, h.1, hx]

/-- **`ofTM M zero` computes what `M` decides, one step later.** It follows `M` until `M` enters a
halting state, and halts at the next step with `M`'s answer. -/
theorem computes_ofTM {f : ℕ → Bool} {T : ℕ → ℕ} (hM : DecidesBinInTime M.toMachine zero f T) :
    Rule30Problem3.Computes (ofTM M zero) f fun n => T n + 1 := by
  intro n
  have hX : IsRun (runW M.toMachine id (binWord M.toMachine zero n)) := isRun_runW id _
  have hex : ∃ s, M.halt (runW M.toMachine id (binWord M.toMachine zero n) s).q = true :=
    ⟨T n, (hM n).1⟩
  classical
  have hs := Nat.find_spec hex
  have hsT : Nat.find hex ≤ T n := Nat.find_min' hex (hM n).1
  have hsim : ∀ t ≤ Nat.find hex, ∃ c', (ofTM M zero).run n t = .inr c' ∧
      Sim M zero c' (runW M.toMachine id (binWord M.toMachine zero n) t) := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨_, rfl, sim_init M zero n⟩
    | succ t ih =>
      intro ht
      obtain ⟨c', hc', hsim⟩ := ih (by omega)
      have hx : M.halt (runW M.toMachine id (binWord M.toMachine zero n) t).q = false := by
        simpa using Nat.find_min hex (show t < Nat.find hex by omega)
      obtain ⟨c'', hc'', hsim'⟩ := sim_step M zero hsim hx
      exact ⟨c'', by simp only [Rule30Problem3.Machine.run, hc', hc''], by rw [hX t]; exact hsim'⟩
  obtain ⟨c', hc', hsim⟩ := hsim _ le_rfl
  have hrun : (ofTM M zero).run n (Nat.find hex + 1) = .inl (f n) := by
    simp only [Rule30Problem3.Machine.run, hc', sim_halt M zero hsim hs]
    rw [← eq_of_halt hX hs hsT]
    exact congrArg Sum.inl (hM n).2
  have := Rule30Problem3.Machine.run_add hrun (T n - Nat.find hex)
  rwa [show Nat.find hex + 1 + (T n - Nat.find hex) = T n + 1 by omega] at this

end OfTM

open OfTM

/-- Time `O(n)` as a real bound gives `T n + 1 ≤ C · (n + 1)` for every `n`. -/
theorem exists_succ_le_mul_of_isBigO {T : ℕ → ℕ}
    (hT : (fun n => (T n : ℝ)) =O[atTop] (fun n => (n : ℝ))) :
    ∃ C, ∀ n, T n + 1 ≤ C * (n + 1) := by
  obtain ⟨c, hc⟩ := hT.bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  set S := ∑ m ∈ Finset.range N, (T m + 1)
  refine ⟨⌈c⌉₊ + 1 + S, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h1 := hN n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at h1
    have h2 : (T n : ℝ) ≤ ⌈c⌉₊ * n := h1.trans (by gcongr; exact Nat.le_ceil c)
    have h3 : T n ≤ ⌈c⌉₊ * n := by exact_mod_cast h2
    calc T n + 1 ≤ ⌈c⌉₊ * n + 1 := by omega
      _ ≤ (⌈c⌉₊ + 1 + S) * n + (⌈c⌉₊ + 1 + S) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
      _ = (⌈c⌉₊ + 1 + S) * (n + 1) := by ring
  · have h1 : T n + 1 ≤ S :=
      Finset.single_le_sum (f := fun m => T m + 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (by omega))
    calc T n + 1 ≤ ⌈c⌉₊ + 1 + S := by omega
      _ ≤ (⌈c⌉₊ + 1 + S) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)

/-- Time `o(n)` as a real bound gives `k · (T n + 1) ≤ n` from some `n` on, for every `k`. -/
theorem exists_mul_succ_le_of_isLittleO {T : ℕ → ℕ}
    (hT : (fun n => (T n : ℝ)) =o[atTop] (fun n => (n : ℝ))) (k : ℕ) :
    ∃ N, ∀ n, N ≤ n → k * (T n + 1) ≤ n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, fun n _ => by simp⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.bound (show (0 : ℝ) < 1 / (2 * k) by positivity))
  refine ⟨max N (2 * k), fun n hn => ?_⟩
  have h1 := hN n (le_of_max_le_left hn)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at h1
  have h2 : (2 * k : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (k : ℝ) * T n ≤ n / 2 := by
    calc (k : ℝ) * T n ≤ k * (1 / (2 * k) * n) := by gcongr
      _ = n / 2 := by field_simp
  have : ((k * (T n + 1) : ℕ) : ℝ) ≤ n := by
    push_cast
    nlinarith
  exact_mod_cast this

/-- **The kit's formal statement implies the one here.** -/
theorem problem3_of_kit (h : Rule30Problem3.Problem3) : Problem3 := by
  rintro ⟨M, zero, T, hT, hM⟩
  obtain ⟨C, hC⟩ := exists_succ_le_mul_of_isBigO hT
  exact h ⟨ofTM M zero, C, (computes_ofTM M zero hM).mono hC⟩

/-- **The kit's verbal statement implies the one here.** -/
theorem problem3Verbal_of_kit (h : Rule30Problem3.Problem3Verbal) : Problem3Verbal := by
  rintro ⟨M, zero, T, hT, hM⟩
  exact h ⟨ofTM M zero, fun n => T n + 1, computes_ofTM M zero hM,
    exists_mul_succ_le_of_isLittleO hT⟩

/-- **The model-independent Problem 3 implies that `c` is not `2`-automatic**: an automatic
sequence takes `|bin n| + 2` steps, which is `n^o(1)`. -/
theorem not_isAutomatic_of_problem3Robust (h : Rule30Problem3.Problem3Robust) :
    ¬ IsAutomatic 2 c := fun ha =>
  h ⟨ofTM (kernelTM c ha) (some false), fun n => n.size + 1 + 1,
    computes_ofTM _ _ (decidesBinInTime_kernelTM ha), exists_size_pow_le⟩

/-- **The model-independent Problem 3 implies Problem 1.** -/
theorem problem1_of_problem3Robust (h : Rule30Problem3.Problem3Robust) : Rule30Prize.Problem1 :=
  fun hep => not_isAutomatic_of_problem3Robust h (isAutomatic_of_eventuallyPeriodic hep le_rfl)

end Rule30Equivalents.ProblemThree
