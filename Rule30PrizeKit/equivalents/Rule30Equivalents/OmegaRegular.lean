module

public import Rule30Equivalents.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Bound

/-!
# Problem 1 ⟺ the center column is not ω-regular

A Büchi automaton reads infinite words; it accepts a word when some run visits accepting states
infinitely often. A set of infinite words is ω-regular when a Büchi automaton accepts exactly it.

* `eventuallyPeriodic_iff_omegaRegular_singleton`: the singleton `{b}` is ω-regular iff `b` is
  eventually periodic.
* `problem1_iff_not_omega_regular`: Problem 1 holds iff no Büchi
  automaton accepts exactly the center column.

**Proof.** If `b` has period `P` from `T`, the lasso automaton with states `0, …, T + P - 1` and a
dead state (`lasso`) accepts exactly `b` (`lasso_accepts_iff`). Conversely
(`eventuallyPeriodic_of_accepts_iff`), an accepting run on `b` visits one accepting state at two
times `m < n`, since there are finitely many states. Repeating the stretch of the run between them
gives an accepting run on `b(0) … b(m - 1) (b(m) … b(n - 1))^ω`, so that word is accepted, hence
equals `b`, and `b` has period `n - m` from `m`.

By Büchi's theorem the ω-regular sets are the sets definable in monadic second-order logic over
`(ℕ, <)`; that form needs Büchi's theorem and is not proved here.

Sources: J. R. Büchi, *On a decision method in restricted second order arithmetic* (1962);
W. Thomas, *Automata on infinite objects*, Handbook of Theoretical Computer Science B (1990).
-/

@[expose] public section

namespace Rule30Equivalents.OmegaRegular

open Ruliology.CellularAutomata

/-- A nondeterministic Büchi automaton over the alphabet `α`. -/
structure Buchi (α : Type) where
  Q : Type
  [fin : Finite Q]
  init : Q
  step : Q → α → Q → Prop
  acc : Set Q

/-- `B` accepts `w`: some run from the initial state visits accepting states infinitely often. -/
def Buchi.Accepts {α : Type} (B : Buchi α) (w : ℕ → α) : Prop :=
  ∃ r : ℕ → B.Q, r 0 = B.init ∧ (∀ n, B.step (r n) (w n) (r (n + 1))) ∧
    ∀ N, ∃ n, N ≤ n ∧ r n ∈ B.acc

/-! ### The lasso automaton of an eventually periodic word -/

section Lasso
variable (b : ℕ → Bool) (T P : ℕ)

/-- The next position on the lasso `0 → 1 → ⋯ → T + P - 1 → T`. -/
def succPos (i : ℕ) : ℕ := if i + 1 < T + P then i + 1 else T

theorem succPos_lt (hP : 0 < P) (i : ℕ) : succPos T P i < T + P := by
  unfold succPos; split_ifs <;> omega

/-- The position on the lasso at time `t`. -/
def pos : ℕ → ℕ
  | 0 => 0
  | t + 1 => succPos T P (pos t)

theorem pos_lt (hP : 0 < P) : ∀ t, pos T P t < T + P
  | 0 => by show 0 < T + P; omega
  | t + 1 => succPos_lt T P hP _

/-- Time `t` is the lasso position plus whole turns of the loop, which starts at `T`. -/
theorem pos_spec (hP : 0 < P) : ∀ t, ∃ k, t = pos T P t + k * P ∧ (0 < k → T ≤ pos T P t)
  | 0 => ⟨0, by simp [pos], fun h => absurd h (by omega)⟩
  | t + 1 => by
    obtain ⟨k, hk, hT⟩ := pos_spec hP t
    have hlt := pos_lt T P hP t
    show ∃ k', t + 1 = succPos T P (pos T P t) + k' * P ∧ (0 < k' → T ≤ succPos T P (pos T P t))
    unfold succPos
    by_cases h : pos T P t + 1 < T + P
    · rw [ite_eq_left h]
      refine ⟨k, by omega, fun hk0 => ?_⟩
      have := hT hk0; omega
    · rw [ite_eq_right h]
      exact ⟨k + 1, by rw [Nat.add_mul]; omega, fun _ => le_refl T⟩

theorem periodic_add_mul (hper : ∀ t, T ≤ t → b (t + P) = b t) {x : ℕ} (hx : T ≤ x) :
    ∀ k, b (x + k * P) = b x
  | 0 => by simp
  | k + 1 => by
    rw [Nat.add_mul, one_mul, ← Nat.add_assoc, hper _ (by omega)]
    exact periodic_add_mul hper hx k

/-- The lasso position reads the same letter as the time. -/
theorem b_pos (hP : 0 < P) (hper : ∀ t, T ≤ t → b (t + P) = b t) (t : ℕ) :
    b (pos T P t) = b t := by
  obtain ⟨k, hk, hT⟩ := pos_spec T P hP t
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Nat.zero_mul, Nat.add_zero] at hk
    rw [← hk]
  · calc b (pos T P t) = b (pos T P t + k * P) := (periodic_add_mul b T P hper (hT hk0) k).symm
      _ = b t := by rw [← hk]

/-- One step of the lasso automaton; `none` is the dead state. -/
def next (hP : 0 < P) : Option (Fin (T + P)) → Bool → Option (Fin (T + P))
  | none, _ => none
  | some i, a => if a = b i then some ⟨succPos T P i, succPos_lt T P hP i⟩ else none

/-- The lasso automaton: state `some i` expects the letter `b i`. -/
def lasso (hP : 0 < P) : Buchi Bool where
  Q := Option (Fin (T + P))
  fin := inferInstance
  init := some ⟨0, by omega⟩
  step q a q' := q' = next b T P hP q a
  acc := {q | q ≠ none}

/-- **The lasso automaton accepts exactly `b`.** -/
theorem lasso_accepts_iff (hP : 0 < P) (hper : ∀ t, T ≤ t → b (t + P) = b t) (w : ℕ → Bool) :
    (lasso b T P hP).Accepts w ↔ w = b := by
  constructor
  · rintro ⟨r, h0, hstep, hacc⟩
    have hstep' : ∀ n, r (n + 1) = next b T P hP (r n) (w n) := hstep
    have hdead : ∀ n, r n = none → ∀ k, r (n + k) = none := by
      intro n hn k
      induction k with
      | zero => exact hn
      | succ k ih => rw [← Nat.add_assoc, hstep', ih]; rfl
    have key : ∀ n, r n = some ⟨pos T P n, pos_lt T P hP n⟩ ∧ w n = b n := by
      intro n
      induction n with
      | zero =>
        refine ⟨h0, ?_⟩
        by_contra hne
        have h1 : r 1 = none := by
          rw [hstep', h0]; show (if w 0 = b 0 then _ else none) = none; rw [ite_eq_right hne]
        obtain ⟨m, hm, hmacc⟩ := hacc 1
        exact hmacc (by rw [show m = 1 + (m - 1) by omega]; exact hdead 1 h1 _)
      | succ n ih =>
        have hrn : r (n + 1) = some ⟨pos T P (n + 1), pos_lt T P hP (n + 1)⟩ := by
          rw [hstep', ih.1]
          show (if w n = b (pos T P n) then _ else none) = _
          rw [ite_eq_left (by rw [b_pos b T P hP hper]; exact ih.2)]
          rfl
        refine ⟨hrn, ?_⟩
        by_contra hne
        have h2 : r (n + 2) = none := by
          rw [hstep', hrn]
          show (if w (n + 1) = b (pos T P (n + 1)) then _ else none) = none
          rw [ite_eq_right (by rw [b_pos b T P hP hper]; exact hne)]
        obtain ⟨m, hm, hmacc⟩ := hacc (n + 2)
        exact hmacc (by rw [show m = n + 2 + (m - (n + 2)) by omega]; exact hdead _ h2 _)
    funext n
    exact (key n).2
  · rintro rfl
    refine ⟨fun n => some ⟨pos T P n, pos_lt T P hP n⟩, rfl, fun n => ?_,
      fun N => ⟨N, le_refl N, Option.some_ne_none _⟩⟩
    show some _ = (if w n = w (pos T P n) then _ else none)
    rw [ite_eq_left (b_pos w T P hP hper n).symm]
    rfl

end Lasso

/-! ### Pumping an accepting run -/

/-- **If a Büchi automaton accepts exactly `b`, then `b` is eventually periodic.** -/
theorem eventuallyPeriodic_of_accepts_iff {b : ℕ → Bool} (B : Buchi Bool)
    (hB : ∀ w, B.Accepts w ↔ w = b) : EventuallyPeriodic b := by
  obtain ⟨r, h0, hstep, hacc⟩ := (hB b).2 rfl
  have := B.fin
  -- an accepting state at two times `m < n`
  have hinf : Set.Infinite {k | r k ∈ B.acc} :=
    Set.infinite_of_forall_exists_gt fun a => by
      obtain ⟨k, hk, hkacc⟩ := hacc (a + 1)
      exact ⟨k, hkacc, by omega⟩
  have := hinf.to_subtype
  obtain ⟨x, y, hxy, hxyr⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : {k | r k ∈ B.acc} => r k)
  have hne : (x : ℕ) ≠ y := fun h => hxy (Subtype.ext h)
  obtain ⟨m, n, hmn, hrmn, hmacc⟩ : ∃ m n, m < n ∧ r m = r n ∧ r m ∈ B.acc := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨x, y, h, hxyr, x.2⟩
    · exact ⟨y, x, h, hxyr.symm, y.2⟩
  -- the pumped word and its run
  let L := n - m
  have hL : 0 < L := by omega
  let φ : ℕ → ℕ := fun t => if t < m then t else m + (t - m) % L
  have hφ_ge : ∀ t, m ≤ t → φ t = m + (t - m) % L := fun t ht => by
    simp only [φ, ite_eq_right (show ¬ t < m by omega)]
  have hφ_lt : ∀ t, φ t < n := fun t => by
    simp only [φ]; split_ifs
    · omega
    · have := Nat.mod_lt (t - m) hL; omega
  have hrφ : ∀ t, r (φ (t + 1)) = r (φ t + 1) := by
    intro t
    by_cases ht : t + 1 < m
    · simp only [φ, ite_eq_left ht, ite_eq_left (show t < m by omega)]
    · by_cases ht' : t < m
      · have : t + 1 = m := by omega
        rw [hφ_ge (t + 1) (by omega), this, Nat.sub_self, Nat.zero_mod, Nat.add_zero]
        simp only [φ, ite_eq_left ht']
        rw [this]
      · rw [hφ_ge t (by omega), hφ_ge (t + 1) (by omega), show t + 1 - m = (t - m) + 1 by omega]
        have hj := Nat.mod_lt (t - m) hL
        have hdiv := Nat.div_add_mod (t - m) L
        by_cases hjL : (t - m) % L + 1 < L
        · rw [show (t - m) + 1 = L * ((t - m) / L) + ((t - m) % L + 1) by omega, Nat.mul_add_mod,
            Nat.mod_eq_of_lt hjL, Nat.add_assoc]
        · have hjL' : (t - m) % L + 1 = L := by omega
          rw [show (t - m) + 1 = L * ((t - m) / L + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
            Nat.mul_mod_right, Nat.add_zero, Nat.add_assoc, hjL', show m + L = n by omega]
          exact hrmn
  have hacc' : (fun t => b (φ t)) = b := by
    refine (hB _).1 ⟨fun t => r (φ t), ?_, fun t => ?_, fun N => ?_⟩
    · show r (φ 0) = B.init
      have hφ0 : φ 0 = 0 := by
        simp only [φ]
        split_ifs with h
        · rfl
        · rw [show m = 0 by omega]; simp
      rw [hφ0]; exact h0
    · show B.step (r (φ t)) (b (φ t)) (r (φ (t + 1)))
      rw [hrφ t]; exact hstep (φ t)
    · refine ⟨m + L * (N + 1), by have := Nat.le_mul_of_pos_left (N + 1) hL; omega, ?_⟩
      show r (φ (m + L * (N + 1))) ∈ B.acc
      rw [hφ_ge _ (by omega), show m + L * (N + 1) - m = L * (N + 1) by omega, Nat.mul_mod_right,
        Nat.add_zero]
      exact hmacc
  refine ⟨m, L, hL, fun t ht => ?_⟩
  have e1 := congrFun hacc' (t + L)
  have e2 := congrFun hacc' t
  rw [← e1, ← e2, hφ_ge _ (by omega), hφ_ge _ ht, show t + L - m = (t - m) + L by omega,
    Nat.add_mod_right]

/-! ### The equivalence -/

/-- **The singleton `{b}` is ω-regular iff `b` is eventually periodic.** -/
theorem eventuallyPeriodic_iff_omegaRegular_singleton (b : ℕ → Bool) :
    EventuallyPeriodic b ↔ ∃ B : Buchi Bool, ∀ w, B.Accepts w ↔ w = b := by
  refine ⟨fun ⟨T, P, hP, hper⟩ => ⟨lasso b T P hP, lasso_accepts_iff b T P hP hper⟩,
    fun ⟨B, hB⟩ => eventuallyPeriodic_of_accepts_iff B hB⟩

/-- **Problem 1 ⟺ no Büchi automaton accepts exactly the center column**. -/
theorem problem1_iff_not_omega_regular : Rule30Prize.Problem1 ↔
    ¬ ∃ B : Buchi Bool, ∀ w, B.Accepts w ↔ w = Rule30Prize.center :=
  problem1_iff_not_eventuallyPeriodic.trans (not_congr (eventuallyPeriodic_iff_omegaRegular_singleton c))

end Rule30Equivalents.OmegaRegular
