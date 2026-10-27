module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30: every column is realizable, and Jen's hypotheses do not decide Problem 1

Two barriers for proofs of Problem 1.

**Realization.** Run rule 30 from an arbitrary configuration `x : Int → Bool` (`evol x`).
* `realize`, `unique`, `column_realizable_unique`: **for every right half `R` (positions
  `p ≥ 1`) and every target column `c : Nat → Bool` there is exactly one configuration that
  agrees with `R` on `p ≥ 1` and whose column `0` is `c`.** The left half is rebuilt column by
  column by left-permutivity (`lc`); the right half is the half driven by `c` (`rh`).
* `seed_perturbation`: for every `n` some configuration agrees with the single seed on all
  positions `≥ -n`, has column `0` equal to the rule-30 center column up to time `n`, and white
  from then on. So no argument that ignores the far left of the configuration can show that the
  center column is not eventually constant, let alone aperiodic. (Such a configuration must
  differ from the seed somewhere left of `-n`, because the seed's center column is not
  eventually constant, `Rule30Prize.no_column_eventually_constant`.)

**Rules 90, 150 and 210.** Consider `left xor g(center, right)` from a single black cell
(`run g`), for any `g` with `g 0 0 = 0` and `g 0 1 = 1`; rule 30 is `g = or` (`run30_eq_cell`).
* `run_not_adjacent`: every such rule is left-permutive with a left edge moving one cell per
  step, and Jen's adjacent-column theorem holds for it verbatim.
* `center90`, `center150`, `center210`, `barrier`: for `g = fun _ r => r` (rule 90),
  `g = xor` (rule 150) and `g = fun c r => !c && r` (rule 210, nonlinear and not right-permutive,
  like rule 30) the single-seed center column is eventually constant. So left-permutivity, the
  left edge and Jen's theorem cannot by themselves imply Problem 1, not even its period-1 case;
  a proof must use something specific to rule 30's `or` together with the finite seed.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242, for
Jen's argument.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Realization

open Rule30Jen

/-! ### Realization from an arbitrary configuration -/

/-- Rule 30 from an arbitrary configuration. -/
def evol (x : Int → Bool) : Nat → Int → Bool
  | 0, p => x p
  | t + 1, p => rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1))

/-- The right half (positions `≥ 1`) driven at position `0` by the column `c`. -/
def rh (R : Int → Bool) (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => R p
  | t + 1, p => rule (if p = 1 then c t else rh R c t (p - 1)) (rh R c t p) (rh R c t (p + 1))

/-- Column `-1`, forced by the requirement that column `0` follows `c`. -/
def ycol (R : Int → Bool) (c : Nat → Bool) (t : Nat) : Bool :=
  xor (c (t + 1)) (c t || rh R c t 1)

/-- `lc m t`: the column at position `-m`, rebuilt leftwards by left-permutivity. -/
def lc (R : Int → Bool) (c : Nat → Bool) : Nat → Nat → Bool
  | 0, t => c t
  | 1, t => ycol R c t
  | m + 2, t => xor (lc R c (m + 1) (t + 1)) (lc R c (m + 1) t || lc R c m t)

/-- The configuration: `R` on the right, the rebuilt left half at time `0` on the left. -/
def conf (R : Int → Bool) (c : Nat → Bool) (p : Int) : Bool :=
  if 1 ≤ p then R p else lc R c (-p).toNat 0

theorem xor_xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem lc_step (R : Int → Bool) (c : Nat → Bool) (m t : Nat) :
    rule (lc R c (m + 2) t) (lc R c (m + 1) t) (lc R c m t) = lc R c (m + 1) (t + 1) := by
  show xor (xor (lc R c (m + 1) (t + 1)) (lc R c (m + 1) t || lc R c m t))
    (lc R c (m + 1) t || lc R c m t) = _
  exact xor_xor_cancel _ _

theorem center_step (R : Int → Bool) (c : Nat → Bool) (t : Nat) :
    rule (lc R c 1 t) (lc R c 0 t) (rh R c t 1) = lc R c 0 (t + 1) := by
  show xor (xor (c (t + 1)) (c t || rh R c t 1)) (c t || rh R c t 1) = c (t + 1)
  exact xor_xor_cancel _ _

/-- **The evolution of `conf R c`**: on the right it is the driven right half, on the left
(including column `0`) it is the rebuilt left columns. -/
theorem evol_conf (R : Int → Bool) (c : Nat → Bool) : ∀ t p,
    evol (conf R c) t p = if 1 ≤ p then rh R c t p else lc R c (-p).toNat t
  | 0, p => by
    simp only [evol, conf]
    by_cases h : 1 ≤ p
    · rw [ite_eq_left h, ite_eq_left h]; rfl
    · rw [ite_eq_right h, ite_eq_right h]
  | t + 1, p => by
    have ih := evol_conf R c t
    show rule (evol (conf R c) t (p - 1)) (evol (conf R c) t p) (evol (conf R c) t (p + 1)) = _
    rw [ih (p - 1), ih p, ih (p + 1)]
    by_cases h1 : 1 ≤ p
    · have e1 : (if 1 ≤ p then rh R c (t + 1) p else lc R c (-p).toNat (t + 1)) = rh R c (t + 1) p :=
        ite_eq_left h1
      have e2 : (if 1 ≤ p then rh R c t p else lc R c (-p).toNat t) = rh R c t p := ite_eq_left h1
      have e3 : (if 1 ≤ p + 1 then rh R c t (p + 1) else lc R c (-(p + 1)).toNat t) = rh R c t (p + 1) :=
        ite_eq_left (by omega)
      rw [e1, e2, e3]
      show _ = rule (if p = 1 then c t else rh R c t (p - 1)) (rh R c t p) (rh R c t (p + 1))
      by_cases h2 : p = 1
      · subst h2
        rw [ite_eq_right (by decide), ite_eq_left rfl]
        rfl
      · rw [ite_eq_left (show 1 ≤ p - 1 by omega), ite_eq_right h2]
    · have e1 : (if 1 ≤ p then rh R c (t + 1) p else lc R c (-p).toNat (t + 1)) = lc R c (-p).toNat (t + 1) :=
        ite_eq_right h1
      have e2 : (if 1 ≤ p then rh R c t p else lc R c (-p).toNat t) = lc R c (-p).toNat t := ite_eq_right h1
      have e4 : (if 1 ≤ p - 1 then rh R c t (p - 1) else lc R c (-(p - 1)).toNat t) =
          lc R c (-(p - 1)).toNat t := ite_eq_right (by omega)
      rw [e1, e2, e4]
      by_cases h0 : p = 0
      · subst h0
        rw [ite_eq_left (by decide)]
        exact center_step R c t
      · -- p ≤ -1: write -p = m + 1
        obtain ⟨m, hm⟩ : ∃ m : Nat, (-p).toNat = m + 1 := ⟨(-p).toNat - 1, by omega⟩
        rw [ite_eq_right (show ¬ 1 ≤ p + 1 by omega), hm,
          show (-(p - 1)).toNat = m + 2 by omega, show (-(p + 1)).toNat = m by omega]
        exact lc_step R c m t

/-- **Realization**: for every right half `R` and every target column `c`, the configuration
`conf R c` agrees with `R` on positions `≥ 1` and its column `0` is exactly `c`. -/
theorem realize (R : Int → Bool) (c : Nat → Bool) :
    (∀ p, 1 ≤ p → conf R c p = R p) ∧ ∀ t, evol (conf R c) t 0 = c t := by
  refine ⟨fun p hp => by simp [conf, hp], fun t => ?_⟩
  rw [evol_conf R c t 0, ite_eq_right (by decide)]
  rfl

/-! ### Uniqueness: the left half is determined by the right half and column `0` -/

/-- Rule 30 can be solved for the left cell. -/
theorem rule_left (a b d : Bool) : a = xor (rule a b d) (b || d) := by
  cases a <;> cases b <;> cases d <;> rfl

/-- If two configurations agree on positions `≥ 1` and have the same column `0`, their right
halves agree at all times. -/
theorem right_agree {x x' : Int → Bool} (hR : ∀ p, 1 ≤ p → x p = x' p)
    (h0 : ∀ t, evol x t 0 = evol x' t 0) : ∀ t p, 0 ≤ p → evol x t p = evol x' t p
  | 0, p, hp => by
    by_cases h : p = 0
    · subst h; exact h0 0
    · exact hR p (by omega)
  | t + 1, p, hp => by
    by_cases h : p = 0
    · subst h; exact h0 (t + 1)
    · show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) =
        rule (evol x' t (p - 1)) (evol x' t p) (evol x' t (p + 1))
      rw [right_agree hR h0 t (p - 1) (by omega), right_agree hR h0 t p hp,
        right_agree hR h0 t (p + 1) (by omega)]

/-- Then the left halves agree too, column by column (left-permutivity). -/
theorem left_agree {x x' : Int → Bool} (hR : ∀ p, 1 ≤ p → x p = x' p)
    (h0 : ∀ t, evol x t 0 = evol x' t 0) :
    ∀ m : Nat, ∀ t, evol x t (-(m : Int)) = evol x' t (-(m : Int)) ∧
      evol x t (-(m : Int) + 1) = evol x' t (-(m : Int) + 1)
  | 0, t => ⟨by simpa using h0 t, right_agree hR h0 t _ (by omega)⟩
  | m + 1, t => by
    have ih := left_agree hR h0 m
    refine ⟨?_, ?_⟩
    · have e : ∀ y : Int → Bool, evol y t (-((m + 1 : Nat) : Int)) =
          xor (evol y (t + 1) (-(m : Int))) (evol y t (-(m : Int)) || evol y t (-(m : Int) + 1)) := by
        intro y
        have := rule_left (evol y t (-((m + 1 : Nat) : Int))) (evol y t (-(m : Int)))
          (evol y t (-(m : Int) + 1))
        rw [this]
        show xor (rule _ _ _) _ = xor (rule (evol y t (-(m : Int) - 1)) _ _) _
        rw [show -(m : Int) - 1 = -((m + 1 : Nat) : Int) by omega]
      rw [e x, e x', (ih (t + 1)).1, (ih t).1, (ih t).2]
    · rw [show -((m + 1 : Nat) : Int) + 1 = -(m : Int) by omega]
      exact (ih t).1

/-- **Uniqueness**: a configuration is determined by its right half and its column `0`. -/
theorem unique {x x' : Int → Bool} (hR : ∀ p, 1 ≤ p → x p = x' p)
    (h0 : ∀ t, evol x t 0 = evol x' t 0) : x = x' := by
  funext p
  by_cases hp : 0 ≤ p
  · exact right_agree hR h0 0 p hp
  · have := (left_agree hR h0 (-p).toNat 0).1
    rwa [show -(((-p).toNat : Nat) : Int) = p by omega] at this

/-- **Every eventually periodic column is realizable with any right half**: so a proof that a
column is aperiodic must use the left half (for the single seed: its left edge). -/
theorem column_realizable_unique (R : Int → Bool) (c : Nat → Bool) :
    ∃ x : Int → Bool, (∀ p, 1 ≤ p → x p = R p) ∧ (∀ t, evol x t 0 = c t) ∧
      ∀ x' : Int → Bool, (∀ p, 1 ≤ p → x' p = R p) → (∀ t, evol x' t 0 = c t) → x' = x :=
  ⟨conf R c, (realize R c).1, (realize R c).2, fun _ h1 h2 =>
    unique (fun p hp => (h1 p hp).trans ((realize R c).1 p hp).symm)
      (fun t => (h2 t).trans ((realize R c).2 t).symm)⟩

/-! ### Finite dependence, and the single seed -/

/-- The driven right half up to time `t` only sees `c` before `t`. -/
theorem rh_congr (R : Int → Bool) {c c' : Nat → Bool} :
    ∀ t, (∀ s, s < t → c s = c' s) → ∀ p, rh R c t p = rh R c' t p
  | 0, _, p => rfl
  | t + 1, h, p => by
    show rule (if p = 1 then c t else rh R c t (p - 1)) (rh R c t p) (rh R c t (p + 1)) =
      rule (if p = 1 then c' t else rh R c' t (p - 1)) (rh R c' t p) (rh R c' t (p + 1))
    have ih := rh_congr R t (fun s hs => h s (by omega))
    rw [ih (p - 1), ih p, ih (p + 1), h t (by omega)]

/-- The rebuilt column `-m` at time `t` only sees `c` up to time `m + t`. -/
theorem lc_congr (R : Int → Bool) {c c' : Nat → Bool} :
    ∀ m t, (∀ s, s ≤ m + t → c s = c' s) → lc R c m t = lc R c' m t
  | 0, t, h => h t (by omega)
  | 1, t, h => by
    show xor (c (t + 1)) (c t || rh R c t 1) = xor (c' (t + 1)) (c' t || rh R c' t 1)
    rw [h (t + 1) (by omega), h t (by omega), rh_congr R t (fun s hs => h s (by omega)) 1]
  | m + 2, t, h => by
    show xor (lc R c (m + 1) (t + 1)) (lc R c (m + 1) t || lc R c m t) =
      xor (lc R c' (m + 1) (t + 1)) (lc R c' (m + 1) t || lc R c' m t)
    rw [lc_congr R (m + 1) (t + 1) (fun s hs => h s (by omega)),
      lc_congr R (m + 1) t (fun s hs => h s (by omega)), lc_congr R m t (fun s hs => h s (by omega))]

/-- The single seed. -/
def seed (p : Int) : Bool := decide (p = 0)

theorem evol_seed : ∀ t p, evol seed t p = cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show rule (evol seed t (p - 1)) (evol seed t p) (evol seed t (p + 1)) = cell (t + 1) p
    rw [evol_seed t (p - 1), evol_seed t p, evol_seed t (p + 1)]
    rfl

/-- **The left edge is essential, already for period 1.** For every `n` there is a
configuration that agrees with the single seed at all positions `≥ -n`, whose column `0`
agrees with the center column of rule 30 up to time `n`, and is white from then on. (It differs
from the seed at infinitely many positions `< -n`; by `no_column_eventually_constant`, no
left-finite such configuration exists for the seed itself.) -/
theorem seed_perturbation (n : Nat) :
    ∃ x : Int → Bool, (∀ p : Int, -(n : Int) ≤ p → x p = seed p) ∧
      (∀ t, t ≤ n → evol x t 0 = cell t 0) ∧ (∀ t, n < t → evol x t 0 = false) := by
  let c' : Nat → Bool := fun t => if t ≤ n then cell t 0 else false
  let cs : Nat → Bool := fun t => cell t 0
  have hreal := realize seed c'
  -- the seed itself is `conf seed cs`, by uniqueness
  have hseed : seed = conf seed cs := by
    refine unique (fun p hp => ((realize seed cs).1 p hp).symm) (fun t => ?_)
    rw [(realize seed cs).2 t, evol_seed]
  refine ⟨conf seed c', fun p hp => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · by_cases h1 : 1 ≤ p
    · exact hreal.1 p h1
    · have e : conf seed c' p = lc seed c' (-p).toNat 0 := ite_eq_right h1
      have e' : conf seed cs p = lc seed cs (-p).toNat 0 := ite_eq_right h1
      rw [e, show seed p = conf seed cs p from congrFun hseed p, e']
      exact lc_congr seed (-p).toNat 0 (fun s hs => by
        show (if s ≤ n then cell s 0 else false) = cell s 0
        rw [ite_eq_left (by omega)])
  · rw [hreal.2 t]; show (if t ≤ n then cell t 0 else false) = _; rw [ite_eq_left ht]
  · rw [hreal.2 t]; show (if t ≤ n then cell t 0 else false) = _; rw [ite_eq_right (by omega)]


/-! ### Left-permutive rules from a single seed -/

/-- The rule `left xor g(center, right)` from a single black cell at `0`. -/
def run (g : Bool → Bool → Bool) : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => xor (run g t (p - 1)) (g (run g t p) (run g t (p + 1)))

section general
variable (g : Bool → Bool → Bool) (g00 : g false false = false) (g01 : g false true = true)
include g00

theorem run_eq_false_of_lt : ∀ (t : Nat) (p : Int), p < -(t : Int) → run g t p = false
  | 0, p, h => by simp [run]; omega
  | t + 1, p, h => by
    show xor (run g t (p - 1)) (g (run g t p) (run g t (p + 1))) = false
    rw [run_eq_false_of_lt t (p - 1) (by omega), run_eq_false_of_lt t p (by omega),
      run_eq_false_of_lt t (p + 1) (by omega), g00]
    rfl

include g01 in
theorem run_left_edge : ∀ t : Nat, run g t (-(t : Int)) = true
  | 0 => rfl
  | t + 1 => by
    show xor (run g t (-((t + 1 : Nat) : Int) - 1)) (g (run g t (-((t + 1 : Nat) : Int)))
      (run g t (-((t + 1 : Nat) : Int) + 1))) = true
    rw [run_eq_false_of_lt g g00 t _ (by omega), run_eq_false_of_lt g g00 t _ (by omega),
      show -((t + 1 : Nat) : Int) + 1 = -(t : Int) by omega, run_left_edge t, g01]
    rfl

omit g00 in
theorem run_left (t : Nat) (i : Int) :
    run g t (i - 1) = xor (run g (t + 1) i) (g (run g t i) (run g t (i + 1))) := by
  show run g t (i - 1) = xor (xor (run g t (i - 1)) (g (run g t i) (run g t (i + 1))))
    (g (run g t i) (run g t (i + 1)))
  cases run g t (i - 1) <;> cases g (run g t i) (run g t (i + 1)) <;> rfl

omit g00 in
theorem run_periodic_left {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → run g (t + P) i = run g t i)
    (h1 : ∀ t, T ≤ t → run g (t + P) (i + 1) = run g t (i + 1)) :
    ∀ t, T ≤ t → run g (t + P) (i - 1) = run g t (i - 1) := by
  intro t ht
  rw [run_left, run_left g t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

omit g00 in
theorem run_periodic_left_all {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → run g (t + P) i = run g t i)
    (h1 : ∀ t, T ≤ t → run g (t + P) (i + 1) = run g t (i + 1)) :
    ∀ m : Nat, (∀ t, T ≤ t → run g (t + P) (i - m) = run g t (i - m)) ∧
      ∀ t, T ≤ t → run g (t + P) (i - m + 1) = run g t (i - m + 1) := by
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · have := run_periodic_left g ih.1 ih.2
      rwa [show i - (m : Int) - 1 = i - ((m + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((m + 1 : Nat) : Int) + 1 = i - (m : Int) by omega]
      exact ih.1

include g01 in
theorem run_no_left_periodic {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ m : Nat, ∀ t, T ≤ t → run g (t + P) (i - m) = run g t (i - m)) : False := by
  let q : Int := min i (-((T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ -((T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = -q := ⟨(-q).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : run g t₁ q = true := by
    have := run_left_edge g g00 g01 t₁
    rwa [show -(t₁ : Int) = q by omega] at this
  have hwhite : run g (t₁ - P) q = false := run_eq_false_of_lt g g00 _ _ (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

include g01 in
/-- **Jen's adjacent-column theorem for every rule `left xor g(center, right)`** with
`g 0 0 = 0`, `g 0 1 = 1`. -/
theorem run_not_adjacent (i : Int) (h0 : EventuallyPeriodic fun t => run g t i)
    (h1 : EventuallyPeriodic fun t => run g t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact run_no_left_periodic g g00 g01 hP fun m => (run_periodic_left_all g hp0 hp1 m).1

end general

/-! ### Rules 90, 150 and 210: the center column is eventually constant -/

/-- Mirror symmetry of a symmetric rule from the symmetric seed. -/
theorem run_symm (g : Bool → Bool → Bool) (hs : ∀ a b c, xor a (g b c) = xor c (g b a)) :
    ∀ t p, run g t (-p) = run g t p
  | 0, p => by simp only [run]; by_cases h : p = 0 <;> simp [h]
  | t + 1, p => by
    show xor (run g t (-p - 1)) (g (run g t (-p)) (run g t (-p + 1))) =
      xor (run g t (p - 1)) (g (run g t p) (run g t (p + 1)))
    rw [show -p - 1 = -(p + 1) by omega, show -p + 1 = -(p - 1) by omega, run_symm g hs t (p + 1),
      run_symm g hs t p, run_symm g hs t (p - 1), hs]

/-- Rule 90: `left xor right`. -/
def g90 (_ r : Bool) : Bool := r
/-- Rule 150: `left xor center xor right`. -/
def g150 (c r : Bool) : Bool := xor c r
/-- Rule 210: `left xor (not center and right)`. -/
def g210 (c r : Bool) : Bool := !c && r
/-- Rule 30: `left xor (center or right)`. -/
def g30 (c r : Bool) : Bool := c || r

theorem run30_eq_cell : ∀ t p, run g30 t p = cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show xor (run g30 t (p - 1)) (g30 (run g30 t p) (run g30 t (p + 1))) = _
    rw [run30_eq_cell t (p - 1), run30_eq_cell t p, run30_eq_cell t (p + 1)]
    rfl

/-- **Rule 90**: the center column is `1, 0, 0, 0, …`. -/
theorem center90 (t : Nat) : run g90 (t + 1) 0 = false := by
  show xor (run g90 t (0 - 1)) (g90 (run g90 t 0) (run g90 t (0 + 1))) = false
  have hs := run_symm g90 (by intro a b c; cases a <;> cases c <;> rfl) t 1
  rw [show (0 : Int) - 1 = -1 by rfl, hs]
  simp [g90]

/-- **Rule 150**: the center column is constantly `1`. -/
theorem center150 : ∀ t, run g150 t 0 = true
  | 0 => rfl
  | t + 1 => by
    show xor (run g150 t (0 - 1)) (g150 (run g150 t 0) (run g150 t (0 + 1))) = true
    have hs := run_symm g150 (by intro a b c; cases a <;> cases b <;> cases c <;> rfl) t 1
    rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, hs, center150 t]
    cases run g150 t 1 <;> rfl

/-- From the single seed, rule 210 draws exactly rule 90's pattern, which lives on the cells
with `t + p` even (where the center cell is always white when it matters). -/
theorem run210_eq : ∀ t p, run g210 t p = run g90 t p ∧
    (run g90 t p = true → ((t : Int) + p) % 2 = 0)
  | 0, p => by
    refine ⟨rfl, fun h => ?_⟩
    simp [run] at h; subst h; rfl
  | t + 1, p => by
    have ih := run210_eq t
    refine ⟨?_, fun h => ?_⟩
    · show xor (run g210 t (p - 1)) (g210 (run g210 t p) (run g210 t (p + 1))) =
        xor (run g90 t (p - 1)) (g90 (run g90 t p) (run g90 t (p + 1)))
      rw [(ih (p - 1)).1, (ih p).1, (ih (p + 1)).1]
      by_cases hpar : ((t : Int) + p) % 2 = 0
      · -- neighbours have odd parity, so they are white
        have hl : run g90 t (p - 1) = false := by
          cases e : run g90 t (p - 1)
          · rfl
          · have := (ih (p - 1)).2 e; omega
        have hr : run g90 t (p + 1) = false := by
          cases e : run g90 t (p + 1)
          · rfl
          · have := (ih (p + 1)).2 e; omega
        rw [hl, hr]; simp [g210, g90]
      · -- the center has odd parity, so it is white
        have hc : run g90 t p = false := by
          cases e : run g90 t p
          · rfl
          · have := (ih p).2 e; omega
        rw [hc]; simp [g210, g90]
    · have h' : xor (run g90 t (p - 1)) (g90 (run g90 t p) (run g90 t (p + 1))) = true := h
      simp only [g90] at h'
      cases e1 : run g90 t (p - 1) <;> cases e2 : run g90 t (p + 1) <;> rw [e1, e2] at h' <;>
        simp at h'
      · have := (ih (p + 1)).2 e2; omega
      · have := (ih (p - 1)).2 e1; omega

/-- **Rule 210**: the center column is `1, 0, 0, 0, …`. -/
theorem center210 (t : Nat) : run g210 (t + 1) 0 = false := by
  rw [(run210_eq (t + 1) 0).1]; exact center90 t

/-- **Barrier.** Rules 90, 150, 210 satisfy the hypotheses of the generalized Jen theorem
(`run_not_adjacent` applies to them) and yet their center columns are eventually periodic. -/
theorem barrier :
    (∀ i, ¬ ((EventuallyPeriodic fun t => run g210 t i) ∧
      EventuallyPeriodic fun t => run g210 t (i + 1))) ∧
    (EventuallyPeriodic fun t => run g90 t 0) ∧ (EventuallyPeriodic fun t => run g150 t 0) ∧
    (EventuallyPeriodic fun t => run g210 t 0) := by
  refine ⟨fun i h => run_not_adjacent g210 rfl rfl i h.1 h.2, ⟨1, 1, by decide, fun t ht => ?_⟩,
    ⟨0, 1, by decide, fun t _ => by
      show run g150 (t + 1) 0 = run g150 t 0
      rw [center150, center150]⟩, ⟨1, 1, by decide, fun t ht => ?_⟩⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show run g90 (s + 1 + 1) 0 = run g90 (s + 1) 0
    rw [center90, center90]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show run g210 (s + 1 + 1) 0 = run g210 (s + 1) 0
    rw [center210, center210]


end Rule30Realization
end Ruliology.CellularAutomata
