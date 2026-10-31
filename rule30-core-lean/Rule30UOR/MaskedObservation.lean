module

public import Rule30UOR.Scale
public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# Exact information bound for a periodic-center hypothesis

The mathematical statements are authored in `rule30-paper/src/Observations.lex.tex`.
This host module connects their observation vocabulary to the Prize Kit evolution.

With matching center windows, the left row prefix and its column-minus-one time trace
determine one another. Black center times fix the neighbor, so only white times need be
recorded. Pigeonhole then bounds the first repeated prefix by the number of compressed
traces. The moving left edge gives a necessary information inequality. No independence,
mixing, or complexity lower bound is assumed; the inequality does not prove Problem 1.
-/

@[expose] public section

namespace Rule30UOR.MaskedObservation

open Ruliology.CellularAutomata Rule30Jen Rule30Prize

def leftDigit (t k : Nat) : Bool := cell t (-(k : Int))

def CenterWindowAgree (t1 t2 n : Nat) : Prop :=
  ∀ s : Nat, s ≤ n → center (t1 + s) = center (t2 + s)

def LeftPrefixAgree (t1 t2 n : Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → k ≤ n → leftDigit t1 k = leftDigit t2 k

def WhiteTraceAgree (t1 t2 n : Nat) : Prop :=
  ∀ s : Nat, s < n → center (t1 + s) = false →
    leftDigit (t1 + s) 1 = leftDigit (t2 + s) 1

/-- The first `M` samples in one temporal residue have distinct left row prefixes. -/
def PrefixSeparated (t P n M : Nat) : Prop :=
  ∀ a b : Nat, a < M → b < M → LeftPrefixAgree (t + a * P) (t + b * P) n → a = b

/-- Only the free, white-center observations are stored. -/
def whiteTrace : Nat → Nat → List Bool
  | _, 0 => []
  | t, n + 1 => if center t then whiteTrace (t + 1) n else leftDigit t 1 :: whiteTrace (t + 1) n

def whiteCount (t n : Nat) : Nat := (whiteTrace t n).length

theorem white_count_zero (t : Nat) : whiteCount t 0 = 0 := rfl

theorem white_count_black_step (t n : Nat) (h : center t = true) :
    whiteCount t (n + 1) = whiteCount (t + 1) n := by
  simp [whiteCount, whiteTrace, h]

theorem white_count_white_step (t n : Nat) (h : center t = false) :
    whiteCount t (n + 1) = whiteCount (t + 1) n + 1 := by
  simp [whiteCount, whiteTrace, h]

/-- The paper uses the LexLean core center; the kit bridge identifies the readout. -/
theorem white_count_black_step_core (t n : Nat) (h : Rule30UOR.Core.center t = true) :
    whiteCount t (n + 1) = whiteCount (t + 1) n :=
  white_count_black_step t n (by simpa only [Rule30UOR.Scale.center_eq_kit] using h)

theorem white_count_white_step_core (t n : Nat) (h : Rule30UOR.Core.center t = false) :
    whiteCount t (n + 1) = whiteCount (t + 1) n + 1 :=
  white_count_white_step t n (by simpa only [Rule30UOR.Scale.center_eq_kit] using h)

private theorem window_succ {t1 t2 n : Nat} (h : CenterWindowAgree t1 t2 (n + 1)) :
    CenterWindowAgree (t1 + 1) (t2 + 1) n := by
  intro s hs
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (s + 1) (by omega)

theorem whiteTrace_eq_iff {t1 t2 n : Nat} (hc : CenterWindowAgree t1 t2 n) :
    whiteTrace t1 n = whiteTrace t2 n ↔ WhiteTraceAgree t1 t2 n := by
  induction n generalizing t1 t2 with
  | zero => simp [whiteTrace, WhiteTraceAgree]
  | succ n ih =>
    have hc0 : center t1 = center t2 := by simpa using hc 0 (by omega)
    have hn := ih (window_succ hc)
    cases h1 : center t1
    · have h2 : center t2 = false := hc0.symm.trans h1
      simp only [whiteTrace, h1, h2, Bool.false_eq_true, ite_false, List.cons.injEq]
      rw [hn]
      constructor
      · rintro ⟨hhead, htail⟩ s hs hw
        cases s with
        | zero => simpa using hhead
        | succ s =>
          have hh := htail s (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      · intro h
        refine ⟨by simpa using h 0 (by omega) (by simpa using h1), ?_⟩
        intro s hs hw
        have hh := h (s + 1) (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · have h2 : center t2 = true := hc0.symm.trans h1
      simp only [whiteTrace, h1, h2, ite_true]
      rw [hn]
      constructor
      · intro h s hs hw
        cases s with
        | zero => simp [h1] at hw
        | succ s =>
          have hh := h s (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      · intro h s hs hw
        have hh := h (s + 1) (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem whiteCount_eq_of_window {t1 t2 n : Nat} (hc : CenterWindowAgree t1 t2 n) :
    whiteCount t1 n = whiteCount t2 n := by
  induction n generalizing t1 t2 with
  | zero => rfl
  | succ n ih =>
    have hc0 : center t1 = center t2 := by simpa using hc 0 (by omega)
    have hn := ih (window_succ hc)
    cases h1 : center t1
    · rw [white_count_white_step _ _ h1,
        white_count_white_step _ _ (hc0.symm.trans h1), hn]
    · rw [white_count_black_step _ _ h1,
        white_count_black_step _ _ (hc0.symm.trans h1), hn]

private theorem full_trace_of_white {t1 t2 n : Nat} (hc : CenterWindowAgree t1 t2 n)
    (hw : WhiteTraceAgree t1 t2 n) :
    ∀ s : Nat, s < n → cell (t1 + s) (-1) = cell (t2 + s) (-1) := by
  intro s hs
  cases h1 : center (t1 + s)
  · exact hw s hs h1
  · have h2 : center (t2 + s) = true := (hc s (by omega)).symm.trans h1
    have hl1 := Rule30MaskedJen.left_of_black (t1 + s) 0 h1
    have hl2 := Rule30MaskedJen.left_of_black (t2 + s) 0 h2
    change cell (t1 + s) (-1) = !center (t1 + s + 1) at hl1
    change cell (t2 + s) (-1) = !center (t2 + s + 1) at hl2
    rw [hl1, hl2]
    have hn := hc (s + 1) (by omega)
    simpa [center, Nat.add_assoc] using congrArg Bool.not hn

theorem prefix_of_white_trace {t1 t2 n : Nat} (hc : CenterWindowAgree t1 t2 n)
    (hw : WhiteTraceAgree t1 t2 n) : LeftPrefixAgree t1 t2 n := by
  intro k hk hkn
  have ht := full_trace_of_white hc hw
  have hh := (Rule30MaskedJen.determine (i := -1) (t₁ := t1) (t₂ := t2) (n - 1)
    (fun s hs => ht s (by omega)) (by
      intro s hs
      change (cell (t1 + s) (-1) || cell (t1 + s) 0) =
        (cell (t2 + s) (-1) || cell (t2 + s) 0)
      change (cell (t1 + s) (-1) || center (t1 + s)) =
        (cell (t2 + s) (-1) || center (t2 + s))
      rw [ht s (by omega), hc s (by omega)]) (k - 1) 0 (by omega)).1
  change cell t1 (-(k : Int)) = cell t2 (-(k : Int))
  simpa only [Nat.add_zero, show (-1 : Int) - ((k - 1 : Nat) : Int) = -(k : Int) by omega]
    using hh

theorem trace_of_prefix {t1 t2 n : Nat} (hc : CenterWindowAgree t1 t2 n)
    (hp : LeftPrefixAgree t1 t2 n) :
    ∀ s : Nat, s < n → cell (t1 + s) (-1) = cell (t2 + s) (-1) := by
  have triangle : ∀ s : Nat, s ≤ n → ∀ p : Int,
      -((n - s : Nat) : Int) ≤ p → p < 0 → cell (t1 + s) p = cell (t2 + s) p := by
    intro s
    induction s with
    | zero =>
      intro hs p hp1 hp2
      have hh := hp (-p).toNat (by omega) (by omega)
      simpa [leftDigit, Int.toNat_of_nonneg (show 0 ≤ -p by omega)] using hh
    | succ s ih =>
      intro hs p hp1 hp2
      have he : ∀ q : Int, -((n - s : Nat) : Int) ≤ q → q ≤ 0 →
          cell (t1 + s) q = cell (t2 + s) q := by
        intro q hq1 hq2
        by_cases hq : q = 0
        · subst q; exact hc s (by omega)
        · exact ih (by omega) q hq1 (by omega)
      rw [show t1 + (s + 1) = (t1 + s) + 1 by omega,
        show t2 + (s + 1) = (t2 + s) + 1 by omega]
      change rule (cell (t1 + s) (p - 1)) (cell (t1 + s) p) (cell (t1 + s) (p + 1)) = _
      rw [he (p - 1) (by omega) (by omega), he p (by omega) (by omega),
        he (p + 1) (by omega) (by omega)]
      rfl
  intro s hs
  exact triangle s (by omega) (-1) (by omega) (by omega)

/-- Exact finite observation equivalence. Black center phases contribute no free bits. -/
theorem prefix_agreement_iff_white_trace (t1 t2 n : Nat) (hc : CenterWindowAgree t1 t2 n) :
    LeftPrefixAgree t1 t2 n ↔ WhiteTraceAgree t1 t2 n :=
  ⟨fun hp s hs _ => trace_of_prefix hc hp s hs, prefix_of_white_trace hc⟩

private theorem periodic_window {T P : Nat} (hc : ∀ t, T ≤ t → center (t + P) = center t)
    (t a b n : Nat) (ht : T ≤ t) : CenterWindowAgree (t + a * P) (t + b * P) n := by
  intro s hs
  have ha := periodic_mul hc a (t + s) (by omega)
  have hb := periodic_mul hc b (t + s) (by omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha.trans hb.symm

/-- Compressed traces give a repetition bound of `2 ^ whiteCount`, without an
independence assumption on those bits or on the initial state. -/
theorem compressed_prefix_repeat_pow {T P : Nat}
    (hc : ∀ t, T ≤ t → center (t + P) = center t) (t n : Nat) (ht : T ≤ t) :
    ∃ a b : Nat, a < b ∧ b ≤ 2 ^ whiteCount t n ∧
      LeftPrefixAgree (t + a * P) (t + b * P) n := by
  obtain ⟨a, b, hab, hb, he⟩ := Rule30UOR.KitConstructive.pigeonhole (whiteCount t n)
    (fun m => whiteTrace (t + m * P) n) (fun m => by
      change whiteCount (t + m * P) n = whiteCount t n
      simpa only [Nat.zero_mul, Nat.add_zero] using
        whiteCount_eq_of_window (periodic_window hc t m 0 n ht))
  exact ⟨a, b, hab, hb,
    prefix_of_white_trace (periodic_window hc t a b n ht)
      ((whiteTrace_eq_iff (periodic_window hc t a b n ht)).mp he)⟩

private theorem pow_eq_twopow (n : Nat) : 2 ^ n = Rule30UOR.Core.twopow n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Rule30UOR.Core.twopow, Nat.pow_succ, ih, Nat.mul_two]

private theorem kit_period {T P : Nat} (hc : Rule30UOR.Scale.CenterPeriodic T P) :
    ∀ t, T ≤ t → center (t + P) = center t := by
  intro t ht
  simpa only [Rule30UOR.Scale.center_eq_kit] using hc t ht

/-- Every separated finite family, not merely consecutive repeated samples, is bounded
by the number of white-mask codes. This is a complexity *upper* bound. -/
theorem separated_prefix_bound (T P t n M : Nat) (_hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t)
    (hsep : PrefixSeparated t P n M) :
    M ≤ Rule30UOR.Core.twopow (whiteCount t n) := by
  let codes := (List.range M).map (fun a => whiteTrace (t + a * P) n)
  have hnd : codes.Nodup := nodup_map_of_inj _ (Rule30UOR.Constructive.nodup_range _) (by
    intro a ha b hb he
    have hw := periodic_window (kit_period hc) t a b n ht
    exact hsep a b (List.mem_range.mp ha) (List.mem_range.mp hb)
      (prefix_of_white_trace hw ((whiteTrace_eq_iff hw).mp he)))
  have hle := Rule30UOR.KitConstructive.length_le_of_subset hnd (l₂ := allLists (whiteCount t n)) (by
    intro code hcode
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hcode
    have hh := mem_allLists (whiteTrace (t + a * P) n)
    have hlen : (whiteTrace (t + a * P) n).length = whiteCount t n := by
      change whiteCount (t + a * P) n = whiteCount t n
      simpa only [Nat.zero_mul, Nat.add_zero] using
        whiteCount_eq_of_window (periodic_window (kit_period hc) t a 0 n ht)
    rwa [hlen] at hh)
  simpa only [codes, List.length_map, List.length_range, length_allLists, pow_eq_twopow] using hle

/-- Paper-facing repetition bound. -/
theorem compressed_prefix_repeat (T P t n : Nat) (_hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    ∃ a b : Nat, a < b ∧ b ≤ Rule30UOR.Core.twopow (whiteCount t n) ∧
      LeftPrefixAgree (t + a * P) (t + b * P) n := by
  simpa only [pow_eq_twopow] using compressed_prefix_repeat_pow (kit_period hc) t n ht

/-- The single seed's moving edge bounds how much observation compression is possible.
This is a necessary inequality, not a contradiction for a general periodic word. -/
theorem edge_information_bound (T P t n : Nat) (hP : 0 < P)
    (hc : Rule30UOR.Scale.CenterPeriodic T P) (ht : T ≤ t) :
    n < t + Rule30UOR.Core.twopow (whiteCount t n) * P := by
  apply Nat.lt_of_not_ge
  intro hn
  obtain ⟨a, b, hab, hb, hp⟩ := compressed_prefix_repeat T P t n hP hc ht
  have hmul : a * P < b * P := Nat.mul_lt_mul_of_pos_right hab hP
  have hupper : b * P ≤ Rule30UOR.Core.twopow (whiteCount t n) * P := Nat.mul_le_mul_right P hb
  have he := hp (t + b * P) (by omega) (by omega)
  unfold leftDigit at he
  rw [cell_eq_false_of_lt (t + a * P) _ (by omega), cell_left_edge] at he
  contradiction

/-- Audit: `2^w` already dominates `w+1`, so a linear window bound of this form
automatically satisfies the numerical edge inequality. This prevents interpreting the
information inequality as a refutation of general periodic masks. -/
theorem information_bound_audit (n t w P : Nat) (hn : n < (w + 1) * P) :
    n < t + Rule30UOR.Core.twopow w * P := by
  have hpow : ∀ w : Nat, w + 1 ≤ Rule30UOR.Core.twopow w := by
    intro w
    induction w with
    | zero => exact Nat.le_refl _
    | succ w ih =>
      rw [Rule30UOR.Core.twopow_succ]
      omega
  have hm := Nat.mul_le_mul_right P (hpow w)
  omega

end Rule30UOR.MaskedObservation
