module

public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# Rule 30: strip certificates exclude periodic words of the center column

Suppose the center column `c` equals `w^∞` from time `T` on (`EventuallyWord w`). Then the
cells just right of the center evolve as a finite nondeterministic system: the strip of the
next `K` cells is updated from its own cells, the known value of `c` on the left, and an unknown
cell on the right. A finite computation over this system can show that column `1`, at the white
times of `c`, is eventually periodic; masked Jen (`Rule30MaskedJen`) forbids that. Two kinds of
certificate are proved sound here.

* `problem1_iff_no_word`: Problem 1 holds exactly when no nonempty word `w` has
  `EventuallyWord w`. Each word exclusion below is one piece of Problem 1, for every transient.

**Bitmask strip certificates** (`stripCert w K k`). A strip of `K` cells is a number below
`2 ^ K`, a set of strips is a bitmask. Start from all strips, apply `k` periods of `w` (both
values of the unknown cell allowed at each step) to get `S0`. The certificate checks that one
more period maps `S0` into itself and that at every white phase of `w` column `1` is constant on
the strips reachable from `S0`.
* `not_eventually_word_strip`: **soundness.** If `w` is nonempty, `K ≥ 1` and `stripCert w K k`
  holds, then `¬ EventuallyWord w`. After `k` periods the true strip lies in `S0` at the start
  of every period, so `orCol 0` is eventually periodic, against
  `Rule30MaskedJen.orCol_not_eventuallyPeriodic`.
* `not_eventually_01111111`: the word `0 1^7` (strip width `5`). For this driver column `1`
  itself appears not to be eventually periodic in simulations, so the masked form is needed.

**Rank certificates** (`Cert`). A certificate gives every node (phase, strip of `b` cells) a
rank and a position. Along every edge, for either value of the unknown cell, the rank does not
increase. Along a rank-preserving edge the position advances like a counter modulo `m rank` at
the white phases and stays put at the black phases, and at a white phase column `1` equals letter
`position` of a fixed word attached to the rank. The Boolean check `Cert.check` verifies the
edge conditions and `Cert.checkG` that every position is below the counter period of its rank;
both are evaluated by the kernel for a concrete certificate. That the counter then returns to
its start after `m · |w|` steps is proved once for all certificates (`Cert.iterG_period`).
* `Cert.sound`, `Cert.not_eventuallyWord`: **soundness.** If both checks pass, `w` is nonempty
  and `b ≥ 1`, then `¬ EventuallyWord w`. Along the true history the rank is eventually
  constant, after which column `1` at the white times is periodic with period `m · |w|`;
  `Rule30MaskedJen.masked_jen` gives the contradiction.
  At a white phase a rank certificate lets column `1` cycle through several values (a counter
  modulo `m`), which a bitmask certificate for `w` itself cannot express.
* `not_eventually_00000011`: the word `0^6 1 1` (strip width `6`, `379` ranks).
* `not_eventually_000000000101`: the word `0^9 1 0 1` (strip width `7`, `1309` ranks).

More instances: `Rule30StripCertificateTable` (30 words of length `8 … 13`, bitmask
certificates). The rank-certificate words `0^6 1 1` and `0^9 1 0 1` are not in that table.

The certificates were found by computer search and are checked here by the kernel. Source: E. Jen,
*Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242, whose argument the
bitmask certificates generalize.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30StripCertificates

open Rule30Jen Rule30Prize Rule30MaskedJen

/-! ### Periodic words of the center column -/

/-- The center column equals `w` repeated from time `T` on, with the first letter of `w` at
time `T`. -/
def EventuallyWord (w : List Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → cell t 0 = w.getD ((t - T) % w.length) false

/-- A nonempty eventual word makes the center column eventually periodic. -/
theorem eventuallyPeriodic_of_word {w : List Bool} (hw : w ≠ []) (h : EventuallyWord w) :
    EventuallyPeriodic center := by
  obtain ⟨T, hT⟩ := h
  have hlen : 0 < w.length := List.length_pos_iff.2 hw
  refine ⟨T, w.length, hlen, fun t ht => ?_⟩
  show cell (t + w.length) 0 = cell t 0
  rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
    Nat.add_mod_right]

/-- An eventually periodic center column is eventually some nonempty word. -/
theorem word_of_eventuallyPeriodic (h : EventuallyPeriodic center) :
    ∃ w : List Bool, w ≠ [] ∧ EventuallyWord w := by
  obtain ⟨T, P, hP, hper⟩ := h
  have hperk := periodic_mul hper
  refine ⟨(List.range P).map (fun i => cell (T + i) 0), ?_, T, fun t ht => ?_⟩
  · intro e
    have := congrArg List.length e
    simp at this
    omega
  · have hlen : ((List.range P).map (fun i => cell (T + i) 0)).length = P := by simp
    rw [hlen]
    have hmod : (t - T) % P < P := Nat.mod_lt _ hP
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hmod]
    simp only [Option.map_some, Option.getD_some]
    have e := hperk ((t - T) / P) (T + (t - T) % P) (by omega)
    have hd := Nat.div_add_mod (t - T) P
    rw [show T + (t - T) % P + (t - T) / P * P = t by rw [Nat.mul_comm] at hd; omega] at e
    exact e

/-- **Problem 1 is the exclusion of every nonempty word.** -/
theorem problem1_iff_no_word : Problem1 ↔ ∀ w : List Bool, w ≠ [] → ¬ EventuallyWord w :=
  ⟨fun h w hw hew => h (eventuallyPeriodic_of_word hw hew),
    fun h hp => by
      obtain ⟨w, hw, hew⟩ := word_of_eventuallyPeriodic hp
      exact h w hw hew⟩

/-! ### Bitmask strip certificates

A strip of `K` cells to the right of column `j` is encoded as a number `r < 2 ^ K` whose bit `k`
is `cell t (j + 1 + k)`. One step needs the column's value (left boundary) and the cell just
right of the strip (right boundary, unknown: both values are allowed). Sets of strip states are
bitmasks. Starting from all states and applying the driver word, the reachable sets
over-approximate the true strip states; if column `j + 1` is constant on them at every white
phase, `orCol` is eventually periodic, which `orCol_not_eventuallyPeriodic` forbids. -/

theorem testBit_toNat (b : Bool) (i : Nat) : b.toNat.testBit i = (decide (i = 0) && b) := by
  cases b <;> cases i <;> simp [Bool.toNat, Nat.testBit_succ]

/-- Strip encoding: `r < 2 ^ K` and bit `k < K` of `r` is `cell t (j + 1 + k)`. -/
def Enc (K t : Nat) (j : Int) (r : Nat) : Prop :=
  r < 2 ^ K ∧ ∀ k, k < K → r.testBit k = cell t (j + 1 + k)

/-- One step of a `K`-cell strip with left boundary `a` and right boundary `z`. -/
def stripStep (K : Nat) (a z : Bool) (r : Nat) : Nat :=
  (((r <<< 1) ||| a.toNat) ^^^ (r ||| (r >>> 1) ||| (z.toNat <<< (K - 1)))) % 2 ^ K

theorem stripStep_lt (K : Nat) (a z : Bool) (r : Nat) : stripStep K a z r < 2 ^ K :=
  Nat.mod_lt _ (Nat.two_pow_pos K)

theorem testBit_stripStep (K : Nat) (a z : Bool) (r : Nat) (hr : r < 2 ^ K) (k : Nat) (hk : k < K) :
    (stripStep K a z r).testBit k =
      rule (if k = 0 then a else r.testBit (k - 1)) (r.testBit k)
        (if k + 1 = K then z else r.testBit (k + 1)) := by
  unfold stripStep
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, testBit_toNat, testBit_toNat,
    decide_eq_true hk, Bool.true_and, Nat.add_comm 1 k]
  unfold rule
  by_cases h0 : k = 0
  · subst h0
    by_cases h1 : 0 + 1 = K
    · have hb : r.testBit (0 + 1) = false := by
        rw [h1]; exact Nat.testBit_lt_two_pow hr
      simp only [ite_eq_left h1, hb]
      simp [← h1]
    · simp only [ite_eq_right h1]
      simp [show ¬ (0 ≥ K - 1) by omega]
  · by_cases h1 : k + 1 = K
    · have hb : r.testBit (k + 1) = false := by
        rw [h1]; exact Nat.testBit_lt_two_pow hr
      simp only [ite_eq_right h0, ite_eq_left h1, hb]
      simp [show k ≥ 1 by omega, show k ≥ K - 1 by omega, show k - (K - 1) = 0 by omega, h0]
    · simp only [ite_eq_right h0, ite_eq_right h1]
      simp [show k ≥ 1 by omega, show ¬ (k ≥ K - 1) by omega, h0]

theorem enc_step {K t : Nat} {j : Int} {r : Nat} (h : Enc K t j r) :
    Enc K (t + 1) j (stripStep K (cell t j) (cell t (j + 1 + K)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun k hk => ?_⟩
  rw [testBit_stripStep K _ _ r h.1 k hk]
  show _ = rule (cell t (j + 1 + (k : Int) - 1)) (cell t (j + 1 + k)) (cell t (j + 1 + k + 1))
  have hc : r.testBit k = cell t (j + 1 + k) := h.2 k hk
  have hl : (if k = 0 then cell t j else r.testBit (k - 1)) = cell t (j + 1 + (k : Int) - 1) := by
    split
    · rename_i h0; subst h0; congr 1; omega
    · rename_i h0; rw [h.2 (k - 1) (by omega)]; congr 1; omega
  have hr : (if k + 1 = K then cell t (j + 1 + K) else r.testBit (k + 1)) =
      cell t (j + 1 + k + 1) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (k + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

/-- The encoding of the actual strip. -/
def encRow (t : Nat) (j : Int) : Nat → Nat
  | 0 => 0
  | K + 1 => encRow t j K ||| ((cell t (j + 1 + K)).toNat <<< K)

theorem testBit_encRow (t : Nat) (j : Int) :
    ∀ K k, (encRow t j K).testBit k = (decide (k < K) && cell t (j + 1 + k))
  | 0, k => by simp [encRow]
  | K + 1, k => by
    rw [encRow, Nat.testBit_or, testBit_encRow t j K k, Nat.testBit_shiftLeft, testBit_toNat]
    by_cases hk : k < K
    · simp [hk, show k < K + 1 by omega, show ¬ K ≤ k by omega]
    · by_cases hk' : k = K
      · subst hk'; simp
      · simp [hk, show ¬ k < K + 1 by omega, show k - K ≠ 0 by omega]

theorem enc_encRow (K t : Nat) (j : Int) : Enc K t j (encRow t j K) := by
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun k hk => ?_⟩
  · rw [testBit_encRow]; simp [show ¬ i < K by omega]
  · rw [testBit_encRow]; simp [hk]

/-! Bitmask sets of strip states. -/

def imageAux (K : Nat) (a : Bool) (S : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => imageAux K a S n |||
      (if S.testBit n then (1 <<< stripStep K a false n) ||| (1 <<< stripStep K a true n) else 0)

/-- All successors of the states in `S`, for both values of the right boundary. -/
def image (K : Nat) (a : Bool) (S : Nat) : Nat := imageAux K a S (2 ^ K)

theorem testBit_one_shiftLeft (m i : Nat) : (1 <<< m).testBit i = decide (m = i) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem mem_imageAux {K : Nat} {a : Bool} {S r : Nat} (hS : S.testBit r = true) (z : Bool) :
    ∀ n, r < n → (imageAux K a S n).testBit (stripStep K a z r) = true
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [imageAux, Nat.testBit_or]
    by_cases hrn : r < n
    · rw [mem_imageAux hS z n hrn]; rfl
    · have : r = n := by omega
      subst this
      rw [ite_eq_left hS, Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft]
      cases z <;> simp

theorem imageAux_mono {K : Nat} {a : Bool} {S S' : Nat}
    (hSS : ∀ s, S.testBit s = true → S'.testBit s = true) :
    ∀ n y, (imageAux K a S n).testBit y = true → (imageAux K a S' n).testBit y = true
  | 0, _, h => h
  | n + 1, y, h => by
    rw [imageAux, Nat.testBit_or] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [imageAux_mono hSS n y h]; rfl
    · by_cases hn : S.testBit n = true
      · rw [ite_eq_left hn] at h
        rw [ite_eq_left (hSS n hn), h]; simp
      · rw [ite_eq_right hn, Nat.zero_testBit] at h; exact absurd h (by decide)

/-- Apply a driver word to a set of strip states. -/
def applyWord (K : Nat) : List Bool → Nat → Nat
  | [], S => S
  | a :: u, S => applyWord K u (image K a S)

theorem applyWord_mono (K : Nat) : ∀ (u : List Bool) {S S' : Nat},
    (∀ s, S.testBit s = true → S'.testBit s = true) →
      ∀ y, (applyWord K u S).testBit y = true → (applyWord K u S').testBit y = true
  | [], _, _, h => h
  | _ :: u, _, _, h => applyWord_mono K u (fun y => imageAux_mono h (2 ^ K) y)

/-- **Soundness of the strip sets.** If the actual strip is in `S` at time `t` and column `j` carries
the word `u` from `t` on, the actual strip at time `t + u.length` is in `applyWord K u S`. -/
theorem enc_applyWord {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), Enc K t j r → S.testBit r = true →
      (∀ s, s < u.length → cell (t + s) j = u.getD s false) →
      ∃ r', Enc K (t + u.length) j r' ∧ (applyWord K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : cell t j = a := by simpa using hu 0 (by simp)
    have he1 := enc_step he
    rw [ha] at he1
    have hS1 : (image K a S).testBit (stripStep K a (cell t (j + 1 + K)) r) = true :=
      mem_imageAux hS _ (2 ^ K) he.1
    obtain ⟨r', he', hS'⟩ := enc_applyWord u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

/-- `k` repetitions of the word. -/
def iterW (K : Nat) (w : List Bool) : Nat → Nat → Nat
  | 0, S => S
  | k + 1, S => iterW K w k (applyWord K w S)

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

theorem allBelow_spec {p : Nat → Bool} : ∀ {n}, allBelow p n = true → ∀ i, i < n → p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    rw [allBelow, Bool.and_eq_true] at h
    by_cases hin : i < n
    · exact allBelow_spec h.1 i hin
    · rw [show i = n by omega]; exact h.2

/-- `S ⊆ S'` on states below `2 ^ K`. -/
def subsetB (K S S' : Nat) : Bool := allBelow (fun s => !S.testBit s || S'.testBit s) (2 ^ K)

/-- Column `j + 1` (bit `0`) equals `b` on every state of `S`. -/
def colConst (K S : Nat) (b : Bool) : Bool := allBelow (fun s => !S.testBit s || s.testBit 0 == b) (2 ^ K)

/-- All `2 ^ K` strip states. -/
def fullSet (K : Nat) : Nat := 2 ^ (2 ^ K) - 1

/-- **Strip certificate** for the word `w` at strip width `K` after `k` warm-up periods: the set `S0`
reached after `k` periods is mapped into itself by one more period, and at every white phase of `w`
column `j + 1` is constant on the corresponding set. -/
def stripCert (w : List Bool) (K k : Nat) : Bool :=
  let S0 := iterW K w k (fullSet K)
  subsetB K (applyWord K w S0) S0 &&
    (List.range w.length).all fun φ => w.getD φ false ||
      colConst K (applyWord K (w.take φ) S0) false || colConst K (applyWord K (w.take φ) S0) true

theorem enc_iterW {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), Enc K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → cell (t + m * w.length + s) j = w.getD s false) →
      ∃ r', Enc K (t + k * w.length) j r' ∧ (iterW K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := enc_applyWord w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := enc_iterW w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-- **Soundness of bitmask strip certificates.** If `stripCert w K k` holds, the center column is
not eventually equal to `w` repeated (in any phase). -/
theorem not_eventually_word_strip (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWord w := by
  rintro ⟨T, hT⟩
  unfold stripCert at hcert
  rw [Bool.and_eq_true] at hcert
  obtain ⟨hsub, hforce⟩ := hcert
  have hsub' := allBelow_spec hsub
  -- the driver is `w` on every period from `T`
  have hblock : ∀ m s, s < w.length → cell (T + m * w.length + s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  let S0 := iterW K w k (fullSet K)
  -- after `k` periods the strip is in `S0`
  have hstart : ∃ r, Enc K (T + k * w.length) 0 r ∧ S0.testBit r = true := by
    have h0 := enc_encRow K T 0
    have hfull : (fullSet K).testBit (encRow T 0 K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
  -- and it stays in `S0` at every later period start
  have hinv : ∀ m, ∃ r, Enc K (T + (k + m) * w.length) 0 r ∧ S0.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := enc_applyWord w _ r S0 he hS (fun s hs => by
        rw [show T + (k + m) * w.length + s = T + (k + m) * w.length + s from rfl]
        exact hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have hlt : r' < 2 ^ K := he'.1
        have := hsub' r' hlt
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  -- the forced value at each white phase
  let g : Nat → Bool := fun φ => w.getD φ false ||
    !colConst K (applyWord K (w.take φ) S0) false
  have hform : ∀ t, T + k * w.length ≤ t → orCol 0 t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t - T) / w.length - k)
    obtain ⟨r', he', hS'⟩ := enc_applyWord (w.take ((t - T) % w.length)) _ r S0 he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t - T) % w.length := by omega
        rw [hblock _ s (by omega)]
        simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : cell t 1 = r'.testBit 0 := by
      rw [he'.2 0 (by omega)]; rfl
    unfold orCol g
    rw [hT t (by omega)]
    simp only [Int.zero_add]
    have hfφ := List.all_eq_true.mp hforce ((t - T) % w.length) (List.mem_range.mpr hφ)
    cases hwφ : w.getD ((t - T) % w.length) false
    · rw [hwφ, Bool.false_or] at hfφ
      simp only [Bool.false_or]
      rw [hcell]
      cases hc0 : colConst K (applyWord K (w.take ((t - T) % w.length)) S0) false
      · rw [hc0, Bool.false_or] at hfφ
        have := allBelow_spec hfφ r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
      · have := allBelow_spec hc0 r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
    · rfl
  refine orCol_not_eventuallyPeriodic 0 ⟨T, w.length, hw, hcper⟩
    ⟨T + k * w.length, w.length, hw, fun t ht => ?_⟩
  show orCol 0 (t + w.length) = orCol 0 t
  rw [hform t ht, hform (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
    Nat.add_mod_right]

/-- **`0 1^7` is excluded** (strip width `5`, `4` warm-up periods). -/
theorem not_eventually_01111111 :
    ¬ EventuallyWord [false, true, true, true, true, true, true, true] :=
  not_eventually_word_strip [false, true, true, true, true, true, true, true] 5 4 (by decide)
    (by decide) (by decide +kernel)

/-! ### Rank certificates: the right strip as lists -/

def lin3 : List Bool → List Bool
  | a :: b :: c :: rest => xor a (b || c) :: lin3 (b :: c :: rest)
  | _ => []

def seg (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => f 0 :: seg (fun i => f (i + 1)) n

theorem lin3_seg : ∀ (m : Nat) (f : Nat → Bool),
    lin3 (seg f (m + 2)) = seg (fun i => xor (f i) (f (i + 1) || f (i + 2))) m
  | 0, f => rfl
  | m + 1, f => by
    show xor (f 0) (f 1 || f 2) :: lin3 (seg (fun i => f (i + 1)) (m + 2)) = _
    rw [lin3_seg m (fun i => f (i + 1))]
    rfl

theorem seg_succ : ∀ (n : Nat) (f : Nat → Bool), seg f (n + 1) = seg f n ++ [f n]
  | 0, f => rfl
  | n + 1, f => by
    show f 0 :: seg (fun i => f (i + 1)) (n + 1) = f 0 :: (seg (fun i => f (i + 1)) n ++ [f (n + 1)])
    rw [seg_succ n (fun i => f (i + 1))]

theorem length_seg : ∀ (n : Nat) (f : Nat → Bool), (seg f n).length = n
  | 0, _ => rfl
  | n + 1, f => by simp [seg, length_seg n]

/-- Columns `1..m` at time `t`. -/
def rowR (t m : Nat) : List Bool := seg (fun i => cell t ((i : Int) + 1)) m

theorem cons_rowR (t m : Nat) :
    cell t 0 :: rowR t m = seg (fun i => cell t (i : Int)) (m + 1) := by
  show cell t 0 :: seg (fun i => cell t ((i : Int) + 1)) m = cell t ((0 : Nat) : Int) :: seg _ m
  congr 2

/-- One step of the strip: the new strip is `lin3` of the old one with the center cell in front and
cell `b+1` at the end. -/
theorem rowR_succ (t b : Nat) :
    rowR (t + 1) b = lin3 (cell t 0 :: (rowR t b ++ [cell t ((b : Int) + 1)])) := by
  have e1 : rowR t b ++ [cell t ((b : Int) + 1)] = rowR t (b + 1) := by
    unfold rowR; rw [seg_succ]
  rw [e1, cons_rowR, lin3_seg]
  unfold rowR
  congr 1
  funext i
  show rule (cell t ((i : Int) + 1 - 1)) (cell t ((i : Int) + 1)) (cell t ((i : Int) + 1 + 1)) =
    xor (cell t (i : Int)) (cell t ((i + 1 : Nat) : Int) || cell t ((i + 2 : Nat) : Int))
  rw [show ((i : Int) + 1 - 1) = (i : Int) by omega, show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega,
    show ((i + 2 : Nat) : Int) = (i : Int) + 1 + 1 by omega]
  rfl

theorem rowR_length (t b : Nat) : (rowR t b).length = b := length_seg b _

theorem rowR_head (t b : Nat) (hb : 0 < b) : (rowR t b).headD false = cell t 1 := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

/-! ### Rank certificates: packed tables and Boolean checks -/

/-- Little-endian encoding of a strip. -/
def encList : List Bool → Nat
  | [] => 0
  | x :: l => (if x then 1 else 0) + 2 * encList l

/-- A certificate with packed tables: `rankP` (16-bit fields indexed by node), `posP` (8-bit fields by
node), `perP` (8-bit fields by rank), `wordP` (64-bit fields by rank, bit `p` = letter `p`).
`nranks` records the number of ranks; the checks do not use it. -/
structure Cert where
  w : List Bool
  b : Nat
  nranks : Nat
  rankP : Nat
  posP : Nat
  perP : Nat
  wordP : Nat

namespace Cert
variable (C : Cert)

def P : Nat := C.w.length
def wAt (φ : Nat) : Bool := C.w.getD φ false
def idx (φ : Nat) (s : List Bool) : Nat := φ * 2 ^ C.b + encList s
def rk (φ : Nat) (s : List Bool) : Nat := (C.rankP >>> (16 * C.idx φ s)) % 65536
def ps (φ : Nat) (s : List Bool) : Nat := (C.posP >>> (8 * C.idx φ s)) % 256
def m (r : Nat) : Nat := (C.perP >>> (8 * r)) % 256
def u (r p : Nat) : Bool := (C.wordP >>> (64 * r + p)) % 2 == 1

/-- Counter update at phase `φ` inside rank class `r`. -/
def nextPos (r p φ : Nat) : Nat := if C.wAt φ then p else (p + 1) % C.m r

/-- The edge condition for `(φ, s) → ((φ+1) % P, s')`. -/
def edgeOK (φ : Nat) (s s' : List Bool) : Bool :=
  let φ' := (φ + 1) % C.P
  let r := C.rk φ s
  decide (C.rk φ' s' ≤ r) &&
  (!(C.rk φ' s' == r) ||
    ((C.ps φ' s' == C.nextPos r (C.ps φ s) φ) && (C.wAt φ || (s.headD false == C.u r (C.ps φ s)))))

def check : Bool :=
  (List.range C.P).all fun φ => (allLists C.b).all fun s =>
    [false, true].all fun x => C.edgeOK φ s (lin3 (C.wAt φ :: (s ++ [x])))

/-- The counter-phase map `G (p, φ) = (nextPos p φ, (φ+1) % P)`. -/
def G (r : Nat) (q : Nat × Nat) : Nat × Nat := (C.nextPos r q.1 q.2, (q.2 + 1) % C.P)

end Cert

def Cert.iterG (C : Cert) (r : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, q => q
  | n + 1, q => Cert.iterG C r n (C.G r q)

namespace Cert
variable (C : Cert)

/-- Every node's position is below the counter period of its rank. (That the counter-phase map
`G` then has period `m · P` is proved once and for all in `Cert.iterG_period`.) -/
def checkG : Bool :=
  (List.range C.P).all fun φ => (allLists C.b).all fun s => decide (C.ps φ s < C.m (C.rk φ s))

end Cert

/-! ### Rank certificates: soundness -/

theorem allLists_mem (l : List Bool) (n : Nat) (h : l.length = n) : l ∈ allLists n := by
  subst h; exact mem_allLists l

theorem antitone_eventually_const (f : Nat → Nat) (T : Nat) (h : ∀ t, T ≤ t → f (t + 1) ≤ f t) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → f t = f T' := by
  have mono : ∀ t s, T ≤ t → f (t + s) ≤ f t := by
    intro t s ht
    induction s with
    | zero => exact Nat.le_refl _
    | succ s ih => exact Nat.le_trans (h (t + s) (by omega)) ih
  -- strong induction on the value f T
  suffices H : ∀ n, ∀ T₀, T ≤ T₀ → f T₀ ≤ n → ∃ T', T₀ ≤ T' ∧ ∀ t, T' ≤ t → f t = f T' by
    obtain ⟨T', h1, h2⟩ := H (f T) T (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨T', h1, h2⟩
  intro n
  induction n with
  | zero =>
    intro T₀ hT₀ hf
    refine ⟨T₀, Nat.le_refl _, fun t ht => ?_⟩
    have := mono T₀ (t - T₀) hT₀
    rw [show T₀ + (t - T₀) = t by omega] at this
    omega
  | succ n ih =>
    intro T₀ hT₀ hf
    by_cases hc : ∀ t, T₀ ≤ t → f t = f T₀
    · exact ⟨T₀, Nat.le_refl _, hc⟩
    · have : ∃ t, T₀ ≤ t ∧ f t ≠ f T₀ := by
        refine Classical.byContradiction fun hn => hc fun t ht => ?_
        exact Classical.byContradiction fun hne => hn ⟨t, ht, hne⟩
      obtain ⟨t₁, ht₁, hne⟩ := this
      have hle := mono T₀ (t₁ - T₀) hT₀
      rw [show T₀ + (t₁ - T₀) = t₁ by omega] at hle
      obtain ⟨T', h1, h2⟩ := ih t₁ (by omega) (by omega)
      exact ⟨T', by omega, h2⟩

theorem iterG_add (C : Cert) (r : Nat) : ∀ (a n : Nat) (q : Nat × Nat), C.iterG r (a + n) q = C.iterG r n (C.iterG r a q)
  | 0, n, q => by simp [Cert.iterG]
  | a + 1, n, q => by
    rw [show a + 1 + n = (a + n) + 1 by omega]
    show C.iterG r (a + n) (C.G r q) = C.iterG r n (C.iterG r a (C.G r q))
    exact iterG_add C r a n (C.G r q)

/-- White phases met by the counter in `n` steps from phase `φ`. -/
def Cert.whites (C : Cert) (φ : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if C.wAt φ then 0 else 1) + Cert.whites C ((φ + 1) % C.P) n

/-- `n` steps of the counter-phase map add the white phases met to the position. -/
theorem Cert.iterG_formula (C : Cert) (r : Nat) (hm : 0 < C.m r) (hP : 0 < C.P) :
    ∀ n φ p, φ < C.P → p < C.m r →
      C.iterG r n (p, φ) = ((p + C.whites φ n) % C.m r, (φ + n) % C.P)
  | 0, φ, p, hφ, hp => by
    simp only [Cert.iterG, Cert.whites, Nat.add_zero, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hφ]
  | n + 1, φ, p, hφ, hp => by
    have hφ' : (φ + 1) % C.P < C.P := Nat.mod_lt _ hP
    have hp' : C.nextPos r p φ < C.m r := by
      unfold Cert.nextPos
      split
      · exact hp
      · exact Nat.mod_lt _ hm
    show C.iterG r n (C.G r (p, φ)) = _
    rw [show C.G r (p, φ) = (C.nextPos r p φ, (φ + 1) % C.P) from rfl,
      Cert.iterG_formula C r hm hP n _ _ hφ' hp', Nat.mod_add_mod,
      show φ + 1 + n = φ + (n + 1) by omega]
    congr 1
    show (C.nextPos r p φ + C.whites ((φ + 1) % C.P) n) % C.m r =
      (p + ((if C.wAt φ then 0 else 1) + C.whites ((φ + 1) % C.P) n)) % C.m r
    unfold Cert.nextPos
    cases C.wAt φ
    · simp only [Bool.false_eq_true, ite_false]
      rw [Nat.mod_add_mod, Nat.add_assoc]
    · simp only [ite_true, Nat.zero_add]

theorem Cert.iterG_mul (C : Cert) (r : Nat) (hm : 0 < C.m r) (hP : 0 < C.P) (φ : Nat)
    (hφ : φ < C.P) : ∀ k p, p < C.m r →
      C.iterG r (k * C.P) (p, φ) = ((p + k * C.whites φ C.P) % C.m r, φ)
  | 0, p, hp => by simp [Cert.iterG, Nat.mod_eq_of_lt hp]
  | k + 1, p, hp => by
    rw [show (k + 1) * C.P = C.P + k * C.P by rw [Nat.succ_mul]; omega, iterG_add,
      Cert.iterG_formula C r hm hP C.P φ p hφ hp, Nat.add_mod_right, Nat.mod_eq_of_lt hφ,
      Cert.iterG_mul C r hm hP φ hφ k _ (Nat.mod_lt _ hm), Nat.mod_add_mod]
    congr 2
    rw [Nat.succ_mul]
    omega

/-- **The counter-phase map has period `m · P`**: over one cycle of phases the position gains
the same number `z` of white phases, and `m` cycles add `m z ≡ 0`. -/
theorem Cert.iterG_period (C : Cert) (r : Nat) (hm : 0 < C.m r) (hP : 0 < C.P) (p φ : Nat)
    (hp : p < C.m r) (hφ : φ < C.P) : C.iterG r (C.m r * C.P) (p, φ) = (p, φ) := by
  rw [Cert.iterG_mul C r hm hP φ hφ (C.m r) p hp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]

theorem Cert.sound (C : Cert) (hC : C.check = true) (hG : C.checkG = true) (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P)) : False := by
  -- the history
  let ph : Nat → Nat := fun t => (t - T) % C.P
  let st : Nat → List Bool := fun t => rowR t C.b
  have hph : ∀ t, T ≤ t → ph (t + 1) = (ph t + 1) % C.P := by
    intro t ht
    show (t + 1 - T) % C.P = ((t - T) % C.P + 1) % C.P
    rw [show t + 1 - T = (t - T) + 1 by omega]
    exact (Nat.mod_add_mod (t - T) C.P 1).symm
  have hphlt : ∀ t, ph t < C.P := fun t => Nat.mod_lt _ hP
  -- every true step is an edge of the certificate graph, hence satisfies edgeOK
  have hedge : ∀ t, T ≤ t → C.edgeOK (ph t) (st t) (st (t + 1)) = true := by
    intro t ht
    have hall := hC
    unfold Cert.check at hall
    have h1 := List.all_eq_true.1 hall (ph t) (List.mem_range.2 (hphlt t))
    have h2 := List.all_eq_true.1 h1 (st t) (allLists_mem _ _ (rowR_length t C.b))
    have h3 := List.all_eq_true.1 h2 (cell t ((C.b : Int) + 1)) (by cases cell t ((C.b : Int) + 1) <;> simp)
    have hs : st (t + 1) = lin3 (C.wAt (ph t) :: (st t ++ [cell t ((C.b : Int) + 1)])) := by
      show rowR (t + 1) C.b = _
      rw [rowR_succ, h t ht]
    rw [hs]; exact h3
  -- rank along the history
  let R : Nat → Nat := fun t => C.rk (ph t) (st t)
  have hRle : ∀ t, T ≤ t → R (t + 1) ≤ R t := by
    intro t ht
    have e := hedge t ht
    unfold Cert.edgeOK at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    show C.rk (ph (t + 1)) (st (t + 1)) ≤ C.rk (ph t) (st t)
    rw [hph t ht]; exact e.1
  obtain ⟨T', hT', hconst⟩ := antitone_eventually_const R T hRle
  let r := R T'
  -- along rank-preserving steps: counter update and output
  have hstep : ∀ t, T' ≤ t →
      C.ps (ph (t + 1)) (st (t + 1)) = C.nextPos r (C.ps (ph t) (st t)) (ph t) ∧
      (C.wAt (ph t) = false → cell t 1 = C.u r (C.ps (ph t) (st t))) := by
    intro t ht
    have e := hedge t (by omega)
    have hRt : R t = r := hconst t ht
    have hRt1 : R (t + 1) = r := hconst (t + 1) (by omega)
    unfold Cert.edgeOK at e
    rw [← hph t (by omega)] at e
    have hr1 : C.rk (ph (t + 1)) (st (t + 1)) = C.rk (ph t) (st t) := by
      show R (t + 1) = R t; rw [hRt, hRt1]
    simp only [hr1, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at e
    have hrt : C.rk (ph t) (st t) = r := hRt
    rw [hrt] at e
    refine ⟨e.2.1, fun hw => ?_⟩
    have e2 := e.2.2
    rw [hw, Bool.false_or, beq_iff_eq] at e2
    rw [← rowR_head t C.b hb]; exact e2
  -- the counter-phase pair follows G
  let q : Nat → Nat × Nat := fun t => (C.ps (ph t) (st t), ph t)
  have hq : ∀ t, T' ≤ t → q (t + 1) = C.G r (q t) := by
    intro t ht
    show (C.ps (ph (t + 1)) (st (t + 1)), ph (t + 1)) = (C.nextPos r (C.ps (ph t) (st t)) (ph t), (ph t + 1) % C.P)
    rw [(hstep t ht).1, hph t (by omega)]
  have hqiter : ∀ t, T' ≤ t → ∀ n, q (t + n) = C.iterG r n (q t) := by
    intro t ht n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show t + (n + 1) = (t + n) + 1 by omega, hq (t + n) (by omega), ih,
        show n + 1 = n + 1 from rfl, iterG_add C r n 1 (q t)]
      rfl
  -- checkG: every node's position is below the counter period of its rank
  have hGn : ∀ φ, φ < C.P → ∀ s, s ∈ allLists C.b → C.ps φ s < C.m (C.rk φ s) := by
    have hG' := hG
    unfold Cert.checkG at hG'
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hG'
    exact hG'
  have hpos0 : C.ps (ph T') (st T') < C.m r :=
    hGn (ph T') (hphlt T') (st T') (allLists_mem _ _ (rowR_length T' C.b))
  have hm : 0 < C.m r := by omega
  -- periodicity of the counter-phase pair after T'
  have hper : ∀ t, T' ≤ t → q (t + C.m r * C.P) = q t := by
    intro t ht
    rw [hqiter t ht]
    have hpos : C.ps (ph t) (st t) < C.m (C.rk (ph t) (st t)) :=
      hGn (ph t) (hphlt t) (st t) (allLists_mem _ _ (rowR_length t C.b))
    have hrt : C.rk (ph t) (st t) = r := hconst t ht
    rw [hrt] at hpos
    exact C.iterG_period r hm hP _ _ hpos (hphlt t)
  -- conclude with masked Jen, Q = m * P
  refine masked_jen 0 (P := C.m r * C.P) (Nat.mul_pos hm hP) (T := T') ?_ ?_
  · intro t ht
    rw [h (t + C.m r * C.P) (by omega), h t (by omega)]
    congr 1
    rw [show t + C.m r * C.P - T = (t - T) + C.P * C.m r by rw [Nat.mul_comm]; omega, Nat.add_mul_mod_self_left]
  · intro t ht hw
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hwt : C.wAt (ph t) = false := by rw [← h t (by omega)]; exact hw
    have hqe := hper t ht
    have hph' : ph (t + C.m r * C.P) = ph t := congrArg Prod.snd hqe
    have hps' : C.ps (ph (t + C.m r * C.P)) (st (t + C.m r * C.P)) = C.ps (ph t) (st t) := congrArg Prod.fst hqe
    have hwt' : C.wAt (ph (t + C.m r * C.P)) = false := by rw [hph']; exact hwt
    rw [(hstep (t + C.m r * C.P) (by omega)).2 hwt', (hstep t ht).2 hwt, hps']


/-- Rank certificates exclude their word, stated with `EventuallyWord`. -/
theorem Cert.not_eventuallyWord (C : Cert) (hC : C.check = true) (hG : C.checkG = true)
    (hP : 0 < C.P) (hb : 0 < C.b) : ¬ EventuallyWord C.w :=
  fun ⟨T, h⟩ => C.sound hC hG hP hb T h

/-! ### A rank certificate: the word `0^6 1 1` -/

-- certificate for w = 00000011, strip width b = 6; generated by export_cert.py
def c00000011_w : List Bool := [false, false, false, false, false, false, true, true]
def c00000011_b : Nat := 6
def c00000011_nranks : Nat := 379
def c00000011_rankP : Nat := 5908444537978224163236655296421498429319017773728926993171828404275953012925332390425109119000201216083462427565142757871849860034626295403931223881241106222150053270466854427020618830510880731386842705443814880999594783283603562414106167428613391073541624499972952176041257964487185201265188274501364916375637453783096125412966729040738264837763245498509308195305617403379355993626269835575599165667633835335349760268041624215318172035553602258853210741899521520588387871713813488899669489346365892219983994031548046282376911597823844992527044282021521943211144368136118542009942969261082802584746445003177406667959687780471481438381226927659892140688804083855429404716349088729666022538008001157091463940885677568914633322104928629314563869611809232015069794040506250953797976457828286149011069602586248035031594358198147559852264021276766229959999329982737016015546050993520172023844311636110312681197707344860771099800649360263409831140795292281231716701191919599136702808141654932861426812314090649581309205702616332544890026199434624599931291165015472338453639465251874925016450272713079418577450432832586417709158654237002493185012643382384999937308940516192132378086242785134506776117779402139339578192968221538643280841921068358627415289097537490658949975342797154667244166474875791570145379791001481192492395970286549067029230609745171548152178890849834503126908805709936697254002368116916462337636977470779177778057421926068775587707223003811762221764731944417741068199673396954817160402226554607134007919986012861151845748153123255223567174269627478127135061383396582874498170371418984183696767447773403788691054932812490119919959417849268593701743002257077339514478004380792476206701938031208487667953021563127130250558892506245879941147512775648567607216033213000197401770370966883559651559079844330958519055134183306598100188036974694731916781016679327919753588452607314452408073354075766833614874356238186865217947652595507854500333807083797722627674560195439781973403780511847983417834988731421937560164194078090263146688775887587421526786916568804767180882022490329837692542831360686246698333817156921225407761241953488170383060856733588641395379521744216045949223077771200478253581793482355585838018753890098018319030481308335367686066997341554738929586666260480632709845825065782793088983902760969852443603447790898751946596110587764011015209849114615887537953087637611119889013739871505669034500845380607854888799699268389003257969101680672871
def c00000011_posP : Nat := 113468867123488522776110738442329421844101097150675934452456924570887630471630423523079603744824693542057907475960951883496790027913174019785447617839097786191275371657440967121299053696727209607798969224894284471651279288846941547866014513929170196622347621724980942065520587383081186963289929406325890527395186194300981924172630837476992509343072055987057164672601305725490170987098593173112763934305565202966222307943342760781957653418688069542609844835121961706799649842478673895801764184975815400214089371218339598678746403023058591266155012153893264975690653607953982367100522103832053935632236768177307917591038191954098948849439931006947144364481303663387133559069541371083555899379997713114999864421272550837282154880719250237005961992476457707853320723227019813898922126610475297734147493899376630802082081987992179517934813087679877372335876120996023434538490621853030053114518108504764119349155264693650147246080
def c00000011_perP : Nat := 20720807341871434971548591111075382931245597538362567183551515765170301561086294167553155850945491433513855528497659990477784743339583039456317061701698735754911081183010824753856806605347580950954596746159386072076740961932256853869261122119573338883596574516148500357707255312412231431434578516140232327088216468051091431784988475057266567128123138324065925448279579486114364737040276292275046511105449541762993321634220128725691028147801542313778252544822215994957935698608552271111344023969712380013171904144753260753831871485157142792096793275495641284957634382019569975693759688897193178515886940958588579348101890468652765609912956077654844299012676162460491077043880718573643589326573815908419270207645302276295427219494174657244021940097552321118889694825120316262326733568541226379827297146436930291422912218534664258817691972246358327595261755038601351874401252892680390532366407563464267509788639489
def c00000011_wordP : Nat := 32754260930411245273845066664824029604168534214239534371933563959653781958516941287413869865034745649469812489581941978090705548689166503309533416664702253768319974407938315218461354095938439345287502440309093681057177754150596827807980607723556261542351392015659755896833

def C_c00000011 : Cert :=
  { w := c00000011_w, b := c00000011_b, nranks := c00000011_nranks, rankP := c00000011_rankP,
    posP := c00000011_posP, perP := c00000011_perP, wordP := c00000011_wordP }

theorem C_c00000011_check : C_c00000011.check = true := by decide +kernel
theorem C_c00000011_checkG : C_c00000011.checkG = true := by decide +kernel

/-- **`0^6 1 1` is excluded**, whatever the transient (rank certificate, strip width `6`). -/
theorem not_eventually_00000011 :
    ¬ EventuallyWord [false, false, false, false, false, false, true, true] :=
  C_c00000011.not_eventuallyWord C_c00000011_check C_c00000011_checkG (by decide) (by decide)

/-! ### A rank certificate: the word `0^9 1 0 1` -/

-- certificate for w = 000000000101, strip width b = 7; generated by export_cert.py
def c000000000101_w : List Bool := [false, false, false, false, false, false, false, false, false, true, false, true]
def c000000000101_b : Nat := 7
def c000000000101_nranks : Nat := 1309
def c000000000101_rankP : Nat := 7960119008967187543090538333469867971823272402989330918753361524556162106388532650062714293427490035204380859003435311983654031178547972751457060583382949714335311260314677125329414297274834259452647475585122843112260159153141238091968053217591686326559631781737173305360551997978423275675290564999369061469766024831207571788555168318334098068123049401006220575397500094564783409148490104244452564030252625835000518442113713380444739292129443562264904578286277782662637871480928569137558389504934460551604977809111184174178189627785862869816170570339936128772726032181217393172436217873199669911425115895296156909752045095535002888877045885506088966218054130751170129839715478611147288109843163799833788306260951186968988200450653792370173974787249554541456228884171931561480771238368700337498210124457862406735259167880087185059492920353560526294528293354509392737926184321150822854361877170452511076765344286376392161046896394946107449903117677650344061903492894948237057694463474407707552687823639953811582495304204591768390414798447757315576965868631938066233057340332274189556233682435469014413835212491154174882555778991693868969123717574742990704984475395138502890929712630866741031513986060201491296059512824122059746565438405551367894740564860813354887788308384635503055330398607142108894078389967814608236910351626627299773834152500593820153424872546233948295728824351110620362117310713281151968926114652633380298725687526949094190271082685700314973380501140672575393418973082156226593067657302321045259327968276668310504785439736067371719661528459409632005614652282570098685460373406167769862943454053941113470903768640921928142441618848175299990363574748897267131053910471674085589029182582387471098034057297768167800767532135415347730022895412989917023300082126504693523554274339348902919896749819911113260327812613795661495831171131146199032200926910329674342131797218043363994398938014204123574779532201573278877276090275830109521179455479018496803906905361409149604251041962204466156486076348914568200228506747675717366737530856898679594533892726621850466910134276574258449157340296076900447937828774055094849716530013585306652445576004128023320843145413707915284149915059874432012590118233824347927363014336985314734535593238217851526937424849550774073194492036755469902038879169146896969583194345587990274555644317642565709093425618244922539975501310174462816396501867958168059682912590635730674823179155084573475875175843319602916575327832929559904247581966619512687139540680816453132501447291742134384508890289204252405915283632160278510683232081067054927468347517622378445244688241901060512002243537977125551690929255512899780454515655947350291031972717200595960550357792239789488615391591373924657340212740627027514161265785178822450124372577538932342529898105658807640469475918856489632513208805017988248423373652090263426386035735128151463938717366800226475783819490686903911917600615271840862727266056505244013443292597791418773532776552058400271838955445703239909857212013442644493769461829467037339418396573597651361174532562392521068119769234036817684714332204738618409947920472876603250228021375182916853086378123972369422774846920857760609390847337750857099770933004067121416658612013339526441561137186462307589973009901665681681137892056655877261380169293550263576233334523833266334236611398316204638967499685219631794136030670769224140385855004493662600526897488793441678653468109212759223255907398373481420456671184480703103507481577535191887516177183893544708462351538783364017004227059047945483658408124261758760546086099116931747478947028278445001808740216459656443435498155961891135000053553464017855413684886940163472989754228225101132359644540170464039740017168163663300436849320443618734599120661262712872353592796054366792429303270672649104810389785082491600480499518332478091432882872325653364294894925316918399161272177762555836297554803512432359253558892677438293069043878171758842980672049041937500210828065918833229042915539122337349531435131570833556082064241949466496668516968602910120351899074297431152316055029176464464214648510969333589707252339779705577234629365143241971808236907714965071463277237100827263694444217794964794549976101075481612892211135198454900420785084445241337645528034389963231551886498927210125422660994921163975506380988734506922610624896935459359949809994111420149840888119479590606715162364605424471257869551855688109440991326200323121673542926231641402181445491010594934518492562322507597546595872239794364845610456970261854683653975943420454437860181633913377574050732144290950768048615089269960299310555798649176182848101952032363483467358255641185498134075192238125582606687006073898723986266906194429533276760214910065275067445077104252528737218176054680240930456085270895765926376238629335812008137512402793810331883753491582968280513204811938775639839510555444659306887424378726560271709453957468235539709318180607543586952960576330904512452056464338495869241710725524670545129655769497819828229756465304317780306663741455910929404453361208866129479626901666036244440575951837182158730243642556730402953467100799193478574537892222859371836963934066819582951800166507785564046721657973869159095641157567457629910470890423875003946229728654592394905835462364609574565746607855588575926020164637635052662831665118012547427302182234228877904366741133402748759874547956802931431310904402893460395307551983535651793332721866725550529654027306197100824070337126933237744465632082762562938788413545146371702099422492400880786816148473358449843043186030201853934392136975854428930169466341635767737895903247982608765562203905978942574441100659434963870474890148908012771881168068973432992010583194235744314470358690400851330782689395788558055485506596675269415909203325483834742356591367407619351662787915299244719916673993870943006435707370949725480952087795539416875115656901961238121958006840345909425683098445015310953263233628881003950016621407399748640350665580514610085250474205214890151155551660304734137761846189875109011373386670686927075677688319238242778684214927671084847462696909324887774852607484997553981045046416313332425875826263028288208061312322518487766409046937618624520260590912278545358746910922631919855772025689480136971002131696472526059074131058934029119394816390944521743858059634934535845840188349059367306358503014437924069923576624392254035405795139172648491330083220833201588655275364308154291198876590355641176423437230739704540962304716247815376153071684998409556532668090144365166282288281556880329757054574128792812896640297870048203949710774645576474500008051757587786224847953329831059571625506352983774501325685605221720963144504906538854462031272589086003125372248973657924530732166697959697414751463222313083857796148036462302466732308728173996515225515108831498689350752672740311120912011106458405137367050599298839253263283374590163697104571682223984171020512550379432281803304180075665101933629965920341730135614161541198854250442368698458146254765669348946994084061409944628679338759430077075699432101581686873121529016184115147137928362128697872400735821166496115841307368420267784747710375188938060052251850642415869801968412334039189668541390100207327904961319483760155169603943242981689663862437925911778960114177678108210567584007591134684147778926900042557012808839681463510951676473652573434803122893243114044558177074490617381970510805712008078530947068783946683384210
def c000000000101_posP : Nat := 13278646434936315288963701352208253598829510232637287348709797308210916353443403179391335315283132295895340755269161762708947047445093398592602715735677060659925269218679695929840834966846188594735744430237248983595403136002472375593035603072765849001381298063167518172041329501446788387217268590777401570514804561416771775527405036280893792676879207681418125945040551121222554430859784848142002181611430396183524371974724797235795426258380921493175768620526808342360015971171869651079540872484693871760219260434027541430172920694802888987945690622076140284109972037031729086859664151659483719770766892181522375760945378231490692473967110401191717861803741719117732352369452848870345759238867367923028329832261716095573276728537855025176156799719206577370532305591704535831050255278637318117526773720190484766529321498105108391440209862639245769389310715612047377848650767830539852097269943301783969515183932953659473108077907112649493409832817364744568160072525254362316856980017533251109308611693452628445358044078717191489118982437598073419942058480800520698586367324582122890278292845196789629741409474193878142801600729042748235277397964325834279114751822976558485559101826300563086534674807163548691384828601067294066015004901378912982272492799029899868393305163000249710491673235448903972982858629325323530008419554125095847348323319860757105795171713115906074511536271872885336395349512185189558675754885549368286112579509513827799624098506920275273304070065245308097953221469264807679371451921274417444802958632339692628853174263773092838233642977379131311879616612362449519252892506836160339660583909001994291403744879682011384876751853373044848672724873005692640942612978983060449968577590201902310129912788577369139464180548152465230411409687265780369257744079666229554881069727496016095119355488555522042612660055203593536857297837553542394517907475964100332499686374087971396248702371163391734415975612581405279739606732183759916439670794711824963515459622026457209739920173662568417605105124239587342600583213767820250736829364729260230315567600951189529359615311633485541099169065753884348076667565699445154367263813367777627170224284528884874059154822548493446132504170675761912887129905707128393361939923356067445247968979478237810520507569050756280353631631131529043339882490523040113128301771834639375968819974444633903989972492349223862161112389352118371317475684292296333487573568653766039396995360724635159438881568782642473872809637150738323623421806512792438788833124109642924419329757862125217752049947996423151852991425593424845858345106027680556562292647245925221837243999291539305654096092873120604329308123298079646364053939754908435381477168740928150744146053868496785402606603182098242226544700740191612006006286027875197539969899018110563804870076149161739910194394827002461691598825169316905485239425445020210053027597781520702756020348932861330638992617757633329069379974010756407118280446224651859055709456039066130966326427620362685711031134404110448359324609658673999670710196393410344689663895131199972070794910279920046457491594660918312716064540647095562993488064426073706188564684758497156803197059345871595932725554109613614672564813527571357489457855469465882841901042371296408826908977684855768467426627081760999854243061489239696746936278531528245573091869396705260184507995486947421778517776787900828924565885139582928477910964121894912
def c000000000101_perP : Nat := 954057198669027643529632226808660167139173863748296064943217129862472380715726046135286929724220761975191967078935295253190443771946088429590141260120311384094723446910510030308303506599464460798243961564785728236298146975143268534374976808708348594910502893614862426766931507526119280373897859961739567782304467620199740351489301120109949303526359580117148275885616605519092113352915870019361240506402296830417421717479213885184022817441255259800483036585162505208446384072907691541330257517995252923056117363495043006639967089933978674320267585676573410164609998775597949307588869273455652871118862992325827024547121121319904003204110330124073831955689119499796470928426543867404277045075274827611222328369633870861575289898803292375304119993803587271560863101155470281544775710491857622246322198771992742242471535754400993104694084966306575334786444879390765194440694928868281712459058912911017006291374450902969469500379508348541300024499084671150070872239565563259462828270878532956347306196680508672276177547977668785073518774017770635640060511063627317802529763659139530657771569057582917465950276242922063268665969804194041375737861336386947136646824744899920507797687416745468194554163773378256164189422301428211967082949082343266724333569356419787755154180404361118600042948178863008196671876358086768091185483116011631425430358526373430940807543598215931002425789065792055671398767754817857454547176997916932400168491736266772365012282894441462211692879289737528990994770341152048609664090934324061425830653970903519555028544434203180549933673734650491667143032497276825646218403024054869439056835364311425768337354237717816398305974651155632400423984096307839005726483879445017858867278436064025498591320359142532867129669070158352552777516509419604653634536516181124762512543579261195499126510380771384037274719654262317106542694701027032554744727935110134766693255878821742694582844043690787251492869974733140272255264563620959464413654861373545510026865413491672585832857908134462729142932548293174936241934294044560128399308552790590040456689295645940486278281036522565822564384330050736963123647861744386998532356624815284177829398658147059758299754047504011046983777293698236612479394888259449768139013873376869801442512236260027960307050191469256570976139184162372590587748579430841384452139305124700160274871318569084382823695767744954752498372918963099667537740686004822206119418207923055881793877340090247534883929770554011790859923858145341058210987686683553703017034124841331514582277147362726302425303696996148283084805074034971822564296251529416010679228163632152106048798113704673162117403298038010243654002679978539243259446498035803560875701343233466973784689962897598524680130989049141972403147924796939725362274410210165325253916348353602977250107876405351431467629994834893711798645318300946426682550120137219276615566110929420428467589511962721403790151759756260163475840385900853185843999511394371059266556286960906149207828482526373992664712198468187523181805515594629925289162849848253700015394332466255784490187439089509757037854388304524884511470191341813290602647374539777939319639020910603227277571504314843402
def c000000000101_wordP : Nat := 249533213899045121398106220228319242097367217476481504165885609906140517805730094084096146449146145669183725917348410793240418374078534854486121382083911216356763025928118944202315613129116837906015025161524603454644703077435041649091421257915428689596648473657903806030933401373791744892949474685338575453656008318079169317972561589760773222292218731334719047861192477657894422890562868143905049212337948104178058075145912076814667492621037118603023426039634575588251711543939279454919358126825482859964417489917237282331515180003098923133382272206229143274553671908652365041359356641935718379841354590058397964591944053598608340318462612229393401218711128779107778944624717151059255568443742733341942576539725760792210113184760210236485357078819368739898757977587501613244236535031249665678233415865449773962046110310549138363444447621693527574651088755345219510008012608392263118253376852831754337006151377482205863176237146076258880191291221443227283384923572061878812174971036602791171480251120071657867663642250609499928068951654756082967439250194042075436319282293547149733028324146427065854706868078797965344491038940296759793515753089466060292161184575854142762040835378960947800262037626211225301936720567082037093578846321259614574495750168939578353586711171569705380734141623212568513822304463926198634878555465539823445388570980449481969640063568869056472776044476792362472018530710680180317566056887577498348789749233559202292277134267072808282340960984102851062399046416991038204370916942664910450025347472083766848391536335343786675871413370006454694264530967835238185672073669853077107719776504535198669944535057753900768784093949420525863473840303551530279583220472789828903580346246595194201900932881925867665910819523452761706497824929559234448617557925557664722050530878873504075095097604188065556844395375882216549947072391187518552382643176564931883112344523916116068731103912284967216620536965807833822636189294705040692629362890654362380972092226590229922585688181545890934547835788762642716159379441360887500426005901293982122427438667522029327530988507772423940610690967170101646171816105876532974274429835571180337811862087726948940560824342070495999244066768369029795256872940034853217670999357270784786746875385205653545993984708509561899184615889121504899776219591615015649168110963804619615540491647507602779414929232711073674513445911268933804919088063874951392813946806619098837618228525554170423668565246085915178031347154415848379257717290680190338112951452356889593830650123863227905706206275856574060830989674760488886229297248109585876379520846259837777917558820473400421953189585110405210690627961959709961080660673324620465761026055525738795278325672297326081885883477088953170911583063853233539176395063329212065677867399929859402247070213726544369901402016986619827842783898899734098353490553518247229880216086383052233797505992400559263809615887585532533069710822613695594216958032025550326869322201168092496397017924657208606673174827926472751078396117422270692130529116597600196263653714087645402866531838258467544295697654575177221759578403128773968709940695266021171151667388557507650984326174321196615221152331446903647039898394013267358546220113969522481180643183781284112075325206440344423427594267677577933875358974898318799326603653970132825907661352071521083006318153323776147484664052711272510330695140097915588560521995743660086744426554863490580051101654517738371271261904157044905874096417688415229644590197854265922601472973029064306634295329429793284024206724092937921549088029833684935415807159030067686976782632336795320701844703927517256370025502331226209069952029381507951122820911957592420682463732465634505398910862892113164311352266092672065270075442458654174475552129338110231855409323025436701435339284686376488089039043836859352975770873666494049711778543505586492293418231850683409547709881725069728072808206514163616852312460057613725242504477849546721011571501432968195296435378691622790420101788017067380642226374921136977042601884189739139957146634232681016568128415639865055485200014445289029481837853897647701220282309683670842320470202101194913655301089349721903451086750208036142338853170229571721879817281238500489958210710012540088149148929911754895423083396274510668149100464544454816689920885537088126295822128707457069851316726747223867004215131029769766847042535973020214114814387922347880784566151961834839638433229072184355778366476224386303538821963707771994032927378215340590593685800475468661317657798745165145465883501513445513751314634092665513779398064666043607179504464728909169135953648605897117935539402285245092662196082212915163613498868847853192907127587873923233516049084962015701929492892974223593679033235297964652161209918533460225632258921800329204922691411296951552918825938654844548516119485698187882277606086576888212063915467604478

def C_c000000000101 : Cert :=
  { w := c000000000101_w, b := c000000000101_b, nranks := c000000000101_nranks,
    rankP := c000000000101_rankP, posP := c000000000101_posP, perP := c000000000101_perP,
    wordP := c000000000101_wordP }

theorem C_c000000000101_check : C_c000000000101.check = true := by decide +kernel
theorem C_c000000000101_checkG : C_c000000000101.checkG = true := by decide +kernel

/-- **`0^9 1 0 1` is excluded**, whatever the transient (rank certificate, strip width `7`). -/
theorem not_eventually_000000000101 :
    ¬ EventuallyWord
      [false, false, false, false, false, false, false, false, false, true, false, true] :=
  C_c000000000101.not_eventuallyWord C_c000000000101_check C_c000000000101_checkG (by decide)
    (by decide)

end Rule30StripCertificates
end Ruliology.CellularAutomata
