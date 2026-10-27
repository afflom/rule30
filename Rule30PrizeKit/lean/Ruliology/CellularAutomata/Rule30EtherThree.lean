module

public import Ruliology.CellularAutomata.Rule30Ether

/-!
# Rule 30, least period 3: the 12 × 3 ether and the ether-and-wall framework

The *period-3 ether* is the spatio-temporally periodic rule-30 orbit of spatial period `12` and
temporal period `3` whose columns at the phases `0, 1, 2` are

    001 001 011 110 010 010 110 101 100 100 101 011.

Both least-period-3 words `001` and `011` are ether columns up to a time shift; `aligned3_*` lists
all six alignments of each word, and `alignments_001_complete`, `alignments_011_complete` show
there are no others. The ether has the glide symmetry `ether3 (j + 4) φ = ether3 j (φ + 1)`.

A *wall* for attachment column `a` and width `b` is a predicate `W φ r` on (ether phase, strip of
`b` cells encoded as bits of `r`) that is closed under every value of the cell right of the strip
and, at the white phases of ether column `a`, has the first strip cell equal to ether column
`a + 1` (`WallOK`). `trap_invariant3`, `ether_wall_trap3`, `absorption3_excludes`: exactly as for
period 4 (`Rule30Ether`), an ether segment followed by a wall state is a trap, and absorption of
every finite right half into the family excludes `w^∞` as a tail of the center column.

Unlike period 4, no wall is known: `no_wall_le_12` (`Rule30EtherThreeNoWall`) proves (kernel
certificate) that no attachment column has a wall of width `≤ 12`, and an exhaustive C search
finds none at widths `≤ 23`. The statements here are
therefore a framework, conditional on a wall; with an empty `W`, `Absorption3` is false and the
theorems are vacuous. For `001` a different trap exists (`Rule30EtherThreeTrap`).

The period-3 study spans the modules `Rule30EtherThree`, `Rule30EtherThreeNoWall`,
`Rule30EtherThreeTrap`, `Rule30EtherThreeReach`, `Rule30EtherThreeLeft` and
`Rule30EtherThreeSkeleton`, all in the namespace `Rule30EtherThree`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThree

open Rule30Jen Rule30StripCertificates Rule30Ether

/-! ### The ether -/

/-- Ether columns `0..11` at the phases `0, 1, 2`. -/
def ether3Table : List (List Bool) :=
  [[false, false, true], [false, false, true], [false, true, true], [true, true, false],
   [false, true, false], [false, true, false], [true, true, false], [true, false, true],
   [true, false, false], [true, false, false], [true, false, true], [false, true, true]]

/-- Ether column `j mod 12` at phase `φ mod 3`. -/
def ether3 (j φ : Nat) : Bool := (ether3Table.getD (j % 12) []).getD (φ % 3) false

theorem ether3_congr {j j' φ φ' : Nat} (hj : j % 12 = j' % 12) (hφ : φ % 3 = φ' % 3) :
    ether3 j φ = ether3 j' φ' := by
  unfold ether3; rw [hj, hφ]

theorem ether3_rule_small : ∀ j, j < 12 → ∀ φ, φ < 3 →
    ether3 j (φ + 1) = rule (ether3 (j + 11) φ) (ether3 j φ) (ether3 (j + 1) φ) := by decide

/-- **The period-3 ether is a rule-30 orbit** (column `j - 1` is column `j + 11`). -/
theorem ether3_rule (j φ : Nat) :
    ether3 j (φ + 1) = rule (ether3 (j + 11) φ) (ether3 j φ) (ether3 (j + 1) φ) := by
  have h := ether3_rule_small (j % 12) (Nat.mod_lt _ (by decide)) (φ % 3) (Nat.mod_lt _ (by decide))
  rw [ether3_congr (j := j % 12) (j' := j) (φ := φ % 3 + 1) (φ' := φ + 1) (by omega) (by omega),
    ether3_congr (j := j % 12 + 11) (j' := j + 11) (φ := φ % 3) (φ' := φ) (by omega) (by omega),
    ether3_congr (j := j % 12) (j' := j) (φ := φ % 3) (φ' := φ) (by omega) (by omega),
    ether3_congr (j := j % 12 + 1) (j' := j + 1) (φ := φ % 3) (φ' := φ) (by omega) (by omega)] at h
  exact h

theorem ether3_period (j φ : Nat) : ether3 j (φ + 3) = ether3 j φ :=
  ether3_congr rfl (by omega)

theorem ether3_glide_small : ∀ j, j < 12 → ∀ φ, φ < 3 → ether3 (j + 4) φ = ether3 j (φ + 1) := by
  decide

/-- **Glide symmetry**: four columns to the right is one step later. -/
theorem ether3_glide (j φ : Nat) : ether3 (j + 4) φ = ether3 j (φ + 1) := by
  have h := ether3_glide_small (j % 12) (Nat.mod_lt _ (by decide)) (φ % 3) (Nat.mod_lt _ (by decide))
  rw [ether3_congr (j := j % 12 + 4) (j' := j + 4) (φ := φ % 3) (φ' := φ) (by omega) (by omega),
    ether3_congr (j := j % 12) (j' := j) (φ := φ % 3 + 1) (φ' := φ + 1) (by omega) (by omega)] at h
  exact h

/-! ### The words `001` and `011` as ether columns -/

/-- The letter of the 3-periodic word `w` at phase `ψ`. -/
def wordAt3 (w : List Bool) (ψ : Nat) : Bool := w.getD (ψ % 3) false

def w001 : List Bool := [false, false, true]
def w011 : List Bool := [false, true, true]

/-- `w` is ether column `j0` shifted by `s` in time: `ether3 j0 (ψ + s) = w[ψ mod 3]`. -/
def aligned3 (w : List Bool) (j0 s : Nat) : Bool :=
  (List.range 3).all fun ψ => ether3 j0 (ψ + s) == wordAt3 w ψ

theorem aligned3_spec {w : List Bool} {j0 s : Nat} (h : aligned3 w j0 s = true) (ψ : Nat) :
    ether3 j0 (ψ + s) = wordAt3 w ψ := by
  have h1 := List.all_eq_true.1 h (ψ % 3) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  have e1 : ether3 j0 (ψ + s) = ether3 j0 (ψ % 3 + s) := ether3_congr rfl (by omega)
  have e2 : wordAt3 w ψ = wordAt3 w (ψ % 3) := by unfold wordAt3; rw [Nat.mod_mod]
  rw [e1, e2]; exact beq_iff_eq.1 h1

/-- The six alignments `(j0, s)` of `001`. -/
def A001 : List (Nat × Nat) := [(0, 0), (1, 0), (4, 2), (5, 2), (8, 1), (9, 1)]
/-- The six alignments `(j0, s)` of `011`. -/
def A011 : List (Nat × Nat) := [(2, 0), (3, 2), (6, 2), (7, 1), (10, 1), (11, 0)]

theorem aligned3_001_0 : aligned3 w001 0 0 = true := by decide
theorem aligned3_001_1 : aligned3 w001 1 0 = true := by decide
theorem aligned3_001_4 : aligned3 w001 4 2 = true := by decide
theorem aligned3_001_5 : aligned3 w001 5 2 = true := by decide
theorem aligned3_001_8 : aligned3 w001 8 1 = true := by decide
theorem aligned3_001_9 : aligned3 w001 9 1 = true := by decide
theorem aligned3_011_2 : aligned3 w011 2 0 = true := by decide
theorem aligned3_011_3 : aligned3 w011 3 2 = true := by decide
theorem aligned3_011_6 : aligned3 w011 6 2 = true := by decide
theorem aligned3_011_7 : aligned3 w011 7 1 = true := by decide
theorem aligned3_011_10 : aligned3 w011 10 1 = true := by decide
theorem aligned3_011_11 : aligned3 w011 11 0 = true := by decide

theorem A001_ok : ∀ a ∈ A001, aligned3 w001 a.1 a.2 = true := by decide
theorem A011_ok : ∀ a ∈ A011, aligned3 w011 a.1 a.2 = true := by decide

/-- **All alignments of `001`**: for `j0 < 12`, `s < 3`, `001` is ether column `j0` shifted by `s`
exactly for the six pairs of `A001`. -/
theorem alignments_001_complete :
    ∀ j0, j0 < 12 → ∀ s, s < 3 → (aligned3 w001 j0 s = true ↔ (j0, s) ∈ A001) := by decide

/-- **All alignments of `011`.** -/
theorem alignments_011_complete :
    ∀ j0, j0 < 12 → ∀ s, s < 3 → (aligned3 w011 j0 s = true ↔ (j0, s) ∈ A011) := by decide

/-! ### A kernel-friendly bounded `all` -/

/-- `p n && …`: evaluates `p n` first, so the kernel walks the range without deep recursion. -/
def allBelowT (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelowT p n

theorem allBelowT_spec {p : Nat → Bool} : ∀ {n}, allBelowT p n = true → ∀ i, i < n → p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    rw [allBelowT, Bool.and_eq_true] at h
    by_cases hin : i < n
    · exact allBelowT_spec h.2 i hin
    · rw [show i = n by omega]; exact h.1

/-! ### Strips of a general evolution, encoded as bit masks -/

/-- `r` encodes columns `k + 1, …, k + b` of `F` at time `t` (bit `i` is column `k + 1 + i`). -/
def EncF (F : Nat → Nat → Bool) (b t k r : Nat) : Prop :=
  r < 2 ^ b ∧ ∀ i, i < b → r.testBit i = F t (k + 1 + i)

theorem encF_step {F : Nat → Nat → Bool} (hF : IsR30 F) {b t k r : Nat} (h : EncF F b t k r) :
    EncF F b (t + 1) k (stripStep b (F t k) (F t (k + 1 + b)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun i hi => ?_⟩
  rw [testBit_stripStep b _ _ r h.1 i hi]
  have e : F (t + 1) (k + 1 + i) = rule (F t (k + i)) (F t (k + i + 1)) (F t (k + i + 2)) := by
    rw [show k + 1 + i = (k + i) + 1 by omega]; exact hF t (k + i)
  rw [e]
  have hc : r.testBit i = F t (k + i + 1) := by rw [h.2 i hi]; congr 1; omega
  have hl : (if i = 0 then F t k else r.testBit (i - 1)) = F t (k + i) := by
    split
    · rename_i h0; subst h0; rfl
    · rename_i h0; rw [h.2 (i - 1) (by omega)]; congr 1; omega
  have hr : (if i + 1 = b then F t (k + 1 + b) else r.testBit (i + 1)) = F t (k + i + 2) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (i + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

theorem encF_head {F : Nat → Nat → Bool} {b t k r : Nat} (h : EncF F b t k r) (hb : 0 < b) :
    r.testBit 0 = F t (k + 1) := h.2 0 hb

/-! ### Walls and the trap invariant -/

/-- **Wall** for attachment column `a` and width `b`: strips (phase, bit mask) that are well formed,
satisfy the U-property (at the white phases of ether column `a` the first cell is ether column
`a + 1`), and are closed under both values of the cell right of the strip. -/
def WallOK (a b : Nat) (W : Nat → Nat → Prop) : Prop :=
  (∀ φ r, W φ r → r < 2 ^ b) ∧
  (∀ φ r, W φ r → ether3 a φ = false → r.testBit 0 = ether3 (a + 1) φ) ∧
  (∀ φ r (z : Bool), W φ r → W ((φ + 1) % 3) (stripStep b (ether3 a φ) z r))

/-- **Trap invariant.** If column `0` is ether column `j0` from `t1` on, columns `1..k` carry the
ether at `t1` (column `k` is ether column `a`), and the next `b` columns form a wall state, then
this stays true forever. -/
theorem trap_invariant3 {F : Nat → Nat → Bool} (hF : IsR30 F) {a b : Nat} {W : Nat → Nat → Prop}
    (hW : WallOK a b W) (hb : 0 < b) (j0 s k t1 : Nat) (hk : (j0 + k) % 12 = a % 12)
    (h0 : ∀ t, t1 ≤ t → F t 0 = ether3 j0 (t + s))
    (hE : ∀ p, 1 ≤ p → p ≤ k → F t1 p = ether3 (j0 + p) (t1 + s))
    (r : Nat) (hr : EncF F b t1 k r) (hWr : W ((t1 + s) % 3) r) :
    ∀ n, (∀ p, p ≤ k → F (t1 + n) p = ether3 (j0 + p) (t1 + n + s)) ∧
      ∃ r', EncF F b (t1 + n) k r' ∧ W ((t1 + n + s) % 3) r' := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun p hp => ?_, r, by simpa using hr, by simpa using hWr⟩
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0; simpa using h0 t1 (Nat.le_refl _)
    · simpa using hE p hp0 hp
  | succ n ih =>
    obtain ⟨hE', r', hr', hW'⟩ := ih
    have hph : t1 + n + 1 + s = (t1 + n + s) + 1 := by omega
    have htt : t1 + (n + 1) = (t1 + n) + 1 := by omega
    have hck : F (t1 + n) k = ether3 a ((t1 + n + s) % 3) := by
      rw [hE' k (Nat.le_refl k)]; exact ether3_congr (by omega) (by omega)
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0; exact h0 (t1 + (n + 1)) (by omega)
      · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [htt, hF, hph, ether3_rule (j0 + (q + 1)) (t1 + n + s)]
        have hl : F (t1 + n) q = ether3 (j0 + (q + 1) + 11) (t1 + n + s) := by
          rw [hE' q (by omega)]; exact ether3_congr (by omega) rfl
        rw [hl, hE' (q + 1) hp]
        by_cases hpk : q + 1 < k
        · rw [hE' (q + 2) (by omega), show j0 + (q + 2) = j0 + (q + 1) + 1 by omega]
        · have hpk' : q + 1 = k := by omega
          cases hbk : ether3 (j0 + (q + 1)) (t1 + n + s) with
          | true => rfl
          | false =>
            have hw2 : ether3 a ((t1 + n + s) % 3) = false := by
              rw [← hbk]; exact ether3_congr (by omega) (by omega)
            have hhead := hW.2.1 _ r' hW' hw2
            rw [encF_head hr' hb, ← hpk'] at hhead
            rw [hhead]
            congr 1
            exact ether3_congr (by omega) (by omega)
    · refine ⟨stripStep b (F (t1 + n) k) (F (t1 + n) (k + 1 + b)) r', ?_, ?_⟩
      · rw [htt]; exact encF_step hF hr'
      · rw [hck]
        have e := hW.2.2 _ r' (F (t1 + n) (k + 1 + b)) hW'
        rwa [show ((t1 + n + s) % 3 + 1) % 3 = (t1 + (n + 1) + s) % 3 by omega] at e

/-! ### The trap for the true pattern -/

/-- **Ether-and-wall trap, period 3.** If the center column is ether column `j0` (phase offset
`s`) from time `T` on, and at some `t1 ≥ T` columns `1..k` carry the ether (column `k` is ether
column `a`) while columns `k + 1..k + b` form a wall state, we get a contradiction. -/
theorem ether_wall_trap3 {a b : Nat} {W : Nat → Nat → Prop} (hW : WallOK a b W) (hb : 0 < b)
    (T t1 j0 s k : Nat) (hk : (j0 + k) % 12 = a % 12)
    (h0 : ∀ t, T ≤ t → cell t 0 = ether3 j0 (t - T + s)) (ht1 : T ≤ t1)
    (hE : ∀ p : Nat, 1 ≤ p → p ≤ k → cell t1 (p : Int) = ether3 (j0 + p) (t1 - T + s))
    (r : Nat) (hr : EncF trueRight b t1 k r) (hWr : W ((t1 - T + s) % 3) r) : False := by
  have hph : ∀ t, T ≤ t → (t + (s + 2 * T)) % 3 = (t - T + s) % 3 := by intro t ht; omega
  have inv := trap_invariant3 trueRight_isR30 hW hb j0 (s + 2 * T) k t1 hk
    (fun t ht => by
      show cell t ((0 : Nat) : Int) = _
      rw [show ((0 : Nat) : Int) = 0 by rfl, h0 t (by omega)]
      exact ether3_congr rfl (hph t (by omega)).symm)
    (fun p hp1 hpk => by
      show cell t1 (p : Int) = _
      rw [hE p hp1 hpk]
      exact ether3_congr rfl (hph t1 ht1).symm)
    r hr (by rw [hph t1 ht1]; exact hWr)
  -- column `1` at the white times of column `0` is ether column `j0 + 1`
  have key : ∀ t, t1 ≤ t → cell t 0 = false → cell t 1 = ether3 (j0 + 1) (t + (s + 2 * T)) := by
    intro t ht hw
    obtain ⟨hE', r', hr', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hr' hW'
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hw2 : ether3 a ((t + (s + 2 * T)) % 3) = false := by
        have e : cell t 0 = ether3 (j0 + 0) (t + (s + 2 * T)) := hE' 0 (Nat.le_refl 0)
        rw [hw] at e
        rw [e]; exact ether3_congr (by omega) (by omega)
      have hhead := hW.2.1 _ r' hW' hw2
      rw [encF_head hr' hb] at hhead
      have e1 : cell t 1 = ether3 (a + 1) ((t + (s + 2 * T)) % 3) := hhead
      rw [e1]; exact ether3_congr (by omega) (by omega)
    · exact hE' 1 hk0
  refine Rule30MaskedJen.masked_jen 0 (P := 3) (T := t1) (by decide) ?_ ?_
  · intro t ht
    rw [h0 (t + 3) (by omega), h0 t (by omega)]
    exact ether3_congr rfl (by omega)
  · intro t ht hw
    have hw3 : cell (t + 3) 0 = false := by
      rw [h0 (t + 3) (by omega), ← hw, h0 t (by omega)]
      exact ether3_congr rfl (by omega)
    rw [show (0 : Int) + 1 = 1 by rfl, key (t + 3) (by omega) hw3, key t ht hw]
    exact ether3_congr rfl (by omega)

/-- **No entry into the period-3 ether-and-wall family.** -/
theorem no_ether_wall_entry3 {a b : Nat} {W : Nat → Nat → Prop} (hW : WallOK a b W) (hb : 0 < b)
    (w : List Bool) (j0 s : Nat) (hal : aligned3 w j0 s = true)
    (T : Nat) (hc : ∀ t, T ≤ t → cell t 0 = wordAt3 w (t - T))
    (t1 k : Nat) (ht1 : T ≤ t1) (hk : (j0 + k) % 12 = a % 12)
    (hE : ∀ p : Nat, 1 ≤ p → p ≤ k → cell t1 (p : Int) = ether3 (j0 + p) (t1 - T + s))
    (r : Nat) (hr : EncF trueRight b t1 k r) (hWr : W ((t1 - T + s) % 3) r) : False :=
  ether_wall_trap3 hW hb T t1 j0 s k hk (fun t ht => by rw [hc t ht, aligned3_spec hal]) ht1 hE r hr hWr

/-! ### Absorption into the family excludes `w^∞` -/

/-- The ether-and-wall family condition for an evolution `F` at time `t1` (ether phase `t1 + s`). -/
def InFamily3 (a b : Nat) (W : Nat → Nat → Prop) (F : Nat → Nat → Bool) (j0 s t1 : Nat) : Prop :=
  ∃ k r, (j0 + k) % 12 = a % 12 ∧ (∀ p, 1 ≤ p → p ≤ k → F t1 p = ether3 (j0 + p) (t1 + s)) ∧
    EncF F b t1 k r ∧ W ((t1 + s) % 3) r

/-- **Absorption** (open; a `Prop`) for a word `w`, alignments `A`, and a wall `W` at column `a`:
every finitely supported right half driven by `w^∞` (any phase `φ`) eventually enters the family. -/
def Absorption3 (w : List Bool) (A : List (Nat × Nat)) (a b : Nat) (W : Nat → Nat → Prop) : Prop :=
  ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ : Nat,
    ∃ al ∈ A, ∃ t1, InFamily3 a b W (drv (fun t => wordAt3 w (t + φ)) x) al.1 (al.2 + φ) t1

/-- **Absorption excludes `w^∞` as a tail of the center column**, for every transient. -/
theorem absorption3_excludes (w : List Bool) (A : List (Nat × Nat))
    (hal : ∀ al ∈ A, aligned3 w al.1 al.2 = true) {a b : Nat} {W : Nat → Nat → Prop}
    (hW : WallOK a b W) (hb : 0 < b) (hA : Absorption3 w A a b W) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w (t - T) := by
  rintro ⟨T, hT⟩
  have hc : (fun t => cell (T + t) 0) = (fun t => wordAt3 w (t + 0)) := by
    funext t; rw [hT (T + t) (by omega)]; congr 1; omega
  have hfin : ∀ p, T < p → (fun p : Nat => cell T (p : Int)) p = false :=
    fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)
  obtain ⟨⟨j0, s⟩, ha, t1, k, r, hk, hE, hr, hWr⟩ := hA (fun p => cell T (p : Int)) T hfin 0
  have hal' := hal (j0, s) ha
  rw [← hc] at hE hr
  have hr' : EncF trueRight b (T + t1) k r := by
    refine ⟨hr.1, fun i hi => ?_⟩
    rw [hr.2 i hi, ← cell_eq_drv T t1 (k + 1 + i)]
    rfl
  refine ether_wall_trap3 hW hb T (T + t1) j0 s k hk (fun t ht => ?_) (by omega)
    (fun p hp1 hpk => ?_) r hr' ?_
  · rw [hT t ht, aligned3_spec hal']
  · rw [cell_eq_drv T t1 p, hE p hp1 hpk]
    exact ether3_congr rfl (by omega)
  · rw [show T + t1 - T + s = t1 + (s + 0) by omega]; exact hWr

/-- **Absorption excludes `001^∞`** (for any wall; with the six alignments of `001`). -/
theorem not_eventually_001_of_absorption3 {a b : Nat} {W : Nat → Nat → Prop} (hW : WallOK a b W)
    (hb : 0 < b) (hA : Absorption3 w001 A001 a b W) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) :=
  absorption3_excludes w001 A001 A001_ok hW hb hA

/-- **Absorption excludes `011^∞`** (for any wall; with the six alignments of `011`). -/
theorem not_eventually_011_of_absorption3 {a b : Nat} {W : Nat → Nat → Prop} (hW : WallOK a b W)
    (hb : 0 < b) (hA : Absorption3 w011 A011 a b W) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T) :=
  absorption3_excludes w011 A011 A011_ok hW hb hA

end Rule30EtherThree
end Ruliology.CellularAutomata
