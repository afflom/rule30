module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# Rule 30: long black runs shield the right half

If a column of the single-seed pattern stays black long enough, the cells to its right are
forced, whatever they were before. With Jen's theorem and its masked form
(`Rule30MaskedJen`) this excludes many would-be eventual periods of the center column, for every
transient.

**The nine-black shield.**
* `nine_black` (Lemma A): if column `m` is black at times `t, …, t + 8`, then at time `t + 9`
  column `m + 1` is white and column `m + 2` is black. A finite check over the `2 ^ 11` possible
  contents of columns `m + 1, …, m + 11` at time `t` (`nine_black_core`). Eight steps do not
  suffice for this argument (`eight_black_not_enough`).
* `black_shield` (Lemma A*): if column `m` is black for `9 j` consecutive steps, then right after
  them columns `m + 1, …, m + 2j` read `(white black)^j`.

**Exclusions.** In each statement the center column `c` is assumed periodic from some time `T`
on, and the transient `T` is arbitrary.
* `not_eventuallyPeriodic_of_long_one_runs_col`: a column in which, from some time on, every black
  run that is followed by a white cell has length at least `9` is not eventually periodic. (Such
  a black run makes column `i + 1` white at the first white cell and black at the later ones of
  the next white run, so `orCol i` becomes a function of column `i`; this contradicts
  `Rule30MaskedJen.orCol_not_eventuallyPeriodic`.) `not_eventuallyPeriodic_of_long_one_runs` is
  the center column, `finitary_long_runs` a finitary version, and `not_eventually_zero_ones` the
  words `0 1^k`, `k ≥ 9`.
* `no_long_black_run` (Theorem B): a period of length `P` cannot contain a black run of length
  `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r` (roughly `r ≥ 0.82 P + 8.2`). By Lemma A*, column `1` becomes
  periodic, against Jen's theorem.
* `no_black_white_run` (Theorem D): a period cannot contain a black run of length `s ≥ 9`
  followed by a white run of length `r ≥ 1 + 9 ⌈(k + 8) / 2⌉`, where `k = P - s - r`.
* `no_white_run_11`: the words `0^r 1 1` with `r ≥ 10` are excluded: column `1` locks into the
  pattern `1^(r+1) 0` or `0^(r+1) 1` within two periods.

Theorem B′, the block-specific sharpening of Theorem B, is in `Rule30BlackRunBlocks`.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242, whose
adjacent-column argument these results extend.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30BlackRuns

open Rule30Jen Rule30Prize Rule30MaskedJen

/-! ### Finite rows -/

/-- The cells at columns `p, p + 1, …, p + n - 1` at time `t`. -/
def rowAt (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t p :: rowAt t (p + 1) n

theorem length_rowAt (t : Nat) : ∀ (n : Nat) (p : Int), (rowAt t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [rowAt, length_rowAt t n (p + 1)]

/-- One rule-30 step on a finite row with left neighbour `l`; the result is one cell shorter. -/
def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []

theorem stepRow_rowAt (t : Nat) : ∀ (n : Nat) (p : Int),
    stepRow (cell t (p - 1)) (rowAt t p (n + 1)) = rowAt (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    have ih := stepRow_rowAt t n (p + 1)
    rw [show p + 1 - 1 = p by omega] at ih
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) ::
        stepRow (cell t p) (rowAt t (p + 1) (n + 1)) = cell (t + 1) p :: rowAt (t + 1) (p + 1) n
    rw [ih]
    rfl

/-- `k` steps with a black left neighbour. -/
def runBlack : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => runBlack k (stepRow true L)

theorem runBlack_rowAt (m : Int) : ∀ (k n t : Nat), (∀ s, s < k → cell (t + s) m = true) →
    runBlack k (rowAt t (m + 1) (n + k)) = rowAt (t + k) (m + 1) n
  | 0, n, t, _ => by simp [runBlack]
  | k + 1, n, t, h => by
    have h0 : cell t m = true := by simpa using h 0 (by omega)
    have hstep : stepRow true (rowAt t (m + 1) (n + k + 1)) = rowAt (t + 1) (m + 1) (n + k) := by
      have := stepRow_rowAt t (n + k) (m + 1)
      rw [show m + 1 - 1 = m by omega, h0] at this
      exact this
    have ih := runBlack_rowAt m k n (t + 1) (fun s hs => by
      have := h (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    show runBlack k (stepRow true (rowAt t (m + 1) (n + (k + 1)))) = rowAt (t + (k + 1)) (m + 1) n
    rw [show n + (k + 1) = n + k + 1 by omega, hstep, ih, show t + 1 + k = t + (k + 1) by omega]

/-! ### The nine-black shield -/

/-- Finite core of Lemma A: all `2 ^ 11` rows. -/
theorem nine_black_core : ∀ L ∈ allLists 11, runBlack 9 L = [false, true] := by
  decide +kernel

/-- The finite check fails with eight steps: the row `1010001000` ends as `(black, white)` after
eight steps next to a black column. So `9` is the least length for this light-cone argument. -/
theorem eight_black_not_enough : ∃ L ∈ allLists 10, runBlack 8 L ≠ [false, true] := by
  refine ⟨[true, false, true, false, false, false, true, false, false, false], ?_, by decide⟩
  exact mem_allLists _

/-- **Lemma A.** A column black for 9 consecutive steps forces white, black right after them in
the next two columns. -/
theorem nine_black (t : Nat) (m : Int) (h : ∀ s, s < 9 → cell (t + s) m = true) :
    cell (t + 9) (m + 1) = false ∧ cell (t + 9) (m + 2) = true := by
  have h1 := runBlack_rowAt m 9 2 t h
  have hmem : rowAt t (m + 1) (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (rowAt t (m + 1) (2 + 9))
    rwa [length_rowAt] at this
  rw [nine_black_core _ hmem] at h1
  have h2 : rowAt (t + 9) (m + 1) 2 = [cell (t + 9) (m + 1), cell (t + 9) (m + 1 + 1)] := rfl
  rw [h2] at h1
  simp only [List.cons.injEq] at h1
  refine ⟨h1.1.symm, ?_⟩
  rw [show m + 2 = m + 1 + 1 by omega]
  exact h1.2.1.symm

/-- **Lemma A\*.** A column black for `9 j` consecutive steps forces `(white black)^j` in the next
`2 j` columns right after them. -/
theorem black_shield (m : Int) : ∀ (j t : Nat), (∀ s, s < 9 * j → cell (t + s) m = true) →
    ∀ i : Nat, 1 ≤ i → i ≤ j →
      cell (t + 9 * j) (m + 2 * (i : Int) - 1) = false ∧ cell (t + 9 * j) (m + 2 * (i : Int)) = true
  | 0, _, _, i, hi1, hij => by omega
  | j + 1, t, h, i, hi1, hij => by
    by_cases hi : i ≤ j
    · have ih := black_shield m j (t + 9) (fun s hs => by
        have := h (9 + s) (by omega)
        rwa [show t + (9 + s) = t + 9 + s by omega] at this) i hi1 hi
      rwa [show t + 9 + 9 * j = t + 9 * (j + 1) by omega] at ih
    · have hieq : i = j + 1 := by omega
      subst hieq
      -- column m + 2 j is black at the 9 times t + 9 j + s, s < 9
      have hcol : ∀ s, s < 9 → cell (t + 9 * j + s) (m + 2 * (j : Int)) = true := by
        intro s hs
        by_cases hj : j = 0
        · subst hj
          have := h s (by omega)
          simpa using this
        · have ih := black_shield m j (t + s) (fun s' hs' => by
            have := h (s + s') (by omega)
            rwa [show t + (s + s') = t + s + s' by omega] at this) j (by omega) (by omega)
          rw [show t + s + 9 * j = t + 9 * j + s by omega] at ih
          exact ih.2
      have hA := nine_black (t + 9 * j) (m + 2 * (j : Int)) hcol
      rw [show t + 9 * j + 9 = t + 9 * (j + 1) by omega,
        show m + 2 * (j : Int) + 1 = m + 2 * ((j + 1 : Nat) : Int) - 1 by omega,
        show m + 2 * (j : Int) + 2 = m + 2 * ((j + 1 : Nat) : Int) by omega] at hA
      exact hA

/-- Agreement in the shrinking cone of the right half, driven by column `0`. -/
theorem cone_agree (t0 t1 n : Nat) (hdrv : ∀ s, cell (t0 + s) 0 = cell (t1 + s) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ n → cell t0 p = cell t1 p) :
    ∀ s : Nat, ∀ p : Int, 1 ≤ p → p + s ≤ n → cell (t0 + s) p = cell (t1 + s) p
  | 0, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s + 1, p, h1, h2 => by
    show rule (cell (t0 + s) (p - 1)) (cell (t0 + s) p) (cell (t0 + s) (p + 1)) =
      rule (cell (t1 + s) (p - 1)) (cell (t1 + s) p) (cell (t1 + s) (p + 1))
    have hl : cell (t0 + s) (p - 1) = cell (t1 + s) (p - 1) := by
      by_cases hp : p = 1
      · rw [show p - 1 = 0 by omega]; exact hdrv s
      · exact cone_agree t0 t1 n hdrv hrow s (p - 1) (by omega) (by omega)
    rw [hl, cone_agree t0 t1 n hdrv hrow s p h1 (by omega),
      cone_agree t0 t1 n hdrv hrow s (p + 1) (by omega) (by omega)]

/-- During a white run of the center column, a black cell in column 1 stays black. -/
theorem black_stays (a n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false) (h1 : cell a 1 = true) :
    ∀ i, i ≤ n → cell (a + i) 1 = true
  | 0, _ => by simpa using h1
  | i + 1, hi => by
    have ih := black_stays a n hc h1 i (by omega)
    show rule (cell (a + i) (1 - 1)) (cell (a + i) 1) (cell (a + i) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, hc i (by omega), ih]
    rfl

/-! ### Long black runs, any column -/

/-- A white run of column `i` right after nine black cells: column `i + 1` is white at the first
white cell and black at the later ones. -/
theorem col_in_white_run' (i : Int) :
    ∀ k u, (∀ s, s < 9 → cell (u + s) i = true) → (∀ j, j ≤ k → cell (u + 9 + j) i = false) →
      cell (u + 9 + k) (i + 1) = decide (k ≠ 0) ∧ (k = 0 → cell (u + 9) (i + 1 + 1) = true) := by
  intro k
  induction k with
  | zero =>
    intro u h9s hz
    have h9 := nine_black u i h9s
    rw [show i + 2 = i + 1 + 1 by omega] at h9
    exact ⟨h9.1, fun _ => h9.2⟩
  | succ k ih =>
    intro u h9s hz
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have hk0 : cell (u + 9 + k) i = false := hz k (by omega)
    have hstep : cell (u + 9 + (k + 1)) (i + 1) =
        rule (cell (u + 9 + k) i) (cell (u + 9 + k) (i + 1)) (cell (u + 9 + k) (i + 1 + 1)) := by
      show rule (cell (u + 9 + k) (i + 1 - 1)) (cell (u + 9 + k) (i + 1))
        (cell (u + 9 + k) (i + 1 + 1)) = _
      rw [show i + 1 - 1 = i by omega]
    have ih' := ih u h9s (fun j hj => hz j (by omega))
    rw [hstep, hk0]
    cases k with
    | zero =>
      have e1 : cell (u + 9 + 0) (i + 1) = false := ih'.1
      have e2 : cell (u + 9) (i + 1 + 1) = true := ih'.2 rfl
      rw [e1, show u + 9 + 0 = u + 9 from rfl, e2]
      rfl
    | succ k =>
      rw [ih'.1]
      rfl

/-- Inside a white run of column `i` that starts right after nine black cells, column `i + 1` is
white at the first white cell and black at the later ones. -/
theorem col_in_white_run (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) i = false → cell (u + 8) i = true →
      ∀ s, s < 9 → cell (u + s) i = true) :
    ∀ k u, T ≤ u → cell (u + 8) i = true → (∀ j, j ≤ k → cell (u + 9 + j) i = false) →
      cell (u + 9 + k) (i + 1) = decide (k ≠ 0) ∧ (k = 0 → cell (u + 9) (i + 1 + 1) = true) :=
  fun k u hu h8 hz => col_in_white_run' i k u (hruns u hu (hz 0 (by omega)) h8) hz

/-- Trailing white cells: either the last `n + 1` values of `f` up to `t` are all white, or there
is a black cell right before a white run of length at most `n` that ends at `t`. -/
theorem trailing (f : Nat → Bool) (t : Nat) (h0 : f t = false) :
    ∀ n, (∀ j, j ≤ n → f (t - j) = false) ∨
      ∃ k, k < n ∧ f (t - (k + 1)) = true ∧ ∀ j, j ≤ k → f (t - j) = false := by
  intro n
  induction n with
  | zero => exact Or.inl fun j hj => by rw [show j = 0 by omega]; simpa using h0
  | succ n ih =>
    rcases ih with h | ⟨k, hk, h1, h2⟩
    · cases hf : f (t - (n + 1))
      · exact Or.inl fun j hj => by
          rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
          · exact h j (by omega)
          · rw [show j = n + 1 by omega]; exact hf
      · exact Or.inr ⟨n, by omega, hf, h⟩
    · exact Or.inr ⟨k, by omega, h1, h2⟩

/-- **Long black runs exclude periodicity, any column.** If from time `T` on every black run of
column `i` that is followed by a white cell has length at least `9`, then column `i` is not
eventually periodic. -/
theorem not_eventuallyPeriodic_of_long_one_runs_col (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) i = false → cell (u + 8) i = true →
      ∀ s, s < 9 → cell (u + s) i = true) :
    ¬ EventuallyPeriodic fun t => cell t i := by
  intro hc
  obtain ⟨T₀, P, hP, hper⟩ := hc
  have hper' : ∀ t, T₀ ≤ t → cell (t + P) i = cell t i := hper
  by_cases hw : ∃ t, T₀ ≤ t ∧ ∀ s, s < P → cell (t + s) i = false
  · -- a white period window: column `i` is eventually white
    obtain ⟨t, ht, hs⟩ := hw
    have hk : ∀ k s, s < P → cell (t + k * P + s) i = false := by
      intro k
      induction k with
      | zero => intro s hs'; simpa using hs s hs'
      | succ k ih =>
        intro s hs'
        rw [show t + (k + 1) * P + s = (t + k * P + s) + P by rw [Nat.succ_mul]; omega,
          hper' _ (by omega)]
        exact ih s hs'
    refine no_column_eventually_constant i ⟨t, false, fun u hu => ?_⟩
    have := hk ((u - t) / P) ((u - t) % P) (Nat.mod_lt _ hP)
    rwa [show t + (u - t) / P * P + (u - t) % P = u by
      have := Nat.div_add_mod (u - t) P; rw [Nat.mul_comm] at this; omega] at this
  · -- every period window after `T₀` contains a black cell
    have hblack : ∀ t, T₀ ≤ t → ∃ s, s < P ∧ cell (t + s) i = true := by
      intro t ht
      refine Classical.byContradiction fun hne => hw ⟨t, ht, fun s hs => ?_⟩
      cases h : cell (t + s) i
      · rfl
      · exact absurd ⟨s, hs, h⟩ hne
    let B := T + T₀ + P + 10
    have hform : ∀ t, B ≤ t → orCol i t = (cell t i || !cell (t - 1) i) := by
      intro t ht
      cases h0 : cell t i
      · rcases trailing (fun u => cell u i) t h0 P with hall | ⟨k, hk, h1, h2⟩
        · obtain ⟨s, hs, hb⟩ := hblack (t - P) (by omega)
          have := hall (P - s) (by omega)
          rw [show t - (P - s) = t - P + s by omega, hb] at this
          exact absurd this (by decide)
        · have hrun := col_in_white_run i hruns k (t - (k + 1) - 8) (by omega)
            (by rw [show t - (k + 1) - 8 + 8 = t - (k + 1) by omega]; exact h1)
            (fun j hj => by
              rw [show t - (k + 1) - 8 + 9 + j = t - (k - j) by omega]; exact h2 (k - j) (by omega))
          rw [show t - (k + 1) - 8 + 9 + k = t by omega] at hrun
          unfold orCol
          rw [h0, Bool.false_or, Bool.false_or, hrun.1]
          cases k with
          | zero =>
            have : cell (t - 1) i = true := by simpa using h1
            rw [this]; rfl
          | succ k =>
            have : cell (t - 1) i = false := by simpa using h2 1 (by omega)
            rw [this]; rfl
      · unfold orCol; rw [h0]; rfl
    refine orCol_not_eventuallyPeriodic i ⟨T₀, P, hP, hper⟩ ⟨B, P, hP, fun t ht => ?_⟩
    show orCol i (t + P) = orCol i t
    rw [hform t (by omega), hform (t + P) (by omega), hper' t (by omega),
      show t + P - 1 = (t - 1) + P by omega, hper' (t - 1) (by omega)]

/-- **Long black runs exclude periodicity of the center column.** If from some time on every
black run of the center column that is followed by a white cell has length at least `9`, the
center column is not eventually periodic. So an eventually periodic center column would contain
black runs of length `1, …, 8` followed by white infinitely often. -/
theorem not_eventuallyPeriodic_of_long_one_runs {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) 0 = false → cell (u + 8) 0 = true →
      ∀ s, s < 9 → cell (u + s) 0 = true) :
    ¬ EventuallyPeriodic fun t => cell t 0 :=
  not_eventuallyPeriodic_of_long_one_runs_col 0 hruns

/-- **Finitary long-runs theorem.** Let `n ≥ a + 2P + 10`. The center column cannot, on the whole
interval `[a, 2n]`, be `P`-periodic, have a black cell in every window of length `P`, and have
all its black runs that are followed by a white cell of length at least `9`. -/
theorem finitary_long_runs {P a n : Nat} (hP : 0 < P) (hn : a + 2 * P + 10 ≤ n)
    (hper : ∀ x, a ≤ x → x + P ≤ 2 * n → cell (x + P) 0 = cell x 0)
    (hblack : ∀ x, a ≤ x → x + P ≤ 2 * n → ∃ s, s < P ∧ cell (x + s) 0 = true)
    (hruns : ∀ u, a ≤ u → u + 9 ≤ 2 * n → cell (u + 9) 0 = false → cell (u + 8) 0 = true →
      ∀ s, s < 9 → cell (u + s) 0 = true) : False := by
  have hform : ∀ x, a + P + 10 ≤ x → x ≤ 2 * n → orCol 0 x = (cell x 0 || !cell (x - 1) 0) := by
    intro x hx1 hx2
    cases h0 : cell x 0
    · rcases trailing (fun u => cell u 0) x h0 P with hall | ⟨k, hk, h1, h2⟩
      · obtain ⟨s, hs, hb⟩ := hblack (x - P) (by omega) (by omega)
        have := hall (P - s) (by omega)
        rw [show x - (P - s) = x - P + s by omega, hb] at this
        exact absurd this (by decide)
      · have h9s := hruns (x - (k + 1) - 8) (by omega) (by omega)
          (by rw [show x - (k + 1) - 8 + 9 = x - k by omega]; exact h2 k (by omega))
          (by rw [show x - (k + 1) - 8 + 8 = x - (k + 1) by omega]; exact h1)
        have hrun := col_in_white_run' 0 k (x - (k + 1) - 8) h9s
          (fun j hj => by
            rw [show x - (k + 1) - 8 + 9 + j = x - (k - j) by omega]; exact h2 (k - j) (by omega))
        rw [show x - (k + 1) - 8 + 9 + k = x by omega] at hrun
        unfold orCol
        rw [h0, Bool.false_or, Bool.false_or, hrun.1]
        cases k with
        | zero =>
          have : cell (x - 1) 0 = true := by simpa using h1
          rw [this]; rfl
        | succ k =>
          have : cell (x - 1) 0 = false := by simpa using h2 1 (by omega)
          rw [this]; rfl
    · unfold orCol; rw [h0]; rfl
  refine window_jen (t₁ := n - P) (t₂ := n) (by omega) (fun s hs => ?_) (fun s hs => ?_)
  · have := hper (n - P + s) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · rw [hform (n - P + s) (by omega) (by omega), hform (n + s) (by omega) (by omega)]
    have e1 := hper (n - P + s) (by omega) (by omega)
    have e2 := hper (n - P + s - 1) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at e1
    rw [show n - P + s - 1 + P = n + s - 1 by omega] at e2
    rw [e1, e2]

/-- **The words `0 1^k`, `k ≥ 9`, are excluded**: the center column is not eventually equal to
`0 1^k` repeated, whatever the transient. -/
theorem not_eventually_zero_ones (k : Nat) (hk : 9 ≤ k) (T : Nat) :
    ¬ ∀ t, T ≤ t → cell t 0 = decide ((t - T) % (k + 1) ≠ 0) := by
  intro h
  refine not_eventuallyPeriodic_of_long_one_runs (T := T) (fun u hu h9 _ s hs => ?_)
    ⟨T, k + 1, by omega, fun t ht => ?_⟩
  · -- `u + 9 - T` is a multiple of `k + 1`, so `u + s - T` is not
    rw [h (u + 9) (by omega)] at h9
    have hz : (u + 9 - T) % (k + 1) = 0 := by simpa using h9
    rw [h (u + s) (by omega)]
    simp only [decide_eq_true_eq]
    intro hm
    have e1 := Nat.div_add_mod (u + 9 - T) (k + 1)
    have e2 := Nat.div_add_mod (u + s - T) (k + 1)
    rw [hz] at e1
    rw [hm] at e2
    have hlt : (u + s - T) / (k + 1) < (u + 9 - T) / (k + 1) :=
      Nat.lt_of_mul_lt_mul_left (a := k + 1) (by omega)
    have hle := Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt hlt)
    rw [Nat.mul_succ] at hle
    omega
  · show cell (t + (k + 1)) 0 = cell t 0
    rw [h (t + (k + 1)) (by omega), h t ht, show t + (k + 1) - T = (t - T) + (k + 1) by omega,
      Nat.add_mod_right]

/-! ### Theorem B: a long black run inside the period -/

/-- **Theorem B.** If the center column is periodic with period `P` from time `T` on, no period
contains a black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r`. -/
theorem no_long_black_run (T P r t1 : Nat) (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (ht1 : T ≤ t1) (hr : r ≤ P) (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hlong : 9 * ((P - r + 10) / 2) ≤ r) : False := by
  have hP : 0 < P := by omega
  -- j = ⌈(P - r + 9) / 2⌉
  have hj1 : P - r + 9 ≤ 2 * ((P - r + 10) / 2) := by omega
  generalize hjdef : (P - r + 10) / 2 = j at hj1 hlong
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := periodic_mul hper
  have hblack : ∀ k s, s < r → cell (t1 + k * P + s) 0 = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    show center (t1 + k * P + s) = true
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  -- the row right after each black run reads (white black)^j on columns 1..2j
  have hrowk : ∀ k i, 1 ≤ i → i ≤ j →
      cell (t1 + r + k * P) (2 * (i : Int) - 1) = false ∧
        cell (t1 + r + k * P) (2 * (i : Int)) = true := by
    intro k i hi1 hij
    have := black_shield 0 j (t1 + k * P + (r - 9 * j)) (fun s hs => by
        have := hblack k (r - 9 * j + s) (by omega)
        rwa [show t1 + k * P + (r - 9 * j + s) = t1 + k * P + (r - 9 * j) + s by omega] at this)
      i hi1 hij
    rw [show t1 + k * P + (r - 9 * j) + 9 * j = t1 + r + k * P by omega] at this
    simpa using this
  have hrowagree : ∀ k, ∀ p : Int, 1 ≤ p → p ≤ (2 * j : Nat) →
      cell (t1 + r) p = cell (t1 + r + k * P) p := by
    intro k p hp1 hp2
    have a0 := hrowk 0
    simp only [Nat.zero_mul, Nat.add_zero] at a0
    by_cases hpar : p % 2 = 0
    · have hi : p = 2 * (((p / 2).toNat : Nat) : Int) := by omega
      rw [hi, (a0 _ (by omega) (by omega)).2, (hrowk k _ (by omega) (by omega)).2]
    · have hi : p = 2 * ((((p + 1) / 2).toNat : Nat) : Int) - 1 := by omega
      rw [hi, (a0 _ (by omega) (by omega)).1, (hrowk k _ (by omega) (by omega)).1]
  have hdrv : ∀ k s, cell (t1 + r + s) 0 = cell (t1 + r + k * P + s) 0 := by
    intro k s
    have := hperk k (t1 + r + s) (by omega)
    show center (t1 + r + s) = center (t1 + r + k * P + s)
    rw [show t1 + r + k * P + s = t1 + r + s + k * P by omega, this]
  -- column 1 is white 9 steps into a black run
  have white1 : ∀ t', (∀ s', s' < 9 → cell (t' + s') 0 = true) → cell (t' + 9) 1 = false := by
    intro t' h
    have := (nine_black t' 0 h).1
    simpa using this
  have hcol : ∀ k s, s < P → cell (t1 + r + s) 1 = cell (t1 + r + k * P + s) 1 := by
    intro k s hs
    by_cases hs1 : s + 1 ≤ 2 * j
    · exact cone_agree (t1 + r) (t1 + r + k * P) (2 * j) (hdrv k) (hrowagree k) s 1 (by omega)
        (by omega)
    · have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have a : cell (t1 + r + s) 1 = false := by
        have := white1 (t1 + r + s - 9) (fun s' hs' => by
          have := hblack 1 (s - 9 + s' - (P - r)) (by omega)
          rwa [show t1 + 1 * P + (s - 9 + s' - (P - r)) = t1 + r + s - 9 + s' by omega] at this)
        rwa [show t1 + r + s - 9 + 9 = t1 + r + s by omega] at this
      have b : cell (t1 + r + k * P + s) 1 = false := by
        have := white1 (t1 + r + k * P + s - 9) (fun s' hs' => by
          have := hblack (k + 1) (s - 9 + s' - (P - r)) (by omega)
          rwa [hPk, show t1 + (k * P + P) + (s - 9 + s' - (P - r)) =
            t1 + r + k * P + s - 9 + s' by omega] at this)
        rwa [show t1 + r + k * P + s - 9 + 9 = t1 + r + k * P + s by omega] at this
      rw [a, b]
  -- column 1 is eventually periodic, contradicting Jen's theorem
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t1 + r, P, hP, fun t ht => ?_⟩
    show cell (t + P) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - (t1 + r)) P
    generalize (t - (t1 + r)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + r)) hP
    generalize (t - (t1 + r)) % P = s at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have e1 := hcol q s hmod
    have e2 := hcol (q + 1) s hmod
    rw [hq1] at e2
    have hcomm : P * q = q * P := Nat.mul_comm P q
    rw [show t + P = t1 + r + (q * P + P) + s by omega, ← e2, e1,
      show t1 + r + q * P + s = t by omega]
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, P, hP, hper⟩
  exact not_adjacent 0 h0 h1

/-! ### Theorem D: a black run of length `≥ 9` followed by a long white run -/

/-- **Theorem D.** If the center column is periodic with period `P` from `T` on, a period cannot
contain a black run of length `s ≥ 9` immediately followed by a white run of length `r` with
`r ≥ 1 + 9 ⌈(k + 8) / 2⌉`, where `k = P - s - r` is the length of the rest of the period. -/
theorem no_black_white_run (T P s r t1 : Nat) (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (ht1 : T ≤ t1) (hs : 9 ≤ s) (hsr : s + r ≤ P)
    (hblk : ∀ i, i < s → center (t1 + i) = true)
    (hwht : ∀ i, i < r → center (t1 + s + i) = false)
    (hlong : 1 + 9 * ((P - s - r + 9) / 2) ≤ r) : False := by
  have hP : 0 < P := by omega
  have hj1 : P - s - r + 8 ≤ 2 * ((P - s - r + 9) / 2) := by omega
  generalize hjdef : (P - s - r + 9) / 2 = j at hj1 hlong
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := periodic_mul hper
  have hMul : ∀ k, (k + 1) * P = k * P + P := fun k => Nat.succ_mul k P
  have cblk : ∀ k i, i < s → cell (t1 + k * P + i) 0 = true := by
    intro k i hi
    have := hperk k (t1 + i) (by omega)
    show center (t1 + k * P + i) = true
    rw [show t1 + k * P + i = t1 + i + k * P by omega, this]; exact hblk i hi
  have cwht : ∀ k i, i < r → cell (t1 + s + k * P + i) 0 = false := by
    intro k i hi
    have := hperk k (t1 + s + i) (by omega)
    show center (t1 + s + k * P + i) = false
    rw [show t1 + s + k * P + i = t1 + s + i + k * P by omega, this]; exact hwht i hi
  -- start of the white run of period k: column 1 white, column 2 black (Lemma A)
  have hstart : ∀ k, cell (t1 + s + k * P) 1 = false ∧ cell (t1 + s + k * P) 2 = true := by
    intro k
    have := nine_black (t1 + k * P + (s - 9)) 0 (fun i hi => by
      have := cblk k (s - 9 + i) (by omega)
      rwa [show t1 + k * P + (s - 9 + i) = t1 + k * P + (s - 9) + i by omega] at this)
    rw [show t1 + k * P + (s - 9) + 9 = t1 + s + k * P by omega] at this
    simpa using this
  -- column 1 is black during the rest of the white run
  have hrun1 : ∀ k i, 1 ≤ i → i ≤ r → cell (t1 + s + k * P + i) 1 = true := by
    intro k i hi1 hir
    have c1 : cell (t1 + s + k * P + 1) 1 = true := by
      show rule (cell (t1 + s + k * P) (1 - 1)) (cell (t1 + s + k * P) 1)
        (cell (t1 + s + k * P) (1 + 1)) = true
      have h0 := cwht k 0 (by omega)
      rw [show t1 + s + k * P + 0 = t1 + s + k * P by omega] at h0
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, h0, (hstart k).1,
        (hstart k).2]
      rfl
    have := black_stays (t1 + s + k * P + 1) (r - 1) (fun i' hi' => by
      have := cwht k (1 + i') (by omega)
      rwa [show t1 + s + k * P + (1 + i') = t1 + s + k * P + 1 + i' by omega] at this) c1
      (i - 1) (by omega)
    rwa [show t1 + s + k * P + 1 + (i - 1) = t1 + s + k * P + i by omega] at this
  -- at the end of the white run: column 1 black, columns 2..2j+1 read (white black)^j
  have hend : ∀ k i, 1 ≤ i → i ≤ j →
      cell (t1 + s + r + k * P) (1 + 2 * (i : Int) - 1) = false ∧
        cell (t1 + s + r + k * P) (1 + 2 * (i : Int)) = true := by
    intro k i hi1 hij
    have := black_shield 1 j (t1 + s + k * P + (r - 9 * j)) (fun i' hi' => by
        have := hrun1 k (r - 9 * j + i') (by omega) (by omega)
        rwa [show t1 + s + k * P + (r - 9 * j + i') = t1 + s + k * P + (r - 9 * j) + i' by omega]
          at this) i hi1 hij
    rwa [show t1 + s + k * P + (r - 9 * j) + 9 * j = t1 + s + r + k * P by omega] at this
  have hrowagree : ∀ k, ∀ p : Int, 1 ≤ p → p ≤ ((2 * j + 1 : Nat) : Int) →
      cell (t1 + s + r) p = cell (t1 + s + r + k * P) p := by
    intro k p hp1 hp2
    by_cases hp : p = 1
    · subst hp
      have a := hrun1 0 r (by omega) (Nat.le_refl r)
      have b := hrun1 k r (by omega) (Nat.le_refl r)
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [show t1 + s + k * P + r = t1 + s + r + k * P by omega] at b
      rw [a, b]
    have a0 := hend 0
    simp only [Nat.zero_mul, Nat.add_zero] at a0
    by_cases hpar : p % 2 = 0
    · have hi : p = 1 + 2 * ((((p) / 2).toNat : Nat) : Int) - 1 := by omega
      rw [hi, (a0 _ (by omega) (by omega)).1, (hend k _ (by omega) (by omega)).1]
    · have hi : p = 1 + 2 * ((((p - 1) / 2).toNat : Nat) : Int) := by omega
      rw [hi, (a0 _ (by omega) (by omega)).2, (hend k _ (by omega) (by omega)).2]
  have hdrv : ∀ k s', cell (t1 + s + r + s') 0 = cell (t1 + s + r + k * P + s') 0 := by
    intro k s'
    have := hperk k (t1 + s + r + s') (by omega)
    show center (t1 + s + r + s') = center (t1 + s + r + k * P + s')
    rw [show t1 + s + r + k * P + s' = t1 + s + r + s' + k * P by omega, this]
  have white1 : ∀ t', (∀ s', s' < 9 → cell (t' + s') 0 = true) → cell (t' + 9) 1 = false := by
    intro t' h
    have := (nine_black t' 0 h).1
    simpa using this
  -- column 1 over one period starting at the white run: independent of the period index
  have hcol : ∀ k i, i < P → cell (t1 + s + i) 1 = cell (t1 + s + k * P + i) 1 := by
    intro k i hi
    by_cases hi0 : i = 0
    · subst hi0
      have a := (hstart 0).1
      simp only [Nat.zero_mul, Nat.add_zero] at a
      simp only [Nat.add_zero]
      rw [a, (hstart k).1]
    by_cases hir : i ≤ r
    · have a := hrun1 0 i (by omega) hir
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [a, hrun1 k i (by omega) hir]
    by_cases hic : i ≤ r + 2 * j
    · have := cone_agree (t1 + s + r) (t1 + s + r + k * P) (2 * j + 1) (hdrv k) (hrowagree k)
        (i - r) 1 (by omega) (by omega)
      rwa [show t1 + s + r + (i - r) = t1 + s + i by omega,
        show t1 + s + r + k * P + (i - r) = t1 + s + k * P + i by omega] at this
    · -- at least nine steps into the next black run
      have wk : ∀ k', cell (t1 + s + k' * P + i) 1 = false := by
        intro k'
        have := white1 (t1 + s + k' * P + i - 9) (fun s' hs' => by
          have := cblk (k' + 1) (s + i - 9 + s' - P) (by omega)
          rwa [hMul k', show t1 + (k' * P + P) + (s + i - 9 + s' - P) =
            t1 + s + k' * P + i - 9 + s' by omega] at this)
        rwa [show t1 + s + k' * P + i - 9 + 9 = t1 + s + k' * P + i by omega] at this
      have w0 := wk 0
      simp only [Nat.zero_mul, Nat.add_zero] at w0
      rw [w0, wk k]
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t1 + s, P, hP, fun t ht => ?_⟩
    show cell (t + P) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - (t1 + s)) P
    generalize (t - (t1 + s)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + s)) hP
    generalize (t - (t1 + s)) % P = i at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have hcomm : P * q = q * P := Nat.mul_comm P q
    have e1 := hcol q i hmod
    have e2 := hcol (q + 1) i hmod
    rw [hq1] at e2
    rw [show t + P = t1 + s + (q * P + P) + i by omega, ← e2, e1,
      show t1 + s + q * P + i = t by omega]
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, P, hP, hper⟩
  exact not_adjacent 0 h0 h1

/-! ### The words `0^r 1 1`, `r ≥ 10` -/

/-- The right edge: the rightmost black cell is at `t`. -/
theorem cell_right_edge (t : Nat) : cell t (t : Int) = true :=
  (Rule30Diagonals.cell_congr (by omega)).trans (Rule30Diagonals.R_zero t)

/-- The first black cell to the right of the center exists at every time `t ≥ 1`. -/
theorem first_black_aux (t : Nat) : ∀ n : Nat, (∀ p : Nat, 1 ≤ p → p ≤ n → cell t p = false) ∨
    ∃ ℓ, ℓ < n ∧ (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell t p = false) ∧ cell t ((ℓ + 1 : Nat) : Int) = true
  | 0 => Or.inl (fun p h1 h2 => by omega)
  | n + 1 => by
    rcases first_black_aux t n with hw | ⟨ℓ, hℓ, hw, hb⟩
    · by_cases hc : cell t ((n + 1 : Nat) : Int) = true
      · exact Or.inr ⟨n, by omega, hw, hc⟩
      · refine Or.inl (fun p h1 h2 => ?_)
        by_cases hp : p ≤ n
        · exact hw p h1 hp
        · have : p = n + 1 := by omega
          subst this
          simpa using hc
    · exact Or.inr ⟨ℓ, by omega, hw, hb⟩

theorem first_black (t : Nat) (ht : 1 ≤ t) :
    ∃ ℓ, (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell t p = false) ∧ cell t ((ℓ + 1 : Nat) : Int) = true := by
  rcases first_black_aux t t with hw | ⟨ℓ, _, hw, hb⟩
  · have := hw t ht (Nat.le_refl t)
    rw [cell_right_edge] at this
    exact absurd this (by decide)
  · exact ⟨ℓ, hw, hb⟩

/-- During a white run, the first black cell right of the center moves one column left per
step. -/
theorem front_moves (a ℓ n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    ∀ i, i ≤ n → i ≤ ℓ →
      (∀ p : Nat, 1 ≤ p → p ≤ ℓ - i → cell (a + i) p = false) ∧
        cell (a + i) ((ℓ - i + 1 : Nat) : Int) = true
  | 0, _, _ => ⟨fun p h1 h2 => by simpa using hw p h1 (by omega), by simpa using hb⟩
  | i + 1, hin, hil => by
    obtain ⟨ihw, ihb⟩ := front_moves a ℓ n hc hw hb i (by omega) (by omega)
    -- white in columns 0..ℓ-i at time a+i (column 0: the center)
    have wh : ∀ q : Int, 0 ≤ q → q ≤ ((ℓ - i : Nat) : Int) → cell (a + i) q = false := by
      intro q hq0 hq1
      by_cases hq : q = 0
      · subst hq; exact hc i (by omega)
      · have := ihw q.toNat (by omega) (by omega)
        rwa [show ((q.toNat : Nat) : Int) = q by omega] at this
    refine ⟨fun p h1 h2 => ?_, ?_⟩
    · show rule (cell (a + i) ((p : Int) - 1)) (cell (a + i) (p : Int))
        (cell (a + i) ((p : Int) + 1)) = false
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega), wh _ (by omega) (by omega)]
      rfl
    · show rule (cell (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) - 1))
        (cell (a + i) ((ℓ - (i + 1) + 1 : Nat) : Int))
        (cell (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) + 1)) = true
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega),
        show ((ℓ - (i + 1) + 1 : Nat) : Int) + 1 = ((ℓ - i + 1 : Nat) : Int) by omega, ihb]
      rfl

section Period
variable (a r : Nat)
  (hwr : ∀ i, i < r → cell (a + i) 0 = false)
  (hb1 : cell (a + r) 0 = true) (hb2 : cell (a + r + 1) 0 = true)
include hwr hb1 hb2

/-- One period of `0^r 1 1` whose first black cell is at column `ℓ + 1 ≤ r - 7`: the next period
starts with a black cell in column 1. -/
theorem period_lock (hr : 8 ≤ r) (ℓ : Nat) (hℓ : ℓ ≤ r - 8)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    (∀ i, ℓ ≤ i → i ≤ r → cell (a + i) 1 = true) ∧ cell (a + r + 1) 1 = false ∧
      cell (a + r + 2) 1 = true := by
  have hfront := (front_moves a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hblk : ∀ i, ℓ ≤ i → i ≤ r → cell (a + i) 1 = true := by
    intro i h1 h2
    have := black_stays (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (i - ℓ) (by omega)
    rwa [show a + ℓ + (i - ℓ) = a + i by omega] at this
  have hA := (nine_black (a + (r - 8)) 1 (fun s hs => by
    have := hblk (r - 8 + s) (by omega) (by omega)
    rwa [show a + (r - 8 + s) = a + (r - 8) + s by omega] at this)).1
  rw [show a + (r - 8) + 9 = a + r + 1 by omega, show (1 : Int) + 1 = 2 by rfl] at hA
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hblk r (by omega) (Nat.le_refl r)]
    rfl
  refine ⟨hblk, c1, ?_⟩
  show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = true
  rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, hA]
  rfl

/-- First black cell at column `ℓ + 1 ∈ [r - 6, r + 1]`: the next period's first black cell is in
column 1 or 2. -/
theorem period_late (ℓ : Nat) (hℓ : ℓ ≤ r)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = true ∨ (cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true) := by
  have hfront := (front_moves a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hr1 : cell (a + r) 1 = true := by
    have := black_stays (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (r - ℓ) (Nat.le_refl _)
    rwa [show a + ℓ + (r - ℓ) = a + r by omega] at this
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hr1]
    rfl
  cases h2 : cell (a + r + 1) 2
  · left
    show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
    rfl
  · right
    constructor
    · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
      rfl
    · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
      rw [show (2 : Int) - 1 = 1 by rfl, c1, h2]
      rfl

omit hb1 hb2 in
/-- The configuration at time `a + r` when the first black cell started at column `r + z + 1`. -/
theorem period_far (z : Nat) (hz : 1 ≤ z)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → cell a p = false)
    (hb : cell a ((r + z + 1 : Nat) : Int) = true) :
    (∀ p : Nat, 1 ≤ p → p ≤ z → cell (a + r) p = false) ∧
      cell (a + r) ((z + 1 : Nat) : Int) = true := by
  have := front_moves a (r + z) r hwr hw hb r (Nat.le_refl r) (by omega)
  rw [show r + z - r = z by omega] at this
  exact this

theorem period_z1 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 1 → cell a p = false)
    (hb : cell a ((r + 1 + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true := by
  obtain ⟨fw, fb⟩ := period_far a r hwr 1 (Nat.le_refl 1) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (Nat.le_refl 1) (Nat.le_refl 1)
  have b2 : cell (a + r) 2 = true := by simpa using fb
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, b2]; rfl
  have c2 : cell (a + r + 1) 2 = true := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, w1, b2]; rfl
  constructor
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, c1, c2]; rfl

omit hb2 in
theorem period_z2 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell a p = false)
    (hb : cell a ((r + 2 + 1 : Nat) : Int) = true) :
    (∀ i, i ≤ r → cell (a + i) 1 = false) ∧ cell (a + r + 1) 1 = true := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have := (front_moves a (r + 2) r hwr hw hb i hi (by omega)).1 1 (Nat.le_refl 1) (by omega)
    simpa using this
  · obtain ⟨fw, _⟩ := period_far a r hwr 2 (by omega) hw hb
    have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
    have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl

theorem period_z3 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 3 → cell a p = false)
    (hb : cell a ((r + 3 + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = false ∧ cell (a + r + 2) 3 = true := by
  obtain ⟨fw, fb⟩ := period_far a r hwr 3 (by omega) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : cell (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have b4 : cell (a + r) 4 = true := by simpa using fb
  have c1 : cell (a + r + 1) 1 = true := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : cell (a + r + 1) 2 = false := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : cell (a + r + 1) 3 = true := by
    show rule (cell (a + r) (3 - 1)) (cell (a + r) 3) (cell (a + r) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, b4]; rfl
  refine ⟨?_, ?_, ?_⟩
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl
  · show rule (cell (a + r + 1) (3 - 1)) (cell (a + r + 1) 3) (cell (a + r + 1) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, c2, c3]; rfl

theorem period_z4 (z : Nat) (hz : 4 ≤ z) (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → cell a p = false)
    (hb : cell a ((r + z + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true := by
  obtain ⟨fw, _⟩ := period_far a r hwr z (by omega) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : cell (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have w4 : cell (a + r) 4 = false := by simpa using fw 4 (by omega) (by omega)
  have c1 : cell (a + r + 1) 1 = true := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : cell (a + r + 1) 2 = false := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : cell (a + r + 1) 3 = false := by
    show rule (cell (a + r) (3 - 1)) (cell (a + r) 3) (cell (a + r) (3 + 1)) = false
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, w4]; rfl
  constructor
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl

end Period

/-- Column 1 is eventually periodic if it repeats a fixed block from some time on. -/
theorem periodic_blocks (B Q : Nat) (hQ : 0 < Q) (g : Nat → Bool)
    (h : ∀ j i, i < Q → cell (B + j * Q + i) 1 = g i) :
    EventuallyPeriodic (fun t => cell t (0 + 1)) := by
  refine ⟨B, Q, hQ, fun t ht => ?_⟩
  show cell (t + Q) (0 + 1) = cell t (0 + 1)
  rw [show (0 : Int) + 1 = 1 by rfl]
  have hdm := Nat.div_add_mod (t - B) Q
  generalize (t - B) / Q = q at hdm
  have hmod := Nat.mod_lt (t - B) hQ
  generalize (t - B) % Q = s at hdm hmod
  have hq1 : (q + 1) * Q = q * Q + Q := Nat.succ_mul q Q
  have hcomm : Q * q = q * Q := Nat.mul_comm Q q
  have e1 := h q s hmod
  have e2 := h (q + 1) s hmod
  rw [hq1] at e2
  rw [show t + Q = B + (q * Q + Q) + s by omega, e2, ← e1, show B + q * Q + s = t by omega]

/-- **The words `0^r 1 1`, `r ≥ 10`, are excluded**: the center column of rule 30 is not
eventually periodic with repeating word `0^r 1 1`, whatever the transient. -/
theorem no_white_run_11 (T r t0 : Nat) (hr : 10 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < r → center (t0 + i) = false) (hb1 : center (t0 + r) = true)
    (hb2 : center (t0 + r + 1) = true) : False := by
  generalize hQdef : r + 2 = Q at hper
  have hQ : 0 < Q := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * Q) = center t := periodic_mul hper
  -- start one period later so that the start time is ≥ 1
  generalize hAdef : t0 + Q = A
  have hMul : ∀ k, (k + 1) * Q = k * Q + Q := fun k => Nat.succ_mul k Q
  have drvw : ∀ k i, i < r → cell (A + k * Q + i) 0 = false := by
    intro k i hi
    have := hperk (k + 1) (t0 + i) (by omega)
    show center (A + k * Q + i) = false
    rw [hMul k, show t0 + i + (k * Q + Q) = A + k * Q + i by omega] at this
    rw [this]; exact hw i hi
  have drvb1 : ∀ k, cell (A + k * Q + r) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r) (by omega)
    show center (A + k * Q + r) = true
    rw [hMul k, show t0 + r + (k * Q + Q) = A + k * Q + r by omega] at this
    rw [this]; exact hb1
  have drvb2 : ∀ k, cell (A + k * Q + r + 1) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r + 1) (by omega)
    show center (A + k * Q + r + 1) = true
    rw [hMul k, show t0 + r + 1 + (k * Q + Q) = A + k * Q + r + 1 by omega] at this
    rw [this]; exact hb2
  have hnext : ∀ k, A + k * Q + r + 2 = A + (k + 1) * Q := by intro k; rw [hMul k]; omega
  -- a first black cell at column ℓ + 1 ≤ r - 7 locks the next period
  have early : ∀ k ℓ, ℓ ≤ r - 8 → (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell (A + k * Q) p = false) →
      cell (A + k * Q) ((ℓ + 1 : Nat) : Int) = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k ℓ hℓ hwℓ hbℓ
    have := (period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (by omega) ℓ hℓ hwℓ hbℓ).2.2
    rwa [hnext k] at this
  have lock_step : ∀ k, cell (A + k * Q) 1 = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k hk
    exact early k 0 (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
  have lock_all : ∀ k, cell (A + k * Q) 1 = true → ∀ j, cell (A + (k + j) * Q) 1 = true := by
    intro k hk j
    induction j with
    | zero => simpa using hk
    | succ j ih => rw [show k + (j + 1) = (k + j) + 1 by omega]; exact lock_step _ ih
  -- the exceptional case: first black cell exactly at column r + 3
  let Z2 : Nat → Prop := fun k => (∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell (A + k * Q) p = false) ∧
    cell (A + k * Q) ((r + 2 + 1 : Nat) : Int) = true
  have two_lock : ∀ k, ¬ Z2 k → cell (A + (k + 2) * Q) 1 = true := by
    intro k hz
    have hA1 : 1 ≤ A + k * Q := by omega
    obtain ⟨ℓ, hwℓ, hbℓ⟩ := first_black (A + k * Q) hA1
    have via1 : cell (A + (k + 1) * Q) 1 = false → cell (A + (k + 1) * Q) 2 = true →
        cell (A + (k + 2) * Q) 1 = true := by
      intro h1 h2
      have := early (k + 1) 1 (by omega) (fun p hp1 hp2 => by
        have : p = 1 := by omega
        subst this; simpa using h1) (by simpa using h2)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c1 : ℓ ≤ r - 8
    · have := lock_step _ (early k ℓ c1 hwℓ hbℓ)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c2 : ℓ ≤ r
    · rcases period_late (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) ℓ c2 hwℓ hbℓ with h | ⟨h1, h2⟩
      · rw [hnext k] at h
        have := lock_step _ h
        rwa [show k + 1 + 1 = k + 2 by omega] at this
      · rw [hnext k] at h1 h2
        exact via1 h1 h2
    by_cases c3 : ℓ = r + 1
    · subst c3
      obtain ⟨h1, h2⟩ := period_z1 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2
      exact via1 h1 h2
    by_cases c4 : ℓ = r + 2
    · subst c4
      exact absurd ⟨hwℓ, hbℓ⟩ hz
    by_cases c5 : ℓ = r + 3
    · subst c5
      obtain ⟨h1, h2, h3⟩ := period_z3 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2 h3
      have := early (k + 1) 2 (by omega) (fun p hp1 hp2 => by
        by_cases hp : p = 1
        · subst hp; simpa using h1
        · have : p = 2 := by omega
          subst this; simpa using h2) (by simpa using h3)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    · have hz4 : 4 ≤ ℓ - r := by omega
      obtain ⟨h1, h2⟩ := period_z4 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (ℓ - r) hz4
        (fun p hp1 hp2 => hwℓ p hp1 (by omega))
        (by rw [show r + (ℓ - r) + 1 = ℓ + 1 by omega]; exact hbℓ)
      rw [hnext k] at h1 h2
      exact via1 h1 h2
  -- column 1 over one period, in the lock and in the exceptional case
  have lock_pattern : ∀ k, cell (A + k * Q) 1 = true → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (i ≤ r) := by
    intro k hk i hi
    obtain ⟨hblk, c1, _⟩ := period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (by omega) 0
      (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp [hir]
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have z2_pattern : ∀ k, Z2 k → ∀ i, i < Q → cell (A + k * Q + i) 1 = decide (i = r + 1) := by
    intro k hk i hi
    obtain ⟨hw0, c1⟩ := period_z2 (A + k * Q) r (drvw k) (drvb1 k) hk.1 hk.2
    by_cases hir : i ≤ r
    · rw [hw0 i hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    by_cases hall : ∀ k, Z2 k
    · exact periodic_blocks A Q hQ (fun i => decide (i = r + 1))
        (fun j i hi => z2_pattern j (hall j) i hi)
    · have hex : ∃ k, ¬ Z2 k := Classical.byContradiction fun hne => hall fun k =>
        Classical.byContradiction fun hk => hne ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hex
      have hlock := two_lock k hk
      refine periodic_blocks (A + (k + 2) * Q) Q hQ (fun i => decide (i ≤ r)) (fun j i hi => ?_)
      have := lock_pattern (k + 2 + j) (lock_all (k + 2) hlock j) i hi
      have hm : (k + 2 + j) * Q = (k + 2) * Q + j * Q := Nat.add_mul (k + 2) j Q
      rwa [hm, show A + ((k + 2) * Q + j * Q) + i = A + (k + 2) * Q + j * Q + i by omega] at this
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, Q, hQ, hper⟩
  exact not_adjacent 0 h0 h1

end Rule30BlackRuns
end Ruliology.CellularAutomata
