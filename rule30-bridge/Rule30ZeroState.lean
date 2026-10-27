module

public import Ruliology.CellularAutomata.Rule30FiniteDiagonals
public import Ruliology.CellularAutomata.Rule30Window

/-!
# The zero-state of rule 30

Read the pattern along its left diagonals, `Ld x lo j t = evol x t (lo - t + j)`. Each diagonal is
fed by the two before it (`Ld_step`), and the feed has two regimes:

* `Ld_reset`: if diagonal `j + 1` is black at `t`, diagonal `j + 2` at `t + 1` is the complement of
  diagonal `j` at `t`; its own past is forgotten.
* `Ld_toggle`: if diagonal `j + 1` is white at `t`, diagonal `j + 2` adds diagonal `j` to its state.

Consequences proved here.

* `rigid`: if two configurations agree eventually on diagonals `j` and `j + 1`, and diagonal
  `j + 1` is black infinitely often, they agree eventually on diagonal `j + 2`.
* `universal`: two configurations, each white left of a black cell, agree eventually on every
  left diagonal up to the first one that is eventually white. The eventual left half is fixed by
  the rule, not by the configuration: this is the zero-state.
* `zero_diag_xor_const`: after an eventually white diagonal the two eventual diagonals differ by a
  constant. One bit of freedom per zero diagonal.
* `toggle_shift`: behind an eventually white diagonal the next one accumulates its input, so a
  period-`L` input of odd weight gives the antiperiod `L` (period doubling).
* `agree_persists`: agreement below a depth persists, so the damage edge between two orbits
  never moves back.
* `entry_iff`: for the single seed, if the left half agrees with a solution `Z` of the diagonal
  recurrence below depth `t` at time `t`, it agrees at depth `t` at time `t + 1` exactly when the
  center agrees with `Z` or the cell of `Z` at column `-1` is black. Damage enters only where the
  zero-state is transparent.
* `D_eq_pat` (kernel certificate): for the single seed, from time `501` on, every left diagonal of
  depth `≤ 401` equals a fixed period-`16` table. Hence `zero_diagonals` (depths 2, 7, 28, 399 are
  eventually white), `antiperiods` (depths 3, 8, 29, 400 have antiperiods 1, 2, 4, 8, so eventual
  periods exactly 2, 4, 8, 16) and `period_eight_below` (every depth `< 400` has period dividing 8).
-/

@[expose] public section

namespace Rule30ZeroState

open Ruliology.CellularAutomata
open Rule30Jen Rule30Diagonals Rule30FiniteDiagonals Rule30Realization

/-! ### One-bit recurrences -/

/-- Induction from a starting index. -/
theorem le_induction {T : Nat} {P : (t : Nat) → T ≤ t → Prop} (base : P T (Nat.le_refl T))
    (succ : ∀ t (h : T ≤ t), P t h → P (t + 1) (Nat.le_succ_of_le h)) : ∀ t (h : T ≤ t), P t h := by
  intro t h
  induction h with
  | refl => exact base
  | step h ih => exact succ _ h ih

/-- Two runs of one one-bit recurrence agree from the step after a time where the transition
forgets its state. -/
theorem agree_after_reset {x y : Nat → Bool} {F : Nat → Bool → Bool} {T s : Nat}
    (hx : ∀ t, T ≤ t → x (t + 1) = F t (x t)) (hy : ∀ t, T ≤ t → y (t + 1) = F t (y t))
    (hs : T ≤ s) (hc : F s true = F s false) : ∀ t, s < t → x t = y t := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rw [hx t (by omega), hy t (by omega)]
    rcases Nat.lt_or_ge s t with h | h
    · rw [ih h]
    · have e : t = s := by omega
      subst e
      cases x t <;> cases y t <;> simp [hc]

/-- A state that accumulates a periodic input changes by the same amount over every period. -/
theorem toggle_shift {x g : Nat → Bool} {T L : Nat} (hx : ∀ t, T ≤ t → x (t + 1) = xor (g t) (x t))
    (hg : ∀ t, T ≤ t → g (t + L) = g t) :
    ∀ t, T ≤ t → xor (x (t + L)) (x t) = xor (x (T + L)) (x T) := by
  intro t ht
  induction t, ht using le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L) (by omega), hx t ht, hg t ht, ← ih]
    cases g t <;> cases x (t + L) <;> cases x t <;> rfl

/-! ### The two regimes of a left diagonal -/

theorem Ld_reset (x : Int → Bool) (lo : Int) (j t : Nat) (h : Ld x lo (j + 1) t = true) :
    Ld x lo (j + 2) (t + 1) = !Ld x lo j t := by
  rw [Ld_step, h]; cases Ld x lo j t <;> rfl

theorem Ld_toggle (x : Int → Bool) (lo : Int) (j t : Nat) (h : Ld x lo (j + 1) t = false) :
    Ld x lo (j + 2) (t + 1) = xor (Ld x lo j t) (Ld x lo (j + 2) t) := by
  rw [Ld_step, h]; rfl

/-! ### Rigidity and universality -/

/-- Eventual equality of two sequences. -/
def EvEq (f g : Nat → Bool) : Prop := ∃ T, ∀ t, T ≤ t → f t = g t

/-- A sequence that is black infinitely often. -/
def Recurrent (f : Nat → Bool) : Prop := ∀ T, ∃ t, T ≤ t ∧ f t = true

/-- **Rigidity.** Eventual agreement on two consecutive left diagonals, the second black
infinitely often, forces eventual agreement on the next. -/
theorem rigid {x y : Int → Bool} {lo lo' : Int} {j : Nat}
    (h0 : EvEq (Ld x lo j) (Ld y lo' j)) (h1 : EvEq (Ld x lo (j + 1)) (Ld y lo' (j + 1)))
    (hr : Recurrent (Ld x lo (j + 1))) : EvEq (Ld x lo (j + 2)) (Ld y lo' (j + 2)) := by
  obtain ⟨T0, h0⟩ := h0
  obtain ⟨T1, h1⟩ := h1
  obtain ⟨s, hs, hst⟩ := hr (max T0 T1)
  refine ⟨s + 1, fun t ht => ?_⟩
  exact agree_after_reset (F := fun t b => xor (Ld x lo j t) (Ld x lo (j + 1) t || b))
    (T := max T0 T1) (fun t _ => Ld_step j t)
    (fun t ht => by rw [Ld_step, ← h0 t (by omega), ← h1 t (by omega)])
    hs (by simp [hst]) t (by omega)

theorem Ld_zero_true {x : Int → Bool} {lo : Int} (hleft : ∀ p, p < lo → x p = false)
    (hlo : x lo = true) (t : Nat) : Ld x lo 0 t = true := by
  have e : Ld x lo 0 t = evol x t (lo - t) := evol_congr (by omega)
  rw [e]; exact Rule30FiniteConfigs.evol_left_edge hlo hleft t

theorem Ld_one_true {x : Int → Bool} {lo : Int} (hleft : ∀ p, p < lo → x p = false)
    (hlo : x lo = true) (t : Nat) : Ld x lo 1 (t + 1) = true := by
  rw [Ld_one_succ hleft, Ld_zero_true hleft hlo]; rfl

/-- **Universality.** Two configurations, each white left of a black cell, agree eventually on
every left diagonal up to the first eventually white one. -/
theorem universal {x y : Int → Bool} {lo lo' : Int}
    (hx : ∀ p, p < lo → x p = false) (hxl : x lo = true)
    (hy : ∀ p, p < lo' → y p = false) (hyl : y lo' = true) :
    ∀ n, (∀ k, k < n → Recurrent (Ld x lo (k + 1))) →
      EvEq (Ld x lo n) (Ld y lo' n) ∧ EvEq (Ld x lo (n + 1)) (Ld y lo' (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨⟨0, fun t _ => by rw [Ld_zero_true hx hxl, Ld_zero_true hy hyl]⟩, ⟨1, fun t ht => ?_⟩⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [Ld_one_true hx hxl, Ld_one_true hy hyl]
  | succ n ih =>
    intro hr
    obtain ⟨a, b⟩ := ih (fun k hk => hr k (by omega))
    exact ⟨b, rigid a b (hr n (by omega))⟩

/-- **One bit per zero diagonal.** Behind an eventually white diagonal, two configurations that
agree eventually on the diagonal before it differ on the diagonal after it by a constant. -/
theorem zero_diag_xor_const {x y : Int → Bool} {lo lo' : Int} {j : Nat}
    (h0 : EvEq (Ld x lo j) (Ld y lo' j)) (hz : EvEq (Ld x lo (j + 1)) (fun _ => false))
    (hz' : EvEq (Ld y lo' (j + 1)) (fun _ => false)) :
    ∃ T, ∀ t, T ≤ t →
      xor (Ld x lo (j + 2) t) (Ld y lo' (j + 2) t) = xor (Ld x lo (j + 2) T) (Ld y lo' (j + 2) T) := by
  obtain ⟨A, hA⟩ := h0
  obtain ⟨B, hB⟩ := hz
  obtain ⟨C, hC⟩ := hz'
  refine ⟨max A (max B C), fun t ht => ?_⟩
  induction t, ht using le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [Ld_toggle x lo j t (hB t (by omega)), Ld_toggle y lo' j t (hC t (by omega)),
      hA t (by omega), ← ih]
    cases Ld y lo' j t <;> cases Ld x lo (j + 2) t <;> cases Ld y lo' (j + 2) t <;> rfl

/-! ### The damage edge -/

/-- **Agreement below a depth persists.** -/
theorem agree_persists {x y : Int → Bool} {lo lo' : Int}
    (hx : ∀ p, p < lo → x p = false) (hxl : x lo = true)
    (hy : ∀ p, p < lo' → y p = false) (hyl : y lo' = true) {e t : Nat}
    (h : ∀ j, j < e → Ld x lo j t = Ld y lo' j t) :
    ∀ j, j < e → Ld x lo j (t + 1) = Ld y lo' j (t + 1) := by
  intro j hj
  match j, hj with
  | 0, _ => rw [Ld_zero_true hx hxl, Ld_zero_true hy hyl]
  | 1, _ => rw [Ld_one_true hx hxl, Ld_one_true hy hyl]
  | k + 2, hk => rw [Ld_step, Ld_step, h k (by omega), h (k + 1) (by omega), h (k + 2) hk]

/-- **Damage enters only where the zero-state is transparent.** For the single seed: if a
solution `Z` of the diagonal recurrence agrees with the left diagonals below depth `s + 2` at time
`s + 2`, the agreement extends to depth `s + 2` at time `s + 3` exactly when the center agrees with
`Z` behind the column `-1` cell of `Z`. -/
theorem entry_iff {Z : Nat → Nat → Bool}
    (hZ : ∀ j t, Z (j + 2) (t + 1) = xor (Z j t) (Z (j + 1) t || Z (j + 2) t)) (s : Nat)
    (h : ∀ j, j < s + 2 → D j (s + 2) = Z j (s + 2)) :
    D (s + 2) (s + 3) = Z (s + 2) (s + 3) ↔
      (Z (s + 1) (s + 2) || cell (s + 2) 0) = (Z (s + 1) (s + 2) || Z (s + 2) (s + 2)) := by
  rw [D_step, hZ, h s (by omega), h (s + 1) (by omega), ← center_eq_D]
  cases Z s (s + 2) <;> cases (Z (s + 1) (s + 2) || cell (s + 2) 0) <;>
    cases (Z (s + 1) (s + 2) || Z (s + 2) (s + 2)) <;> simp

/-! ### The single seed to depth 401: a kernel certificate -/

/-- From this time on, every left diagonal of depth `≤ 401` is periodic with period `16`. -/
def T0 : Nat := 501

/-- The table: bit `16 j + φ` is diagonal `j` at the times `≡ φ (mod 16)`. -/
def tbl : Nat := 16785319393766780613805743289741117625313002880896287854578378032281885682618661999456528601564135956916767897466368650829386714901730525116791317562971550136678326554140003326413662764753820522494878726743252270698911371326317517898681684107862890258284882738857986736571265309916675003335473620839615420993253231275018129310576463935656019543424350642117880207798378035160786053564002330360874949094348777529434855560405664261682720474210393217197800450426376090105477809469256499661889863906172245767855435535013407400134295341552082029886197433907752085326102634102164365712325911877901317940097248922659162903152822171140180772050599130195619938880119160393327532409336984819198523629766513103549181140974761514016277215003227470985416253928956163208452281902104193721992431329713853242489335402787799025416742463488425031824312378100567872918313256589011245099628541362879908605340318318255097436796340761332666440559162185264021275496695598773033703107201034581829855733041547389009522534966879454671012407064331424614696856850801029617994001961967449518047244414661602940374451499398680865391795214488803267024550319620717726921507177626464734121528211045863732962999148397982574682430963823535819812482479222382713617187765319952480657190586020035632891984657492598856617395840868661747407045003097188761871018933073633403497938047425993674578623388115286589712629998027848145792022692533576199150786189225217991700271717081769981013792315332274730076750516042546334782805715456849478654461221608138492099715648424922574649569298264522662102102796352538740672181968728499935354940238136421696252326007788714563733960399155129887436735134918366095833750277812321416340239595362700192568114003474912573847521023099812007729678097646173080367618090005379255789243406938005505798746385728037410836384755902662734284187501267326262424012624041427151624868228427900322149251472433856176422031298904960078578632721724719112605570957311

def pat (j φ : Nat) : Bool := tbl.testBit (16 * j + φ)

/-- The table obeys the diagonal recurrence for depths `2 … n + 1`. -/
def stepOK : Nat → Bool
  | 0 => true
  | n + 1 => stepOK n && (List.range 16).all (fun φ =>
      pat (n + 2) ((φ + 1) % 16) == xor (pat n φ) (pat (n + 1) φ || pat (n + 2) φ))

theorem stepOK_400 : stepOK 400 = true := by decide +kernel

theorem stepOK_spec : ∀ n, stepOK n = true → ∀ j, j < n → ∀ φ, φ < 16 →
    pat (j + 2) ((φ + 1) % 16) = xor (pat j φ) (pat (j + 1) φ || pat (j + 2) φ) := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro h j hj φ hφ
    simp only [stepOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    rcases Nat.lt_or_ge j n with hj' | hj'
    · exact ih h.1 j hj' φ hφ
    · have e : j = n := by omega
      subst e; exact h.2 φ hφ

theorem pat_edges : (List.range 16).all (fun φ => pat 0 φ && pat 1 φ) = true := by decide +kernel

theorem baseOK : (List.range 402).all (fun j => (Rule30Window.row T0 T0).testBit j == pat j (T0 % 16)) = true := by
  decide +kernel

theorem D_eq_row (j : Nat) : D j T0 = (Rule30Window.row T0 T0).testBit j := by
  rw [Rule30Window.row_testBit T0 T0 (Nat.le_refl _) j]; rfl

/-- **The certificate.** From time `T0` on, diagonal `j ≤ 401` reads the table. -/
theorem D_eq_pat : ∀ t, T0 ≤ t → ∀ j, j ≤ 401 → D j t = pat j (t % 16) := by
  intro t ht
  induction t, ht using le_induction with
  | base =>
    intro j hj
    have := baseOK
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at this
    rw [D_eq_row]; exact this j (by omega)
  | succ t ht ih =>
    have hed := pat_edges
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hed
    intro j hj
    match j, hj with
    | 0, _ => rw [D_zero]; exact ((hed _ (Nat.mod_lt _ (by omega))).1).symm
    | 1, _ => rw [D_one]; exact ((hed _ (Nat.mod_lt _ (by omega))).2).symm
    | k + 2, hk =>
      rw [D_step, ih k (by omega), ih (k + 1) (by omega), ih (k + 2) hk,
        show (t + 1) % 16 = (t % 16 + 1) % 16 by omega]
      exact (stepOK_spec 400 stepOK_400 k (by omega) (t % 16) (Nat.mod_lt _ (by omega))).symm

theorem pat_zero_rows : (List.range 16).all (fun φ =>
    !pat 2 φ && !pat 7 φ && !pat 28 φ && !pat 399 φ) = true := by decide +kernel

/-- **Zero diagonals.** Depths 2, 7, 28 and 399 are eventually white. -/
theorem zero_diagonals : ∀ t, T0 ≤ t → D 2 t = false ∧ D 7 t = false ∧ D 28 t = false ∧ D 399 t = false := by
  intro t ht
  have h := pat_zero_rows
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h
  have := h (t % 16) (Nat.mod_lt _ (by omega))
  rw [D_eq_pat t ht 2 (by omega), D_eq_pat t ht 7 (by omega), D_eq_pat t ht 28 (by omega),
    D_eq_pat t ht 399 (by omega)]
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem pat_anti : (List.range 16).all (fun φ =>
    (pat 3 ((φ + 1) % 16) == !pat 3 φ) && (pat 8 ((φ + 2) % 16) == !pat 8 φ) &&
    (pat 29 ((φ + 4) % 16) == !pat 29 φ) && (pat 400 ((φ + 8) % 16) == !pat 400 φ)) = true := by
  decide +kernel

/-- **Period doubling.** Depths 3, 8, 29, 400 have antiperiods 1, 2, 4, 8: their eventual periods
are exactly 2, 4, 8, 16. -/
theorem antiperiods : ∀ t, T0 ≤ t →
    D 3 (t + 1) = !D 3 t ∧ D 8 (t + 2) = !D 8 t ∧ D 29 (t + 4) = !D 29 t ∧ D 400 (t + 8) = !D 400 t := by
  intro t ht
  have h := pat_anti
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  have := h (t % 16) (Nat.mod_lt _ (by omega))
  rw [D_eq_pat t ht 3 (by omega), D_eq_pat (t + 1) (by omega) 3 (by omega),
    D_eq_pat t ht 8 (by omega), D_eq_pat (t + 2) (by omega) 8 (by omega),
    D_eq_pat t ht 29 (by omega), D_eq_pat (t + 4) (by omega) 29 (by omega),
    D_eq_pat t ht 400 (by omega), D_eq_pat (t + 8) (by omega) 400 (by omega),
    show (t + 1) % 16 = (t % 16 + 1) % 16 by omega, show (t + 2) % 16 = (t % 16 + 2) % 16 by omega,
    show (t + 4) % 16 = (t % 16 + 4) % 16 by omega, show (t + 8) % 16 = (t % 16 + 8) % 16 by omega]
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

def per8OK : Nat → Bool
  | 0 => true
  | n + 1 => per8OK n && (List.range 16).all (fun φ => pat n ((φ + 8) % 16) == pat n φ)

theorem per8OK_400 : per8OK 400 = true := by decide +kernel

theorem per8_spec : ∀ n, per8OK n = true → ∀ j, j < n → ∀ φ, φ < 16 → pat j ((φ + 8) % 16) = pat j φ := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro h j hj φ hφ
    simp only [per8OK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    rcases Nat.lt_or_ge j n with hj' | hj'
    · exact ih h.1 j hj' φ hφ
    · have e : j = n := by omega
      subst e; exact h.2 φ hφ

/-- Every left diagonal of depth `< 400` has eventual period dividing 8. -/
theorem period_eight_below : ∀ j, j < 400 → ∀ t, T0 ≤ t → D j (t + 8) = D j t := by
  intro j hj t ht
  rw [D_eq_pat t ht j (by omega), D_eq_pat (t + 8) (by omega) j (by omega),
    show (t + 8) % 16 = (t % 16 + 8) % 16 by omega]
  exact per8_spec 400 per8OK_400 j hj (t % 16) (Nat.mod_lt _ (by omega))

end Rule30ZeroState
