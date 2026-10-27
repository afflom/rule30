module

public import Ruliology.CellularAutomata.Rule30Ether

/-!
# No fixed-width trap of the right strip contains the pure ether

Under an eventually periodic center column `w^∞` (period `4`), the columns `1, …, b` of the right
half evolve as the *strip relaxation*: a node is `(φ, s)` (phase `φ`, strip `s` of `b` cells) and
its successors are `((φ + 1) % 4, lin3 (w[φ] :: s ++ [x]))` for both values `x` of the unknown
column `b + 1` (`stepW`, exactly the step of `Rule30StripCertificates.rowR_succ`).

A *trap* is a set of nodes closed under every input on which column `1`, read at the white phases
of `w`, is eventually periodic along every path (`Trap`). This is the property used with masked
Jen (`Rule30MaskedJen`): if the true right half enters a trap, the center column cannot be `w^∞`.

* `word_lemma`: a set closed under every input that contains a node reachable to a node with two
  closed walks of equal length (a multiple of `4`) whose column-`1` outputs at some white phase
  differ contains a path whose white-phase output is not eventually periodic. (Two closed walks
  `c₁`, `c₂` with non-commuting outputs give the equal-length walks `c₁c₂` and `c₂c₁`.)
* `certOK`, `escapes_of_certOK`: a Boolean certificate check, sound by `word_lemma`.
* `Rule30Certificates.EtherTrap0` – `EtherTrap5`: kernel checks of certificates for every
  pure-ether node of width `20` of `0001`, `0011`, `0111`; `Rule30EtherTrapWidth20` combines them.
* `stepW_take`, `escapes_take`: a closed set of width `b ≤ 20` lifts to width `20`.
* `node_succ`, `node_traj`: the driven right half (`Rule30Ether.node`) is a path of the
  relaxation along column `b + 1`, so the trap notion here is the one masked Jen uses.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherTrap

open Rule30Ether Rule30StripCertificates

/-! ## The strip relaxation -/

/-- One step of the strip relaxation (column `0` is `w` at phase `φ`, column `b + 1` is `x`). -/
def stepW (w : List Bool) (st : Nat × List Bool) (x : Bool) : Nat × List Bool :=
  ((st.1 + 1) % 4, lin3 (wordAt w st.1 :: (st.2 ++ [x])))

/-- A path along an input sequence. -/
def traj (w : List Bool) (st : Nat × List Bool) (u : Nat → Bool) : Nat → Nat × List Bool
  | 0 => st
  | n + 1 => stepW w (traj w st u n) (u n)

/-- A walk along an input list. -/
def runW (w : List Bool) : Nat × List Bool → List Bool → Nat × List Bool
  | st, [] => st
  | st, x :: xs => runW w (stepW w st x) xs

/-- Column `1`. -/
def col1 (st : Nat × List Bool) : Bool := st.2.headD false

/-- The phase is white. -/
def white (w : List Bool) (st : Nat × List Bool) : Bool := !wordAt w st.1

/-- Column `1` at the white phases is eventually periodic, with a period that is a multiple of
`4` (any eventual period of the masked column gives one). -/
def MaskedPer (w : List Bool) (tr : Nat → Nat × List Bool) : Prop :=
  ∃ N Q, 0 < Q ∧ Q % 4 = 0 ∧ ∀ n, N ≤ n → white w (tr n) = true → col1 (tr (n + Q)) = col1 (tr n)

/-- A set of nodes closed under every input. -/
def Closed (w : List Bool) (T : Nat × List Bool → Prop) : Prop :=
  ∀ st, T st → ∀ x, T (stepW w st x)

/-- A trap: closed, and column `1` at the white phases is eventually periodic along every path. -/
def Trap (w : List Bool) (T : Nat × List Bool → Prop) : Prop :=
  Closed w T ∧ ∀ st, T st → ∀ u, MaskedPer w (traj w st u)

/-! ## Paths -/

theorem traj_shift (w : List Bool) (st : Nat × List Bool) (u : Nat → Bool) (m : Nat) :
    ∀ n, traj w st u (m + n) = traj w (traj w st u m) (fun k => u (m + k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => show stepW w (traj w st u (m + n)) (u (m + n)) = _; rw [ih]; rfl

theorem traj_congr (w : List Bool) (st : Nat × List Bool) (u v : Nat → Bool) :
    ∀ n, (∀ k, k < n → u k = v k) → traj w st u n = traj w st v n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    show stepW w (traj w st u n) (u n) = stepW w (traj w st v n) (v n)
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem traj_closed (w : List Bool) (T : Nat × List Bool → Prop) (hT : Closed w T)
    (st : Nat × List Bool) (hst : T st) (u : Nat → Bool) : ∀ n, T (traj w st u n) := by
  intro n
  induction n with
  | zero => exact hst
  | succ n ih => exact hT _ ih _

theorem traj_phase (w : List Bool) (st : Nat × List Bool) (hst : st.1 < 4) (u : Nat → Bool) :
    ∀ n, (traj w st u n).1 = (st.1 + n) % 4 := by
  intro n
  induction n with
  | zero => show st.1 = _; omega
  | succ n ih => show ((traj w st u n).1 + 1) % 4 = _; rw [ih]; omega

theorem traj_succ' (w : List Bool) (u : Nat → Bool) :
    ∀ n st, traj w st u (n + 1) = traj w (stepW w st (u 0)) (fun k => u (k + 1)) n := by
  intro n
  induction n with
  | zero => intro st; rfl
  | succ n ih =>
    intro st
    show stepW w (traj w st u (n + 1)) (u (n + 1)) = stepW w (traj w _ _ n) (u (n + 1))
    rw [ih]

theorem runW_traj (w : List Bool) : ∀ (l : List Bool) (st : Nat × List Bool),
    runW w st l = traj w st (fun n => l.getD n false) l.length
  | [], st => rfl
  | x :: xs, st => by
    show runW w (stepW w st x) xs = _
    rw [runW_traj w xs, show (x :: xs).length = xs.length + 1 by simp, traj_succ']
    rfl

/-! ## A pattern that is not eventually periodic -/

/-- The powers of two. -/
noncomputable def pat (i : Nat) : Bool := @decide (∃ k, 2 ^ k = i) (Classical.propDecidable _)

theorem pat_not_eventually_periodic (N Q : Nat) (hQ : 0 < Q) :
    ∃ i, N ≤ i ∧ pat (i + Q) ≠ pat i := by
  have h1 : N + Q < 2 ^ (N + Q) := Nat.lt_two_pow_self
  refine ⟨2 ^ (N + Q), by omega, ?_⟩
  have ht : pat (2 ^ (N + Q)) = true := by
    unfold pat; exact @decide_eq_true _ (Classical.propDecidable _) ⟨N + Q, rfl⟩
  have hf : pat (2 ^ (N + Q) + Q) = false := by
    unfold pat
    apply @decide_eq_false _ (Classical.propDecidable _)
    rintro ⟨m, hm⟩
    have a1 : 2 ^ (N + Q) < 2 ^ m := by omega
    have a2 : 2 ^ m < 2 ^ (N + Q + 1) := by rw [Nat.pow_succ]; omega
    rw [Nat.pow_lt_pow_iff_right (by decide)] at a1 a2
    omega
  rw [ht, hf]; decide

/-! ## The word lemma -/

/-- **Word lemma.** Let `T` be closed under every input and contain `x0`. Suppose the input list
`P` leads from `x0` to `y`, and the input sequences `a`, `b` are closed walks at `y` of the same
length `L` (a positive multiple of `4`) whose outputs differ at the white offset `j0`. Then some
path from `x0` stays in `T` and its column `1` at the white phases is not eventually periodic. -/
theorem word_lemma (w : List Bool) (T : Nat × List Bool → Prop) (hT : Closed w T)
    (x0 y : Nat × List Bool) (hx0 : T x0) (hx04 : x0.1 < 4) (P : List Bool) (a b : Nat → Bool)
    (L j0 : Nat) (hP : traj w x0 (fun n => P.getD n false) P.length = y)
    (ha : traj w y a L = y) (hb : traj w y b L = y) (hL4 : L % 4 = 0) (hL0 : 0 < L)
    (hj0 : j0 < L) (hwhite : white w (traj w y a j0) = true)
    (hdiff : col1 (traj w y a j0) ≠ col1 (traj w y b j0)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w x0 u n)) ∧ ¬ MaskedPer w (traj w x0 u) := by
  let blk : Nat → Nat → Bool := fun i => if pat i then b else a
  let u : Nat → Bool := fun n =>
    if n < P.length then P.getD n false else blk ((n - P.length) / L) ((n - P.length) % L)
  refine ⟨u, traj_closed w T hT x0 hx0 u, ?_⟩
  -- the path: prefix `P`, then the blocks
  have hy : traj w x0 u P.length = y := by
    rw [← hP]; exact traj_congr w x0 u _ _ (fun k hk => by simp [u, hk])
  have hin : ∀ i j, j < L → u (P.length + i * L + j) = blk i j := by
    intro i j hj
    have e1 : ¬ (P.length + i * L + j < P.length) ↔ True := by simp; omega
    simp only [u]
    rw [ite_eq_right (by omega), show P.length + i * L + j - P.length = j + L * i by
      rw [Nat.mul_comm]; omega, Nat.add_mul_div_left _ _ hL0, Nat.add_mul_mod_self_left,
      Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.zero_add]
  have hblk : ∀ i, traj w y (blk i) L = y := by
    intro i; simp only [blk]; split
    · exact hb
    · exact ha
  have hstart : ∀ i, traj w x0 u (P.length + i * L) = y := by
    intro i
    induction i with
    | zero => rw [Nat.zero_mul, Nat.add_zero]; exact hy
    | succ i ih =>
      rw [show P.length + (i + 1) * L = (P.length + i * L) + L by rw [Nat.succ_mul]; omega,
        traj_shift, ih, traj_congr w y _ (blk i) L (fun k hk => hin i k hk)]
      exact hblk i
  have hmid : ∀ i j, j ≤ L → traj w x0 u (P.length + i * L + j) = traj w y (blk i) j := by
    intro i j hj
    rw [traj_shift, hstart i]
    exact traj_congr w y _ _ j (fun k hk => hin i k (by omega))
  -- whiteness only depends on the time mod 4
  have hph : ∀ n, (traj w x0 u n).1 = (x0.1 + n) % 4 := traj_phase w x0 hx04 u
  have hwh : ∀ n m, n % 4 = m % 4 → white w (traj w x0 u n) = white w (traj w x0 u m) := by
    intro n m h
    unfold white; rw [hph, hph, show (x0.1 + n) % 4 = (x0.1 + m) % 4 by omega]
  rintro ⟨N, Q, hQ, hQ4, hper⟩
  -- iterate the period
  have hiter : ∀ k n, N ≤ n → white w (traj w x0 u n) = true →
      col1 (traj w x0 u (n + k * Q)) = col1 (traj w x0 u n) := by
    intro k
    induction k with
    | zero => intro n _ _; rw [Nat.zero_mul, Nat.add_zero]
    | succ k ih =>
      intro n hn hw
      have e1 : n + (k + 1) * Q = (n + k * Q) + Q := by rw [Nat.succ_mul]; omega
      have e2 : k * Q % 4 = 0 := by rw [Nat.mul_mod, hQ4, Nat.mul_zero, Nat.zero_mod]
      have e3 : (n + k * Q) % 4 = n % 4 := by omega
      have hw' : white w (traj w x0 u (n + k * Q)) = true := by rw [hwh _ n e3]; exact hw
      rw [e1, hper (n + k * Q) (by omega) hw', ih n hn hw]
  -- the white times `P.length + i * L + j0`
  have hwhite_i : ∀ i, white w (traj w x0 u (P.length + i * L + j0)) = true := by
    intro i
    have e2 : i * L % 4 = 0 := by rw [Nat.mul_mod, hL4, Nat.mul_zero, Nat.zero_mod]
    have e3 : (P.length + i * L + j0) % 4 = (P.length + 0 * L + j0) % 4 := by omega
    rw [hwh _ _ e3, hmid 0 j0 (by omega)]
    have hy4 : y.1 < 4 := by rw [← hy, hph]; exact Nat.mod_lt _ (by decide)
    have e : white w (traj w y (blk 0) j0) = white w (traj w y a j0) := by
      unfold white; rw [traj_phase w y hy4, traj_phase w y hy4]
    rw [e]; exact hwhite
  have hout : ∀ i, N ≤ i → pat (i + Q) = pat i := by
    intro i hi
    have h := hiter L (P.length + i * L + j0) (by
      have : i ≤ i * L := Nat.le_mul_of_pos_right i hL0
      omega) (hwhite_i i)
    rw [show P.length + i * L + j0 + L * Q = P.length + (i + Q) * L + j0 by
      rw [Nat.add_mul, Nat.mul_comm L Q]; omega, hmid _ _ (by omega), hmid _ _ (by omega)] at h
    have key : ∀ p q : Bool, col1 (traj w y (if q = true then b else a) j0) =
        col1 (traj w y (if p = true then b else a) j0) → q = p := by
      intro p q hpq
      cases p <;> cases q
      · rfl
      · simp only [↓reduceIte, Bool.false_eq_true] at hpq; exact absurd hpq.symm hdiff
      · simp only [↓reduceIte, Bool.false_eq_true] at hpq; exact absurd hpq hdiff
      · rfl
    exact key (pat i) (pat (i + Q)) h
  obtain ⟨i, hi, hne⟩ := pat_not_eventually_periodic N Q hQ
  exact hne (hout i hi)

/-! ## Certificates -/

/-- The certificate check: the walk `P` leads from `x0` to `y`; `A`, `B` are closed walks at `y`
of equal length (a positive multiple of `4`) whose column `1` differs at the white offset `j0`. -/
def certOK (w : List Bool) (x0 : Nat × List Bool) (P A B : List Bool) (j0 : Nat) : Bool :=
  let y := runW w x0 P
  (runW w y A == y) && (runW w y B == y) && (A.length == B.length) && (A.length % 4 == 0) &&
    decide (0 < A.length) && decide (j0 < A.length) && decide (x0.1 < 4) &&
    white w (traj w y (fun n => A.getD n false) j0) &&
    (col1 (traj w y (fun n => A.getD n false) j0) != col1 (traj w y (fun n => B.getD n false) j0))

/-- **Soundness of a certificate.** -/
theorem escapes_of_certOK (w : List Bool) (x0 : Nat × List Bool) (P A B : List Bool) (j0 : Nat)
    (hc : certOK w x0 P A B j0 = true) (T : Nat × List Bool → Prop) (hT : Closed w T)
    (hx0 : T x0) : ∃ u : Nat → Bool, (∀ n, T (traj w x0 u n)) ∧ ¬ MaskedPer w (traj w x0 u) := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hlen⟩, h4⟩, h0⟩, hj⟩, hx4⟩, hw⟩, hd⟩ := hc
  rw [runW_traj] at hA hB
  rw [← hlen] at hB
  exact word_lemma w T hT x0 (runW w x0 P) hx0 hx4 P _ _ A.length j0 (by rw [runW_traj]) hA hB
    (by simpa using h4) h0 hj hw hd

/-- No trap contains a node with a valid certificate. -/
theorem not_trap_of_certOK (w : List Bool) (x0 : Nat × List Bool) (P A B : List Bool) (j0 : Nat)
    (hc : certOK w x0 P A B j0 = true) (T : Nat × List Bool → Prop) (hT : Trap w T) : ¬ T x0 := by
  intro hx0
  obtain ⟨u, _, hu⟩ := escapes_of_certOK w x0 P A B j0 hc T hT.1 hx0
  exact hu (hT.2 x0 hx0 u)

/-! ## Smaller widths -/

theorem getD_cons_succ' (c : Bool) (l : List Bool) (i : Nat) : (c :: l).getD (i + 1) false = l.getD i false := rfl

theorem getD_append_left' (l1 l2 : List Bool) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l1 l2 : List Bool) (i : Nat) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i false = l2.getD (i - l1.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_take' (l : List Bool) (b i : Nat) (h : i < b) : (l.take b).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left h]

theorem take_seg : ∀ (b n : Nat) (f : Nat → Bool), b ≤ n → (seg f n).take b = seg f b
  | 0, _, _, _ => by simp [seg]
  | b + 1, n + 1, f, h => by
    show f 0 :: (seg (fun i => f (i + 1)) n).take b = f 0 :: seg (fun i => f (i + 1)) b
    rw [take_seg b n _ (by omega)]
  | _ + 1, 0, _, h => by omega

/-- `lin3` of a strip, as a `seg`. -/
theorem lin3_strip (c : Bool) (s : List Bool) (x : Bool) :
    lin3 (c :: (s ++ [x])) = seg (fun i => xor ((c :: (s ++ [x])).getD i false)
      (((c :: (s ++ [x])).getD (i + 1) false) || ((c :: (s ++ [x])).getD (i + 2) false))) s.length := by
  have e : c :: (s ++ [x]) = seg (fun i => (c :: (s ++ [x])).getD i false) (s.length + 2) := by
    have := seg_getD_self (c :: (s ++ [x]))
    rw [show (c :: (s ++ [x])).length = s.length + 2 by simp] at this
    exact this.symm
  conv => lhs; rw [e]
  rw [lin3_seg]

/-- **Projection.** The first `b` cells of a step of a wider strip are the step of the narrower strip
whose input is cell `b + 1`. -/
theorem stepW_take (w : List Bool) (st : Nat × List Bool) (x : Bool) (b : Nat) (hb : b < st.2.length) :
    ((stepW w st x).1, (stepW w st x).2.take b) =
      stepW w (st.1, st.2.take b) (st.2.getD b false) := by
  unfold stepW
  simp only [Prod.mk.injEq, true_and]
  rw [lin3_strip, lin3_strip, take_seg _ _ _ (by omega)]
  have hlen : (st.2.take b).length = b := by simp; omega
  rw [hlen]
  apply seg_congr
  intro i hi
  have g : ∀ k, k ≤ b + 1 → (wordAt w st.1 :: (st.2 ++ [x])).getD k false =
      (wordAt w st.1 :: (st.2.take b ++ [st.2.getD b false])).getD k false := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      rw [getD_cons_succ', getD_cons_succ', getD_append_left' _ _ _ (by omega)]
      rcases Nat.lt_or_ge k b with h | h
      · rw [getD_append_left' _ _ _ (by rw [hlen]; exact h), getD_take' _ _ _ h]
      · rw [getD_append_right' _ _ _ (by rw [hlen]; exact h), show k = b by omega, hlen,
          Nat.sub_self]
        rfl
  rw [g i (by omega), g (i + 1) (by omega), g (i + 2) (by omega)]

theorem stepW_length (w : List Bool) (st : Nat × List Bool) (x : Bool) :
    (stepW w st x).2.length = st.2.length := by
  unfold stepW
  rw [lin3_strip, length_seg]

/-- **Lifting a closed set of a narrower strip.** If `T` is closed for width `b`-strips and contains
the first `b` cells of a node of a wider strip from which some path has a white-phase output that
is not eventually periodic, then `T` contains such a path too. -/
theorem escapes_take (w : List Bool) (b : Nat) (hb : 1 ≤ b) (x0 : Nat × List Bool)
    (hbx : b < x0.2.length) (u : Nat → Bool) (hu : ¬ MaskedPer w (traj w x0 u))
    (T : Nat × List Bool → Prop) (hT : Closed w T) (hx0 : T (x0.1, x0.2.take b)) :
    ∃ u' : Nat → Bool, (∀ n, T (traj w (x0.1, x0.2.take b) u' n)) ∧
      ¬ MaskedPer w (traj w (x0.1, x0.2.take b) u') := by
  let u' : Nat → Bool := fun n => (traj w x0 u n).2.getD b false
  have hlen : ∀ n, (traj w x0 u n).2.length = x0.2.length := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show (stepW w _ _).2.length = _; rw [stepW_length, ih]
  have hproj : ∀ n, traj w (x0.1, x0.2.take b) u' n = ((traj w x0 u n).1, (traj w x0 u n).2.take b) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show stepW w (traj w (x0.1, x0.2.take b) u' n) (u' n) = _
      rw [ih]
      exact (stepW_take w _ (u n) b (by rw [hlen]; exact hbx)).symm
  refine ⟨u', traj_closed w T hT _ hx0 u', fun ⟨N, Q, hQ, hQ4, hper⟩ => hu ⟨N, Q, hQ, hQ4, fun n hn hw => ?_⟩⟩
  have h := hper n hn (by rw [hproj]; exact hw)
  rw [hproj, hproj] at h
  have hc : ∀ m, col1 ((traj w x0 u m).1, (traj w x0 u m).2.take b) = col1 (traj w x0 u m) := by
    intro m
    unfold col1
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    cases (traj w x0 u m).2 with
    | nil => rfl
    | cons c l => rfl
  rw [hc, hc] at h
  exact h

/-! ## The relaxation contains the true dynamics -/

/-- **The driven right half walks in the strip relaxation.** For the right half driven by `w^∞`
(`Rule30Ether.drv`), the node at time `t + 1` (`Rule30Ether.node`) is the relaxation step of the
node at time `t` with input column `b + 1`. So if the true right half enters a closed set, it stays
in it, and its column `1` at the white phases is the output of a path of the relaxation. -/
theorem node_succ (w : List Bool) (x : Nat → Bool) (t b : Nat) :
    node w x (t + 1) b = stepW w (node w x t b) (drv (wordAt w) x t (b + 1)) := by
  unfold node stepW
  simp only [Prod.mk.injEq]
  refine ⟨by omega, ?_⟩
  rw [rowOf_succ (drv_isR30 (wordAt w) x) t 0 b, drv_col0, show 0 + b + 1 = b + 1 by omega]
  congr 2
  unfold wordAt
  rw [Nat.mod_mod]

/-- The nodes of the driven right half form the path of the relaxation along column `b + 1`. -/
theorem node_traj (w : List Bool) (x : Nat → Bool) (b : Nat) :
    ∀ t, node w x t b = traj w (node w x 0 b) (fun t => drv (wordAt w) x t (b + 1)) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [node_succ, ih]; rfl

end Rule30EtherTrap
end Ruliology.CellularAutomata
