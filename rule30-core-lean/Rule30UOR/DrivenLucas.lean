module
public import Rule30UOR.DiagonalCone
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

/-! # The Lucas window of the driven half

The Pascal transport of `DiagonalCone` (rule 60 with sources) restarted at any time `t` is the
binomial transport of the state at `t` plus the window of the sources of `[t, t + N)`
(`transport_add`). At a lag `Q·2^n` Lucas's theorem keeps only the depths `2^n·i`, with weight
`C(Q, i)` (`pascalParity_lattice`, `pascalParity_offLattice`, `transport_add_lucas`); on the lattice
`(2^n m, 2^n A)` every transport is the Pascal transport of its block windows
(`transport_block_lucas`, the Sierpinski coarse-graining of the sources).

For the half driven from white by any boundary `c` (`Fixed.Lh`), the depths `≥ 2^(n+1)` are beyond
the edge before time `2^(n+1)` (`drivenDepth_beyond`) and the edge is `c 0` (`drivenDepth_edge`), so
the window of length `Q·2^n` read at column `0` is the cone increment plus the edge term
`C(Q, 1)·(column −2^n)` (`driven_window_cone`, no hypothesis on `c`). Under black-time consistency
and a period `P` from `T` the cone increment vanishes (`driven_window_of_periodic`): the window is
white on `[T, 2^n)` (`driven_window_white`) and `C(P, 1) = P mod 2` at `t = 2^n`
(`driven_window_edge`).

This is a restatement of the period through the bijection `transport_unique`, not a route: the same
identities hold for every field with the cone identity, the black edge and white beyond it, whether
or not it is rule 30 (register note under `duhamel-and-tails`).
-/

@[expose] public section

namespace Rule30UOR.DrivenLucas

open Rule30UOR.Core Rule30UOR.EdgeSplit Rule30UOR.EdgeParity Rule30UOR.Antidiagonal
  Rule30UOR.DiagonalCone Rule30UOR.Fixed

/-! ## Duhamel from any start -/

/-- The sources of the times `[t, t + N)` transported to depth `a` at time `t + N`. -/
def transportWindow (S : Nat → Nat → Bool) (N t a : Nat) : Bool :=
  xorBelow (fun i => transportRow S (N - 1 - i) (t + i) a) N

/-- **Duhamel from any start**: the transport at time `t + N` is the Pascal transport of the
state at time `t` plus the window of the sources of `[t, t + N)`. -/
theorem transport_add (S : Nat → Nat → Bool) (N t a : Nat) :
    transport S (t + N) a =
      bxor (xorBelow (fun q => pascalParity N q && transport S t (a + q)) (N + 1))
        (transportWindow S N t a) := by
  have hstep : ∀ M b,
      bxor (transport S (t + (M + 1)) b) (transportRow (fun _ b => transport S t b) (M + 1) 0 b) =
        bxor (bxor (bxor (transport S (t + M) b) (transportRow (fun _ b => transport S t b) M 0 b))
          (bxor (transport S (t + M) (b + 1)) (transportRow (fun _ b => transport S t b) M 0 (b + 1))))
          (S (t + M) b) := by
    intro M b
    show bxor (transport S (t + M + 1) b) (transportRow (fun _ b => transport S t b) (M + 1) 0 b) = _
    rw [transport_succ, transportRow_pascal]
    cases transport S (t + M) b <;> cases transport S (t + M) (b + 1) <;>
      cases transportRow (fun _ b => transport S t b) M 0 b <;>
      cases transportRow (fun _ b => transport S t b) M 0 (b + 1) <;> cases S (t + M) b <;> rfl
  have h0 : ∀ b, bxor (transport S (t + 0) b) (transportRow (fun _ b => transport S t b) 0 0 b) = false := by
    intro b
    show bxor (transport S t b) (bxor false (pascalParity 0 0 && transport S t b)) = false
    rw [pascalParity_zero_right, Bool.true_and, cone_bxor_false]
    cases transport S t b <;> rfl
  have hX : bxor (transport S (t + N) a) (xorBelow (fun q => pascalParity N q && transport S t (a + q)) (N + 1)) =
      transportWindow S N t a :=
    transport_unique (fun j b => S (t + j) b)
      (fun M b => bxor (transport S (t + M) b) (transportRow (fun _ b => transport S t b) M 0 b))
      hstep h0 N a
  revert hX
  cases transport S (t + N) a <;> cases xorBelow (fun q => pascalParity N q && transport S t (a + q)) (N + 1) <;>
    cases transportWindow S N t a <;> decide

/-! ## Lucas at the scale `2^n` -/

/-- **Lucas on the lattice**: `C(Q·2^n, 2^n·i) ≡ C(Q, i)`. -/
theorem pascalParity_lattice (Q n i : Nat) : pascalParity (Q * twopow n) (twopow n * i) = pascalParity Q i := by
  induction n generalizing i with
  | zero => rw [show twopow 0 = 1 from rfl, Nat.mul_one, Nat.one_mul]
  | succ n ih =>
    have h2 : twopow (n + 1) = 2 * twopow n := by rw [twopow_succ]; cfomega
    rw [h2, show Q * (2 * twopow n) = 2 * (Q * twopow n) by rw [Nat.mul_left_comm],
      Nat.mul_assoc, pascalParity_even_even, ih]

/-- **Lucas off the lattice**: `C(Q·2^n, 2^n·i + r)` is even for `0 < r < 2^n`. -/
theorem pascalParity_offLattice (Q n i r : Nat) (h0 : 0 < r) (hr : r < twopow n) :
    pascalParity (Q * twopow n) (twopow n * i + r) = false := by
  induction n generalizing i r with
  | zero =>
    have h1 : twopow 0 = 1 := rfl
    exact absurd hr (by cfomega)
  | succ n ih =>
    have h2 : twopow (n + 1) = 2 * twopow n := by rw [twopow_succ]; cfomega
    rw [h2] at hr ⊢
    rw [show Q * (2 * twopow n) = 2 * (Q * twopow n) by rw [Nat.mul_left_comm], Nat.mul_assoc]
    obtain ⟨s, f, hf, rfl⟩ : ∃ s f, f < 2 ∧ r = 2 * s + f :=
      ⟨r / 2, r % 2, Nat.mod_lt _ (by decide), by cfomega⟩
    rcases Nat.lt_or_ge f 1 with hf0 | hf1
    · obtain rfl : f = 0 := by cfomega
      rw [show 2 * (twopow n * i) + (2 * s + 0) = 2 * (twopow n * i + s) by cfomega, pascalParity_even_even]
      exact ih i s (by cfomega) (by cfomega)
    · obtain rfl : f = 1 := by cfomega
      rw [show 2 * (twopow n * i) + (2 * s + 1) = 2 * (twopow n * i + s) + 1 by cfomega]
      exact pascalParity_even_odd _ _

/-- Lucas at the scale `2^n`: `C(Q·2^n, q)` is odd only at `q = 2^n·i`, where it is `C(Q, i)`. -/
theorem pascalParity_mul_twopow (Q n q : Nat) :
    pascalParity (Q * twopow n) q = (decide (q % twopow n = 0) && pascalParity Q (q / twopow n)) := by
  have hpos := Rule30UOR.Scale.twopow_pos n
  have hq : twopow n * (q / twopow n) + q % twopow n = q := by
    have := Nat.mod_add_div q (twopow n)
    cfomega
  have hlt : q % twopow n < twopow n := Nat.mod_lt _ hpos
  have e : pascalParity (Q * twopow n) q =
      pascalParity (Q * twopow n) (twopow n * (q / twopow n) + q % twopow n) := by rw [hq]
  rw [e]
  rcases Nat.eq_zero_or_pos (q % twopow n) with h | h
  · rw [h, decide_eq_true rfl, Bool.true_and, Nat.add_zero, pascalParity_lattice]
  · rw [decide_eq_false (by cfomega), Bool.false_and, pascalParity_offLattice Q n _ _ h hlt]

/-- A fold over `M·Q` places is the fold of its `Q` blocks of length `M`. -/
theorem xorBelow_blocks (h : Nat → Bool) (M : Nat) : ∀ Q,
    xorBelow h (M * Q) = xorBelow (fun i => xorBelow (fun r => h (M * i + r)) M) Q
  | 0 => by rw [Nat.mul_zero]; rfl
  | Q + 1 => by
    rw [Nat.mul_add, Nat.mul_one, xorBelow_split h (M * Q) M, xorBelow_blocks h M Q]
    rfl

/-- One block of a Lucas-weighted fold: only its first place survives. -/
theorem block_lucas (g : Nat → Bool) (Q n i : Nat) :
    xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + r) && g (twopow n * i + r)) (twopow n) =
      (pascalParity Q i && g (twopow n * i)) := by
  obtain ⟨M, hM⟩ : ∃ M, twopow n = M + 1 :=
    ⟨twopow n - 1, by have := Rule30UOR.Scale.twopow_pos n; cfomega⟩
  have e : xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + r) && g (twopow n * i + r)) (twopow n) =
      xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + r) && g (twopow n * i + r)) (M + 1) := by
    rw [hM]
  have hf : xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + r) && g (twopow n * i + r)) (M + 1) =
      bxor (pascalParity (Q * twopow n) (twopow n * i + 0) && g (twopow n * i + 0))
        (xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + (r + 1)) && g (twopow n * i + (r + 1))) M) :=
    xorBelow_front _ M
  have ht : xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + (r + 1)) && g (twopow n * i + (r + 1))) M =
      false := by
    rw [xorBelow_congr _ (fun _ => false) M (fun r hr => by
        show (pascalParity (Q * twopow n) (twopow n * i + (r + 1)) && g (twopow n * i + (r + 1))) = false
        rw [pascalParity_offLattice Q n i (r + 1) (by cfomega) (by cfomega), Bool.false_and])]
    exact xorBelow_false M
  rw [e, hf, ht, cone_bxor_false_right, Nat.add_zero, pascalParity_lattice]

/-- **The sparse Pascal row**: a fold weighted by `C(Q·2^n, q)` is the fold over the lattice
`q = 2^n·i` weighted by `C(Q, i)`. -/
theorem xorBelow_lucas (g : Nat → Bool) (Q n : Nat) :
    xorBelow (fun q => pascalParity (Q * twopow n) q && g q) (Q * twopow n + 1) =
      xorBelow (fun i => pascalParity Q i && g (twopow n * i)) (Q + 1) := by
  have hb : xorBelow (fun q => pascalParity (Q * twopow n) q && g q) (twopow n * Q) =
      xorBelow (fun i => xorBelow (fun r => pascalParity (Q * twopow n) (twopow n * i + r) &&
        g (twopow n * i + r)) (twopow n)) Q :=
    xorBelow_blocks _ (twopow n) Q
  have hc : xorBelow (fun q => pascalParity (Q * twopow n) q && g q) (Q * twopow n) =
      xorBelow (fun q => pascalParity (Q * twopow n) q && g q) (twopow n * Q) :=
    congrArg (xorBelow (fun q => pascalParity (Q * twopow n) q && g q)) (Nat.mul_comm Q (twopow n))
  have hg : g (Q * twopow n) = g (twopow n * Q) := congrArg g (Nat.mul_comm Q (twopow n))
  show bxor (xorBelow (fun q => pascalParity (Q * twopow n) q && g q) (Q * twopow n))
      (pascalParity (Q * twopow n) (Q * twopow n) && g (Q * twopow n)) =
    bxor (xorBelow (fun i => pascalParity Q i && g (twopow n * i)) Q) (pascalParity Q Q && g (twopow n * Q))
  rw [hc, hb, xorBelow_congr _ _ Q (fun i _ => block_lucas g Q n i), pascalParity_self, pascalParity_self, hg]

/-- **Frobenius and Lucas at the lag `Q·2^n`**: the state at time `t` reaches time `t + Q·2^n` only
from the depths `a + 2^n·i`, with weight `C(Q, i)`. -/
theorem transport_add_lucas (S : Nat → Nat → Bool) (Q n t a : Nat) :
    transport S (t + Q * twopow n) a =
      bxor (xorBelow (fun i => pascalParity Q i && transport S t (a + twopow n * i)) (Q + 1))
        (transportWindow S (Q * twopow n) t a) := by
  have h : xorBelow (fun q => pascalParity (Q * twopow n) q && transport S t (a + q)) (Q * twopow n + 1) =
      xorBelow (fun i => pascalParity Q i && transport S t (a + twopow n * i)) (Q + 1) :=
    xorBelow_lucas (fun q => transport S t (a + q)) Q n
  rw [transport_add S (Q * twopow n) t a, h]

/-- The block window at scale `2^n`: the sources of the times `[2^n J, 2^n (J + 1))` transported to
depth `2^n B` at the end of the block. -/
def blockWindow (S : Nat → Nat → Bool) (n J B : Nat) : Bool :=
  transportWindow S (twopow n) (twopow n * J) (twopow n * B)

/-- **Lucas renormalization**: on the lattice `(2^n m, 2^n A)` every transport is the Pascal
transport of its block windows (the sources coarse-grained by the Sierpinski gasket). -/
theorem transport_block_lucas (S : Nat → Nat → Bool) (n m A : Nat) :
    transport S (twopow n * m) (twopow n * A) = transport (blockWindow S n) m A := by
  have hstep : ∀ k B, transport S (twopow n * (k + 1)) (twopow n * B) =
      bxor (bxor (transport S (twopow n * k) (twopow n * B)) (transport S (twopow n * k) (twopow n * (B + 1))))
        (blockWindow S n k B) := by
    intro k B
    have h := transport_add_lucas S 1 n (twopow n * k) (twopow n * B)
    rw [Nat.one_mul] at h
    have e1 : twopow n * k + twopow n = twopow n * (k + 1) := by rw [Nat.mul_add, Nat.mul_one]
    have e2 : twopow n * B + twopow n * 1 = twopow n * (B + 1) := by rw [Nat.mul_add]
    have e0 : twopow n * B + twopow n * 0 = twopow n * B := by rw [Nat.mul_zero, Nat.add_zero]
    rw [e1] at h
    rw [h]
    show bxor (bxor (bxor false (pascalParity 1 0 && transport S (twopow n * k) (twopow n * B + twopow n * 0)))
        (pascalParity 1 1 && transport S (twopow n * k) (twopow n * B + twopow n * 1)))
        (transportWindow S (twopow n) (twopow n * k) (twopow n * B)) =
      bxor (bxor (transport S (twopow n * k) (twopow n * B)) (transport S (twopow n * k) (twopow n * (B + 1))))
        (transportWindow S (twopow n) (twopow n * k) (twopow n * B))
    rw [e0, e2, pascalParity_zero_right, pascalParity_self, Bool.true_and, Bool.true_and, cone_bxor_false]
  have h0 : ∀ B, transport S (twopow n * 0) (twopow n * B) = false := by
    intro B
    rw [Nat.mul_zero]
    rfl
  exact transport_unique (blockWindow S n) (fun k B => transport S (twopow n * k) (twopow n * B)) hstep h0 m A

/-! ## The driven half read through Lucas -/

/-- Column `−a` of the half driven by `c` from white. -/
def drivenDepth (c : Nat → Bool) (t a : Nat) : Bool := Lh c t (-(a : Int))

/-- The driven half is white beyond its edge. -/
theorem drivenDepth_beyond (c : Nat → Bool) : ∀ t a, t < a → drivenDepth c t a = false := by
  intro t
  induction t with
  | zero => intro a h; exact Lh_zero_neg c _ (by cfomega)
  | succ t ih =>
    intro a h
    have h1 := ih (a + 1) (by cfomega)
    have h2 := ih a (by cfomega)
    have h3 := ih (a - 1) (by cfomega)
    unfold drivenDepth at h1 h2 h3 ⊢
    rw [Lh_succ_neg c t _ (by cfomega), show -(a : Int) - 1 = -((a + 1 : Nat) : Int) by cfomega,
      show -(a : Int) + 1 = -((a - 1 : Nat) : Int) by cfomega, h1, h2, h3]
    rfl

/-- The edge of the driven half is the seed `c 0`. -/
theorem drivenDepth_edge (c : Nat → Bool) : ∀ t, drivenDepth c t t = c 0 := by
  intro t
  induction t with
  | zero =>
    unfold drivenDepth
    rw [show (-((0 : Nat) : Int)) = 0 by cfomega, Lh_col0]
  | succ t ih =>
    have h1 := drivenDepth_beyond c t (t + 1 + 1) (by cfomega)
    have h2 := drivenDepth_beyond c t (t + 1) (by cfomega)
    unfold drivenDepth at h1 h2 ih ⊢
    rw [Lh_succ_neg c t _ (by cfomega), show -((t + 1 : Nat) : Int) - 1 = -((t + 1 + 1 : Nat) : Int) by cfomega,
      show -((t + 1 : Nat) : Int) + 1 = -(t : Int) by cfomega, h1, h2, ih]
    cases c 0 <;> rfl

/-- Below the edge the transport of the driven sources is the driven half (Duhamel). -/
theorem transport_drivenEnd_eq (c : Nat → Bool) (t a : Nat) (ha : 0 < a) :
    transport (drivenEnd c) t a = drivenDepth c t a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by cfomega⟩
  exact driven_duhamel c t b

theorem transport_drivenEnd_beyond (c : Nat → Bool) (t a : Nat) (h : t < a) :
    transport (drivenEnd c) t a = false := by
  rw [transport_drivenEnd_eq c t a (by cfomega), drivenDepth_beyond c t a h]

/-- **The driven Lucas window**: before time `2^(n+1)`, the window of the driven sources of length
`Q·2^n` read at column `0` is the cone increment across the lag plus the edge term
`C(Q, 1)·(column −2^n)`. No hypothesis on the boundary. -/
theorem driven_window_cone (c : Nat → Bool) (Q n t : Nat) (ht : t < twopow (n + 1)) :
    transportWindow (drivenEnd c) (Q * twopow n) t 0 =
      bxor (bxor (drivenCone c (t + Q * twopow n)) (drivenCone c t))
        (pascalParity Q 1 && drivenDepth c t (twopow n)) := by
  have hpos := Rule30UOR.Scale.twopow_pos n
  have h2 : twopow (n + 1) = 2 * twopow n := by rw [twopow_succ]; cfomega
  have h := transport_add_lucas (drivenEnd c) Q n t 0
  have e1 : xorBelow (fun i => pascalParity Q i && transport (drivenEnd c) t (0 + twopow n * i)) (Q + 1) =
      xorBelow (fun i => pascalParity Q i && transport (drivenEnd c) t (0 + twopow n * i)) (Q + 1 + 1) := by
    show _ = bxor _ (pascalParity Q (Q + 1) && transport (drivenEnd c) t (0 + twopow n * (Q + 1)))
    rw [pascalParity_gt Q (Q + 1) (by cfomega), Bool.false_and, cone_bxor_false_right]
  have e2 := xorBelow_of_vanish (fun i => pascalParity Q i && transport (drivenEnd c) t (0 + twopow n * i))
    2 (Q + 1 + 1)
    (fun j hj _ => by
      show (pascalParity Q j && transport (drivenEnd c) t (0 + twopow n * j)) = false
      have hm := Nat.mul_le_mul_left (twopow n) hj
      rw [transport_drivenEnd_beyond c t _ (by cfomega), Bool.and_false])
    (Q + 1 + 1) (by cfomega) (Nat.le_refl _)
  have hlin : xorBelow (fun i => pascalParity Q i && transport (drivenEnd c) t (0 + twopow n * i)) (Q + 1) =
      bxor (drivenCone c t) (pascalParity Q 1 && drivenDepth c t (twopow n)) := by
    rw [e1, e2]
    show bxor (bxor false (pascalParity Q 0 && transport (drivenEnd c) t (0 + twopow n * 0)))
        (pascalParity Q 1 && transport (drivenEnd c) t (0 + twopow n * 1)) =
      bxor (transport (drivenEnd c) t 0) (pascalParity Q 1 && drivenDepth c t (twopow n))
    rw [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.zero_add, pascalParity_zero_right, Bool.true_and,
      cone_bxor_false, transport_drivenEnd_eq c t (twopow n) hpos]
  rw [hlin] at h
  show _ = bxor (bxor (transport (drivenEnd c) (t + Q * twopow n) 0) (drivenCone c t)) _
  rw [h]
  cases drivenCone c t <;> cases (pascalParity Q 1 && drivenDepth c t (twopow n)) <;>
    cases transportWindow (drivenEnd c) (Q * twopow n) t 0 <;> rfl

/-- A boundary column with period `P` from time `T`. -/
def PeriodFrom (c : Nat → Bool) (T P : Nat) : Prop := ∀ s, T ≤ s → c (s + P) = c s

/-- **What a period forces on the driven sources, read through Lucas**: for a black-time-consistent
boundary with period `P` from `T`, before time `2^(n+1)` the window of length `P·2^n` read at
column `0` is the edge term `C(P, 1)·(column −2^n)` alone. -/
theorem driven_window_of_periodic (c : Nat → Bool) (h0 : c 0 = true) (hb : BlackTimeConsistent c)
    (T P n t : Nat) (hper : PeriodFrom c T P) (hT : T ≤ t) (ht : t < twopow (n + 1)) :
    transportWindow (drivenEnd c) (P * twopow n) t 0 = (pascalParity P 1 && drivenDepth c t (twopow n)) := by
  have hc := (driven_cone_iff_btc c h0).mpr hb
  have hp := Ruliology.CellularAutomata.Rule30Jen.periodic_mul (f := c) (T := T) (P := P) hper (twopow n) t hT
  have hpq : c (t + P * twopow n) = c t := by rw [Nat.mul_comm]; exact hp
  have e1 : drivenCone c (t + P * twopow n) = drivenCone c t := by
    have a1 := hc (t + P * twopow n)
    have a2 := hc t
    rw [hpq, a2] at a1
    revert a1
    cases drivenCone c t <;> cases drivenCone c (t + P * twopow n) <;> decide
  rw [driven_window_cone c P n t ht, e1]
  cases drivenCone c t <;> cases (pascalParity P 1 && drivenDepth c t (twopow n)) <;> rfl

/-- Under a period, the driven window of length `P·2^n` is white on `[T, 2^n)`. -/
theorem driven_window_white (c : Nat → Bool) (h0 : c 0 = true) (hb : BlackTimeConsistent c)
    (T P n t : Nat) (hper : PeriodFrom c T P) (hT : T ≤ t) (ht : t < twopow n) :
    transportWindow (drivenEnd c) (P * twopow n) t 0 = false := by
  have h2 : twopow (n + 1) = 2 * twopow n := by rw [twopow_succ]; cfomega
  rw [driven_window_of_periodic c h0 hb T P n t hper hT (by cfomega), drivenDepth_beyond c t (twopow n) ht,
    Bool.and_false]

/-- Under a period from `T ≤ 2^n`, the driven window of length `P·2^n` at time `2^n` is the black
edge weighted by `C(P, 1)`. -/
theorem driven_window_edge (c : Nat → Bool) (h0 : c 0 = true) (hb : BlackTimeConsistent c)
    (T P n : Nat) (hper : PeriodFrom c T P) (hT : T ≤ twopow n) :
    transportWindow (drivenEnd c) (P * twopow n) (twopow n) 0 = pascalParity P 1 := by
  have hpos := Rule30UOR.Scale.twopow_pos n
  have h2 : twopow (n + 1) = 2 * twopow n := by rw [twopow_succ]; cfomega
  rw [driven_window_of_periodic c h0 hb T P n (twopow n) hper hT (by cfomega), drivenDepth_edge, h0,
    Bool.and_true]

/-! ## First-order forms -/

/-- The Lucas part of the transport at the lag `Q·2^n`: the state at time `t` at the depths
`a + 2^n·i`, weighted by `C(Q, i)`. -/
def lucasPart (S : Nat → Nat → Bool) (Q n t a : Nat) : Bool :=
  xorBelow (fun i => pascalParity Q i && transport S t (a + twopow n * i)) (Q + 1)

/-- Every transport at the lag `Q·2^n` is its Lucas part plus the window of the lag. -/
def TransportAddLucas : Prop :=
  ∀ (S : Nat → Nat → Bool) (Q n t a : Nat),
    transport S (t + Q * twopow n) a = bxor (lucasPart S Q n t a) (transportWindow S (Q * twopow n) t a)

theorem transportAddLucas : TransportAddLucas := transport_add_lucas

/-- Every transport on the lattice of scale `2^n` is the transport of its block windows. -/
def TransportBlockLucas : Prop :=
  ∀ (S : Nat → Nat → Bool) (n m A : Nat),
    transport S (twopow n * m) (twopow n * A) = transport (blockWindow S n) m A

theorem transportBlockLucas : TransportBlockLucas := transport_block_lucas

/-- The window of the driven sources of the times `[t, t + N)`, read at column `0`. -/
def drivenWindow (c : Nat → Bool) (N t : Nat) : Bool := transportWindow (drivenEnd c) N t 0

/-- For every boundary, before time `2^(n+1)` the driven window of length `Q·2^n` is the cone
increment plus `C(Q, 1)` times column `−2^n`. -/
def DrivenWindowCone : Prop :=
  ∀ (c : Nat → Bool) (Q n t : Nat), t < twopow (n + 1) →
    drivenWindow c (Q * twopow n) t =
      bxor (bxor (drivenCone c (t + Q * twopow n)) (drivenCone c t)) (pascalParity Q 1 && drivenDepth c t (twopow n))

theorem drivenWindowCone : DrivenWindowCone := driven_window_cone

/-- For every black-time-consistent boundary with `c 0 = true` and a period `P` from `T`, the driven
window of length `P·2^n` at a time `T ≤ t < 2^(n+1)` is `C(P, 1)` times column `−2^n`. -/
def DrivenWindowOfPeriod : Prop :=
  ∀ (c : Nat → Bool), c 0 = true → BlackTimeConsistent c → ∀ (T P n t : Nat), PeriodFrom c T P → T ≤ t →
    t < twopow (n + 1) → drivenWindow c (P * twopow n) t = (pascalParity P 1 && drivenDepth c t (twopow n))

theorem drivenWindowOfPeriod : DrivenWindowOfPeriod := driven_window_of_periodic

/-- Under a period from `T`, the driven window of length `P·2^n` is white on `[T, 2^n)`. -/
def DrivenWindowWhite : Prop :=
  ∀ (c : Nat → Bool), c 0 = true → BlackTimeConsistent c → ∀ (T P n t : Nat), PeriodFrom c T P → T ≤ t →
    t < twopow n → drivenWindow c (P * twopow n) t = false

theorem drivenWindowWhite : DrivenWindowWhite := driven_window_white

/-- Under a period from `T ≤ 2^n`, the driven window of length `P·2^n` at time `2^n` is `C(P, 1)`. -/
def DrivenWindowEdge : Prop :=
  ∀ (c : Nat → Bool), c 0 = true → BlackTimeConsistent c → ∀ (T P n : Nat), PeriodFrom c T P →
    T ≤ twopow n → drivenWindow c (P * twopow n) (twopow n) = pascalParity P 1

theorem drivenWindowEdge : DrivenWindowEdge := driven_window_edge

end Rule30UOR.DrivenLucas
