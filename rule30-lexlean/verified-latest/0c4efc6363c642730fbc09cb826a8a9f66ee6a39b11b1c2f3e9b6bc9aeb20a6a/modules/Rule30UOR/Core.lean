module
public import Init
public import LexLeanRuntime.Portable
public import LexLeanRuntime.Collections
public import LexLeanRuntime.Laws
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
set_option linter.constructorNameAsVariable false
namespace Rule30UOR.Core

@[expose] public def bxor (a : Bool) (b : Bool) : Bool := (if a then (!b) else b)

@[expose] public def rule (a : Bool) (b : Bool) (c : Bool) : Bool := bxor (a) ((b || c))

@[expose] public def rule90 (a : Bool) (_b : Bool) (c : Bool) : Bool := bxor (a) (c)

@[expose] public def rule150 (a : Bool) (b : Bool) (c : Bool) : Bool := bxor (bxor (a) (b)) (c)

@[expose] public def rule210 (a : Bool) (b : Bool) (c : Bool) : Bool := bxor (a) (((!b) && c))

public theorem barrier_plane : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (rule (a) (b) (c) = bxor (bxor (rule90 (a) (b) (c)) (rule150 (a) (b) (c))) (rule210 (a) (b) (c)))))) := by
  decide

public theorem left_permutive : (forall (b : Bool), (forall (c : Bool), (rule (true) (b) (c) = (!rule (false) (b) (c))))) := by
  decide

@[expose] public def cell : (t : Nat) -> (p : Int) -> Bool
  | Nat.zero, p => ((!(LexLeanCollections.lessThan (p) ((0 : Int)) : Bool)) && (!(LexLeanCollections.lessThan ((0 : Int)) (p) : Bool)))
  | Nat.succ s, p => rule (cell (s) ((LexLeanRuntime.subtract (p) ((1 : Int)) : Int))) (cell (s) (p)) (cell (s) ((LexLeanRuntime.subtract (p) ((-1 : Int)) : Int)))

@[expose] public def center (t : Nat) : Bool := cell (t) ((0 : Int))

public theorem center_prefix : ((center (0) = true) /\ ((center (1) = true) /\ ((center (2) = false) /\ (center (3) = true)))) := by
  decide

@[expose] public def leftOf (p : Int) : Int := (LexLeanRuntime.subtract (p) ((1 : Int)) : Int)

@[expose] public def rightOf (p : Int) : Int := (LexLeanRuntime.subtract (p) ((-1 : Int)) : Int)

public theorem cell_succ (t : Nat) (p : Int) : (cell (Nat.succ (t)) (p) = rule (cell (t) (leftOf (p))) (cell (t) (p)) (cell (t) (rightOf (p)))) := by
  rfl

public theorem rule_black_black : (forall (c : Bool), (rule (true) (true) (c) = false)) := by
  decide

public theorem rule_white_white : (forall (a : Bool), (rule (a) (false) (false) = a)) := by
  decide

public theorem rule_left_edge_of_white_pair : (forall (c : Bool), (rule (false) (false) (c) = c)) := by
  decide

public theorem rule_reset : (forall (a : Bool), (forall (c : Bool), (rule (a) (true) (c) = (!a)))) := by
  decide

@[expose] public def ldiag : (j : Nat) -> (t : Nat) -> Bool
  | j, Nat.zero => (match j with | Nat.zero => true | Nat.succ _ => false)
  | j, Nat.succ s => (match j with | Nat.zero => true | Nat.succ i => (match i with | Nat.zero => true | Nat.succ k => bxor (ldiag (k) (s)) ((ldiag (Nat.succ (k)) (s) || ldiag (Nat.succ (Nat.succ (k))) (s)))))

@[expose] public def lcenter (t : Nat) : Bool := ldiag (t) (t)

public theorem ldiag_step (k : Nat) (s : Nat) : (ldiag (Nat.succ (Nat.succ (k))) (Nat.succ (s)) = bxor (ldiag (k) (s)) ((ldiag (Nat.succ (k)) (s) || ldiag (Nat.succ (Nat.succ (k))) (s)))) := by
  rfl

public theorem ldiag_zero (s : Nat) : (ldiag (0) (Nat.succ (s)) = true) := by
  rfl

public theorem ldiag_one (s : Nat) : (ldiag (1) (Nat.succ (s)) = true) := by
  rfl

@[expose] public def rdiag : (j : Nat) -> (t : Nat) -> Bool
  | j, Nat.zero => (match j with | Nat.zero => true | Nat.succ _ => false)
  | j, Nat.succ s => (match j with | Nat.zero => true | Nat.succ i => (match i with | Nat.zero => (!rdiag (Nat.succ (i)) (s)) | Nat.succ k => bxor (rdiag (Nat.succ (Nat.succ (k))) (s)) ((rdiag (Nat.succ (k)) (s) || rdiag (k) (s)))))

@[expose] public def rcenter (t : Nat) : Bool := rdiag (t) (t)

public theorem rdiag_step (k : Nat) (s : Nat) : (rdiag (Nat.succ (Nat.succ (k))) (Nat.succ (s)) = bxor (rdiag (Nat.succ (Nat.succ (k))) (s)) ((rdiag (Nat.succ (k)) (s) || rdiag (k) (s)))) := by
  rfl

public theorem rdiag_zero (s : Nat) : (rdiag (0) (Nat.succ (s)) = true) := by
  rfl

public theorem rdiag_one (s : Nat) : (rdiag (1) (Nat.succ (s)) = (!rdiag (1) (s))) := by
  rfl

@[expose] public def rule60 (a : Bool) (b : Bool) (_c : Bool) : Bool := bxor (a) (b)

@[expose] public def rule15 (a : Bool) (_b : Bool) (_c : Bool) : Bool := (!a)

public theorem split150 : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (rule (a) (b) (c) = bxor (rule150 (a) (b) (c)) ((b && c)))))) := by
  decide

public theorem split90 : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (rule (a) (b) (c) = bxor (rule90 (a) (b) (c)) ((b && (!c))))))) := by
  decide

public theorem split60 : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (rule (a) (b) (c) = bxor (rule60 (a) (b) (c)) (((!b) && c)))))) := by
  decide

public theorem split15 : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (rule (a) (b) (c) = bxor (rule15 (a) (b) (c)) (((!b) && (!c))))))) := by
  decide

public theorem carries_cover : (forall (b : Bool), (forall (c : Bool), ((((b && c) || (b && (!c))) || (((!b) && c) || ((!b) && (!c)))) = true))) := by
  decide

public theorem carries_orthogonal : (forall (b : Bool), (forall (c : Bool), (((((b && c) && (b && (!c))) = false) /\ ((((b && c) && ((!b) && c)) = false) /\ (((b && c) && ((!b) && (!c))) = false))) /\ (((((b && (!c)) && ((!b) && c)) = false) /\ (((b && (!c)) && ((!b) && (!c))) = false)) /\ ((((!b) && c) && ((!b) && (!c))) = false))))) := by
  decide

@[expose] public def aff (u0 : Bool) (u1 : Bool) (u2 : Bool) (u3 : Bool) (a : Bool) (b : Bool) (c : Bool) : Bool := bxor (u0) (bxor ((u1 && a)) (bxor ((u2 && b)) ((u3 && c))))

@[expose] public def miss (u0 : Bool) (u1 : Bool) (u2 : Bool) (u3 : Bool) (a : Bool) (b : Bool) (c : Bool) : Nat := (if bxor (rule (a) (b) (c)) (aff (u0) (u1) (u2) (u3) (a) (b) (c)) then 1 else 0)

@[expose] public def dist30 (u0 : Bool) (u1 : Bool) (u2 : Bool) (u3 : Bool) : Nat := (((miss (u0) (u1) (u2) (u3) (false) (false) (false) + miss (u0) (u1) (u2) (u3) (false) (false) (true)) + (miss (u0) (u1) (u2) (u3) (false) (true) (false) + miss (u0) (u1) (u2) (u3) (false) (true) (true))) + ((miss (u0) (u1) (u2) (u3) (true) (false) (false) + miss (u0) (u1) (u2) (u3) (true) (false) (true)) + (miss (u0) (u1) (u2) (u3) (true) (true) (false) + miss (u0) (u1) (u2) (u3) (true) (true) (true))))

public theorem deep_hole : (forall (u0 : Bool), (forall (u1 : Bool), (forall (u2 : Bool), (forall (u3 : Bool), (2 <= dist30 (u0) (u1) (u2) (u3)))))) := by
  decide

public theorem nearest_affine : (((dist30 (false) (true) (true) (true) = 2) /\ (dist30 (false) (true) (false) (true) = 2)) /\ ((dist30 (false) (true) (true) (false) = 2) /\ (dist30 (true) (true) (false) (false) = 2))) := by
  decide

@[expose] public def carry60 (s : Nat) (p : Int) : Bool := ((!cell (s) (p)) && cell (s) ((LexLeanRuntime.subtract (p) ((-1 : Int)) : Int)))

@[expose] public def window60 : (t0 : Nat) -> (n : Nat) -> (p : Int) -> Bool
  | _t0, Nat.zero, _p => false
  | t0, Nat.succ m, p => bxor (bxor (window60 (t0) (m) ((LexLeanRuntime.subtract (p) ((1 : Int)) : Int))) (window60 (t0) (m) (p))) (carry60 ((t0 + m)) (p))

@[expose] public def twopow : (k : Nat) -> Nat
  | Nat.zero => 1
  | Nat.succ j => (twopow (j) + twopow (j))

public theorem window60_step (t0 : Nat) (m : Nat) (p : Int) : (window60 (t0) (Nat.succ (m)) (p) = bxor (bxor (window60 (t0) (m) ((LexLeanRuntime.subtract (p) ((1 : Int)) : Int))) (window60 (t0) (m) (p))) (carry60 ((t0 + m)) (p))) := by
  rfl

public theorem twopow_succ (j : Nat) : (twopow (Nat.succ (j)) = (twopow (j) + twopow (j))) := by
  rfl

@[expose] public def displacement (a : Bool) (b : Bool) (c : Bool) : Bool := bxor (rule (a) (b) (c)) (rule150 (a) (b) (c))

public theorem displacement_is_carry : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (displacement (a) (b) (c) = (b && c))))) := by
  decide

public theorem frame_direction : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (displacement ((!a)) (b) (c) = displacement (a) (b) (c))))) := by
  decide

public theorem affine_left_linear : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (rule150 ((!a)) (b) (c) = (!rule150 (a) (b) (c)))))) := by
  decide

public theorem nearest_exactly : (forall (u0 : Bool), (forall (u1 : Bool), (forall (u2 : Bool), (forall (u3 : Bool), ((dist30 (u0) (u1) (u2) (u3) = 2) -> (((((!u0) && (u1 && (u2 && u3))) || ((!u0) && (u1 && ((!u2) && u3)))) || (((!u0) && (u1 && (u2 && (!u3)))) || (u0 && (u1 && ((!u2) && (!u3)))))) = true)))))) := by
  decide

@[expose] public def ldrem : (b : Nat) -> (r : Nat) -> (t : Nat) -> Nat
  | _b, r, Nat.zero => r
  | b, r, Nat.succ s => (if (LexLeanCollections.lessThan ((ldrem (b) (r) (s) + ldrem (b) (r) (s))) (b) : Bool) then (ldrem (b) (r) (s) + ldrem (b) (r) (s)) else (LexLeanRuntime.subtract ((ldrem (b) (r) (s) + ldrem (b) (r) (s))) (b) : Nat))

@[expose] public def lddig (b : Nat) (r : Nat) (t : Nat) : Bool := (!(LexLeanCollections.lessThan ((ldrem (b) (r) (t) + ldrem (b) (r) (t))) (b) : Bool))

@[expose] public def sgn (x : Bool) : Int := (if x then (-1 : Int) else (1 : Int))

@[expose] public def iadd (x : Int) (y : Int) : Int := (LexLeanRuntime.subtract (x) ((LexLeanRuntime.negate (y) : Int)) : Int)

public theorem frame_projection : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (iadd (sgn (rule (a) (b) (c))) (sgn (rule (a) (b) (c))) = iadd (iadd (sgn (rule150 (a) (b) (c))) (sgn (rule90 (a) (b) (c)))) (iadd (sgn (rule60 (a) (b) (c))) (sgn (rule15 (a) (b) (c)))))))) := by
  decide

@[expose] public def dissent (a : Bool) (b : Bool) (c : Bool) : Nat := (((if bxor (rule (a) (b) (c)) (rule150 (a) (b) (c)) then 1 else 0) + (if bxor (rule (a) (b) (c)) (rule90 (a) (b) (c)) then 1 else 0)) + ((if bxor (rule (a) (b) (c)) (rule60 (a) (b) (c)) then 1 else 0) + (if bxor (rule (a) (b) (c)) (rule15 (a) (b) (c)) then 1 else 0)))

public theorem one_dissent : (forall (a : Bool), (forall (b : Bool), (forall (c : Bool), (dissent (a) (b) (c) = 1)))) := by
  decide

@[expose] public def corr (u0 : Bool) (u1 : Bool) (u2 : Bool) (u3 : Bool) (v0 : Bool) (v1 : Bool) (v2 : Bool) (v3 : Bool) : Int := iadd (iadd (iadd ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (false) (false) (false))) (sgn (aff (v0) (v1) (v2) (v3) (false) (false) (false))) : Int)) ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (false) (false) (true))) (sgn (aff (v0) (v1) (v2) (v3) (false) (false) (true))) : Int))) (iadd ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (false) (true) (false))) (sgn (aff (v0) (v1) (v2) (v3) (false) (true) (false))) : Int)) ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (false) (true) (true))) (sgn (aff (v0) (v1) (v2) (v3) (false) (true) (true))) : Int)))) (iadd (iadd ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (true) (false) (false))) (sgn (aff (v0) (v1) (v2) (v3) (true) (false) (false))) : Int)) ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (true) (false) (true))) (sgn (aff (v0) (v1) (v2) (v3) (true) (false) (true))) : Int))) (iadd ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (true) (true) (false))) (sgn (aff (v0) (v1) (v2) (v3) (true) (true) (false))) : Int)) ((LexLeanRuntime.multiply (sgn (aff (u0) (u1) (u2) (u3) (true) (true) (true))) (sgn (aff (v0) (v1) (v2) (v3) (true) (true) (true))) : Int))))

public theorem frame_orthogonal : (forall (u0 : Bool), (forall (u1 : Bool), (forall (u2 : Bool), (forall (u3 : Bool), (forall (v0 : Bool), (forall (v1 : Bool), (forall (v2 : Bool), (forall (v3 : Bool), (((bxor (u1) (v1) || (bxor (u2) (v2) || bxor (u3) (v3))) = true) -> (corr (u0) (u1) (u2) (u3) (v0) (v1) (v2) (v3) = (0 : Int))))))))))) := by
  decide

public theorem bxor_reset : (forall (a : Bool), (forall (c : Bool), (bxor (a) ((true || c)) = (!a)))) := by
  decide

public theorem bxor_toggle : (forall (a : Bool), (forall (c : Bool), (bxor (a) ((false || c)) = bxor (a) (c)))) := by
  decide

public theorem rule_toggle : (forall (a : Bool), (forall (c : Bool), (rule (a) (false) (c) = bxor (a) (c)))) := by
  decide

@[expose] public def phi (y : Nat) : Nat := (Nat.xor (y) ((Nat.lor ((Nat.shiftLeft (y) (1) : Nat)) ((Nat.shiftLeft (y) (2) : Nat)) : Nat)) : Nat)

@[expose] public def carry (y : Nat) : Nat := (Nat.land (y) ((Nat.shiftLeft (y) (1) : Nat)) : Nat)

@[expose] public def phiLinear (y : Nat) : Nat := (Nat.xor ((Nat.xor (y) ((Nat.shiftLeft (y) (1) : Nat)) : Nat)) ((Nat.shiftLeft (y) (2) : Nat)) : Nat)

public theorem phi_split (y : Nat) : (phi (y) = (Nat.xor (phiLinear (y)) ((Nat.shiftLeft (carry (y)) (1) : Nat)) : Nat)) := by
  exact @LexLeanLaws.nat_witt_step (y)

public theorem or_witt_split (a : Nat) (b : Nat) : ((Nat.lor (a) (b) : Nat) = (Nat.xor ((Nat.xor (a) (b) : Nat)) ((Nat.land (a) (b) : Nat)) : Nat)) := by
  exact @LexLeanLaws.nat_or_xor_and (a) (b)

@[expose] public def bit (n : Nat) (k : Nat) : Nat := (LexLeanRuntime.remainder ((Nat.shiftRight (n) (k) : Nat)) (2) (0) : Nat)

public theorem bit_and_law (a : Nat) (b : Nat) (k : Nat) : (bit ((Nat.land (a) (b) : Nat)) (k) = (Nat.land (bit (a) (k)) (bit (b) (k)) : Nat)) := by
  exact @LexLeanLaws.nat_bit_and (a) (b) (k)

public theorem bit_or_law (a : Nat) (b : Nat) (k : Nat) : (bit ((Nat.lor (a) (b) : Nat)) (k) = (Nat.lor (bit (a) (k)) (bit (b) (k)) : Nat)) := by
  exact @LexLeanLaws.nat_bit_or (a) (b) (k)

public theorem bit_xor_law (a : Nat) (b : Nat) (k : Nat) : (bit ((Nat.xor (a) (b) : Nat)) (k) = (Nat.xor (bit (a) (k)) (bit (b) (k)) : Nat)) := by
  exact @LexLeanLaws.nat_bit_xor (a) (b) (k)

public theorem bit_shift_right_law (a : Nat) (m : Nat) (k : Nat) : (bit ((Nat.shiftRight (a) (m) : Nat)) (k) = bit (a) ((m + k))) := by
  exact @LexLeanLaws.nat_bit_shift_right (a) (m) (k)

public theorem bit_shift_left_law (a : Nat) (m : Nat) (k : Nat) : (bit ((Nat.shiftLeft (a) (m) : Nat)) ((m + k)) = bit (a) (k)) := by
  exact @LexLeanLaws.nat_bit_shift_left (a) (m) (k)

@[expose] public def row : (t : Nat) -> Nat
  | Nat.zero => 1
  | Nat.succ s => phi (row (s))

@[expose] public def rowCenter (t : Nat) : Nat := bit (row (t)) (t)

public theorem row_center_prefix : ((rowCenter (0) = 1) /\ ((rowCenter (1) = 1) /\ ((rowCenter (2) = 0) /\ (rowCenter (3) = 1)))) := by
  decide

@[expose] public def phiLinearPow : (n : Nat) -> (y : Nat) -> Nat
  | Nat.zero, y => y
  | Nat.succ m, y => phiLinear (phiLinearPow (m) (y))

public theorem phiLinearPow_step (m : Nat) (y : Nat) : (phiLinearPow (Nat.succ (m)) (y) = phiLinear (phiLinearPow (m) (y))) := by
  rfl

@[expose] public def phiScale (k : Nat) (y : Nat) : Nat := (Nat.xor ((Nat.xor (y) ((Nat.shiftLeft (y) (twopow (k)) : Nat)) : Nat)) ((Nat.shiftLeft (y) ((twopow (k) + twopow (k))) : Nat)) : Nat)

@[expose] public def winWitt : (t0 : Nat) -> (n : Nat) -> Nat
  | _t0, Nat.zero => 0
  | t0, Nat.succ m => (Nat.xor (phiLinear (winWitt (t0) (m))) ((Nat.shiftLeft (carry (row ((t0 + m)))) (1) : Nat)) : Nat)

public theorem winWitt_step (t0 : Nat) (m : Nat) : (winWitt (t0) (Nat.succ (m)) = (Nat.xor (phiLinear (winWitt (t0) (m))) ((Nat.shiftLeft (carry (row ((t0 + m)))) (1) : Nat)) : Nat)) := by
  rfl

@[expose] public def wittResponse (t : Nat) (k : Nat) : Nat := bit (winWitt (t) (twopow (k))) ((t + twopow (k)))

end Rule30UOR.Core
