module

public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30SpacingRenormalization

/-!
# Packed prefixes of the alternating-driven right half

The packed update represents spatial cells at positions 1,2,..., in low to
high bits. The prefix agreement lemmas retain the exact dependence on the
unrepresented tail. No finite-prefix observation is assumed to be invariant.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DrivenPrefix

open Rule30Jen Rule30Ether Rule30PeriodTwoCoupled Rule30PeriodTwoSideways

def step (b : Bool) (a : Nat) : Nat :=
  ((a <<< 1) ||| b.toNat) ^^^ (a ||| (a >>> 1))

theorem step_bit (b : Bool) (a j : Nat) :
    (step b a).testBit j = xor (if j=0 then b else a.testBit (j-1))
      (a.testBit j || a.testBit (j+1)) := by
  simp only [step,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight,Nat.testBit_bool_toNat]
  cases j <;> simp [Nat.add_comm]

theorem step_agree (b : Bool) {a c k : Nat}
    (h : ∀ j, j<k+1 → a.testBit j=c.testBit j) :
    ∀ j, j<k → (step b a).testBit j=(step b c).testBit j := by
  intro j hj
  rw [step_bit,step_bit,h j (by omega),h (j+1) (by omega)]
  by_cases h0 : j=0
  · simp [h0]
  · simp [h0,h (j-1) (by omega)]

def packed (c : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => step (c t) (packed c a t)

theorem packed_sound (c R : Nat → Bool) (a : Nat)
    (ha : ∀ j, a.testBit j=R (j+1)) : ∀ t j,
    (packed c a t).testBit j=drv c R t (j+1) := by
  intro t
  induction t with
  | zero => intro j; simpa [packed,drv] using ha j
  | succ t ih =>
      intro j
      rw [packed,step_bit]
      cases j with
      | zero => simp [drv,rule,ih,drv_col0]
      | succ j => simp [drv,rule,ih,Nat.add_assoc]

def double (a : Nat) : Nat := step true (step false a)

def white : Nat → Nat
  | 0 => 1
  | n+1 => double (white n)

theorem packed_white : ∀ n, packed altCol 0 (2*n+1)=white n
  | 0 => by decide
  | n+1 => by
      rw [show 2*(n+1)+1=(2*n+1+1)+1 by omega,packed,packed]
      rw [show 2*n+1+1=2*(n+1) by omega,altCol_even,altCol_odd,packed_white]
      rfl

theorem white_sound (n j : Nat) :
    (white n).testBit j=drv altCol empty (2*n+1) (j+1) := by
  rw [← packed_white]
  exact packed_sound altCol empty 0 (by intro j; simp [empty]) (2*n+1) j

theorem white_gate (n : Nat) : (white n).testBit 0=u empty n := white_sound n 0

theorem double_agree {a c k : Nat}
    (h : ∀ j, j<k+2 → a.testBit j=c.testBit j) :
    ∀ j, j<k → (double a).testBit j=(double c).testBit j := by
  exact step_agree true (step_agree false (by intro j hj; exact h j (by omega)))

def iterate (a : Nat) : Nat → Nat
  | 0 => a
  | n+1 => double (iterate a n)

theorem iterate_agree : ∀ n {a c k : Nat},
    (∀ j, j<k+2*n → a.testBit j=c.testBit j) →
    ∀ j, j<k → (iterate a n).testBit j=(iterate c n).testBit j
  | 0,a,c,k,h => by simpa [iterate] using h
  | n+1,a,c,k,h => by
      apply double_agree
      apply iterate_agree n
      intro j hj
      exact h j (by omega)

theorem iterate_white (r n : Nat) : iterate (white r) n=white (r+n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate,ih,show r+(n+1)=(r+n)+1 by omega,white]

theorem double_prefix (a k : Nat) : double a % 2^k=double (a % 2^(k+2)) % 2^k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and]
    apply double_agree (k:=k)
    · intro i hi
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    · exact hj
  · simp [hj]

theorem iterate_mod_bit (a k n j : Nat) (hj : j+2*n<k) :
    (iterate (a % 2^k) n).testBit j=(iterate a n).testBit j := by
  apply iterate_agree n (k:=j+1)
  · intro i hi
    rw [Nat.testBit_mod_two_pow]
    simp [show i<k by omega]
  · omega

/-- The local gate window needed for exact spacings three or five. -/
def Window (f : Nat → Bool) (r : Nat) : Prop :=
  (f r && f (r+1))=false ∧ (f r && f (r+2))=false ∧
  (f r=true →
    (f (r+3)=true ∧ f (r+4)=false ∧ f (r+5)=false) ∨
    (f (r+3)=false ∧ f (r+4)=false ∧ f (r+5)=true)) ∧
  (f r || f (r+1) || f (r+2) || f (r+3) || f (r+4) || f (r+5))=true

instance (f : Nat → Bool) (r : Nat) : Decidable (Window f r) := inferInstanceAs
  (Decidable ((f r && f (r+1))=false ∧ (f r && f (r+2))=false ∧
  (f r=true →
    (f (r+3)=true ∧ f (r+4)=false ∧ f (r+5)=false) ∨
    (f (r+3)=false ∧ f (r+4)=false ∧ f (r+5)=true)) ∧
  (f r || f (r+1) || f (r+2) || f (r+3) || f (r+4) || f (r+5))=true))

def Observe (a : Nat) : Prop := Window (fun n => (iterate a n).testBit 0) 0

instance (a : Nat) : Decidable (Observe a) := inferInstanceAs
  (Decidable (Window (fun n => (iterate a n).testBit 0) 0))

theorem observe_trim (a : Nat) : Observe (a % 2^18) ↔ Observe a := by
  simp only [Observe,Window,Nat.zero_add]
  rw [iterate_mod_bit a 18 0 0 (by decide),iterate_mod_bit a 18 1 0 (by decide),
    iterate_mod_bit a 18 2 0 (by decide),iterate_mod_bit a 18 3 0 (by decide),
    iterate_mod_bit a 18 4 0 (by decide),iterate_mod_bit a 18 5 0 (by decide)]

end Ruliology.CellularAutomata.Rule30DrivenPrefix
