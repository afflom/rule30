module

public import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap0
public import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap1
public import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap2
public import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap3
public import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap4
public import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap5

/-!
# The pure-ether strip lies in no trap of width `≤ 20`

For each of the words `0001`, `0011`, `0111`, each ether alignment `(j₀, s)` of the word
(`Rule30Ether.A0001`, `A0011`, `A0111`), each phase `φ < 4` and each width `1 ≤ b ≤ 20`: every set of
strip nodes closed under every input that contains the pure-ether node
`(φ, etherRow j₀ ((φ + s) % 4) b)` contains a path whose column `1` at the white phases is not
eventually periodic (`pure_ether_escapes_*`). Hence no trap of width `≤ 20` contains the pure-ether
node (`pure_ether_not_in_trap_*`). The theorems live in the namespace `Rule30EtherTrap`; the
`24` certificates are in `Rule30Certificates.EtherTrap0` – `EtherTrap5`.

This concerns the strip relaxation, where column `b + 1` is arbitrary. It says nothing about
whether the true right half reaches the pure ether, and absorption remains open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherTrap

open Rule30Ether Rule30StripCertificates

/-- From a width-`20` certificate to every width `1 ≤ b ≤ 20`. -/
theorem escape_of_cert20 (w : List Bool) (j0 s φ : Nat) (P A B : List Bool) (j0w : Nat)
    (hc : certOK w (φ, etherRow j0 ((φ + s) % 4) 20) P A B j0w = true)
    (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Closed w T)
    (hx : T (φ, etherRow j0 ((φ + s) % 4) b)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w (φ, etherRow j0 ((φ + s) % 4) b) u n)) ∧
      ¬ MaskedPer w (traj w (φ, etherRow j0 ((φ + s) % 4) b) u) := by
  rcases Nat.lt_or_ge b 20 with h | h
  · obtain ⟨u, -, hu⟩ := escapes_of_certOK w _ P A B j0w hc (fun _ => True) (fun _ _ _ => trivial) trivial
    have e : etherRow j0 ((φ + s) % 4) b = (etherRow j0 ((φ + s) % 4) 20).take b := by
      unfold etherRow; rw [take_seg _ _ _ (by omega)]
    rw [e] at hx ⊢
    exact escapes_take w b hb1 (φ, etherRow j0 ((φ + s) % 4) 20)
      (by unfold etherRow; rw [length_seg]; exact h) u hu T hT hx
  · rw [show b = 20 by omega] at hx ⊢
    exact escapes_of_certOK w _ P A B j0w hc T hT hx

/-- **`0001`: the pure ether escapes every closed set of width `≤ 20`.** -/
theorem pure_ether_escapes_0001 (a : Nat × Nat) (ha : a ∈ A0001) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Closed w0001 T)
    (hx : T (φ, etherRow a.1 ((φ + a.2) % 4) b)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w0001 (φ, etherRow a.1 ((φ + a.2) % 4) b) u n)) ∧
      ¬ MaskedPer w0001 (traj w0001 (φ, etherRow a.1 ((φ + a.2) % 4) b) u) := by
  simp only [A0001, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl
  · exact escape_of_cert20 w0001 5 0 0 _ _ _ _ cert_0001_5_0 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 5 0 1 _ _ _ _ cert_0001_5_1 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 5 0 2 _ _ _ _ cert_0001_5_2 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 5 0 3 _ _ _ _ cert_0001_5_3 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 6 0 0 _ _ _ _ cert_0001_6_0 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 6 0 1 _ _ _ _ cert_0001_6_1 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 6 0 2 _ _ _ _ cert_0001_6_2 b hb1 hb T hT hx
  · exact escape_of_cert20 w0001 6 0 3 _ _ _ _ cert_0001_6_3 b hb1 hb T hT hx

/-- **`0001`: no trap of width `≤ 20` contains a pure-ether node.** -/
theorem pure_ether_not_in_trap_0001 (a : Nat × Nat) (ha : a ∈ A0001) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w0001 T) :
    ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b) := by
  intro hx
  obtain ⟨u, -, hu⟩ := pure_ether_escapes_0001 a ha φ hφ b hb1 hb T hT.1 hx
  exact hu (hT.2 _ hx u)

/-- **`0011`: the pure ether escapes every closed set of width `≤ 20`.** -/
theorem pure_ether_escapes_0011 (a : Nat × Nat) (ha : a ∈ A0011) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Closed w0011 T)
    (hx : T (φ, etherRow a.1 ((φ + a.2) % 4) b)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w0011 (φ, etherRow a.1 ((φ + a.2) % 4) b) u n)) ∧
      ¬ MaskedPer w0011 (traj w0011 (φ, etherRow a.1 ((φ + a.2) % 4) b) u) := by
  simp only [A0011, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;>
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl
  · exact escape_of_cert20 w0011 0 0 0 _ _ _ _ cert_0011_0_0 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 0 0 1 _ _ _ _ cert_0011_0_1 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 0 0 2 _ _ _ _ cert_0011_0_2 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 0 0 3 _ _ _ _ cert_0011_0_3 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 1 3 0 _ _ _ _ cert_0011_1_0 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 1 3 1 _ _ _ _ cert_0011_1_1 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 1 3 2 _ _ _ _ cert_0011_1_2 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 1 3 3 _ _ _ _ cert_0011_1_3 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 4 0 0 _ _ _ _ cert_0011_4_0 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 4 0 1 _ _ _ _ cert_0011_4_1 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 4 0 2 _ _ _ _ cert_0011_4_2 b hb1 hb T hT hx
  · exact escape_of_cert20 w0011 4 0 3 _ _ _ _ cert_0011_4_3 b hb1 hb T hT hx

/-- **`0011`: no trap of width `≤ 20` contains a pure-ether node.** -/
theorem pure_ether_not_in_trap_0011 (a : Nat × Nat) (ha : a ∈ A0011) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w0011 T) :
    ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b) := by
  intro hx
  obtain ⟨u, -, hu⟩ := pure_ether_escapes_0011 a ha φ hφ b hb1 hb T hT.1 hx
  exact hu (hT.2 _ hx u)

/-- **`0111`: the pure ether escapes every closed set of width `≤ 20`.** -/
theorem pure_ether_escapes_0111 (a : Nat × Nat) (ha : a ∈ A0111) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Closed w0111 T)
    (hx : T (φ, etherRow a.1 ((φ + a.2) % 4) b)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w0111 (φ, etherRow a.1 ((φ + a.2) % 4) b) u n)) ∧
      ¬ MaskedPer w0111 (traj w0111 (φ, etherRow a.1 ((φ + a.2) % 4) b) u) := by
  simp only [A0111, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl <;>
    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl
  · exact escape_of_cert20 w0111 2 2 0 _ _ _ _ cert_0111_2_0 b hb1 hb T hT hx
  · exact escape_of_cert20 w0111 2 2 1 _ _ _ _ cert_0111_2_1 b hb1 hb T hT hx
  · exact escape_of_cert20 w0111 2 2 2 _ _ _ _ cert_0111_2_2 b hb1 hb T hT hx
  · exact escape_of_cert20 w0111 2 2 3 _ _ _ _ cert_0111_2_3 b hb1 hb T hT hx

/-- **`0111`: no trap of width `≤ 20` contains a pure-ether node.** -/
theorem pure_ether_not_in_trap_0111 (a : Nat × Nat) (ha : a ∈ A0111) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w0111 T) :
    ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b) := by
  intro hx
  obtain ⟨u, -, hu⟩ := pure_ether_escapes_0111 a ha φ hφ b hb1 hb T hT.1 hx
  exact hu (hT.2 _ hx u)

end Rule30EtherTrap
end Ruliology.CellularAutomata
