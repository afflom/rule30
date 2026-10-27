module

public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Rule 30: thirty periodic words excluded by bitmask strip certificates

Each entry `(n, bits, K, k)` of `certTable` is the word `wordOf n bits` of length `n` (the
binary digits of `bits`, most significant first) together with a strip width `K` and a number
`k` of warm-up periods for which the bitmask strip certificate
`Rule30StripCertificates.stripCert` holds. The kernel evaluates all thirty certificates
(`certTable_ok`), and soundness (`Rule30StripCertificates.not_eventually_word_strip`) gives:

* `not_eventually_certTable`: **for every entry, the center column is not eventually equal to
  the entry's word repeated**, whatever the transient and the phase.

The words, each written as its least rotation (the phase is absorbed into the transient):

* length 8: `01111111`;
* length 10: `0000000011`, `0011111111`, `0111111111`;
* length 11: `00000000001`, `00000000011`, `00111111111`, `01011111111`, `01111111111`;
* length 12: `000000000001`, `000000000011`, `000111111111`, `001111111111`, `010111111111`,
  `011111111111`;
* length 13: `0000000000001`, `0000000000011`, `0000000000101`, `0000000001011`,
  `0000000010011`, `0000000101111`, `0000111111111`, `0001011111111`, `0001111111111`,
  `0010111111111`, `0011111111101`, `0011111111111`, `0101111111111`, `0110111111111`,
  `0111111111111`.

They are the words that a search over lengths `8 … 13` certified at strip width `K ≤ 9`. Only the
certificates are checked here, not the completeness of that search.

Some of these also follow from general theorems: `0 1^k` with `k ≥ 9` from
`Rule30BlackRuns.not_eventually_zero_ones`, `0^r 1 1` with `r ≥ 10` from
`Rule30BlackRuns.no_white_run_11`.

The table was found by a search and is checked here by the kernel.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30StripCertificateTable

open Rule30Jen Rule30StripCertificates

/-- The word of length `n` spelled by the binary digits of `bits`, most significant first. -/
def wordOf (n bits : Nat) : List Bool := (List.range n).map fun i => bits.testBit (n - 1 - i)

theorem wordOf_length (n bits : Nat) : (wordOf n bits).length = n := by simp [wordOf]

/-- Entries `(n, bits, K, k)`: word length, word bits, strip width, warm-up periods. -/
def certTable : List (Nat × Nat × Nat × Nat) := [
    (8, 127, 5, 2),
    (10, 3, 9, 4),
    (10, 255, 8, 4),
    (10, 511, 5, 1),
    (11, 1, 8, 2),
    (11, 3, 6, 2),
    (11, 511, 5, 1),
    (11, 767, 5, 2),
    (11, 1023, 5, 1),
    (12, 1, 8, 2),
    (12, 3, 6, 2),
    (12, 511, 5, 1),
    (12, 1023, 5, 1),
    (12, 1535, 5, 1),
    (12, 2047, 5, 1),
    (13, 1, 8, 2),
    (13, 3, 6, 2),
    (13, 5, 9, 3),
    (13, 11, 6, 2),
    (13, 19, 9, 4),
    (13, 47, 6, 2),
    (13, 511, 5, 1),
    (13, 767, 5, 2),
    (13, 1023, 5, 1),
    (13, 1535, 5, 1),
    (13, 2045, 5, 1),
    (13, 2047, 5, 1),
    (13, 3071, 5, 1),
    (13, 3583, 5, 1),
    (13, 4095, 5, 1)]

theorem certTable_ok :
    certTable.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

/-- **Every word in the table is excluded** as an eventual repeating word of the center column. -/
theorem not_eventually_certTable (e : Nat × Nat × Nat × Nat) (he : e ∈ certTable) :
    ¬ EventuallyWord (wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp certTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_word_strip (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2 h.1.1
    (by rw [wordOf_length]; exact h.1.2) h.2

end Rule30StripCertificateTable
end Ruliology.CellularAutomata
