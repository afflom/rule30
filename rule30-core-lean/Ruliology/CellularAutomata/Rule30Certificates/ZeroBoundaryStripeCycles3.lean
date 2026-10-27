module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-!
# Stripe prefixes with four tail cells: front-window cycles

Data for `Rule30ZeroBoundaryStripeFour`: the kernel-checked front-window cycles (window `32`,
post-arrival horizon `31`) of the four-cell tails that the cycles of
`Rule30Certificates.ZeroBoundaryStripeCycles0` – `2` do not cover, as
`Rule30ZeroBoundaryStripeFront.Cycle` certificates whose segments are checked by `seg` with
`decide +kernel` and joined by `seg_sound` and `path_append`: `cyc4_9`, `cyc4_10`, `cyc4_12`,
`cyc4_15` (one `seg` check each), `cyc4_8` (two) and `cyc4_11`, `cyc4_14` (four, length `65536`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles3

open Rule30ZeroBoundaryStripeFront

theorem seg4_8_0 : seg 32 31 0 1073741832 1 16384 0 8 1 = true := by decide +kernel

theorem seg4_8_1 : seg 32 31 0 8 1 16384 16384 1073741832 1 = true := by decide +kernel

theorem cyc4_8 : Cycle 32 31 8 1 32768 :=
  ⟨by decide, by decide, (path_append (seg_sound 32 31 0 1073741832 1 16384 0 8 1 seg4_8_0) (seg_sound 32 31 0 8 1 16384 16384 1073741832 1 seg4_8_1))⟩

theorem seg4_9_0 : seg 32 31 1 9 0 4096 0 9 0 = true := by decide +kernel

theorem cyc4_9 : Cycle 32 31 9 0 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 9 0 4096 0 9 0 seg4_9_0)⟩

theorem seg4_10_0 : seg 32 31 0 10 1 8192 0 10 1 = true := by decide +kernel

theorem cyc4_10 : Cycle 32 31 10 1 8192 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 10 1 8192 0 10 1 seg4_10_0)⟩

theorem seg4_11_0 : seg 32 31 1 1073741835 0 16384 0 11 0 = true := by decide +kernel

theorem seg4_11_1 : seg 32 31 1 2147483659 0 16384 16384 1073741835 0 = true := by decide +kernel

theorem seg4_11_2 : seg 32 31 1 3221225483 0 16384 32768 2147483659 0 = true := by decide +kernel

theorem seg4_11_3 : seg 32 31 1 11 0 16384 49152 3221225483 0 = true := by decide +kernel

theorem cyc4_11 : Cycle 32 31 11 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 1073741835 0 16384 0 11 0 seg4_11_0) (seg_sound 32 31 1 2147483659 0 16384 16384 1073741835 0 seg4_11_1)) (seg_sound 32 31 1 3221225483 0 16384 32768 2147483659 0 seg4_11_2)) (seg_sound 32 31 1 11 0 16384 49152 3221225483 0 seg4_11_3))⟩

theorem seg4_12_0 : seg 32 31 0 12 1 16384 0 12 1 = true := by decide +kernel

theorem cyc4_12 : Cycle 32 31 12 1 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 12 1 16384 0 12 1 seg4_12_0)⟩

theorem seg4_14_0 : seg 32 31 0 3758096398 1 16384 0 14 1 = true := by decide +kernel

theorem seg4_14_1 : seg 32 31 0 3221225486 1 16384 16384 3758096398 1 = true := by decide +kernel

theorem seg4_14_2 : seg 32 31 0 2684354574 1 16384 32768 3221225486 1 = true := by decide +kernel

theorem seg4_14_3 : seg 32 31 0 14 1 16384 49152 2684354574 1 = true := by decide +kernel

theorem cyc4_14 : Cycle 32 31 14 1 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 0 3758096398 1 16384 0 14 1 seg4_14_0) (seg_sound 32 31 0 3221225486 1 16384 16384 3758096398 1 seg4_14_1)) (seg_sound 32 31 0 2684354574 1 16384 32768 3221225486 1 seg4_14_2)) (seg_sound 32 31 0 14 1 16384 49152 2684354574 1 seg4_14_3))⟩

theorem seg4_15_0 : seg 32 31 1 15 0 16384 0 15 0 = true := by decide +kernel

theorem cyc4_15 : Cycle 32 31 15 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 15 0 16384 0 15 0 seg4_15_0)⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles3
