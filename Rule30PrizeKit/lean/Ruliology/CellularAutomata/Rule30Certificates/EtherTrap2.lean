module

public import Ruliology.CellularAutomata.Rule30EtherTrap

/-!
# Pure ether, word `0011`: certificates for the alignment `j₀ = 0`

Data for `Rule30EtherTrapWidth20`: kernel-checked certificates for `0011` (data:
`B-edge-trap/cert_0011_20.txt`, converted to column-`21` inputs): from each pure-ether node of
width `20`, a path to a node with two closed walks of equal length whose white-phase outputs
differ (`certOK`, `decide +kernel`): `cert_0011_0_0` – `cert_0011_0_3` (phases `0` – `3`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherTrap

open Rule30Ether

theorem cert_0011_0_0 : certOK w0011 (0, etherRow 0 ((0 + 0) % 4) 20)
    []
    [false, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, true, true, true, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false]
    [true, false, false, false, true, false, false, false, false, false, false, true, true, true, true, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false, false, true]
    104 = true := by decide +kernel

theorem cert_0011_0_1 : certOK w0011 (1, etherRow 0 ((1 + 0) % 4) 20)
    []
    [true, false, false, false, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false, true, false, false, false, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false]
    [false, false, true, true, false, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false, true, false, false, false, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true, false, false, false, false, true, true, false, true, false, true, false]
    123 = true := by decide +kernel

theorem cert_0011_0_2 : certOK w0011 (2, etherRow 0 ((2 + 0) % 4) 20)
    []
    [false, true, false, false, true, false, true, false, false, true, false, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false]
    [true, false, true, false, false, true, false, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false, false, true, false, false]
    106 = true := by decide +kernel

theorem cert_0011_0_3 : certOK w0011 (3, etherRow 0 ((3 + 0) % 4) 20)
    [false]
    [true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false]
    [true, false, false, false, true, false, false, false, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false, false, false, true, true, false, true, false, false, false, true]
    104 = true := by decide +kernel

end Ruliology.CellularAutomata.Rule30EtherTrap
