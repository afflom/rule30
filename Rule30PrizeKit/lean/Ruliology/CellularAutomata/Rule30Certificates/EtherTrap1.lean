module

public import Ruliology.CellularAutomata.Rule30EtherTrap

/-!
# Pure ether, word `0001`: certificates for the alignment `j₀ = 6`

Data for `Rule30EtherTrapWidth20`: kernel-checked certificates for `0001` (data:
`B-edge-trap/cert_0001_20.txt`, converted to column-`21` inputs): from each pure-ether node of
width `20`, a path to a node with two closed walks of equal length whose white-phase outputs
differ (`certOK`, `decide +kernel`): `cert_0001_6_0` – `cert_0001_6_3` (phases `0` – `3`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherTrap

open Rule30Ether

theorem cert_0001_6_0 : certOK w0001 (0, etherRow 6 ((0 + 0) % 4) 20)
    []
    [false, false, true, true, false, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true]
    [false, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, false, true, true]
    109 = true := by decide +kernel

theorem cert_0001_6_1 : certOK w0001 (1, etherRow 6 ((1 + 0) % 4) 20)
    []
    [true, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false]
    [true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, true, false, true, false]
    88 = true := by decide +kernel

theorem cert_0001_6_2 : certOK w0001 (2, etherRow 6 ((2 + 0) % 4) 20)
    []
    [true, true, false, false, true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true]
    [true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, false]
    107 = true := by decide +kernel

theorem cert_0001_6_3 : certOK w0001 (3, etherRow 6 ((3 + 0) % 4) 20)
    [false]
    [true, false, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true]
    [false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true]
    113 = true := by decide +kernel

end Ruliology.CellularAutomata.Rule30EtherTrap
