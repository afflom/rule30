module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `52`: the chunk checks `64` to `127`

Data for `Rule30ZeroBoundaryWidth52`: the kernel checks `check 52 97 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 64, …, 127` of `256`
(`2 ^ 18` lanes each, `97` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth52.C4` –
`C7`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 52 97 18 lo 16`.

The `16` chunks are regrouped here, four to a module.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `52`: chunks `64` to `79` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C4

theorem c64 : check 52 97 18 64 = true := by decide +kernel
theorem c65 : check 52 97 18 65 = true := by decide +kernel
theorem c66 : check 52 97 18 66 = true := by decide +kernel
theorem c67 : check 52 97 18 67 = true := by decide +kernel
theorem c68 : check 52 97 18 68 = true := by decide +kernel
theorem c69 : check 52 97 18 69 = true := by decide +kernel
theorem c70 : check 52 97 18 70 = true := by decide +kernel
theorem c71 : check 52 97 18 71 = true := by decide +kernel
theorem c72 : check 52 97 18 72 = true := by decide +kernel
theorem c73 : check 52 97 18 73 = true := by decide +kernel
theorem c74 : check 52 97 18 74 = true := by decide +kernel
theorem c75 : check 52 97 18 75 = true := by decide +kernel
theorem c76 : check 52 97 18 76 = true := by decide +kernel
theorem c77 : check 52 97 18 77 = true := by decide +kernel
theorem c78 : check 52 97 18 78 = true := by decide +kernel
theorem c79 : check 52 97 18 79 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 64 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c64) (chunksOK_one c65)) (chunksOK_append (chunksOK_one c66) (chunksOK_one c67))) (chunksOK_append (chunksOK_append (chunksOK_one c68) (chunksOK_one c69)) (chunksOK_append (chunksOK_one c70) (chunksOK_one c71)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c72) (chunksOK_one c73)) (chunksOK_append (chunksOK_one c74) (chunksOK_one c75))) (chunksOK_append (chunksOK_append (chunksOK_one c76) (chunksOK_one c77)) (chunksOK_append (chunksOK_one c78) (chunksOK_one c79)))))

end C4

/-! Kernel checks for `Q01` at width `52`: chunks `80` to `95` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C5

theorem c80 : check 52 97 18 80 = true := by decide +kernel
theorem c81 : check 52 97 18 81 = true := by decide +kernel
theorem c82 : check 52 97 18 82 = true := by decide +kernel
theorem c83 : check 52 97 18 83 = true := by decide +kernel
theorem c84 : check 52 97 18 84 = true := by decide +kernel
theorem c85 : check 52 97 18 85 = true := by decide +kernel
theorem c86 : check 52 97 18 86 = true := by decide +kernel
theorem c87 : check 52 97 18 87 = true := by decide +kernel
theorem c88 : check 52 97 18 88 = true := by decide +kernel
theorem c89 : check 52 97 18 89 = true := by decide +kernel
theorem c90 : check 52 97 18 90 = true := by decide +kernel
theorem c91 : check 52 97 18 91 = true := by decide +kernel
theorem c92 : check 52 97 18 92 = true := by decide +kernel
theorem c93 : check 52 97 18 93 = true := by decide +kernel
theorem c94 : check 52 97 18 94 = true := by decide +kernel
theorem c95 : check 52 97 18 95 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 80 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c80) (chunksOK_one c81)) (chunksOK_append (chunksOK_one c82) (chunksOK_one c83))) (chunksOK_append (chunksOK_append (chunksOK_one c84) (chunksOK_one c85)) (chunksOK_append (chunksOK_one c86) (chunksOK_one c87)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c88) (chunksOK_one c89)) (chunksOK_append (chunksOK_one c90) (chunksOK_one c91))) (chunksOK_append (chunksOK_append (chunksOK_one c92) (chunksOK_one c93)) (chunksOK_append (chunksOK_one c94) (chunksOK_one c95)))))

end C5

/-! Kernel checks for `Q01` at width `52`: chunks `96` to `111` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C6

theorem c96 : check 52 97 18 96 = true := by decide +kernel
theorem c97 : check 52 97 18 97 = true := by decide +kernel
theorem c98 : check 52 97 18 98 = true := by decide +kernel
theorem c99 : check 52 97 18 99 = true := by decide +kernel
theorem c100 : check 52 97 18 100 = true := by decide +kernel
theorem c101 : check 52 97 18 101 = true := by decide +kernel
theorem c102 : check 52 97 18 102 = true := by decide +kernel
theorem c103 : check 52 97 18 103 = true := by decide +kernel
theorem c104 : check 52 97 18 104 = true := by decide +kernel
theorem c105 : check 52 97 18 105 = true := by decide +kernel
theorem c106 : check 52 97 18 106 = true := by decide +kernel
theorem c107 : check 52 97 18 107 = true := by decide +kernel
theorem c108 : check 52 97 18 108 = true := by decide +kernel
theorem c109 : check 52 97 18 109 = true := by decide +kernel
theorem c110 : check 52 97 18 110 = true := by decide +kernel
theorem c111 : check 52 97 18 111 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 96 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c96) (chunksOK_one c97)) (chunksOK_append (chunksOK_one c98) (chunksOK_one c99))) (chunksOK_append (chunksOK_append (chunksOK_one c100) (chunksOK_one c101)) (chunksOK_append (chunksOK_one c102) (chunksOK_one c103)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c104) (chunksOK_one c105)) (chunksOK_append (chunksOK_one c106) (chunksOK_one c107))) (chunksOK_append (chunksOK_append (chunksOK_one c108) (chunksOK_one c109)) (chunksOK_append (chunksOK_one c110) (chunksOK_one c111)))))

end C6

/-! Kernel checks for `Q01` at width `52`: chunks `112` to `127` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C7

theorem c112 : check 52 97 18 112 = true := by decide +kernel
theorem c113 : check 52 97 18 113 = true := by decide +kernel
theorem c114 : check 52 97 18 114 = true := by decide +kernel
theorem c115 : check 52 97 18 115 = true := by decide +kernel
theorem c116 : check 52 97 18 116 = true := by decide +kernel
theorem c117 : check 52 97 18 117 = true := by decide +kernel
theorem c118 : check 52 97 18 118 = true := by decide +kernel
theorem c119 : check 52 97 18 119 = true := by decide +kernel
theorem c120 : check 52 97 18 120 = true := by decide +kernel
theorem c121 : check 52 97 18 121 = true := by decide +kernel
theorem c122 : check 52 97 18 122 = true := by decide +kernel
theorem c123 : check 52 97 18 123 = true := by decide +kernel
theorem c124 : check 52 97 18 124 = true := by decide +kernel
theorem c125 : check 52 97 18 125 = true := by decide +kernel
theorem c126 : check 52 97 18 126 = true := by decide +kernel
theorem c127 : check 52 97 18 127 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 112 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c112) (chunksOK_one c113)) (chunksOK_append (chunksOK_one c114) (chunksOK_one c115))) (chunksOK_append (chunksOK_append (chunksOK_one c116) (chunksOK_one c117)) (chunksOK_append (chunksOK_one c118) (chunksOK_one c119)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c120) (chunksOK_one c121)) (chunksOK_append (chunksOK_one c122) (chunksOK_one c123))) (chunksOK_append (chunksOK_append (chunksOK_one c124) (chunksOK_one c125)) (chunksOK_append (chunksOK_one c126) (chunksOK_one c127)))))

end C7

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
