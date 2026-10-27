module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `52`: the chunk checks `0` to `63`

Data for `Rule30ZeroBoundaryWidth52`: the kernel checks `check 52 97 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 0, …, 63` of `256`
(`2 ^ 18` lanes each, `97` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth52.C0` –
`C3`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 52 97 18 lo 16`.

The `16` chunks are regrouped here, four to a module.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `52`: chunks `0` to `15` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C0

theorem c0 : check 52 97 18 0 = true := by decide +kernel
theorem c1 : check 52 97 18 1 = true := by decide +kernel
theorem c2 : check 52 97 18 2 = true := by decide +kernel
theorem c3 : check 52 97 18 3 = true := by decide +kernel
theorem c4 : check 52 97 18 4 = true := by decide +kernel
theorem c5 : check 52 97 18 5 = true := by decide +kernel
theorem c6 : check 52 97 18 6 = true := by decide +kernel
theorem c7 : check 52 97 18 7 = true := by decide +kernel
theorem c8 : check 52 97 18 8 = true := by decide +kernel
theorem c9 : check 52 97 18 9 = true := by decide +kernel
theorem c10 : check 52 97 18 10 = true := by decide +kernel
theorem c11 : check 52 97 18 11 = true := by decide +kernel
theorem c12 : check 52 97 18 12 = true := by decide +kernel
theorem c13 : check 52 97 18 13 = true := by decide +kernel
theorem c14 : check 52 97 18 14 = true := by decide +kernel
theorem c15 : check 52 97 18 15 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 0 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c0) (chunksOK_one c1)) (chunksOK_append (chunksOK_one c2) (chunksOK_one c3))) (chunksOK_append (chunksOK_append (chunksOK_one c4) (chunksOK_one c5)) (chunksOK_append (chunksOK_one c6) (chunksOK_one c7)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c8) (chunksOK_one c9)) (chunksOK_append (chunksOK_one c10) (chunksOK_one c11))) (chunksOK_append (chunksOK_append (chunksOK_one c12) (chunksOK_one c13)) (chunksOK_append (chunksOK_one c14) (chunksOK_one c15)))))

end C0

/-! Kernel checks for `Q01` at width `52`: chunks `16` to `31` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C1

theorem c16 : check 52 97 18 16 = true := by decide +kernel
theorem c17 : check 52 97 18 17 = true := by decide +kernel
theorem c18 : check 52 97 18 18 = true := by decide +kernel
theorem c19 : check 52 97 18 19 = true := by decide +kernel
theorem c20 : check 52 97 18 20 = true := by decide +kernel
theorem c21 : check 52 97 18 21 = true := by decide +kernel
theorem c22 : check 52 97 18 22 = true := by decide +kernel
theorem c23 : check 52 97 18 23 = true := by decide +kernel
theorem c24 : check 52 97 18 24 = true := by decide +kernel
theorem c25 : check 52 97 18 25 = true := by decide +kernel
theorem c26 : check 52 97 18 26 = true := by decide +kernel
theorem c27 : check 52 97 18 27 = true := by decide +kernel
theorem c28 : check 52 97 18 28 = true := by decide +kernel
theorem c29 : check 52 97 18 29 = true := by decide +kernel
theorem c30 : check 52 97 18 30 = true := by decide +kernel
theorem c31 : check 52 97 18 31 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 16 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c16) (chunksOK_one c17)) (chunksOK_append (chunksOK_one c18) (chunksOK_one c19))) (chunksOK_append (chunksOK_append (chunksOK_one c20) (chunksOK_one c21)) (chunksOK_append (chunksOK_one c22) (chunksOK_one c23)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c24) (chunksOK_one c25)) (chunksOK_append (chunksOK_one c26) (chunksOK_one c27))) (chunksOK_append (chunksOK_append (chunksOK_one c28) (chunksOK_one c29)) (chunksOK_append (chunksOK_one c30) (chunksOK_one c31)))))

end C1

/-! Kernel checks for `Q01` at width `52`: chunks `32` to `47` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C2

theorem c32 : check 52 97 18 32 = true := by decide +kernel
theorem c33 : check 52 97 18 33 = true := by decide +kernel
theorem c34 : check 52 97 18 34 = true := by decide +kernel
theorem c35 : check 52 97 18 35 = true := by decide +kernel
theorem c36 : check 52 97 18 36 = true := by decide +kernel
theorem c37 : check 52 97 18 37 = true := by decide +kernel
theorem c38 : check 52 97 18 38 = true := by decide +kernel
theorem c39 : check 52 97 18 39 = true := by decide +kernel
theorem c40 : check 52 97 18 40 = true := by decide +kernel
theorem c41 : check 52 97 18 41 = true := by decide +kernel
theorem c42 : check 52 97 18 42 = true := by decide +kernel
theorem c43 : check 52 97 18 43 = true := by decide +kernel
theorem c44 : check 52 97 18 44 = true := by decide +kernel
theorem c45 : check 52 97 18 45 = true := by decide +kernel
theorem c46 : check 52 97 18 46 = true := by decide +kernel
theorem c47 : check 52 97 18 47 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 32 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c32) (chunksOK_one c33)) (chunksOK_append (chunksOK_one c34) (chunksOK_one c35))) (chunksOK_append (chunksOK_append (chunksOK_one c36) (chunksOK_one c37)) (chunksOK_append (chunksOK_one c38) (chunksOK_one c39)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c40) (chunksOK_one c41)) (chunksOK_append (chunksOK_one c42) (chunksOK_one c43))) (chunksOK_append (chunksOK_append (chunksOK_one c44) (chunksOK_one c45)) (chunksOK_append (chunksOK_one c46) (chunksOK_one c47)))))

end C2

/-! Kernel checks for `Q01` at width `52`: chunks `48` to `63` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C3

theorem c48 : check 52 97 18 48 = true := by decide +kernel
theorem c49 : check 52 97 18 49 = true := by decide +kernel
theorem c50 : check 52 97 18 50 = true := by decide +kernel
theorem c51 : check 52 97 18 51 = true := by decide +kernel
theorem c52 : check 52 97 18 52 = true := by decide +kernel
theorem c53 : check 52 97 18 53 = true := by decide +kernel
theorem c54 : check 52 97 18 54 = true := by decide +kernel
theorem c55 : check 52 97 18 55 = true := by decide +kernel
theorem c56 : check 52 97 18 56 = true := by decide +kernel
theorem c57 : check 52 97 18 57 = true := by decide +kernel
theorem c58 : check 52 97 18 58 = true := by decide +kernel
theorem c59 : check 52 97 18 59 = true := by decide +kernel
theorem c60 : check 52 97 18 60 = true := by decide +kernel
theorem c61 : check 52 97 18 61 = true := by decide +kernel
theorem c62 : check 52 97 18 62 = true := by decide +kernel
theorem c63 : check 52 97 18 63 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 48 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c48) (chunksOK_one c49)) (chunksOK_append (chunksOK_one c50) (chunksOK_one c51))) (chunksOK_append (chunksOK_append (chunksOK_one c52) (chunksOK_one c53)) (chunksOK_append (chunksOK_one c54) (chunksOK_one c55)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c56) (chunksOK_one c57)) (chunksOK_append (chunksOK_one c58) (chunksOK_one c59))) (chunksOK_append (chunksOK_append (chunksOK_one c60) (chunksOK_one c61)) (chunksOK_append (chunksOK_one c62) (chunksOK_one c63)))))

end C3

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
