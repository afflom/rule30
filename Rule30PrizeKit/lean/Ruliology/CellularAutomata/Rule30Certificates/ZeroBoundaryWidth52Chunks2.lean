module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `52`: the chunk checks `128` to `191`

Data for `Rule30ZeroBoundaryWidth52`: the kernel checks `check 52 97 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 128, …, 191` of `256`
(`2 ^ 18` lanes each, `97` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth52.C8` –
`C11`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 52 97 18 lo 16`.

The `16` chunks are regrouped here, four to a module.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `52`: chunks `128` to `143` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C8

theorem c128 : check 52 97 18 128 = true := by decide +kernel
theorem c129 : check 52 97 18 129 = true := by decide +kernel
theorem c130 : check 52 97 18 130 = true := by decide +kernel
theorem c131 : check 52 97 18 131 = true := by decide +kernel
theorem c132 : check 52 97 18 132 = true := by decide +kernel
theorem c133 : check 52 97 18 133 = true := by decide +kernel
theorem c134 : check 52 97 18 134 = true := by decide +kernel
theorem c135 : check 52 97 18 135 = true := by decide +kernel
theorem c136 : check 52 97 18 136 = true := by decide +kernel
theorem c137 : check 52 97 18 137 = true := by decide +kernel
theorem c138 : check 52 97 18 138 = true := by decide +kernel
theorem c139 : check 52 97 18 139 = true := by decide +kernel
theorem c140 : check 52 97 18 140 = true := by decide +kernel
theorem c141 : check 52 97 18 141 = true := by decide +kernel
theorem c142 : check 52 97 18 142 = true := by decide +kernel
theorem c143 : check 52 97 18 143 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 128 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c128) (chunksOK_one c129)) (chunksOK_append (chunksOK_one c130) (chunksOK_one c131))) (chunksOK_append (chunksOK_append (chunksOK_one c132) (chunksOK_one c133)) (chunksOK_append (chunksOK_one c134) (chunksOK_one c135)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c136) (chunksOK_one c137)) (chunksOK_append (chunksOK_one c138) (chunksOK_one c139))) (chunksOK_append (chunksOK_append (chunksOK_one c140) (chunksOK_one c141)) (chunksOK_append (chunksOK_one c142) (chunksOK_one c143)))))

end C8

/-! Kernel checks for `Q01` at width `52`: chunks `144` to `159` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C9

theorem c144 : check 52 97 18 144 = true := by decide +kernel
theorem c145 : check 52 97 18 145 = true := by decide +kernel
theorem c146 : check 52 97 18 146 = true := by decide +kernel
theorem c147 : check 52 97 18 147 = true := by decide +kernel
theorem c148 : check 52 97 18 148 = true := by decide +kernel
theorem c149 : check 52 97 18 149 = true := by decide +kernel
theorem c150 : check 52 97 18 150 = true := by decide +kernel
theorem c151 : check 52 97 18 151 = true := by decide +kernel
theorem c152 : check 52 97 18 152 = true := by decide +kernel
theorem c153 : check 52 97 18 153 = true := by decide +kernel
theorem c154 : check 52 97 18 154 = true := by decide +kernel
theorem c155 : check 52 97 18 155 = true := by decide +kernel
theorem c156 : check 52 97 18 156 = true := by decide +kernel
theorem c157 : check 52 97 18 157 = true := by decide +kernel
theorem c158 : check 52 97 18 158 = true := by decide +kernel
theorem c159 : check 52 97 18 159 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 144 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c144) (chunksOK_one c145)) (chunksOK_append (chunksOK_one c146) (chunksOK_one c147))) (chunksOK_append (chunksOK_append (chunksOK_one c148) (chunksOK_one c149)) (chunksOK_append (chunksOK_one c150) (chunksOK_one c151)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c152) (chunksOK_one c153)) (chunksOK_append (chunksOK_one c154) (chunksOK_one c155))) (chunksOK_append (chunksOK_append (chunksOK_one c156) (chunksOK_one c157)) (chunksOK_append (chunksOK_one c158) (chunksOK_one c159)))))

end C9

/-! Kernel checks for `Q01` at width `52`: chunks `160` to `175` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C10

theorem c160 : check 52 97 18 160 = true := by decide +kernel
theorem c161 : check 52 97 18 161 = true := by decide +kernel
theorem c162 : check 52 97 18 162 = true := by decide +kernel
theorem c163 : check 52 97 18 163 = true := by decide +kernel
theorem c164 : check 52 97 18 164 = true := by decide +kernel
theorem c165 : check 52 97 18 165 = true := by decide +kernel
theorem c166 : check 52 97 18 166 = true := by decide +kernel
theorem c167 : check 52 97 18 167 = true := by decide +kernel
theorem c168 : check 52 97 18 168 = true := by decide +kernel
theorem c169 : check 52 97 18 169 = true := by decide +kernel
theorem c170 : check 52 97 18 170 = true := by decide +kernel
theorem c171 : check 52 97 18 171 = true := by decide +kernel
theorem c172 : check 52 97 18 172 = true := by decide +kernel
theorem c173 : check 52 97 18 173 = true := by decide +kernel
theorem c174 : check 52 97 18 174 = true := by decide +kernel
theorem c175 : check 52 97 18 175 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 160 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c160) (chunksOK_one c161)) (chunksOK_append (chunksOK_one c162) (chunksOK_one c163))) (chunksOK_append (chunksOK_append (chunksOK_one c164) (chunksOK_one c165)) (chunksOK_append (chunksOK_one c166) (chunksOK_one c167)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c168) (chunksOK_one c169)) (chunksOK_append (chunksOK_one c170) (chunksOK_one c171))) (chunksOK_append (chunksOK_append (chunksOK_one c172) (chunksOK_one c173)) (chunksOK_append (chunksOK_one c174) (chunksOK_one c175)))))

end C10

/-! Kernel checks for `Q01` at width `52`: chunks `176` to `191` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C11

theorem c176 : check 52 97 18 176 = true := by decide +kernel
theorem c177 : check 52 97 18 177 = true := by decide +kernel
theorem c178 : check 52 97 18 178 = true := by decide +kernel
theorem c179 : check 52 97 18 179 = true := by decide +kernel
theorem c180 : check 52 97 18 180 = true := by decide +kernel
theorem c181 : check 52 97 18 181 = true := by decide +kernel
theorem c182 : check 52 97 18 182 = true := by decide +kernel
theorem c183 : check 52 97 18 183 = true := by decide +kernel
theorem c184 : check 52 97 18 184 = true := by decide +kernel
theorem c185 : check 52 97 18 185 = true := by decide +kernel
theorem c186 : check 52 97 18 186 = true := by decide +kernel
theorem c187 : check 52 97 18 187 = true := by decide +kernel
theorem c188 : check 52 97 18 188 = true := by decide +kernel
theorem c189 : check 52 97 18 189 = true := by decide +kernel
theorem c190 : check 52 97 18 190 = true := by decide +kernel
theorem c191 : check 52 97 18 191 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 176 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c176) (chunksOK_one c177)) (chunksOK_append (chunksOK_one c178) (chunksOK_one c179))) (chunksOK_append (chunksOK_append (chunksOK_one c180) (chunksOK_one c181)) (chunksOK_append (chunksOK_one c182) (chunksOK_one c183)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c184) (chunksOK_one c185)) (chunksOK_append (chunksOK_one c186) (chunksOK_one c187))) (chunksOK_append (chunksOK_append (chunksOK_one c188) (chunksOK_one c189)) (chunksOK_append (chunksOK_one c190) (chunksOK_one c191)))))

end C11

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
