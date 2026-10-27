module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-!
# `Q01` at width `52`: the chunk checks `192` to `255`

Data for `Rule30ZeroBoundaryWidth52`: the kernel checks `check 52 97 18 c = true`
(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks `c = 192, …, 255` of `256`
(`2 ^ 18` lanes each, `97` levels). They sit in the namespaces `Rule30ZeroBoundaryWidth52.C12` –
`C15`, `16` chunks each; each of these namespaces combines its chunks into
`range : ChunksOK 52 97 18 lo 16`.

The `16` chunks are regrouped here, four to a module.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52

open Rule30ZeroBoundaryLanes

/-! Kernel checks for `Q01` at width `52`: chunks `192` to `207` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C12

theorem c192 : check 52 97 18 192 = true := by decide +kernel
theorem c193 : check 52 97 18 193 = true := by decide +kernel
theorem c194 : check 52 97 18 194 = true := by decide +kernel
theorem c195 : check 52 97 18 195 = true := by decide +kernel
theorem c196 : check 52 97 18 196 = true := by decide +kernel
theorem c197 : check 52 97 18 197 = true := by decide +kernel
theorem c198 : check 52 97 18 198 = true := by decide +kernel
theorem c199 : check 52 97 18 199 = true := by decide +kernel
theorem c200 : check 52 97 18 200 = true := by decide +kernel
theorem c201 : check 52 97 18 201 = true := by decide +kernel
theorem c202 : check 52 97 18 202 = true := by decide +kernel
theorem c203 : check 52 97 18 203 = true := by decide +kernel
theorem c204 : check 52 97 18 204 = true := by decide +kernel
theorem c205 : check 52 97 18 205 = true := by decide +kernel
theorem c206 : check 52 97 18 206 = true := by decide +kernel
theorem c207 : check 52 97 18 207 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 192 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c192) (chunksOK_one c193)) (chunksOK_append (chunksOK_one c194) (chunksOK_one c195))) (chunksOK_append (chunksOK_append (chunksOK_one c196) (chunksOK_one c197)) (chunksOK_append (chunksOK_one c198) (chunksOK_one c199)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c200) (chunksOK_one c201)) (chunksOK_append (chunksOK_one c202) (chunksOK_one c203))) (chunksOK_append (chunksOK_append (chunksOK_one c204) (chunksOK_one c205)) (chunksOK_append (chunksOK_one c206) (chunksOK_one c207)))))

end C12

/-! Kernel checks for `Q01` at width `52`: chunks `208` to `223` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C13

theorem c208 : check 52 97 18 208 = true := by decide +kernel
theorem c209 : check 52 97 18 209 = true := by decide +kernel
theorem c210 : check 52 97 18 210 = true := by decide +kernel
theorem c211 : check 52 97 18 211 = true := by decide +kernel
theorem c212 : check 52 97 18 212 = true := by decide +kernel
theorem c213 : check 52 97 18 213 = true := by decide +kernel
theorem c214 : check 52 97 18 214 = true := by decide +kernel
theorem c215 : check 52 97 18 215 = true := by decide +kernel
theorem c216 : check 52 97 18 216 = true := by decide +kernel
theorem c217 : check 52 97 18 217 = true := by decide +kernel
theorem c218 : check 52 97 18 218 = true := by decide +kernel
theorem c219 : check 52 97 18 219 = true := by decide +kernel
theorem c220 : check 52 97 18 220 = true := by decide +kernel
theorem c221 : check 52 97 18 221 = true := by decide +kernel
theorem c222 : check 52 97 18 222 = true := by decide +kernel
theorem c223 : check 52 97 18 223 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 208 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c208) (chunksOK_one c209)) (chunksOK_append (chunksOK_one c210) (chunksOK_one c211))) (chunksOK_append (chunksOK_append (chunksOK_one c212) (chunksOK_one c213)) (chunksOK_append (chunksOK_one c214) (chunksOK_one c215)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c216) (chunksOK_one c217)) (chunksOK_append (chunksOK_one c218) (chunksOK_one c219))) (chunksOK_append (chunksOK_append (chunksOK_one c220) (chunksOK_one c221)) (chunksOK_append (chunksOK_one c222) (chunksOK_one c223)))))

end C13

/-! Kernel checks for `Q01` at width `52`: chunks `224` to `239` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C14

theorem c224 : check 52 97 18 224 = true := by decide +kernel
theorem c225 : check 52 97 18 225 = true := by decide +kernel
theorem c226 : check 52 97 18 226 = true := by decide +kernel
theorem c227 : check 52 97 18 227 = true := by decide +kernel
theorem c228 : check 52 97 18 228 = true := by decide +kernel
theorem c229 : check 52 97 18 229 = true := by decide +kernel
theorem c230 : check 52 97 18 230 = true := by decide +kernel
theorem c231 : check 52 97 18 231 = true := by decide +kernel
theorem c232 : check 52 97 18 232 = true := by decide +kernel
theorem c233 : check 52 97 18 233 = true := by decide +kernel
theorem c234 : check 52 97 18 234 = true := by decide +kernel
theorem c235 : check 52 97 18 235 = true := by decide +kernel
theorem c236 : check 52 97 18 236 = true := by decide +kernel
theorem c237 : check 52 97 18 237 = true := by decide +kernel
theorem c238 : check 52 97 18 238 = true := by decide +kernel
theorem c239 : check 52 97 18 239 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 224 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c224) (chunksOK_one c225)) (chunksOK_append (chunksOK_one c226) (chunksOK_one c227))) (chunksOK_append (chunksOK_append (chunksOK_one c228) (chunksOK_one c229)) (chunksOK_append (chunksOK_one c230) (chunksOK_one c231)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c232) (chunksOK_one c233)) (chunksOK_append (chunksOK_one c234) (chunksOK_one c235))) (chunksOK_append (chunksOK_append (chunksOK_one c236) (chunksOK_one c237)) (chunksOK_append (chunksOK_one c238) (chunksOK_one c239)))))

end C14

/-! Kernel checks for `Q01` at width `52`: chunks `240` to `255` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace C15

theorem c240 : check 52 97 18 240 = true := by decide +kernel
theorem c241 : check 52 97 18 241 = true := by decide +kernel
theorem c242 : check 52 97 18 242 = true := by decide +kernel
theorem c243 : check 52 97 18 243 = true := by decide +kernel
theorem c244 : check 52 97 18 244 = true := by decide +kernel
theorem c245 : check 52 97 18 245 = true := by decide +kernel
theorem c246 : check 52 97 18 246 = true := by decide +kernel
theorem c247 : check 52 97 18 247 = true := by decide +kernel
theorem c248 : check 52 97 18 248 = true := by decide +kernel
theorem c249 : check 52 97 18 249 = true := by decide +kernel
theorem c250 : check 52 97 18 250 = true := by decide +kernel
theorem c251 : check 52 97 18 251 = true := by decide +kernel
theorem c252 : check 52 97 18 252 = true := by decide +kernel
theorem c253 : check 52 97 18 253 = true := by decide +kernel
theorem c254 : check 52 97 18 254 = true := by decide +kernel
theorem c255 : check 52 97 18 255 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 240 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c240) (chunksOK_one c241)) (chunksOK_append (chunksOK_one c242) (chunksOK_one c243))) (chunksOK_append (chunksOK_append (chunksOK_one c244) (chunksOK_one c245)) (chunksOK_append (chunksOK_one c246) (chunksOK_one c247)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c248) (chunksOK_one c249)) (chunksOK_append (chunksOK_one c250) (chunksOK_one c251))) (chunksOK_append (chunksOK_append (chunksOK_one c252) (chunksOK_one c253)) (chunksOK_append (chunksOK_one c254) (chunksOK_one c255)))))

end C15

end Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
