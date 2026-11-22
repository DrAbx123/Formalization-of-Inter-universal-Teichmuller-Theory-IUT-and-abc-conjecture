import tmp.sheaf.xif.paper.S2564Chain1Mid3Actual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Verify

/- Type acceptance: the lemmas have exactly the requested statement. -/
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 161 = (G * S0).coeff 161 := chain1_coeff_161
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 200 = (G * S0).coeff 200 := chain1_coeff_200
example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 240 = (G * S0).coeff 240 := chain1_coeff_240
example : S0.coeff 149 = 345 := S0_coeff_149
example : S0.coeff 240 = 455 := S0_coeff_240

/- Axiom audit for every declaration in the new module. -/

#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_149
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_150
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_151
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_152
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_153
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_154
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_155
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_156
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_157
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_158
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_159
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_160
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_161
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_162
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_163
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_164
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_165
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_166
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_167
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_168
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_169
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_170
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_171
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_172
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_173
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_174
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_175
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_176
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_177
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_178
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_179
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_180
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_181
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_182
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_183
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_184
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_185
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_186
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_187
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_188
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_189
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_190
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_191
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_192
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_193
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_194
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_195
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_196
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_197
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_198
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_199
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_200
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_201
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_202
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_203
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_204
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_205
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_206
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_207
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_208
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_209
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_210
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_211
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_212
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_213
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_214
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_215
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_216
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_217
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_218
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_219
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_220
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_221
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_222
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_223
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_224
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_225
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_226
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_227
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_228
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_229
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_230
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_231
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_232
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_233
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_234
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_235
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_236
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_237
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_238
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_239
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.S0_coeff_240
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.R0_coeff_eq_zero_of_gt
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.R1_coeff_eq_zero_of_gt
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_161
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_162
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_163
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_164
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_165
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_166
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_167
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_168
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_169
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_170
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_171
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_172
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_173
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_174
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_175
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_176
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_177
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_178
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_179
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_180
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_181
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_182
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_183
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_184
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_185
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_186
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_187
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_188
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_189
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_190
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_191
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_192
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_193
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_194
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_195
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_196
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_197
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_198
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_199
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_200
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_201
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_202
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_203
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_204
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_205
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_206
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_207
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_208
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_209
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_210
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_211
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_212
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_213
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_214
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_215
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_216
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_217
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_218
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_219
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_220
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_221
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_222
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_223
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_224
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_225
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_226
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_227
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_228
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_229
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_230
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_231
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_232
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_233
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_234
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_235
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_236
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_237
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_238
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_239
#print axioms LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_240

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Verify
