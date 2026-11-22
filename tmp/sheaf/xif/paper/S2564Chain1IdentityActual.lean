/-
S2564 chain 1: assembly of the actual coefficient ranges.

Goal: the polynomial identity
  (X : (ZMod 613)[X]) ^ 613 - T1 = G * S0
and the induced divisibility `G ∣ X ^ 613 - T1`.

Every coefficient `n ≤ 613` is discharged by the already-actual range files:
* [0, 11]    S2564Chain1LowActual.chain1_coeff_0 .. _11;
* [12, 80]   S2564Chain1Mid1Actual.chain1_coeff_12 .. _80;
* [81, 160]  S2564Chain1Mid2Actual.chain1_coeff_mid2;
* [161, 240] S2564Chain1Mid3Actual.chain1_coeff_161 .. _240;
* [241, 320] S2564Chain1Mid4Actual.chain1_coeff_241 .. _320;
* [321, 400] S2564Chain1Mid5Actual.chain1_coeff_321 .. _400;
* [401, 480] S2564Chain1Mid6Actual.chain1_mid6;
* [481, 560] S2564Chain1Mid7Actual.chain1_coeff_mid;
* [561, 613] S2564Chain1Mid8Actual.chain1_coeff_mid.

For `n ≥ 614` both sides have vanishing coefficient: the left side has degree
at most `613 = deg (X ^ 613)`, and the right side has degree at most
`12 + 601` since `natDegree G ≤ 12` and `natDegree S0 ≤ 601`.

No axioms, no `sorry`, no `native_decide` are used here.
-/

import tmp.sheaf.xif.paper.S2564Chain1LowActual
import tmp.sheaf.xif.paper.S2564Chain1Mid1Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid2Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid3Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid4Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid5Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid6Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid7Actual
import tmp.sheaf.xif.paper.S2564Chain1Mid8Actual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual

/-- Degree form of the range `[0, 11]` (no uniform range theorem in the source file). -/
lemma chain1_coeff_le_11 (n : ℕ) (hn : n ≤ 11) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n
  exacts [LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_0,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_1,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_2,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_3,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_4,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_5,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_6,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_7,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_8,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_9,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_10,
    LeanFormal.IUT.XiFPaper.S2564Chain1LowActual.chain1_coeff_11]

/-- Degree form of the range `[12, 80]`. -/
lemma chain1_coeff_12_80 (n : ℕ) (h1 : 12 ≤ n) (h2 : n ≤ 80) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n
  exacts [LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_12,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_13,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_14,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_15,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_16,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_17,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_18,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_19,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_20,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_21,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_22,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_23,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_24,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_25,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_26,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_27,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_28,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_29,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_30,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_31,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_32,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_33,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_34,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_35,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_36,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_37,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_38,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_39,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_40,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_41,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_42,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_43,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_44,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_45,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_46,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_47,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_48,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_49,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_50,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_51,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_52,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_53,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_54,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_55,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_56,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_57,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_58,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_59,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_60,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_61,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_62,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_63,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_64,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_65,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_66,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_67,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_68,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_69,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_70,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_71,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_72,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_73,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_74,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_75,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_76,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_77,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_78,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_79,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual.chain1_coeff_80]

/-- Degree form of the range `[161, 240]`. -/
lemma chain1_coeff_161_240 (n : ℕ) (h1 : 161 ≤ n) (h2 : n ≤ 240) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n
  exacts [LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_161,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_162,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_163,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_164,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_165,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_166,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_167,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_168,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_169,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_170,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_171,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_172,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_173,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_174,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_175,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_176,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_177,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_178,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_179,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_180,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_181,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_182,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_183,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_184,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_185,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_186,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_187,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_188,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_189,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_190,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_191,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_192,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_193,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_194,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_195,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_196,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_197,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_198,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_199,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_200,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_201,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_202,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_203,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_204,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_205,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_206,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_207,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_208,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_209,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_210,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_211,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_212,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_213,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_214,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_215,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_216,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_217,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_218,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_219,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_220,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_221,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_222,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_223,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_224,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_225,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_226,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_227,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_228,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_229,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_230,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_231,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_232,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_233,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_234,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_235,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_236,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_237,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_238,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_239,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual.chain1_coeff_240]

/-- Degree form of the range `[241, 320]`. -/
lemma chain1_coeff_241_320 (n : ℕ) (h1 : 241 ≤ n) (h2 : n ≤ 320) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n
  exacts [LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_241,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_242,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_243,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_244,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_245,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_246,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_247,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_248,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_249,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_250,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_251,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_252,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_253,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_254,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_255,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_256,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_257,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_258,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_259,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_260,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_261,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_262,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_263,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_264,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_265,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_266,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_267,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_268,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_269,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_270,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_271,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_272,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_273,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_274,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_275,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_276,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_277,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_278,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_279,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_280,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_281,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_282,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_283,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_284,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_285,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_286,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_287,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_288,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_289,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_290,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_291,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_292,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_293,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_294,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_295,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_296,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_297,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_298,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_299,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_300,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_301,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_302,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_303,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_304,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_305,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_306,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_307,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_308,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_309,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_310,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_311,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_312,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_313,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_314,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_315,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_316,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_317,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_318,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_319,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid4Actual.chain1_coeff_320]

/-- Degree form of the range `[321, 400]`. -/
lemma chain1_coeff_321_400 (n : ℕ) (h1 : 321 ≤ n) (h2 : n ≤ 400) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n
  exacts [LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_321,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_322,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_323,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_324,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_325,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_326,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_327,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_328,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_329,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_330,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_331,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_332,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_333,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_334,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_335,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_336,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_337,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_338,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_339,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_340,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_341,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_342,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_343,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_344,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_345,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_346,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_347,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_348,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_349,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_350,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_351,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_352,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_353,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_354,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_355,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_356,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_357,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_358,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_359,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_360,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_361,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_362,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_363,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_364,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_365,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_366,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_367,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_368,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_369,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_370,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_371,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_372,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_373,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_374,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_375,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_376,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_377,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_378,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_379,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_380,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_381,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_382,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_383,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_384,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_385,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_386,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_387,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_388,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_389,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_390,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_391,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_392,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_393,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_394,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_395,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_396,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_397,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_398,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_399,
    LeanFormal.IUT.XiFPaper.S2564Chain1Mid5Actual.chain1_coeff_400]

/-! ## Vanishing of `S0` coefficients above degree `601` -/

/-- The support of `S0` ends at degree `601`: each shifted part `S0_i = X ^ m_i * R_i`
contributes only degrees `≤ m_i + 40` (`i = 7`) or `≤ m_i + 79`, all at most `601`. -/
lemma S0_coeff_eq_zero_of_gt (k : ℕ) (hk : 601 < k) : S0.coeff k = 0 := by
  have h0 : S0_0.coeff k = 0 := by
    rw [S0_0_coeff]
    simp only [if_pos (Nat.zero_le k), Nat.sub_zero]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R0_natDegree_le (by omega)
  have h1 : S0_1.coeff k = 0 := by
    rw [S0_1_coeff]
    simp only [if_pos (by omega : 81 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R1_natDegree_le (by omega)
  have h2 : S0_2.coeff k = 0 := by
    rw [S0_2_coeff]
    simp only [if_pos (by omega : 161 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R2_natDegree_le (by omega)
  have h3 : S0_3.coeff k = 0 := by
    rw [S0_3_coeff]
    simp only [if_pos (by omega : 241 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R3_natDegree_le (by omega)
  have h4 : S0_4.coeff k = 0 := by
    rw [S0_4_coeff]
    simp only [if_pos (by omega : 321 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R4_natDegree_le (by omega)
  have h5 : S0_5.coeff k = 0 := by
    rw [S0_5_coeff]
    simp only [if_pos (by omega : 401 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R5_natDegree_le (by omega)
  have h6 : S0_6.coeff k = 0 := by
    rw [S0_6_coeff]
    simp only [if_pos (by omega : 481 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R6_natDegree_le (by omega)
  have h7 : S0_7.coeff k = 0 := by
    rw [S0_7_coeff]
    simp only [if_pos (by omega : 561 ≤ k)]
    exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.coeff_zero_of_natDegree_le
      LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.R7_natDegree_le (by omega)
  rw [S0]
  simp only [coeff_add, h0, h1, h2, h3, h4, h5, h6, h7, add_zero]

lemma S0_natDegree_le : S0.natDegree ≤ 601 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  exact S0_coeff_eq_zero_of_gt m hm

/-! ## Degree bounds for the two sides -/

lemma G_natDegree_le : G.natDegree ≤ 12 := by
  unfold G
  compute_degree!

lemma lhs_natDegree_le : ((X : (ZMod 613)[X]) ^ 613 - T1).natDegree ≤ 613 := by
  unfold T1
  compute_degree!

lemma rhs_natDegree_le : (G * S0).natDegree ≤ 613 := by
  have hG : G.natDegree ≤ 12 := G_natDegree_le
  have hS : S0.natDegree ≤ 601 := S0_natDegree_le
  have hmul : (G * S0).natDegree ≤ G.natDegree + S0.natDegree := natDegree_mul_le
  omega

/-! ## Assembly -/

/-- The chain-1 identity `X ^ 613 - T1 = G * S0` in `(ZMod 613)[X]`. -/
theorem chain1_identity : (X : (ZMod 613)[X]) ^ 613 - T1 = G * S0 := by
  ext n
  by_cases h0 : n ≤ 11
  · exact chain1_coeff_le_11 n h0
  have h0' : 12 ≤ n := by omega
  by_cases h1 : n ≤ 80
  · exact chain1_coeff_12_80 n h0' h1
  have h1' : 81 ≤ n := by omega
  by_cases h2 : n ≤ 160
  · exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid2Actual.chain1_coeff_mid2 n h1' h2
  have h2' : 161 ≤ n := by omega
  by_cases h3 : n ≤ 240
  · exact chain1_coeff_161_240 n h2' h3
  have h3' : 241 ≤ n := by omega
  by_cases h4 : n ≤ 320
  · exact chain1_coeff_241_320 n h3' h4
  have h4' : 321 ≤ n := by omega
  by_cases h5 : n ≤ 400
  · exact chain1_coeff_321_400 n h4' h5
  have h5' : 401 ≤ n := by omega
  by_cases h6 : n ≤ 480
  · exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid6Actual.chain1_mid6 n h5' h6
  have h6' : 481 ≤ n := by omega
  by_cases h7 : n ≤ 560
  · exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid7Actual.chain1_coeff_mid n h6' h7
  have h7' : 561 ≤ n := by omega
  by_cases h8 : n ≤ 613
  · exact LeanFormal.IUT.XiFPaper.S2564Chain1Mid8Actual.chain1_coeff_mid n h7' h8
  · have hL : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := lhs_natDegree_le
      omega
    have hR : (G * S0).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := rhs_natDegree_le
      omega
    rw [hL, hR]

/-- `G` divides `X ^ 613 - T1` in `(ZMod 613)[X]`. -/
theorem chain1_dvd : G ∣ (X : (ZMod 613)[X]) ^ 613 - T1 := ⟨S0, chain1_identity⟩

end LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual

end
