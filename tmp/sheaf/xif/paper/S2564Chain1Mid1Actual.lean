/-
S2564 chain 1: actual coefficients in degrees 12..80.

Target, for every n in [12, 80]:
  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

Since deg T1 <= 11 and n < 613, the left-hand side is -T1.coeff n = 0.
The right-hand side is expanded into its 13-term support sum
(G_mul_coeff_ge), and each S0.coeff k with k <= 80 is looked up through
the eight shifted pieces S0_i: only S0_0 = R0 contributes in this range,
because 81 * i > 80 for i >= 1.  The resulting numeric identity is
closed by decide.

Dependencies (all actual, no axioms added):
* S2560S0ShiftedPartsActual: R0..R7, S0_i, S0, S0_i_coeff;
* S2554Mod613ChainDataActual: G, T1;
* S2562GmulCoeffActual: G_mul_coeff_ge;
* S2563R0LookupActual: R0_coeff_0 .. R0_coeff_80;
* S2564Chain1LowActual: S0_coeff_0 .. S0_coeff_11 (degrees < 12).
-/

import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R0LookupActual
import tmp.sheaf.xif.paper.S2564Chain1LowActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual

open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R0LookupActual
open LeanFormal.IUT.XiFPaper.S2564Chain1LowActual

/-! ## S0 coefficient lookups, degrees 12..80

Only S0_0 = R0 can contribute below degree 81, so on this range
S0.coeff k = R0.coeff k; the values come from R0_coeff_k. -/

lemma S0_coeff_12 : S0.coeff 12 = 455 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_12]

lemma S0_coeff_13 : S0.coeff 13 = 168 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_13]

lemma S0_coeff_14 : S0.coeff 14 = 532 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_14]

lemma S0_coeff_15 : S0.coeff 15 = 32 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_15]

lemma S0_coeff_16 : S0.coeff 16 = 500 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_16]

lemma S0_coeff_17 : S0.coeff 17 = 163 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_17]

lemma S0_coeff_18 : S0.coeff 18 = 586 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_18]

lemma S0_coeff_19 : S0.coeff 19 = 118 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_19]

lemma S0_coeff_20 : S0.coeff 20 = 264 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_20]

lemma S0_coeff_21 : S0.coeff 21 = 560 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_21]

lemma S0_coeff_22 : S0.coeff 22 = 360 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_22]

lemma S0_coeff_23 : S0.coeff 23 = 309 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_23]

lemma S0_coeff_24 : S0.coeff 24 = 168 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_24]

lemma S0_coeff_25 : S0.coeff 25 = 601 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_25]

lemma S0_coeff_26 : S0.coeff 26 = 373 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_26]

lemma S0_coeff_27 : S0.coeff 27 = 288 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_27]

lemma S0_coeff_28 : S0.coeff 28 = 519 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_28]

lemma S0_coeff_29 : S0.coeff 29 = 73 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_29]

lemma S0_coeff_30 : S0.coeff 30 = 567 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_30]

lemma S0_coeff_31 : S0.coeff 31 = 465 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_31]

lemma S0_coeff_32 : S0.coeff 32 = 162 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_32]

lemma S0_coeff_33 : S0.coeff 33 = 370 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_33]

lemma S0_coeff_34 : S0.coeff 34 = 329 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_34]

lemma S0_coeff_35 : S0.coeff 35 = 331 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_35]

lemma S0_coeff_36 : S0.coeff 36 = 157 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_36]

lemma S0_coeff_37 : S0.coeff 37 = 337 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_37]

lemma S0_coeff_38 : S0.coeff 38 = 530 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_38]

lemma S0_coeff_39 : S0.coeff 39 = 236 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_39]

lemma S0_coeff_40 : S0.coeff 40 = 563 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_40]

lemma S0_coeff_41 : S0.coeff 41 = 120 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_41]

lemma S0_coeff_42 : S0.coeff 42 = 108 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_42]

lemma S0_coeff_43 : S0.coeff 43 = 117 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_43]

lemma S0_coeff_44 : S0.coeff 44 = 152 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_44]

lemma S0_coeff_45 : S0.coeff 45 = 368 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_45]

lemma S0_coeff_46 : S0.coeff 46 = 229 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_46]

lemma S0_coeff_47 : S0.coeff 47 = 448 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_47]

lemma S0_coeff_48 : S0.coeff 48 = 481 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_48]

lemma S0_coeff_49 : S0.coeff 49 = 152 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_49]

lemma S0_coeff_50 : S0.coeff 50 = 376 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_50]

lemma S0_coeff_51 : S0.coeff 51 = 161 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_51]

lemma S0_coeff_52 : S0.coeff 52 = 277 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_52]

lemma S0_coeff_53 : S0.coeff 53 = 224 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_53]

lemma S0_coeff_54 : S0.coeff 54 = 296 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_54]

lemma S0_coeff_55 : S0.coeff 55 = 525 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_55]

lemma S0_coeff_56 : S0.coeff 56 = 104 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_56]

lemma S0_coeff_57 : S0.coeff 57 = 92 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_57]

lemma S0_coeff_58 : S0.coeff 58 = 172 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_58]

lemma S0_coeff_59 : S0.coeff 59 = 219 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_59]

lemma S0_coeff_60 : S0.coeff 60 = 51 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_60]

lemma S0_coeff_61 : S0.coeff 61 = 530 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_61]

lemma S0_coeff_62 : S0.coeff 62 = 145 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_62]

lemma S0_coeff_63 : S0.coeff 63 = 520 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_63]

lemma S0_coeff_64 : S0.coeff 64 = 411 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_64]

lemma S0_coeff_65 : S0.coeff 65 = 489 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_65]

lemma S0_coeff_66 : S0.coeff 66 = 430 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_66]

lemma S0_coeff_67 : S0.coeff 67 = 373 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_67]

lemma S0_coeff_68 : S0.coeff 68 = 431 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_68]

lemma S0_coeff_69 : S0.coeff 69 = 240 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_69]

lemma S0_coeff_70 : S0.coeff 70 = 376 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_70]

lemma S0_coeff_71 : S0.coeff 71 = 185 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_71]

lemma S0_coeff_72 : S0.coeff 72 = 505 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_72]

lemma S0_coeff_73 : S0.coeff 73 = 200 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_73]

lemma S0_coeff_74 : S0.coeff 74 = 102 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_74]

lemma S0_coeff_75 : S0.coeff 75 = 60 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_75]

lemma S0_coeff_76 : S0.coeff 76 = 526 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_76]

lemma S0_coeff_77 : S0.coeff 77 = 47 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_77]

lemma S0_coeff_78 : S0.coeff 78 = 487 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_78]

lemma S0_coeff_79 : S0.coeff 79 = 295 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_79]

lemma S0_coeff_80 : S0.coeff 80 = 590 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_80]

/-! ## Chain 1 coefficients, degrees 12..80

For each n the support sum has the 13 terms G.coeff a * S0.coeff (n - a),
a = 0..12, whose S0 indices range over n - 12 .. n within [0, 80]. -/

lemma chain1_coeff_12 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 12 = (G * S0).coeff 12 := by
  rw [G_mul_coeff_ge S0 12 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_13 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 13 = (G * S0).coeff 13 := by
  rw [G_mul_coeff_ge S0 13 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1]
  simp [G, T1]
  decide

lemma chain1_coeff_14 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 14 = (G * S0).coeff 14 := by
  rw [G_mul_coeff_ge S0 14 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2]
  simp [G, T1]
  decide

lemma chain1_coeff_15 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 15 = (G * S0).coeff 15 := by
  rw [G_mul_coeff_ge S0 15 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3]
  simp [G, T1]
  decide

lemma chain1_coeff_16 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 16 = (G * S0).coeff 16 := by
  rw [G_mul_coeff_ge S0 16 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4]
  simp [G, T1]
  decide

lemma chain1_coeff_17 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 17 = (G * S0).coeff 17 := by
  rw [G_mul_coeff_ge S0 17 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5]
  simp [G, T1]
  decide

lemma chain1_coeff_18 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 18 = (G * S0).coeff 18 := by
  rw [G_mul_coeff_ge S0 18 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6]
  simp [G, T1]
  decide

lemma chain1_coeff_19 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 19 = (G * S0).coeff 19 := by
  rw [G_mul_coeff_ge S0 19 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7]
  simp [G, T1]
  decide

lemma chain1_coeff_20 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 20 = (G * S0).coeff 20 := by
  rw [G_mul_coeff_ge S0 20 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8]
  simp [G, T1]
  decide

lemma chain1_coeff_21 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 21 = (G * S0).coeff 21 := by
  rw [G_mul_coeff_ge S0 21 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9]
  simp [G, T1]
  decide

lemma chain1_coeff_22 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 22 = (G * S0).coeff 22 := by
  rw [G_mul_coeff_ge S0 22 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10]
  simp [G, T1]
  decide

lemma chain1_coeff_23 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 23 = (G * S0).coeff 23 := by
  rw [G_mul_coeff_ge S0 23 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12, S0_coeff_11]
  simp [G, T1]
  decide

lemma chain1_coeff_24 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 24 = (G * S0).coeff 24 := by
  rw [G_mul_coeff_ge S0 24 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13, S0_coeff_12]
  simp [G, T1]
  decide

lemma chain1_coeff_25 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 25 = (G * S0).coeff 25 := by
  rw [G_mul_coeff_ge S0 25 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14, S0_coeff_13]
  simp [G, T1]
  decide

lemma chain1_coeff_26 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 26 = (G * S0).coeff 26 := by
  rw [G_mul_coeff_ge S0 26 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15, S0_coeff_14]
  simp [G, T1]
  decide

lemma chain1_coeff_27 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 27 = (G * S0).coeff 27 := by
  rw [G_mul_coeff_ge S0 27 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16, S0_coeff_15]
  simp [G, T1]
  decide

lemma chain1_coeff_28 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 28 = (G * S0).coeff 28 := by
  rw [G_mul_coeff_ge S0 28 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17, S0_coeff_16]
  simp [G, T1]
  decide

lemma chain1_coeff_29 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 29 = (G * S0).coeff 29 := by
  rw [G_mul_coeff_ge S0 29 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18, S0_coeff_17]
  simp [G, T1]
  decide

lemma chain1_coeff_30 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 30 = (G * S0).coeff 30 := by
  rw [G_mul_coeff_ge S0 30 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19, S0_coeff_18]
  simp [G, T1]
  decide

lemma chain1_coeff_31 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 31 = (G * S0).coeff 31 := by
  rw [G_mul_coeff_ge S0 31 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20, S0_coeff_19]
  simp [G, T1]
  decide

lemma chain1_coeff_32 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 32 = (G * S0).coeff 32 := by
  rw [G_mul_coeff_ge S0 32 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21, S0_coeff_20]
  simp [G, T1]
  decide

lemma chain1_coeff_33 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 33 = (G * S0).coeff 33 := by
  rw [G_mul_coeff_ge S0 33 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22, S0_coeff_21]
  simp [G, T1]
  decide

lemma chain1_coeff_34 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 34 = (G * S0).coeff 34 := by
  rw [G_mul_coeff_ge S0 34 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23, S0_coeff_22]
  simp [G, T1]
  decide

lemma chain1_coeff_35 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 35 = (G * S0).coeff 35 := by
  rw [G_mul_coeff_ge S0 35 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24, S0_coeff_23]
  simp [G, T1]
  decide

lemma chain1_coeff_36 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 36 = (G * S0).coeff 36 := by
  rw [G_mul_coeff_ge S0 36 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25, S0_coeff_24]
  simp [G, T1]
  decide

lemma chain1_coeff_37 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 37 = (G * S0).coeff 37 := by
  rw [G_mul_coeff_ge S0 37 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26, S0_coeff_25]
  simp [G, T1]
  decide

lemma chain1_coeff_38 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 38 = (G * S0).coeff 38 := by
  rw [G_mul_coeff_ge S0 38 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27, S0_coeff_26]
  simp [G, T1]
  decide

lemma chain1_coeff_39 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 39 = (G * S0).coeff 39 := by
  rw [G_mul_coeff_ge S0 39 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28, S0_coeff_27]
  simp [G, T1]
  decide

lemma chain1_coeff_40 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 40 = (G * S0).coeff 40 := by
  rw [G_mul_coeff_ge S0 40 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29, S0_coeff_28]
  simp [G, T1]
  decide

lemma chain1_coeff_41 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 41 = (G * S0).coeff 41 := by
  rw [G_mul_coeff_ge S0 41 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30, S0_coeff_29]
  simp [G, T1]
  decide

lemma chain1_coeff_42 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 42 = (G * S0).coeff 42 := by
  rw [G_mul_coeff_ge S0 42 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31, S0_coeff_30]
  simp [G, T1]
  decide

lemma chain1_coeff_43 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 43 = (G * S0).coeff 43 := by
  rw [G_mul_coeff_ge S0 43 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32, S0_coeff_31]
  simp [G, T1]
  decide

lemma chain1_coeff_44 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 44 = (G * S0).coeff 44 := by
  rw [G_mul_coeff_ge S0 44 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33, S0_coeff_32]
  simp [G, T1]
  decide

lemma chain1_coeff_45 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 45 = (G * S0).coeff 45 := by
  rw [G_mul_coeff_ge S0 45 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34, S0_coeff_33]
  simp [G, T1]
  decide

lemma chain1_coeff_46 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 46 = (G * S0).coeff 46 := by
  rw [G_mul_coeff_ge S0 46 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35, S0_coeff_34]
  simp [G, T1]
  decide

lemma chain1_coeff_47 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 47 = (G * S0).coeff 47 := by
  rw [G_mul_coeff_ge S0 47 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36, S0_coeff_35]
  simp [G, T1]
  decide

lemma chain1_coeff_48 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 48 = (G * S0).coeff 48 := by
  rw [G_mul_coeff_ge S0 48 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37, S0_coeff_36]
  simp [G, T1]
  decide

lemma chain1_coeff_49 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 49 = (G * S0).coeff 49 := by
  rw [G_mul_coeff_ge S0 49 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38, S0_coeff_37]
  simp [G, T1]
  decide

lemma chain1_coeff_50 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 50 = (G * S0).coeff 50 := by
  rw [G_mul_coeff_ge S0 50 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39, S0_coeff_38]
  simp [G, T1]
  decide

lemma chain1_coeff_51 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 51 = (G * S0).coeff 51 := by
  rw [G_mul_coeff_ge S0 51 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40, S0_coeff_39]
  simp [G, T1]
  decide

lemma chain1_coeff_52 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 52 = (G * S0).coeff 52 := by
  rw [G_mul_coeff_ge S0 52 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41, S0_coeff_40]
  simp [G, T1]
  decide

lemma chain1_coeff_53 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 53 = (G * S0).coeff 53 := by
  rw [G_mul_coeff_ge S0 53 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42, S0_coeff_41]
  simp [G, T1]
  decide

lemma chain1_coeff_54 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 54 = (G * S0).coeff 54 := by
  rw [G_mul_coeff_ge S0 54 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43, S0_coeff_42]
  simp [G, T1]
  decide

lemma chain1_coeff_55 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 55 = (G * S0).coeff 55 := by
  rw [G_mul_coeff_ge S0 55 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44, S0_coeff_43]
  simp [G, T1]
  decide

lemma chain1_coeff_56 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 56 = (G * S0).coeff 56 := by
  rw [G_mul_coeff_ge S0 56 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45, S0_coeff_44]
  simp [G, T1]
  decide

lemma chain1_coeff_57 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 57 = (G * S0).coeff 57 := by
  rw [G_mul_coeff_ge S0 57 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46, S0_coeff_45]
  simp [G, T1]
  decide

lemma chain1_coeff_58 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 58 = (G * S0).coeff 58 := by
  rw [G_mul_coeff_ge S0 58 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47, S0_coeff_46]
  simp [G, T1]
  decide

lemma chain1_coeff_59 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 59 = (G * S0).coeff 59 := by
  rw [G_mul_coeff_ge S0 59 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48, S0_coeff_47]
  simp [G, T1]
  decide

lemma chain1_coeff_60 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 60 = (G * S0).coeff 60 := by
  rw [G_mul_coeff_ge S0 60 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49, S0_coeff_48]
  simp [G, T1]
  decide

lemma chain1_coeff_61 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 61 = (G * S0).coeff 61 := by
  rw [G_mul_coeff_ge S0 61 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50, S0_coeff_49]
  simp [G, T1]
  decide

lemma chain1_coeff_62 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 62 = (G * S0).coeff 62 := by
  rw [G_mul_coeff_ge S0 62 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51, S0_coeff_50]
  simp [G, T1]
  decide

lemma chain1_coeff_63 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 63 = (G * S0).coeff 63 := by
  rw [G_mul_coeff_ge S0 63 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52, S0_coeff_51]
  simp [G, T1]
  decide

lemma chain1_coeff_64 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 64 = (G * S0).coeff 64 := by
  rw [G_mul_coeff_ge S0 64 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53, S0_coeff_52]
  simp [G, T1]
  decide

lemma chain1_coeff_65 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 65 = (G * S0).coeff 65 := by
  rw [G_mul_coeff_ge S0 65 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54, S0_coeff_53]
  simp [G, T1]
  decide

lemma chain1_coeff_66 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 66 = (G * S0).coeff 66 := by
  rw [G_mul_coeff_ge S0 66 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55, S0_coeff_54]
  simp [G, T1]
  decide

lemma chain1_coeff_67 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 67 = (G * S0).coeff 67 := by
  rw [G_mul_coeff_ge S0 67 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56, S0_coeff_55]
  simp [G, T1]
  decide

lemma chain1_coeff_68 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 68 = (G * S0).coeff 68 := by
  rw [G_mul_coeff_ge S0 68 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57, S0_coeff_56]
  simp [G, T1]
  decide

lemma chain1_coeff_69 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 69 = (G * S0).coeff 69 := by
  rw [G_mul_coeff_ge S0 69 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58, S0_coeff_57]
  simp [G, T1]
  decide

lemma chain1_coeff_70 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 70 = (G * S0).coeff 70 := by
  rw [G_mul_coeff_ge S0 70 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59, S0_coeff_58]
  simp [G, T1]
  decide

lemma chain1_coeff_71 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 71 = (G * S0).coeff 71 := by
  rw [G_mul_coeff_ge S0 71 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60, S0_coeff_59]
  simp [G, T1]
  decide

lemma chain1_coeff_72 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 72 = (G * S0).coeff 72 := by
  rw [G_mul_coeff_ge S0 72 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61, S0_coeff_60]
  simp [G, T1]
  decide

lemma chain1_coeff_73 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 73 = (G * S0).coeff 73 := by
  rw [G_mul_coeff_ge S0 73 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62, S0_coeff_61]
  simp [G, T1]
  decide

lemma chain1_coeff_74 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 74 = (G * S0).coeff 74 := by
  rw [G_mul_coeff_ge S0 74 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63, S0_coeff_62]
  simp [G, T1]
  decide

lemma chain1_coeff_75 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 75 = (G * S0).coeff 75 := by
  rw [G_mul_coeff_ge S0 75 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64, S0_coeff_63]
  simp [G, T1]
  decide

lemma chain1_coeff_76 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 76 = (G * S0).coeff 76 := by
  rw [G_mul_coeff_ge S0 76 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65, S0_coeff_64]
  simp [G, T1]
  decide

lemma chain1_coeff_77 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 77 = (G * S0).coeff 77 := by
  rw [G_mul_coeff_ge S0 77 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66, S0_coeff_65]
  simp [G, T1]
  decide

lemma chain1_coeff_78 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 78 = (G * S0).coeff 78 := by
  rw [G_mul_coeff_ge S0 78 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67, S0_coeff_66]
  simp [G, T1]
  decide

lemma chain1_coeff_79 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 79 = (G * S0).coeff 79 := by
  rw [G_mul_coeff_ge S0 79 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68, S0_coeff_67]
  simp [G, T1]
  decide

lemma chain1_coeff_80 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 80 = (G * S0).coeff 80 := by
  rw [G_mul_coeff_ge S0 80 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69, S0_coeff_68]
  simp [G, T1]
  decide

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid1Actual

end
