import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R0LookupActual
import tmp.sheaf.xif.paper.S2563R1LookupActual

/-!
# S2565Chain1Mid2ActualAdapted

Chain-1 coefficient identity for the middle range n in [81, 160]:

  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

Sources (all already verified in this repository):
* S2560S0ShiftedPartsActual : R0..R7, S0_0..S0_7, S0 := S0_0 + ... + S0_7
  (block i is X^(81*i) * R_i for i <= 1, and X^(80*i+1) * R_i for i >= 1)
* S2563R0LookupActual, S2563R1LookupActual : R_i.coeff j
* S2562GmulCoeffActual : G_mul_coeff_ge (13-term support sum for n >= 12)
* S2554Mod613ChainDataActual : G, T1

Strategy (mirrors S2564Chain1LowActual for n < 12):
* S0 is split into 8 shifted blocks.  For 69 <= k <= 160 only blocks 0 and 1
  can contribute: block 0 starts at 0, block 1 starts at 81, blocks 2..7 start
  at 161,241,321,401,481,561 > 160.  R0 has degree 80, so:
    - 69 <= k <= 80  : S0.coeff k = R0.coeff k
    - 81 <= k <= 160 : S0.coeff k = R1.coeff (k-81)
* For each n in [81,160], expand (G*S0).coeff n with G_mul_coeff_ge, split the
  13-term sum, rewrite the 13 S0 lookups, then close the concrete ZMod 613
  computation by simp [G, T1] + decide.
* Since n < 613, ((X)^613).coeff n = 0, so the left side is 0 (T1 has degree 11).
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2565Chain1Mid2ActualAdapted

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R0LookupActual
open LeanFormal.IUT.XiFPaper.S2563R1LookupActual

/-! ## Degree bounds for the first two blocks -/

/-- Transparent alias of `S2560S0ShiftedPartsActual.R0`; the root namespace also
contains an unrelated dummy `R0 : (ZMod 29)[X]`, which this alias disambiguates. -/
abbrev R0p : (ZMod 613)[X] := LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0

/-- Transparent alias of `S2560S0ShiftedPartsActual.R1` (cf. the root `R1`). -/
abbrev R1p : (ZMod 613)[X] := LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1

/-- R0 has degree at most 80, so its coefficients vanish beyond 80. -/
lemma R0_coeff_eq_zero_of_gt (k : ℕ) (hk : 80 < k) : R0p.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : R0p.natDegree ≤ 80 := by
    unfold R0p LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0
    compute_degree!
  omega

/-- R1 has degree at most 79, so its coefficients vanish beyond 79. -/
lemma R1_coeff_eq_zero_of_gt (k : ℕ) (hk : 79 < k) : R1p.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : R1p.natDegree ≤ 79 := by
    unfold R1p LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1
    compute_degree!
  omega

/-! ## S0 coefficient lookup on 69 .. 160 -/

/-- `S0.coeff 69 = 240` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_69 : S0.coeff 69 = 240 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_69]

/-- `S0.coeff 70 = 376` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_70 : S0.coeff 70 = 376 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_70]

/-- `S0.coeff 71 = 185` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_71 : S0.coeff 71 = 185 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_71]

/-- `S0.coeff 72 = 505` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_72 : S0.coeff 72 = 505 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_72]

/-- `S0.coeff 73 = 200` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_73 : S0.coeff 73 = 200 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_73]

/-- `S0.coeff 74 = 102` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_74 : S0.coeff 74 = 102 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_74]

/-- `S0.coeff 75 = 60` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_75 : S0.coeff 75 = 60 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_75]

/-- `S0.coeff 76 = 526` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_76 : S0.coeff 76 = 526 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_76]

/-- `S0.coeff 77 = 47` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_77 : S0.coeff 77 = 47 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_77]

/-- `S0.coeff 78 = 487` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_78 : S0.coeff 78 = 487 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_78]

/-- `S0.coeff 79 = 295` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_79 : S0.coeff 79 = 295 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_79]

/-- `S0.coeff 80 = 590` (block 0 only: `S0_0 = R0`). -/
lemma S0_coeff_80 : S0.coeff 80 = 590 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, R0_coeff_80]

/-- `S0.coeff 81 = 240` (blocks 0 and 1 only: `R1.coeff 0`). -/
lemma S0_coeff_81 : S0.coeff 81 = 240 := by
  have h0 : R0p.coeff 81 = 0 := R0_coeff_eq_zero_of_gt 81 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_0]

/-- `S0.coeff 82 = 573` (blocks 0 and 1 only: `R1.coeff 1`). -/
lemma S0_coeff_82 : S0.coeff 82 = 573 := by
  have h0 : R0p.coeff 82 = 0 := R0_coeff_eq_zero_of_gt 82 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_1]

/-- `S0.coeff 83 = 118` (blocks 0 and 1 only: `R1.coeff 2`). -/
lemma S0_coeff_83 : S0.coeff 83 = 118 := by
  have h0 : R0p.coeff 83 = 0 := R0_coeff_eq_zero_of_gt 83 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_2]

/-- `S0.coeff 84 = 491` (blocks 0 and 1 only: `R1.coeff 3`). -/
lemma S0_coeff_84 : S0.coeff 84 = 491 := by
  have h0 : R0p.coeff 84 = 0 := R0_coeff_eq_zero_of_gt 84 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_3]

/-- `S0.coeff 85 = 112` (blocks 0 and 1 only: `R1.coeff 4`). -/
lemma S0_coeff_85 : S0.coeff 85 = 112 := by
  have h0 : R0p.coeff 85 = 0 := R0_coeff_eq_zero_of_gt 85 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_4]

/-- `S0.coeff 86 = 556` (blocks 0 and 1 only: `R1.coeff 5`). -/
lemma S0_coeff_86 : S0.coeff 86 = 556 := by
  have h0 : R0p.coeff 86 = 0 := R0_coeff_eq_zero_of_gt 86 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_5]

/-- `S0.coeff 87 = 112` (blocks 0 and 1 only: `R1.coeff 6`). -/
lemma S0_coeff_87 : S0.coeff 87 = 112 := by
  have h0 : R0p.coeff 87 = 0 := R0_coeff_eq_zero_of_gt 87 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_6]

/-- `S0.coeff 88 = 294` (blocks 0 and 1 only: `R1.coeff 7`). -/
lemma S0_coeff_88 : S0.coeff 88 = 294 := by
  have h0 : R0p.coeff 88 = 0 := R0_coeff_eq_zero_of_gt 88 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_7]

/-- `S0.coeff 89 = 564` (blocks 0 and 1 only: `R1.coeff 8`). -/
lemma S0_coeff_89 : S0.coeff 89 = 564 := by
  have h0 : R0p.coeff 89 = 0 := R0_coeff_eq_zero_of_gt 89 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_8]

/-- `S0.coeff 90 = 216` (blocks 0 and 1 only: `R1.coeff 9`). -/
lemma S0_coeff_90 : S0.coeff 90 = 216 := by
  have h0 : R0p.coeff 90 = 0 := R0_coeff_eq_zero_of_gt 90 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_9]

/-- `S0.coeff 91 = 245` (blocks 0 and 1 only: `R1.coeff 10`). -/
lemma S0_coeff_91 : S0.coeff 91 = 245 := by
  have h0 : R0p.coeff 91 = 0 := R0_coeff_eq_zero_of_gt 91 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_10]

/-- `S0.coeff 92 = 6` (blocks 0 and 1 only: `R1.coeff 11`). -/
lemma S0_coeff_92 : S0.coeff 92 = 6 := by
  have h0 : R0p.coeff 92 = 0 := R0_coeff_eq_zero_of_gt 92 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_11]

/-- `S0.coeff 93 = 208` (blocks 0 and 1 only: `R1.coeff 12`). -/
lemma S0_coeff_93 : S0.coeff 93 = 208 := by
  have h0 : R0p.coeff 93 = 0 := R0_coeff_eq_zero_of_gt 93 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_12]

/-- `S0.coeff 94 = 204` (blocks 0 and 1 only: `R1.coeff 13`). -/
lemma S0_coeff_94 : S0.coeff 94 = 204 := by
  have h0 : R0p.coeff 94 = 0 := R0_coeff_eq_zero_of_gt 94 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_13]

/-- `S0.coeff 95 = 477` (blocks 0 and 1 only: `R1.coeff 14`). -/
lemma S0_coeff_95 : S0.coeff 95 = 477 := by
  have h0 : R0p.coeff 95 = 0 := R0_coeff_eq_zero_of_gt 95 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_14]

/-- `S0.coeff 96 = 533` (blocks 0 and 1 only: `R1.coeff 15`). -/
lemma S0_coeff_96 : S0.coeff 96 = 533 := by
  have h0 : R0p.coeff 96 = 0 := R0_coeff_eq_zero_of_gt 96 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_15]

/-- `S0.coeff 97 = 72` (blocks 0 and 1 only: `R1.coeff 16`). -/
lemma S0_coeff_97 : S0.coeff 97 = 72 := by
  have h0 : R0p.coeff 97 = 0 := R0_coeff_eq_zero_of_gt 97 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_16]

/-- `S0.coeff 98 = 84` (blocks 0 and 1 only: `R1.coeff 17`). -/
lemma S0_coeff_98 : S0.coeff 98 = 84 := by
  have h0 : R0p.coeff 98 = 0 := R0_coeff_eq_zero_of_gt 98 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_17]

/-- `S0.coeff 99 = 238` (blocks 0 and 1 only: `R1.coeff 18`). -/
lemma S0_coeff_99 : S0.coeff 99 = 238 := by
  have h0 : R0p.coeff 99 = 0 := R0_coeff_eq_zero_of_gt 99 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_18]

/-- `S0.coeff 100 = 259` (blocks 0 and 1 only: `R1.coeff 19`). -/
lemma S0_coeff_100 : S0.coeff 100 = 259 := by
  have h0 : R0p.coeff 100 = 0 := R0_coeff_eq_zero_of_gt 100 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_19]

/-- `S0.coeff 101 = 506` (blocks 0 and 1 only: `R1.coeff 20`). -/
lemma S0_coeff_101 : S0.coeff 101 = 506 := by
  have h0 : R0p.coeff 101 = 0 := R0_coeff_eq_zero_of_gt 101 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_20]

/-- `S0.coeff 102 = 391` (blocks 0 and 1 only: `R1.coeff 21`). -/
lemma S0_coeff_102 : S0.coeff 102 = 391 := by
  have h0 : R0p.coeff 102 = 0 := R0_coeff_eq_zero_of_gt 102 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_21]

/-- `S0.coeff 103 = 459` (blocks 0 and 1 only: `R1.coeff 22`). -/
lemma S0_coeff_103 : S0.coeff 103 = 459 := by
  have h0 : R0p.coeff 103 = 0 := R0_coeff_eq_zero_of_gt 103 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_22]

/-- `S0.coeff 104 = 486` (blocks 0 and 1 only: `R1.coeff 23`). -/
lemma S0_coeff_104 : S0.coeff 104 = 486 := by
  have h0 : R0p.coeff 104 = 0 := R0_coeff_eq_zero_of_gt 104 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_23]

/-- `S0.coeff 105 = 280` (blocks 0 and 1 only: `R1.coeff 24`). -/
lemma S0_coeff_105 : S0.coeff 105 = 280 := by
  have h0 : R0p.coeff 105 = 0 := R0_coeff_eq_zero_of_gt 105 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_24]

/-- `S0.coeff 106 = 331` (blocks 0 and 1 only: `R1.coeff 25`). -/
lemma S0_coeff_106 : S0.coeff 106 = 331 := by
  have h0 : R0p.coeff 106 = 0 := R0_coeff_eq_zero_of_gt 106 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_25]

/-- `S0.coeff 107 = 499` (blocks 0 and 1 only: `R1.coeff 26`). -/
lemma S0_coeff_107 : S0.coeff 107 = 499 := by
  have h0 : R0p.coeff 107 = 0 := R0_coeff_eq_zero_of_gt 107 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_26]

/-- `S0.coeff 108 = 504` (blocks 0 and 1 only: `R1.coeff 27`). -/
lemma S0_coeff_108 : S0.coeff 108 = 504 := by
  have h0 : R0p.coeff 108 = 0 := R0_coeff_eq_zero_of_gt 108 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_27]

/-- `S0.coeff 109 = 68` (blocks 0 and 1 only: `R1.coeff 28`). -/
lemma S0_coeff_109 : S0.coeff 109 = 68 := by
  have h0 : R0p.coeff 109 = 0 := R0_coeff_eq_zero_of_gt 109 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_28]

/-- `S0.coeff 110 = 520` (blocks 0 and 1 only: `R1.coeff 29`). -/
lemma S0_coeff_110 : S0.coeff 110 = 520 := by
  have h0 : R0p.coeff 110 = 0 := R0_coeff_eq_zero_of_gt 110 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_29]

/-- `S0.coeff 111 = 436` (blocks 0 and 1 only: `R1.coeff 30`). -/
lemma S0_coeff_111 : S0.coeff 111 = 436 := by
  have h0 : R0p.coeff 111 = 0 := R0_coeff_eq_zero_of_gt 111 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_30]

/-- `S0.coeff 112 = 217` (blocks 0 and 1 only: `R1.coeff 31`). -/
lemma S0_coeff_112 : S0.coeff 112 = 217 := by
  have h0 : R0p.coeff 112 = 0 := R0_coeff_eq_zero_of_gt 112 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_31]

/-- `S0.coeff 113 = 226` (blocks 0 and 1 only: `R1.coeff 32`). -/
lemma S0_coeff_113 : S0.coeff 113 = 226 := by
  have h0 : R0p.coeff 113 = 0 := R0_coeff_eq_zero_of_gt 113 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_32]

/-- `S0.coeff 114 = 471` (blocks 0 and 1 only: `R1.coeff 33`). -/
lemma S0_coeff_114 : S0.coeff 114 = 471 := by
  have h0 : R0p.coeff 114 = 0 := R0_coeff_eq_zero_of_gt 114 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_33]

/-- `S0.coeff 115 = 604` (blocks 0 and 1 only: `R1.coeff 34`). -/
lemma S0_coeff_115 : S0.coeff 115 = 604 := by
  have h0 : R0p.coeff 115 = 0 := R0_coeff_eq_zero_of_gt 115 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_34]

/-- `S0.coeff 116 = 442` (blocks 0 and 1 only: `R1.coeff 35`). -/
lemma S0_coeff_116 : S0.coeff 116 = 442 := by
  have h0 : R0p.coeff 116 = 0 := R0_coeff_eq_zero_of_gt 116 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_35]

/-- `S0.coeff 117 = 217` (blocks 0 and 1 only: `R1.coeff 36`). -/
lemma S0_coeff_117 : S0.coeff 117 = 217 := by
  have h0 : R0p.coeff 117 = 0 := R0_coeff_eq_zero_of_gt 117 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_36]

/-- `S0.coeff 118 = 197` (blocks 0 and 1 only: `R1.coeff 37`). -/
lemma S0_coeff_118 : S0.coeff 118 = 197 := by
  have h0 : R0p.coeff 118 = 0 := R0_coeff_eq_zero_of_gt 118 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_37]

/-- `S0.coeff 119 = 553` (blocks 0 and 1 only: `R1.coeff 38`). -/
lemma S0_coeff_119 : S0.coeff 119 = 553 := by
  have h0 : R0p.coeff 119 = 0 := R0_coeff_eq_zero_of_gt 119 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_38]

/-- `S0.coeff 120 = 192` (blocks 0 and 1 only: `R1.coeff 39`). -/
lemma S0_coeff_120 : S0.coeff 120 = 192 := by
  have h0 : R0p.coeff 120 = 0 := R0_coeff_eq_zero_of_gt 120 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_39]

/-- `S0.coeff 121 = 83` (blocks 0 and 1 only: `R1.coeff 40`). -/
lemma S0_coeff_121 : S0.coeff 121 = 83 := by
  have h0 : R0p.coeff 121 = 0 := R0_coeff_eq_zero_of_gt 121 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_40]

/-- `S0.coeff 122 = 100` (blocks 0 and 1 only: `R1.coeff 41`). -/
lemma S0_coeff_122 : S0.coeff 122 = 100 := by
  have h0 : R0p.coeff 122 = 0 := R0_coeff_eq_zero_of_gt 122 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_41]

/-- `S0.coeff 123 = 319` (blocks 0 and 1 only: `R1.coeff 42`). -/
lemma S0_coeff_123 : S0.coeff 123 = 319 := by
  have h0 : R0p.coeff 123 = 0 := R0_coeff_eq_zero_of_gt 123 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_42]

/-- `S0.coeff 124 = 116` (blocks 0 and 1 only: `R1.coeff 43`). -/
lemma S0_coeff_124 : S0.coeff 124 = 116 := by
  have h0 : R0p.coeff 124 = 0 := R0_coeff_eq_zero_of_gt 124 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_43]

/-- `S0.coeff 125 = 256` (blocks 0 and 1 only: `R1.coeff 44`). -/
lemma S0_coeff_125 : S0.coeff 125 = 256 := by
  have h0 : R0p.coeff 125 = 0 := R0_coeff_eq_zero_of_gt 125 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_44]

/-- `S0.coeff 126 = 444` (blocks 0 and 1 only: `R1.coeff 45`). -/
lemma S0_coeff_126 : S0.coeff 126 = 444 := by
  have h0 : R0p.coeff 126 = 0 := R0_coeff_eq_zero_of_gt 126 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_45]

/-- `S0.coeff 127 = 168` (blocks 0 and 1 only: `R1.coeff 46`). -/
lemma S0_coeff_127 : S0.coeff 127 = 168 := by
  have h0 : R0p.coeff 127 = 0 := R0_coeff_eq_zero_of_gt 127 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_46]

/-- `S0.coeff 128 = 336` (blocks 0 and 1 only: `R1.coeff 47`). -/
lemma S0_coeff_128 : S0.coeff 128 = 336 := by
  have h0 : R0p.coeff 128 = 0 := R0_coeff_eq_zero_of_gt 128 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_47]

/-- `S0.coeff 129 = 383` (blocks 0 and 1 only: `R1.coeff 48`). -/
lemma S0_coeff_129 : S0.coeff 129 = 383 := by
  have h0 : R0p.coeff 129 = 0 := R0_coeff_eq_zero_of_gt 129 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_48]

/-- `S0.coeff 130 = 463` (blocks 0 and 1 only: `R1.coeff 49`). -/
lemma S0_coeff_130 : S0.coeff 130 = 463 := by
  have h0 : R0p.coeff 130 = 0 := R0_coeff_eq_zero_of_gt 130 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_49]

/-- `S0.coeff 131 = 115` (blocks 0 and 1 only: `R1.coeff 50`). -/
lemma S0_coeff_131 : S0.coeff 131 = 115 := by
  have h0 : R0p.coeff 131 = 0 := R0_coeff_eq_zero_of_gt 131 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_50]

/-- `S0.coeff 132 = 570` (blocks 0 and 1 only: `R1.coeff 51`). -/
lemma S0_coeff_132 : S0.coeff 132 = 570 := by
  have h0 : R0p.coeff 132 = 0 := R0_coeff_eq_zero_of_gt 132 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_51]

/-- `S0.coeff 133 = 516` (blocks 0 and 1 only: `R1.coeff 52`). -/
lemma S0_coeff_133 : S0.coeff 133 = 516 := by
  have h0 : R0p.coeff 133 = 0 := R0_coeff_eq_zero_of_gt 133 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_52]

/-- `S0.coeff 134 = 62` (blocks 0 and 1 only: `R1.coeff 53`). -/
lemma S0_coeff_134 : S0.coeff 134 = 62 := by
  have h0 : R0p.coeff 134 = 0 := R0_coeff_eq_zero_of_gt 134 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_53]

/-- `S0.coeff 135 = 29` (blocks 0 and 1 only: `R1.coeff 54`). -/
lemma S0_coeff_135 : S0.coeff 135 = 29 := by
  have h0 : R0p.coeff 135 = 0 := R0_coeff_eq_zero_of_gt 135 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_54]

/-- `S0.coeff 136 = 45` (blocks 0 and 1 only: `R1.coeff 55`). -/
lemma S0_coeff_136 : S0.coeff 136 = 45 := by
  have h0 : R0p.coeff 136 = 0 := R0_coeff_eq_zero_of_gt 136 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_55]

/-- `S0.coeff 137 = 127` (blocks 0 and 1 only: `R1.coeff 56`). -/
lemma S0_coeff_137 : S0.coeff 137 = 127 := by
  have h0 : R0p.coeff 137 = 0 := R0_coeff_eq_zero_of_gt 137 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_56]

/-- `S0.coeff 138 = 353` (blocks 0 and 1 only: `R1.coeff 57`). -/
lemma S0_coeff_138 : S0.coeff 138 = 353 := by
  have h0 : R0p.coeff 138 = 0 := R0_coeff_eq_zero_of_gt 138 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_57]

/-- `S0.coeff 139 = 128` (blocks 0 and 1 only: `R1.coeff 58`). -/
lemma S0_coeff_139 : S0.coeff 139 = 128 := by
  have h0 : R0p.coeff 139 = 0 := R0_coeff_eq_zero_of_gt 139 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_58]

/-- `S0.coeff 140 = 479` (blocks 0 and 1 only: `R1.coeff 59`). -/
lemma S0_coeff_140 : S0.coeff 140 = 479 := by
  have h0 : R0p.coeff 140 = 0 := R0_coeff_eq_zero_of_gt 140 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_59]

/-- `S0.coeff 141 = 218` (blocks 0 and 1 only: `R1.coeff 60`). -/
lemma S0_coeff_141 : S0.coeff 141 = 218 := by
  have h0 : R0p.coeff 141 = 0 := R0_coeff_eq_zero_of_gt 141 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_60]

/-- `S0.coeff 142 = 474` (blocks 0 and 1 only: `R1.coeff 61`). -/
lemma S0_coeff_142 : S0.coeff 142 = 474 := by
  have h0 : R0p.coeff 142 = 0 := R0_coeff_eq_zero_of_gt 142 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_61]

/-- `S0.coeff 143 = 570` (blocks 0 and 1 only: `R1.coeff 62`). -/
lemma S0_coeff_143 : S0.coeff 143 = 570 := by
  have h0 : R0p.coeff 143 = 0 := R0_coeff_eq_zero_of_gt 143 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_62]

/-- `S0.coeff 144 = 441` (blocks 0 and 1 only: `R1.coeff 63`). -/
lemma S0_coeff_144 : S0.coeff 144 = 441 := by
  have h0 : R0p.coeff 144 = 0 := R0_coeff_eq_zero_of_gt 144 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_63]

/-- `S0.coeff 145 = 530` (blocks 0 and 1 only: `R1.coeff 64`). -/
lemma S0_coeff_145 : S0.coeff 145 = 530 := by
  have h0 : R0p.coeff 145 = 0 := R0_coeff_eq_zero_of_gt 145 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_64]

/-- `S0.coeff 146 = 449` (blocks 0 and 1 only: `R1.coeff 65`). -/
lemma S0_coeff_146 : S0.coeff 146 = 449 := by
  have h0 : R0p.coeff 146 = 0 := R0_coeff_eq_zero_of_gt 146 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_65]

/-- `S0.coeff 147 = 26` (blocks 0 and 1 only: `R1.coeff 66`). -/
lemma S0_coeff_147 : S0.coeff 147 = 26 := by
  have h0 : R0p.coeff 147 = 0 := R0_coeff_eq_zero_of_gt 147 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_66]

/-- `S0.coeff 148 = 371` (blocks 0 and 1 only: `R1.coeff 67`). -/
lemma S0_coeff_148 : S0.coeff 148 = 371 := by
  have h0 : R0p.coeff 148 = 0 := R0_coeff_eq_zero_of_gt 148 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_67]

/-- `S0.coeff 149 = 345` (blocks 0 and 1 only: `R1.coeff 68`). -/
lemma S0_coeff_149 : S0.coeff 149 = 345 := by
  have h0 : R0p.coeff 149 = 0 := R0_coeff_eq_zero_of_gt 149 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_68]

/-- `S0.coeff 150 = 547` (blocks 0 and 1 only: `R1.coeff 69`). -/
lemma S0_coeff_150 : S0.coeff 150 = 547 := by
  have h0 : R0p.coeff 150 = 0 := R0_coeff_eq_zero_of_gt 150 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_69]

/-- `S0.coeff 151 = 485` (blocks 0 and 1 only: `R1.coeff 70`). -/
lemma S0_coeff_151 : S0.coeff 151 = 485 := by
  have h0 : R0p.coeff 151 = 0 := R0_coeff_eq_zero_of_gt 151 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_70]

/-- `S0.coeff 152 = 184` (blocks 0 and 1 only: `R1.coeff 71`). -/
lemma S0_coeff_152 : S0.coeff 152 = 184 := by
  have h0 : R0p.coeff 152 = 0 := R0_coeff_eq_zero_of_gt 152 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_71]

/-- `S0.coeff 153 = 501` (blocks 0 and 1 only: `R1.coeff 72`). -/
lemma S0_coeff_153 : S0.coeff 153 = 501 := by
  have h0 : R0p.coeff 153 = 0 := R0_coeff_eq_zero_of_gt 153 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_72]

/-- `S0.coeff 154 = 518` (blocks 0 and 1 only: `R1.coeff 73`). -/
lemma S0_coeff_154 : S0.coeff 154 = 518 := by
  have h0 : R0p.coeff 154 = 0 := R0_coeff_eq_zero_of_gt 154 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_73]

/-- `S0.coeff 155 = 612` (blocks 0 and 1 only: `R1.coeff 74`). -/
lemma S0_coeff_155 : S0.coeff 155 = 612 := by
  have h0 : R0p.coeff 155 = 0 := R0_coeff_eq_zero_of_gt 155 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_74]

/-- `S0.coeff 156 = 107` (blocks 0 and 1 only: `R1.coeff 75`). -/
lemma S0_coeff_156 : S0.coeff 156 = 107 := by
  have h0 : R0p.coeff 156 = 0 := R0_coeff_eq_zero_of_gt 156 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_75]

/-- `S0.coeff 157 = 253` (blocks 0 and 1 only: `R1.coeff 76`). -/
lemma S0_coeff_157 : S0.coeff 157 = 253 := by
  have h0 : R0p.coeff 157 = 0 := R0_coeff_eq_zero_of_gt 157 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_76]

/-- `S0.coeff 158 = 483` (blocks 0 and 1 only: `R1.coeff 77`). -/
lemma S0_coeff_158 : S0.coeff 158 = 483 := by
  have h0 : R0p.coeff 158 = 0 := R0_coeff_eq_zero_of_gt 158 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_77]

/-- `S0.coeff 159 = 21` (blocks 0 and 1 only: `R1.coeff 78`). -/
lemma S0_coeff_159 : S0.coeff 159 = 21 := by
  have h0 : R0p.coeff 159 = 0 := R0_coeff_eq_zero_of_gt 159 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_78]

/-- `S0.coeff 160 = 363` (blocks 0 and 1 only: `R1.coeff 79`). -/
lemma S0_coeff_160 : S0.coeff 160 = 363 := by
  have h0 : R0p.coeff 160 = 0 := R0_coeff_eq_zero_of_gt 160 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff,
    S0_6_coeff, S0_7_coeff, h0, R1_coeff_79]

/-! ## Chain-1 identity on the range [81, 160] -/

lemma chain1_coeff_81 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 81 = (G * S0).coeff 81 := by
  rw [G_mul_coeff_ge S0 81 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70, S0_coeff_69]
  simp [G, T1]
  decide

lemma chain1_coeff_82 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 82 = (G * S0).coeff 82 := by
  rw [G_mul_coeff_ge S0 82 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71, S0_coeff_70]
  simp [G, T1]
  decide

lemma chain1_coeff_83 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 83 = (G * S0).coeff 83 := by
  rw [G_mul_coeff_ge S0 83 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72, S0_coeff_71]
  simp [G, T1]
  decide

lemma chain1_coeff_84 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 84 = (G * S0).coeff 84 := by
  rw [G_mul_coeff_ge S0 84 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73, S0_coeff_72]
  simp [G, T1]
  decide

lemma chain1_coeff_85 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 85 = (G * S0).coeff 85 := by
  rw [G_mul_coeff_ge S0 85 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74, S0_coeff_73]
  simp [G, T1]
  decide

lemma chain1_coeff_86 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 86 = (G * S0).coeff 86 := by
  rw [G_mul_coeff_ge S0 86 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75, S0_coeff_74]
  simp [G, T1]
  decide

lemma chain1_coeff_87 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 87 = (G * S0).coeff 87 := by
  rw [G_mul_coeff_ge S0 87 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76, S0_coeff_75]
  simp [G, T1]
  decide

lemma chain1_coeff_88 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 88 = (G * S0).coeff 88 := by
  rw [G_mul_coeff_ge S0 88 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77, S0_coeff_76]
  simp [G, T1]
  decide

lemma chain1_coeff_89 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 89 = (G * S0).coeff 89 := by
  rw [G_mul_coeff_ge S0 89 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78, S0_coeff_77]
  simp [G, T1]
  decide

lemma chain1_coeff_90 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 90 = (G * S0).coeff 90 := by
  rw [G_mul_coeff_ge S0 90 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79, S0_coeff_78]
  simp [G, T1]
  decide

lemma chain1_coeff_91 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 91 = (G * S0).coeff 91 := by
  rw [G_mul_coeff_ge S0 91 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80, S0_coeff_79]
  simp [G, T1]
  decide

lemma chain1_coeff_92 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 92 = (G * S0).coeff 92 := by
  rw [G_mul_coeff_ge S0 92 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81, S0_coeff_80]
  simp [G, T1]
  decide

lemma chain1_coeff_93 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 93 = (G * S0).coeff 93 := by
  rw [G_mul_coeff_ge S0 93 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82, S0_coeff_81]
  simp [G, T1]
  decide

lemma chain1_coeff_94 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 94 = (G * S0).coeff 94 := by
  rw [G_mul_coeff_ge S0 94 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83, S0_coeff_82]
  simp [G, T1]
  decide

lemma chain1_coeff_95 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 95 = (G * S0).coeff 95 := by
  rw [G_mul_coeff_ge S0 95 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84, S0_coeff_83]
  simp [G, T1]
  decide

lemma chain1_coeff_96 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 96 = (G * S0).coeff 96 := by
  rw [G_mul_coeff_ge S0 96 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85, S0_coeff_84]
  simp [G, T1]
  decide

lemma chain1_coeff_97 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 97 = (G * S0).coeff 97 := by
  rw [G_mul_coeff_ge S0 97 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86, S0_coeff_85]
  simp [G, T1]
  decide

lemma chain1_coeff_98 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 98 = (G * S0).coeff 98 := by
  rw [G_mul_coeff_ge S0 98 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87, S0_coeff_86]
  simp [G, T1]
  decide

lemma chain1_coeff_99 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 99 = (G * S0).coeff 99 := by
  rw [G_mul_coeff_ge S0 99 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88, S0_coeff_87]
  simp [G, T1]
  decide

lemma chain1_coeff_100 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 100 = (G * S0).coeff 100 := by
  rw [G_mul_coeff_ge S0 100 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89, S0_coeff_88]
  simp [G, T1]
  decide

lemma chain1_coeff_101 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 101 = (G * S0).coeff 101 := by
  rw [G_mul_coeff_ge S0 101 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90, S0_coeff_89]
  simp [G, T1]
  decide

lemma chain1_coeff_102 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 102 = (G * S0).coeff 102 := by
  rw [G_mul_coeff_ge S0 102 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91, S0_coeff_90]
  simp [G, T1]
  decide

lemma chain1_coeff_103 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 103 = (G * S0).coeff 103 := by
  rw [G_mul_coeff_ge S0 103 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92, S0_coeff_91]
  simp [G, T1]
  decide

lemma chain1_coeff_104 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 104 = (G * S0).coeff 104 := by
  rw [G_mul_coeff_ge S0 104 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93, S0_coeff_92]
  simp [G, T1]
  decide

lemma chain1_coeff_105 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 105 = (G * S0).coeff 105 := by
  rw [G_mul_coeff_ge S0 105 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94, S0_coeff_93]
  simp [G, T1]
  decide

lemma chain1_coeff_106 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 106 = (G * S0).coeff 106 := by
  rw [G_mul_coeff_ge S0 106 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95, S0_coeff_94]
  simp [G, T1]
  decide

lemma chain1_coeff_107 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 107 = (G * S0).coeff 107 := by
  rw [G_mul_coeff_ge S0 107 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96, S0_coeff_95]
  simp [G, T1]
  decide

lemma chain1_coeff_108 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 108 = (G * S0).coeff 108 := by
  rw [G_mul_coeff_ge S0 108 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97, S0_coeff_96]
  simp [G, T1]
  decide

lemma chain1_coeff_109 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 109 = (G * S0).coeff 109 := by
  rw [G_mul_coeff_ge S0 109 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98, S0_coeff_97]
  simp [G, T1]
  decide

lemma chain1_coeff_110 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 110 = (G * S0).coeff 110 := by
  rw [G_mul_coeff_ge S0 110 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99, S0_coeff_98]
  simp [G, T1]
  decide

lemma chain1_coeff_111 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 111 = (G * S0).coeff 111 := by
  rw [G_mul_coeff_ge S0 111 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100, S0_coeff_99]
  simp [G, T1]
  decide

lemma chain1_coeff_112 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 112 = (G * S0).coeff 112 := by
  rw [G_mul_coeff_ge S0 112 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101, S0_coeff_100]
  simp [G, T1]
  decide

lemma chain1_coeff_113 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 113 = (G * S0).coeff 113 := by
  rw [G_mul_coeff_ge S0 113 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102, S0_coeff_101]
  simp [G, T1]
  decide

lemma chain1_coeff_114 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 114 = (G * S0).coeff 114 := by
  rw [G_mul_coeff_ge S0 114 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103, S0_coeff_102]
  simp [G, T1]
  decide

lemma chain1_coeff_115 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 115 = (G * S0).coeff 115 := by
  rw [G_mul_coeff_ge S0 115 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104, S0_coeff_103]
  simp [G, T1]
  decide

lemma chain1_coeff_116 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 116 = (G * S0).coeff 116 := by
  rw [G_mul_coeff_ge S0 116 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105, S0_coeff_104]
  simp [G, T1]
  decide

lemma chain1_coeff_117 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 117 = (G * S0).coeff 117 := by
  rw [G_mul_coeff_ge S0 117 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106, S0_coeff_105]
  simp [G, T1]
  decide

lemma chain1_coeff_118 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 118 = (G * S0).coeff 118 := by
  rw [G_mul_coeff_ge S0 118 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107, S0_coeff_106]
  simp [G, T1]
  decide

lemma chain1_coeff_119 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 119 = (G * S0).coeff 119 := by
  rw [G_mul_coeff_ge S0 119 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108, S0_coeff_107]
  simp [G, T1]
  decide

lemma chain1_coeff_120 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 120 = (G * S0).coeff 120 := by
  rw [G_mul_coeff_ge S0 120 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109, S0_coeff_108]
  simp [G, T1]
  decide

lemma chain1_coeff_121 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 121 = (G * S0).coeff 121 := by
  rw [G_mul_coeff_ge S0 121 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110, S0_coeff_109]
  simp [G, T1]
  decide

lemma chain1_coeff_122 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 122 = (G * S0).coeff 122 := by
  rw [G_mul_coeff_ge S0 122 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111, S0_coeff_110]
  simp [G, T1]
  decide

lemma chain1_coeff_123 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 123 = (G * S0).coeff 123 := by
  rw [G_mul_coeff_ge S0 123 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112, S0_coeff_111]
  simp [G, T1]
  decide

lemma chain1_coeff_124 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 124 = (G * S0).coeff 124 := by
  rw [G_mul_coeff_ge S0 124 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113, S0_coeff_112]
  simp [G, T1]
  decide

lemma chain1_coeff_125 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 125 = (G * S0).coeff 125 := by
  rw [G_mul_coeff_ge S0 125 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114, S0_coeff_113]
  simp [G, T1]
  decide

lemma chain1_coeff_126 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 126 = (G * S0).coeff 126 := by
  rw [G_mul_coeff_ge S0 126 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115, S0_coeff_114]
  simp [G, T1]
  decide

lemma chain1_coeff_127 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 127 = (G * S0).coeff 127 := by
  rw [G_mul_coeff_ge S0 127 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116, S0_coeff_115]
  simp [G, T1]
  decide

lemma chain1_coeff_128 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 128 = (G * S0).coeff 128 := by
  rw [G_mul_coeff_ge S0 128 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117, S0_coeff_116]
  simp [G, T1]
  decide

lemma chain1_coeff_129 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 129 = (G * S0).coeff 129 := by
  rw [G_mul_coeff_ge S0 129 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118, S0_coeff_117]
  simp [G, T1]
  decide

lemma chain1_coeff_130 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 130 = (G * S0).coeff 130 := by
  rw [G_mul_coeff_ge S0 130 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119, S0_coeff_118]
  simp [G, T1]
  decide

lemma chain1_coeff_131 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 131 = (G * S0).coeff 131 := by
  rw [G_mul_coeff_ge S0 131 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120, S0_coeff_119]
  simp [G, T1]
  decide

lemma chain1_coeff_132 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 132 = (G * S0).coeff 132 := by
  rw [G_mul_coeff_ge S0 132 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121, S0_coeff_120]
  simp [G, T1]
  decide

lemma chain1_coeff_133 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 133 = (G * S0).coeff 133 := by
  rw [G_mul_coeff_ge S0 133 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122, S0_coeff_121]
  simp [G, T1]
  decide

lemma chain1_coeff_134 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 134 = (G * S0).coeff 134 := by
  rw [G_mul_coeff_ge S0 134 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123, S0_coeff_122]
  simp [G, T1]
  decide

lemma chain1_coeff_135 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 135 = (G * S0).coeff 135 := by
  rw [G_mul_coeff_ge S0 135 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124, S0_coeff_123]
  simp [G, T1]
  decide

lemma chain1_coeff_136 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 136 = (G * S0).coeff 136 := by
  rw [G_mul_coeff_ge S0 136 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125, S0_coeff_124]
  simp [G, T1]
  decide

lemma chain1_coeff_137 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 137 = (G * S0).coeff 137 := by
  rw [G_mul_coeff_ge S0 137 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126, S0_coeff_125]
  simp [G, T1]
  decide

lemma chain1_coeff_138 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 138 = (G * S0).coeff 138 := by
  rw [G_mul_coeff_ge S0 138 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127, S0_coeff_126]
  simp [G, T1]
  decide

lemma chain1_coeff_139 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 139 = (G * S0).coeff 139 := by
  rw [G_mul_coeff_ge S0 139 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128, S0_coeff_127]
  simp [G, T1]
  decide

lemma chain1_coeff_140 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 140 = (G * S0).coeff 140 := by
  rw [G_mul_coeff_ge S0 140 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129, S0_coeff_128]
  simp [G, T1]
  decide

lemma chain1_coeff_141 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 141 = (G * S0).coeff 141 := by
  rw [G_mul_coeff_ge S0 141 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130, S0_coeff_129]
  simp [G, T1]
  decide

lemma chain1_coeff_142 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 142 = (G * S0).coeff 142 := by
  rw [G_mul_coeff_ge S0 142 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131, S0_coeff_130]
  simp [G, T1]
  decide

lemma chain1_coeff_143 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 143 = (G * S0).coeff 143 := by
  rw [G_mul_coeff_ge S0 143 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132, S0_coeff_131]
  simp [G, T1]
  decide

lemma chain1_coeff_144 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 144 = (G * S0).coeff 144 := by
  rw [G_mul_coeff_ge S0 144 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133, S0_coeff_132]
  simp [G, T1]
  decide

lemma chain1_coeff_145 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 145 = (G * S0).coeff 145 := by
  rw [G_mul_coeff_ge S0 145 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134, S0_coeff_133]
  simp [G, T1]
  decide

lemma chain1_coeff_146 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 146 = (G * S0).coeff 146 := by
  rw [G_mul_coeff_ge S0 146 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135, S0_coeff_134]
  simp [G, T1]
  decide

lemma chain1_coeff_147 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 147 = (G * S0).coeff 147 := by
  rw [G_mul_coeff_ge S0 147 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136, S0_coeff_135]
  simp [G, T1]
  decide

lemma chain1_coeff_148 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 148 = (G * S0).coeff 148 := by
  rw [G_mul_coeff_ge S0 148 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137, S0_coeff_136]
  simp [G, T1]
  decide

lemma chain1_coeff_149 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 149 = (G * S0).coeff 149 := by
  rw [G_mul_coeff_ge S0 149 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138, S0_coeff_137]
  simp [G, T1]
  decide

lemma chain1_coeff_150 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 150 = (G * S0).coeff 150 := by
  rw [G_mul_coeff_ge S0 150 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139, S0_coeff_138]
  simp [G, T1]
  decide

lemma chain1_coeff_151 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 151 = (G * S0).coeff 151 := by
  rw [G_mul_coeff_ge S0 151 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140, S0_coeff_139]
  simp [G, T1]
  decide

lemma chain1_coeff_152 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 152 = (G * S0).coeff 152 := by
  rw [G_mul_coeff_ge S0 152 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141, S0_coeff_140]
  simp [G, T1]
  decide

lemma chain1_coeff_153 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 153 = (G * S0).coeff 153 := by
  rw [G_mul_coeff_ge S0 153 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142, S0_coeff_141]
  simp [G, T1]
  decide

lemma chain1_coeff_154 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 154 = (G * S0).coeff 154 := by
  rw [G_mul_coeff_ge S0 154 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143, S0_coeff_142]
  simp [G, T1]
  decide

lemma chain1_coeff_155 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 155 = (G * S0).coeff 155 := by
  rw [G_mul_coeff_ge S0 155 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144, S0_coeff_143]
  simp [G, T1]
  decide

lemma chain1_coeff_156 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 156 = (G * S0).coeff 156 := by
  rw [G_mul_coeff_ge S0 156 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145, S0_coeff_144]
  simp [G, T1]
  decide

lemma chain1_coeff_157 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 157 = (G * S0).coeff 157 := by
  rw [G_mul_coeff_ge S0 157 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146, S0_coeff_145]
  simp [G, T1]
  decide

lemma chain1_coeff_158 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 158 = (G * S0).coeff 158 := by
  rw [G_mul_coeff_ge S0 158 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147, S0_coeff_146]
  simp [G, T1]
  decide

lemma chain1_coeff_159 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 159 = (G * S0).coeff 159 := by
  rw [G_mul_coeff_ge S0 159 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148, S0_coeff_147]
  simp [G, T1]
  decide

lemma chain1_coeff_160 :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 160 = (G * S0).coeff 160 := by
  rw [G_mul_coeff_ge S0 160 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149, S0_coeff_148]
  simp [G, T1]
  decide

/-- The chain-1 coefficient identity on the whole middle range `81 ≤ n ≤ 160`. -/
theorem chain1_coeff_mid2 (n : ℕ) (hn1 : 81 ≤ n) (hn2 : n ≤ 160) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    simp only [chain1_coeff_81, chain1_coeff_82, chain1_coeff_83, chain1_coeff_84, chain1_coeff_85, chain1_coeff_86, chain1_coeff_87, chain1_coeff_88, chain1_coeff_89, chain1_coeff_90, chain1_coeff_91, chain1_coeff_92, chain1_coeff_93, chain1_coeff_94, chain1_coeff_95, chain1_coeff_96, chain1_coeff_97, chain1_coeff_98, chain1_coeff_99, chain1_coeff_100, chain1_coeff_101, chain1_coeff_102, chain1_coeff_103, chain1_coeff_104, chain1_coeff_105, chain1_coeff_106, chain1_coeff_107, chain1_coeff_108, chain1_coeff_109, chain1_coeff_110, chain1_coeff_111, chain1_coeff_112, chain1_coeff_113, chain1_coeff_114, chain1_coeff_115, chain1_coeff_116, chain1_coeff_117, chain1_coeff_118, chain1_coeff_119, chain1_coeff_120, chain1_coeff_121, chain1_coeff_122, chain1_coeff_123, chain1_coeff_124, chain1_coeff_125, chain1_coeff_126, chain1_coeff_127, chain1_coeff_128, chain1_coeff_129, chain1_coeff_130, chain1_coeff_131, chain1_coeff_132, chain1_coeff_133, chain1_coeff_134, chain1_coeff_135, chain1_coeff_136, chain1_coeff_137, chain1_coeff_138, chain1_coeff_139, chain1_coeff_140, chain1_coeff_141, chain1_coeff_142, chain1_coeff_143, chain1_coeff_144, chain1_coeff_145, chain1_coeff_146, chain1_coeff_147, chain1_coeff_148, chain1_coeff_149, chain1_coeff_150, chain1_coeff_151, chain1_coeff_152, chain1_coeff_153, chain1_coeff_154, chain1_coeff_155, chain1_coeff_156, chain1_coeff_157, chain1_coeff_158, chain1_coeff_159, chain1_coeff_160]

end LeanFormal.IUT.XiFPaper.S2565Chain1Mid2ActualAdapted

end
