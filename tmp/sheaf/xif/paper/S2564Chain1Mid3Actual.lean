import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R1LookupActual
import tmp.sheaf.xif.paper.S2563R2LookupActual

/-!
# S2564Chain1Mid3Actual

Chain-1 coefficient identity for the middle range n in [161, 240]:

  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n

Sources (all already verified in this repository):
* S2560S0ShiftedPartsActual  : R0..R7, S0_0..S0_7, S0 := S0_0 + ... + S0_7
* S2563R1LookupActual, S2563R2LookupActual : R1.coeff j, R2.coeff j
  (R0/R1 vanishing beyond their degrees is proved here, so S2563R0LookupActual
  is not needed)
* S2562GmulCoeffActual       : G_mul_coeff_ge (13-term support sum for n >= 12)
* S2554Mod613ChainDataActual : G, T1

Strategy (mirrors S2564Chain1LowActual for n < 12):
* S0 is split into 8 shifted blocks (block i starts at 81*i).
  For 149 <= k <= 240 only blocks 0, 1, 2 can contribute; blocks 3..7 start
  at 241,401,481,561 > 240 and R0 (degree 80), R1 (degree 79) have no
  coefficient that far, so:
    - 149 <= k <= 160 : S0.coeff k = R1.coeff (k-81)
    - 161 <= k <= 240 : S0.coeff k = R2.coeff (k-161)
* For each n, expand (G*S0).coeff n with G_mul_coeff_ge, split the 13-term
  sum, rewrite the 13 S0 lookups, then close the concrete ZMod 613
  computation by simp [G, T1] + decide.
* Since n < 613, ((X)^613).coeff n = 0, so the left side is -T1.coeff n.

Note on names: the repository also contains root-level R0, R1 over ZMod 29
(from the mod-29 development), so all references to the mod-613 R0, R1 are
written with their full name.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R1LookupActual
open LeanFormal.IUT.XiFPaper.S2563R2LookupActual

/-- R0 has degree at most 80, so its coefficients vanish beyond 80. -/
lemma R0_coeff_eq_zero_of_gt (k : ℕ) (hk : 80 < k) :
    LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.natDegree ≤ 80 := by
    unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0
    compute_degree!
  omega

/-- R1 has degree at most 79, so its coefficients vanish beyond 79. -/
lemma R1_coeff_eq_zero_of_gt (k : ℕ) (hk : 79 < k) :
    LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.natDegree ≤ 79 := by
    unfold LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1
    compute_degree!
  omega

/-! ## S0 coefficient lookup on 149 .. 240 -/
lemma S0_coeff_149 : S0.coeff 149 = 345 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 149 = 0 := R0_coeff_eq_zero_of_gt 149 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_68]

lemma S0_coeff_150 : S0.coeff 150 = 547 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 150 = 0 := R0_coeff_eq_zero_of_gt 150 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_69]

lemma S0_coeff_151 : S0.coeff 151 = 485 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 151 = 0 := R0_coeff_eq_zero_of_gt 151 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_70]

lemma S0_coeff_152 : S0.coeff 152 = 184 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 152 = 0 := R0_coeff_eq_zero_of_gt 152 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_71]

lemma S0_coeff_153 : S0.coeff 153 = 501 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 153 = 0 := R0_coeff_eq_zero_of_gt 153 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_72]

lemma S0_coeff_154 : S0.coeff 154 = 518 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 154 = 0 := R0_coeff_eq_zero_of_gt 154 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_73]

lemma S0_coeff_155 : S0.coeff 155 = 612 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 155 = 0 := R0_coeff_eq_zero_of_gt 155 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_74]

lemma S0_coeff_156 : S0.coeff 156 = 107 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 156 = 0 := R0_coeff_eq_zero_of_gt 156 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_75]

lemma S0_coeff_157 : S0.coeff 157 = 253 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 157 = 0 := R0_coeff_eq_zero_of_gt 157 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_76]

lemma S0_coeff_158 : S0.coeff 158 = 483 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 158 = 0 := R0_coeff_eq_zero_of_gt 158 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_77]

lemma S0_coeff_159 : S0.coeff 159 = 21 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 159 = 0 := R0_coeff_eq_zero_of_gt 159 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_78]

lemma S0_coeff_160 : S0.coeff 160 = 363 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 160 = 0 := R0_coeff_eq_zero_of_gt 160 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, R1_coeff_79]

lemma S0_coeff_161 : S0.coeff 161 = 122 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 161 = 0 := R0_coeff_eq_zero_of_gt 161 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 80 = 0 := R1_coeff_eq_zero_of_gt 80 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_0]

lemma S0_coeff_162 : S0.coeff 162 = 379 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 162 = 0 := R0_coeff_eq_zero_of_gt 162 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 81 = 0 := R1_coeff_eq_zero_of_gt 81 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_1]

lemma S0_coeff_163 : S0.coeff 163 = 221 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 163 = 0 := R0_coeff_eq_zero_of_gt 163 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 82 = 0 := R1_coeff_eq_zero_of_gt 82 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_2]

lemma S0_coeff_164 : S0.coeff 164 = 373 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 164 = 0 := R0_coeff_eq_zero_of_gt 164 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 83 = 0 := R1_coeff_eq_zero_of_gt 83 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_3]

lemma S0_coeff_165 : S0.coeff 165 = 182 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 165 = 0 := R0_coeff_eq_zero_of_gt 165 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 84 = 0 := R1_coeff_eq_zero_of_gt 84 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_4]

lemma S0_coeff_166 : S0.coeff 166 = 341 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 166 = 0 := R0_coeff_eq_zero_of_gt 166 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 85 = 0 := R1_coeff_eq_zero_of_gt 85 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_5]

lemma S0_coeff_167 : S0.coeff 167 = 406 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 167 = 0 := R0_coeff_eq_zero_of_gt 167 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 86 = 0 := R1_coeff_eq_zero_of_gt 86 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_6]

lemma S0_coeff_168 : S0.coeff 168 = 356 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 168 = 0 := R0_coeff_eq_zero_of_gt 168 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 87 = 0 := R1_coeff_eq_zero_of_gt 87 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_7]

lemma S0_coeff_169 : S0.coeff 169 = 395 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 169 = 0 := R0_coeff_eq_zero_of_gt 169 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 88 = 0 := R1_coeff_eq_zero_of_gt 88 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_8]

lemma S0_coeff_170 : S0.coeff 170 = 403 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 170 = 0 := R0_coeff_eq_zero_of_gt 170 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 89 = 0 := R1_coeff_eq_zero_of_gt 89 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_9]

lemma S0_coeff_171 : S0.coeff 171 = 278 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 171 = 0 := R0_coeff_eq_zero_of_gt 171 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 90 = 0 := R1_coeff_eq_zero_of_gt 90 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_10]

lemma S0_coeff_172 : S0.coeff 172 = 253 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 172 = 0 := R0_coeff_eq_zero_of_gt 172 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 91 = 0 := R1_coeff_eq_zero_of_gt 91 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_11]

lemma S0_coeff_173 : S0.coeff 173 = 24 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 173 = 0 := R0_coeff_eq_zero_of_gt 173 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 92 = 0 := R1_coeff_eq_zero_of_gt 92 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_12]

lemma S0_coeff_174 : S0.coeff 174 = 170 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 174 = 0 := R0_coeff_eq_zero_of_gt 174 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 93 = 0 := R1_coeff_eq_zero_of_gt 93 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_13]

lemma S0_coeff_175 : S0.coeff 175 = 438 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 175 = 0 := R0_coeff_eq_zero_of_gt 175 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 94 = 0 := R1_coeff_eq_zero_of_gt 94 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_14]

lemma S0_coeff_176 : S0.coeff 176 = 256 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 176 = 0 := R0_coeff_eq_zero_of_gt 176 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 95 = 0 := R1_coeff_eq_zero_of_gt 95 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_15]

lemma S0_coeff_177 : S0.coeff 177 = 341 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 177 = 0 := R0_coeff_eq_zero_of_gt 177 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 96 = 0 := R1_coeff_eq_zero_of_gt 96 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_16]

lemma S0_coeff_178 : S0.coeff 178 = 453 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 178 = 0 := R0_coeff_eq_zero_of_gt 178 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 97 = 0 := R1_coeff_eq_zero_of_gt 97 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_17]

lemma S0_coeff_179 : S0.coeff 179 = 198 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 179 = 0 := R0_coeff_eq_zero_of_gt 179 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 98 = 0 := R1_coeff_eq_zero_of_gt 98 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_18]

lemma S0_coeff_180 : S0.coeff 180 = 283 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 180 = 0 := R0_coeff_eq_zero_of_gt 180 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 99 = 0 := R1_coeff_eq_zero_of_gt 99 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_19]

lemma S0_coeff_181 : S0.coeff 181 = 343 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 181 = 0 := R0_coeff_eq_zero_of_gt 181 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 100 = 0 := R1_coeff_eq_zero_of_gt 100 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_20]

lemma S0_coeff_182 : S0.coeff 182 = 312 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 182 = 0 := R0_coeff_eq_zero_of_gt 182 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 101 = 0 := R1_coeff_eq_zero_of_gt 101 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_21]

lemma S0_coeff_183 : S0.coeff 183 = 33 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 183 = 0 := R0_coeff_eq_zero_of_gt 183 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 102 = 0 := R1_coeff_eq_zero_of_gt 102 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_22]

lemma S0_coeff_184 : S0.coeff 184 = 136 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 184 = 0 := R0_coeff_eq_zero_of_gt 184 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 103 = 0 := R1_coeff_eq_zero_of_gt 103 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_23]

lemma S0_coeff_185 : S0.coeff 185 = 427 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 185 = 0 := R0_coeff_eq_zero_of_gt 185 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 104 = 0 := R1_coeff_eq_zero_of_gt 104 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_24]

lemma S0_coeff_186 : S0.coeff 186 = 0 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 186 = 0 := R0_coeff_eq_zero_of_gt 186 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 105 = 0 := R1_coeff_eq_zero_of_gt 105 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_25]

lemma S0_coeff_187 : S0.coeff 187 = 9 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 187 = 0 := R0_coeff_eq_zero_of_gt 187 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 106 = 0 := R1_coeff_eq_zero_of_gt 106 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_26]

lemma S0_coeff_188 : S0.coeff 188 = 154 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 188 = 0 := R0_coeff_eq_zero_of_gt 188 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 107 = 0 := R1_coeff_eq_zero_of_gt 107 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_27]

lemma S0_coeff_189 : S0.coeff 189 = 63 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 189 = 0 := R0_coeff_eq_zero_of_gt 189 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 108 = 0 := R1_coeff_eq_zero_of_gt 108 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_28]

lemma S0_coeff_190 : S0.coeff 190 = 80 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 190 = 0 := R0_coeff_eq_zero_of_gt 190 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 109 = 0 := R1_coeff_eq_zero_of_gt 109 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_29]

lemma S0_coeff_191 : S0.coeff 191 = 91 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 191 = 0 := R0_coeff_eq_zero_of_gt 191 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 110 = 0 := R1_coeff_eq_zero_of_gt 110 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_30]

lemma S0_coeff_192 : S0.coeff 192 = 405 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 192 = 0 := R0_coeff_eq_zero_of_gt 192 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 111 = 0 := R1_coeff_eq_zero_of_gt 111 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_31]

lemma S0_coeff_193 : S0.coeff 193 = 539 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 193 = 0 := R0_coeff_eq_zero_of_gt 193 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 112 = 0 := R1_coeff_eq_zero_of_gt 112 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_32]

lemma S0_coeff_194 : S0.coeff 194 = 603 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 194 = 0 := R0_coeff_eq_zero_of_gt 194 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 113 = 0 := R1_coeff_eq_zero_of_gt 113 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_33]

lemma S0_coeff_195 : S0.coeff 195 = 244 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 195 = 0 := R0_coeff_eq_zero_of_gt 195 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 114 = 0 := R1_coeff_eq_zero_of_gt 114 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_34]

lemma S0_coeff_196 : S0.coeff 196 = 609 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 196 = 0 := R0_coeff_eq_zero_of_gt 196 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 115 = 0 := R1_coeff_eq_zero_of_gt 115 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_35]

lemma S0_coeff_197 : S0.coeff 197 = 583 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 197 = 0 := R0_coeff_eq_zero_of_gt 197 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 116 = 0 := R1_coeff_eq_zero_of_gt 116 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_36]

lemma S0_coeff_198 : S0.coeff 198 = 384 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 198 = 0 := R0_coeff_eq_zero_of_gt 198 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 117 = 0 := R1_coeff_eq_zero_of_gt 117 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_37]

lemma S0_coeff_199 : S0.coeff 199 = 287 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 199 = 0 := R0_coeff_eq_zero_of_gt 199 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 118 = 0 := R1_coeff_eq_zero_of_gt 118 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_38]

lemma S0_coeff_200 : S0.coeff 200 = 265 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 200 = 0 := R0_coeff_eq_zero_of_gt 200 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 119 = 0 := R1_coeff_eq_zero_of_gt 119 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_39]

lemma S0_coeff_201 : S0.coeff 201 = 552 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 201 = 0 := R0_coeff_eq_zero_of_gt 201 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 120 = 0 := R1_coeff_eq_zero_of_gt 120 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_40]

lemma S0_coeff_202 : S0.coeff 202 = 9 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 202 = 0 := R0_coeff_eq_zero_of_gt 202 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 121 = 0 := R1_coeff_eq_zero_of_gt 121 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_41]

lemma S0_coeff_203 : S0.coeff 203 = 405 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 203 = 0 := R0_coeff_eq_zero_of_gt 203 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 122 = 0 := R1_coeff_eq_zero_of_gt 122 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_42]

lemma S0_coeff_204 : S0.coeff 204 = 75 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 204 = 0 := R0_coeff_eq_zero_of_gt 204 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 123 = 0 := R1_coeff_eq_zero_of_gt 123 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_43]

lemma S0_coeff_205 : S0.coeff 205 = 285 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 205 = 0 := R0_coeff_eq_zero_of_gt 205 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 124 = 0 := R1_coeff_eq_zero_of_gt 124 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_44]

lemma S0_coeff_206 : S0.coeff 206 = 62 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 206 = 0 := R0_coeff_eq_zero_of_gt 206 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 125 = 0 := R1_coeff_eq_zero_of_gt 125 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_45]

lemma S0_coeff_207 : S0.coeff 207 = 245 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 207 = 0 := R0_coeff_eq_zero_of_gt 207 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 126 = 0 := R1_coeff_eq_zero_of_gt 126 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_46]

lemma S0_coeff_208 : S0.coeff 208 = 93 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 208 = 0 := R0_coeff_eq_zero_of_gt 208 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 127 = 0 := R1_coeff_eq_zero_of_gt 127 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_47]

lemma S0_coeff_209 : S0.coeff 209 = 574 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 209 = 0 := R0_coeff_eq_zero_of_gt 209 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 128 = 0 := R1_coeff_eq_zero_of_gt 128 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_48]

lemma S0_coeff_210 : S0.coeff 210 = 205 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 210 = 0 := R0_coeff_eq_zero_of_gt 210 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 129 = 0 := R1_coeff_eq_zero_of_gt 129 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_49]

lemma S0_coeff_211 : S0.coeff 211 = 576 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 211 = 0 := R0_coeff_eq_zero_of_gt 211 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 130 = 0 := R1_coeff_eq_zero_of_gt 130 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_50]

lemma S0_coeff_212 : S0.coeff 212 = 490 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 212 = 0 := R0_coeff_eq_zero_of_gt 212 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 131 = 0 := R1_coeff_eq_zero_of_gt 131 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_51]

lemma S0_coeff_213 : S0.coeff 213 = 29 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 213 = 0 := R0_coeff_eq_zero_of_gt 213 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 132 = 0 := R1_coeff_eq_zero_of_gt 132 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_52]

lemma S0_coeff_214 : S0.coeff 214 = 420 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 214 = 0 := R0_coeff_eq_zero_of_gt 214 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 133 = 0 := R1_coeff_eq_zero_of_gt 133 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_53]

lemma S0_coeff_215 : S0.coeff 215 = 186 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 215 = 0 := R0_coeff_eq_zero_of_gt 215 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 134 = 0 := R1_coeff_eq_zero_of_gt 134 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_54]

lemma S0_coeff_216 : S0.coeff 216 = 247 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 216 = 0 := R0_coeff_eq_zero_of_gt 216 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 135 = 0 := R1_coeff_eq_zero_of_gt 135 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_55]

lemma S0_coeff_217 : S0.coeff 217 = 65 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 217 = 0 := R0_coeff_eq_zero_of_gt 217 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 136 = 0 := R1_coeff_eq_zero_of_gt 136 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_56]

lemma S0_coeff_218 : S0.coeff 218 = 405 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 218 = 0 := R0_coeff_eq_zero_of_gt 218 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 137 = 0 := R1_coeff_eq_zero_of_gt 137 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_57]

lemma S0_coeff_219 : S0.coeff 219 = 410 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 219 = 0 := R0_coeff_eq_zero_of_gt 219 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 138 = 0 := R1_coeff_eq_zero_of_gt 138 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_58]

lemma S0_coeff_220 : S0.coeff 220 = 193 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 220 = 0 := R0_coeff_eq_zero_of_gt 220 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 139 = 0 := R1_coeff_eq_zero_of_gt 139 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_59]

lemma S0_coeff_221 : S0.coeff 221 = 55 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 221 = 0 := R0_coeff_eq_zero_of_gt 221 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 140 = 0 := R1_coeff_eq_zero_of_gt 140 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_60]

lemma S0_coeff_222 : S0.coeff 222 = 544 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 222 = 0 := R0_coeff_eq_zero_of_gt 222 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 141 = 0 := R1_coeff_eq_zero_of_gt 141 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_61]

lemma S0_coeff_223 : S0.coeff 223 = 470 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 223 = 0 := R0_coeff_eq_zero_of_gt 223 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 142 = 0 := R1_coeff_eq_zero_of_gt 142 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_62]

lemma S0_coeff_224 : S0.coeff 224 = 276 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 224 = 0 := R0_coeff_eq_zero_of_gt 224 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 143 = 0 := R1_coeff_eq_zero_of_gt 143 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_63]

lemma S0_coeff_225 : S0.coeff 225 = 180 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 225 = 0 := R0_coeff_eq_zero_of_gt 225 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 144 = 0 := R1_coeff_eq_zero_of_gt 144 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_64]

lemma S0_coeff_226 : S0.coeff 226 = 604 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 226 = 0 := R0_coeff_eq_zero_of_gt 226 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 145 = 0 := R1_coeff_eq_zero_of_gt 145 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_65]

lemma S0_coeff_227 : S0.coeff 227 = 117 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 227 = 0 := R0_coeff_eq_zero_of_gt 227 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 146 = 0 := R1_coeff_eq_zero_of_gt 146 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_66]

lemma S0_coeff_228 : S0.coeff 228 = 314 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 228 = 0 := R0_coeff_eq_zero_of_gt 228 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 147 = 0 := R1_coeff_eq_zero_of_gt 147 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_67]

lemma S0_coeff_229 : S0.coeff 229 = 417 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 229 = 0 := R0_coeff_eq_zero_of_gt 229 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 148 = 0 := R1_coeff_eq_zero_of_gt 148 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_68]

lemma S0_coeff_230 : S0.coeff 230 = 477 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 230 = 0 := R0_coeff_eq_zero_of_gt 230 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 149 = 0 := R1_coeff_eq_zero_of_gt 149 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_69]

lemma S0_coeff_231 : S0.coeff 231 = 386 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 231 = 0 := R0_coeff_eq_zero_of_gt 231 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 150 = 0 := R1_coeff_eq_zero_of_gt 150 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_70]

lemma S0_coeff_232 : S0.coeff 232 = 369 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 232 = 0 := R0_coeff_eq_zero_of_gt 232 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 151 = 0 := R1_coeff_eq_zero_of_gt 151 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_71]

lemma S0_coeff_233 : S0.coeff 233 = 110 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 233 = 0 := R0_coeff_eq_zero_of_gt 233 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 152 = 0 := R1_coeff_eq_zero_of_gt 152 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_72]

lemma S0_coeff_234 : S0.coeff 234 = 172 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 234 = 0 := R0_coeff_eq_zero_of_gt 234 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 153 = 0 := R1_coeff_eq_zero_of_gt 153 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_73]

lemma S0_coeff_235 : S0.coeff 235 = 358 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 235 = 0 := R0_coeff_eq_zero_of_gt 235 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 154 = 0 := R1_coeff_eq_zero_of_gt 154 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_74]

lemma S0_coeff_236 : S0.coeff 236 = 512 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 236 = 0 := R0_coeff_eq_zero_of_gt 236 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 155 = 0 := R1_coeff_eq_zero_of_gt 155 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_75]

lemma S0_coeff_237 : S0.coeff 237 = 397 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 237 = 0 := R0_coeff_eq_zero_of_gt 237 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 156 = 0 := R1_coeff_eq_zero_of_gt 156 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_76]

lemma S0_coeff_238 : S0.coeff 238 = 431 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 238 = 0 := R0_coeff_eq_zero_of_gt 238 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 157 = 0 := R1_coeff_eq_zero_of_gt 157 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_77]

lemma S0_coeff_239 : S0.coeff 239 = 456 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 239 = 0 := R0_coeff_eq_zero_of_gt 239 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 158 = 0 := R1_coeff_eq_zero_of_gt 158 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_78]

lemma S0_coeff_240 : S0.coeff 240 = 455 := by
  have h0 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R0.coeff 240 = 0 := R0_coeff_eq_zero_of_gt 240 (by norm_num)
  have h1 : LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual.R1.coeff 159 = 0 := R1_coeff_eq_zero_of_gt 159 (by norm_num)
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, h0, h1, R2_coeff_79]

/-! ## Chain-1 coefficient identity on 161 .. 240 -/

lemma chain1_coeff_161 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 161 = (G * S0).coeff 161 := by
  rw [G_mul_coeff_ge S0 161 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150, S0_coeff_149]
  simp [G, T1]
  decide

lemma chain1_coeff_162 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 162 = (G * S0).coeff 162 := by
  rw [G_mul_coeff_ge S0 162 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151, S0_coeff_150]
  simp [G, T1]
  decide

lemma chain1_coeff_163 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 163 = (G * S0).coeff 163 := by
  rw [G_mul_coeff_ge S0 163 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152, S0_coeff_151]
  simp [G, T1]
  decide

lemma chain1_coeff_164 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 164 = (G * S0).coeff 164 := by
  rw [G_mul_coeff_ge S0 164 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153, S0_coeff_152]
  simp [G, T1]
  decide

lemma chain1_coeff_165 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 165 = (G * S0).coeff 165 := by
  rw [G_mul_coeff_ge S0 165 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154, S0_coeff_153]
  simp [G, T1]
  decide

lemma chain1_coeff_166 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 166 = (G * S0).coeff 166 := by
  rw [G_mul_coeff_ge S0 166 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155, S0_coeff_154]
  simp [G, T1]
  decide

lemma chain1_coeff_167 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 167 = (G * S0).coeff 167 := by
  rw [G_mul_coeff_ge S0 167 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156, S0_coeff_155]
  simp [G, T1]
  decide

lemma chain1_coeff_168 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 168 = (G * S0).coeff 168 := by
  rw [G_mul_coeff_ge S0 168 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157, S0_coeff_156]
  simp [G, T1]
  decide

lemma chain1_coeff_169 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 169 = (G * S0).coeff 169 := by
  rw [G_mul_coeff_ge S0 169 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158, S0_coeff_157]
  simp [G, T1]
  decide

lemma chain1_coeff_170 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 170 = (G * S0).coeff 170 := by
  rw [G_mul_coeff_ge S0 170 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159, S0_coeff_158]
  simp [G, T1]
  decide

lemma chain1_coeff_171 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 171 = (G * S0).coeff 171 := by
  rw [G_mul_coeff_ge S0 171 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160, S0_coeff_159]
  simp [G, T1]
  decide

lemma chain1_coeff_172 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 172 = (G * S0).coeff 172 := by
  rw [G_mul_coeff_ge S0 172 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161, S0_coeff_160]
  simp [G, T1]
  decide

lemma chain1_coeff_173 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 173 = (G * S0).coeff 173 := by
  rw [G_mul_coeff_ge S0 173 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162, S0_coeff_161]
  simp [G, T1]
  decide

lemma chain1_coeff_174 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 174 = (G * S0).coeff 174 := by
  rw [G_mul_coeff_ge S0 174 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163, S0_coeff_162]
  simp [G, T1]
  decide

lemma chain1_coeff_175 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 175 = (G * S0).coeff 175 := by
  rw [G_mul_coeff_ge S0 175 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164, S0_coeff_163]
  simp [G, T1]
  decide

lemma chain1_coeff_176 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 176 = (G * S0).coeff 176 := by
  rw [G_mul_coeff_ge S0 176 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165, S0_coeff_164]
  simp [G, T1]
  decide

lemma chain1_coeff_177 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 177 = (G * S0).coeff 177 := by
  rw [G_mul_coeff_ge S0 177 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166, S0_coeff_165]
  simp [G, T1]
  decide

lemma chain1_coeff_178 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 178 = (G * S0).coeff 178 := by
  rw [G_mul_coeff_ge S0 178 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167, S0_coeff_166]
  simp [G, T1]
  decide

lemma chain1_coeff_179 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 179 = (G * S0).coeff 179 := by
  rw [G_mul_coeff_ge S0 179 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168, S0_coeff_167]
  simp [G, T1]
  decide

lemma chain1_coeff_180 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 180 = (G * S0).coeff 180 := by
  rw [G_mul_coeff_ge S0 180 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169, S0_coeff_168]
  simp [G, T1]
  decide

lemma chain1_coeff_181 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 181 = (G * S0).coeff 181 := by
  rw [G_mul_coeff_ge S0 181 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170, S0_coeff_169]
  simp [G, T1]
  decide

lemma chain1_coeff_182 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 182 = (G * S0).coeff 182 := by
  rw [G_mul_coeff_ge S0 182 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171, S0_coeff_170]
  simp [G, T1]
  decide

lemma chain1_coeff_183 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 183 = (G * S0).coeff 183 := by
  rw [G_mul_coeff_ge S0 183 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172, S0_coeff_171]
  simp [G, T1]
  decide

lemma chain1_coeff_184 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 184 = (G * S0).coeff 184 := by
  rw [G_mul_coeff_ge S0 184 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173, S0_coeff_172]
  simp [G, T1]
  decide

lemma chain1_coeff_185 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 185 = (G * S0).coeff 185 := by
  rw [G_mul_coeff_ge S0 185 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174, S0_coeff_173]
  simp [G, T1]
  decide

lemma chain1_coeff_186 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 186 = (G * S0).coeff 186 := by
  rw [G_mul_coeff_ge S0 186 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175, S0_coeff_174]
  simp [G, T1]
  decide

lemma chain1_coeff_187 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 187 = (G * S0).coeff 187 := by
  rw [G_mul_coeff_ge S0 187 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176, S0_coeff_175]
  simp [G, T1]
  decide

lemma chain1_coeff_188 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 188 = (G * S0).coeff 188 := by
  rw [G_mul_coeff_ge S0 188 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177, S0_coeff_176]
  simp [G, T1]
  decide

lemma chain1_coeff_189 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 189 = (G * S0).coeff 189 := by
  rw [G_mul_coeff_ge S0 189 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178, S0_coeff_177]
  simp [G, T1]
  decide

lemma chain1_coeff_190 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 190 = (G * S0).coeff 190 := by
  rw [G_mul_coeff_ge S0 190 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179, S0_coeff_178]
  simp [G, T1]
  decide

lemma chain1_coeff_191 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 191 = (G * S0).coeff 191 := by
  rw [G_mul_coeff_ge S0 191 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180, S0_coeff_179]
  simp [G, T1]
  decide

lemma chain1_coeff_192 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 192 = (G * S0).coeff 192 := by
  rw [G_mul_coeff_ge S0 192 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181, S0_coeff_180]
  simp [G, T1]
  decide

lemma chain1_coeff_193 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 193 = (G * S0).coeff 193 := by
  rw [G_mul_coeff_ge S0 193 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182, S0_coeff_181]
  simp [G, T1]
  decide

lemma chain1_coeff_194 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 194 = (G * S0).coeff 194 := by
  rw [G_mul_coeff_ge S0 194 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183, S0_coeff_182]
  simp [G, T1]
  decide

lemma chain1_coeff_195 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 195 = (G * S0).coeff 195 := by
  rw [G_mul_coeff_ge S0 195 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184, S0_coeff_183]
  simp [G, T1]
  decide

lemma chain1_coeff_196 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 196 = (G * S0).coeff 196 := by
  rw [G_mul_coeff_ge S0 196 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185, S0_coeff_184]
  simp [G, T1]
  decide

lemma chain1_coeff_197 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 197 = (G * S0).coeff 197 := by
  rw [G_mul_coeff_ge S0 197 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186, S0_coeff_185]
  simp [G, T1]
  decide

lemma chain1_coeff_198 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 198 = (G * S0).coeff 198 := by
  rw [G_mul_coeff_ge S0 198 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187, S0_coeff_186]
  simp [G, T1]
  decide

lemma chain1_coeff_199 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 199 = (G * S0).coeff 199 := by
  rw [G_mul_coeff_ge S0 199 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188, S0_coeff_187]
  simp [G, T1]
  decide

lemma chain1_coeff_200 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 200 = (G * S0).coeff 200 := by
  rw [G_mul_coeff_ge S0 200 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189, S0_coeff_188]
  simp [G, T1]
  decide

lemma chain1_coeff_201 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 201 = (G * S0).coeff 201 := by
  rw [G_mul_coeff_ge S0 201 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190, S0_coeff_189]
  simp [G, T1]
  decide

lemma chain1_coeff_202 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 202 = (G * S0).coeff 202 := by
  rw [G_mul_coeff_ge S0 202 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191, S0_coeff_190]
  simp [G, T1]
  decide

lemma chain1_coeff_203 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 203 = (G * S0).coeff 203 := by
  rw [G_mul_coeff_ge S0 203 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192, S0_coeff_191]
  simp [G, T1]
  decide

lemma chain1_coeff_204 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 204 = (G * S0).coeff 204 := by
  rw [G_mul_coeff_ge S0 204 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193, S0_coeff_192]
  simp [G, T1]
  decide

lemma chain1_coeff_205 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 205 = (G * S0).coeff 205 := by
  rw [G_mul_coeff_ge S0 205 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194, S0_coeff_193]
  simp [G, T1]
  decide

lemma chain1_coeff_206 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 206 = (G * S0).coeff 206 := by
  rw [G_mul_coeff_ge S0 206 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195, S0_coeff_194]
  simp [G, T1]
  decide

lemma chain1_coeff_207 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 207 = (G * S0).coeff 207 := by
  rw [G_mul_coeff_ge S0 207 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196, S0_coeff_195]
  simp [G, T1]
  decide

lemma chain1_coeff_208 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 208 = (G * S0).coeff 208 := by
  rw [G_mul_coeff_ge S0 208 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197, S0_coeff_196]
  simp [G, T1]
  decide

lemma chain1_coeff_209 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 209 = (G * S0).coeff 209 := by
  rw [G_mul_coeff_ge S0 209 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198, S0_coeff_197]
  simp [G, T1]
  decide

lemma chain1_coeff_210 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 210 = (G * S0).coeff 210 := by
  rw [G_mul_coeff_ge S0 210 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199, S0_coeff_198]
  simp [G, T1]
  decide

lemma chain1_coeff_211 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 211 = (G * S0).coeff 211 := by
  rw [G_mul_coeff_ge S0 211 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200, S0_coeff_199]
  simp [G, T1]
  decide

lemma chain1_coeff_212 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 212 = (G * S0).coeff 212 := by
  rw [G_mul_coeff_ge S0 212 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201, S0_coeff_200]
  simp [G, T1]
  decide

lemma chain1_coeff_213 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 213 = (G * S0).coeff 213 := by
  rw [G_mul_coeff_ge S0 213 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202, S0_coeff_201]
  simp [G, T1]
  decide

lemma chain1_coeff_214 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 214 = (G * S0).coeff 214 := by
  rw [G_mul_coeff_ge S0 214 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203, S0_coeff_202]
  simp [G, T1]
  decide

lemma chain1_coeff_215 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 215 = (G * S0).coeff 215 := by
  rw [G_mul_coeff_ge S0 215 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204, S0_coeff_203]
  simp [G, T1]
  decide

lemma chain1_coeff_216 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 216 = (G * S0).coeff 216 := by
  rw [G_mul_coeff_ge S0 216 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205, S0_coeff_204]
  simp [G, T1]
  decide

lemma chain1_coeff_217 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 217 = (G * S0).coeff 217 := by
  rw [G_mul_coeff_ge S0 217 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206, S0_coeff_205]
  simp [G, T1]
  decide

lemma chain1_coeff_218 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 218 = (G * S0).coeff 218 := by
  rw [G_mul_coeff_ge S0 218 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207, S0_coeff_206]
  simp [G, T1]
  decide

lemma chain1_coeff_219 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 219 = (G * S0).coeff 219 := by
  rw [G_mul_coeff_ge S0 219 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208, S0_coeff_207]
  simp [G, T1]
  decide

lemma chain1_coeff_220 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 220 = (G * S0).coeff 220 := by
  rw [G_mul_coeff_ge S0 220 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209, S0_coeff_208]
  simp [G, T1]
  decide

lemma chain1_coeff_221 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 221 = (G * S0).coeff 221 := by
  rw [G_mul_coeff_ge S0 221 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210, S0_coeff_209]
  simp [G, T1]
  decide

lemma chain1_coeff_222 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 222 = (G * S0).coeff 222 := by
  rw [G_mul_coeff_ge S0 222 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211, S0_coeff_210]
  simp [G, T1]
  decide

lemma chain1_coeff_223 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 223 = (G * S0).coeff 223 := by
  rw [G_mul_coeff_ge S0 223 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212, S0_coeff_211]
  simp [G, T1]
  decide

lemma chain1_coeff_224 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 224 = (G * S0).coeff 224 := by
  rw [G_mul_coeff_ge S0 224 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213, S0_coeff_212]
  simp [G, T1]
  decide

lemma chain1_coeff_225 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 225 = (G * S0).coeff 225 := by
  rw [G_mul_coeff_ge S0 225 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214, S0_coeff_213]
  simp [G, T1]
  decide

lemma chain1_coeff_226 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 226 = (G * S0).coeff 226 := by
  rw [G_mul_coeff_ge S0 226 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215, S0_coeff_214]
  simp [G, T1]
  decide

lemma chain1_coeff_227 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 227 = (G * S0).coeff 227 := by
  rw [G_mul_coeff_ge S0 227 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216, S0_coeff_215]
  simp [G, T1]
  decide

lemma chain1_coeff_228 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 228 = (G * S0).coeff 228 := by
  rw [G_mul_coeff_ge S0 228 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217, S0_coeff_216]
  simp [G, T1]
  decide

lemma chain1_coeff_229 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 229 = (G * S0).coeff 229 := by
  rw [G_mul_coeff_ge S0 229 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218, S0_coeff_217]
  simp [G, T1]
  decide

lemma chain1_coeff_230 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 230 = (G * S0).coeff 230 := by
  rw [G_mul_coeff_ge S0 230 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219, S0_coeff_218]
  simp [G, T1]
  decide

lemma chain1_coeff_231 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 231 = (G * S0).coeff 231 := by
  rw [G_mul_coeff_ge S0 231 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220, S0_coeff_219]
  simp [G, T1]
  decide

lemma chain1_coeff_232 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 232 = (G * S0).coeff 232 := by
  rw [G_mul_coeff_ge S0 232 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221, S0_coeff_220]
  simp [G, T1]
  decide

lemma chain1_coeff_233 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 233 = (G * S0).coeff 233 := by
  rw [G_mul_coeff_ge S0 233 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222, S0_coeff_221]
  simp [G, T1]
  decide

lemma chain1_coeff_234 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 234 = (G * S0).coeff 234 := by
  rw [G_mul_coeff_ge S0 234 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223, S0_coeff_222]
  simp [G, T1]
  decide

lemma chain1_coeff_235 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 235 = (G * S0).coeff 235 := by
  rw [G_mul_coeff_ge S0 235 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224, S0_coeff_223]
  simp [G, T1]
  decide

lemma chain1_coeff_236 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 236 = (G * S0).coeff 236 := by
  rw [G_mul_coeff_ge S0 236 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225, S0_coeff_224]
  simp [G, T1]
  decide

lemma chain1_coeff_237 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 237 = (G * S0).coeff 237 := by
  rw [G_mul_coeff_ge S0 237 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226, S0_coeff_225]
  simp [G, T1]
  decide

lemma chain1_coeff_238 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 238 = (G * S0).coeff 238 := by
  rw [G_mul_coeff_ge S0 238 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227, S0_coeff_226]
  simp [G, T1]
  decide

lemma chain1_coeff_239 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 239 = (G * S0).coeff 239 := by
  rw [G_mul_coeff_ge S0 239 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228, S0_coeff_227]
  simp [G, T1]
  decide

lemma chain1_coeff_240 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 240 = (G * S0).coeff 240 := by
  rw [G_mul_coeff_ge S0 240 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_240, S0_coeff_239, S0_coeff_238, S0_coeff_237, S0_coeff_236, S0_coeff_235, S0_coeff_234, S0_coeff_233, S0_coeff_232, S0_coeff_231, S0_coeff_230, S0_coeff_229, S0_coeff_228]
  simp [G, T1]
  decide

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid3Actual

end
