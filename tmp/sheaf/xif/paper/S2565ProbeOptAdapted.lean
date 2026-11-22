/- Probe for S2565Chain1Mid1Actual proof pattern. -/
import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R0LookupActual
import tmp.sheaf.xif.paper.S2563R1LookupActual
import tmp.sheaf.xif.paper.S2563R2LookupActual
import tmp.sheaf.xif.paper.S2563R3LookupActual
import tmp.sheaf.xif.paper.S2563R4LookupActual
import tmp.sheaf.xif.paper.S2563R5LookupActual
import tmp.sheaf.xif.paper.S2563R6LookupActual
import tmp.sheaf.xif.paper.S2563R7LookupActual
import tmp.sheaf.xif.paper.S2564Chain1LowActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option profiler true
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2565ProbeOptAdapted

open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R0LookupActual
open LeanFormal.IUT.XiFPaper.S2563R1LookupActual
open LeanFormal.IUT.XiFPaper.S2563R2LookupActual
open LeanFormal.IUT.XiFPaper.S2563R3LookupActual
open LeanFormal.IUT.XiFPaper.S2563R4LookupActual
open LeanFormal.IUT.XiFPaper.S2563R5LookupActual
open LeanFormal.IUT.XiFPaper.S2563R6LookupActual
open LeanFormal.IUT.XiFPaper.S2563R7LookupActual
open LeanFormal.IUT.XiFPaper.S2564Chain1LowActual

lemma S0_coeff_12 : S0.coeff 12 = 455 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_12]

lemma S0_coeff_13 : S0.coeff 13 = 168 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_13]

lemma G_coeff_0 : G.coeff 0 = 451 := by simp [G]

lemma G_coeff_1 : G.coeff 1 = 0 := by simp [G]

lemma G_coeff_2 : G.coeff 2 = 389 := by simp [G]

lemma G_coeff_3 : G.coeff 3 = 412 := by simp [G]

lemma G_coeff_4 : G.coeff 4 = 251 := by simp [G]

lemma G_coeff_5 : G.coeff 5 = 501 := by simp [G]

lemma G_coeff_6 : G.coeff 6 = 586 := by simp [G]

lemma G_coeff_7 : G.coeff 7 = 82 := by simp [G]

lemma G_coeff_8 : G.coeff 8 = 551 := by simp [G]

lemma G_coeff_9 : G.coeff 9 = 327 := by simp [G]

lemma G_coeff_10 : G.coeff 10 = 210 := by simp [G]

lemma G_coeff_11 : G.coeff 11 = 272 := by simp [G]

lemma G_coeff_12 : G.coeff 12 = 1 := by simp [G]

lemma chain1_coeff_12 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 12 = (G * S0).coeff 12 := by
  rw [G_mul_coeff_ge S0 12 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [T1]
  decide

lemma chain1_coeff_13 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 13 = (G * S0).coeff 13 := by
  rw [G_mul_coeff_ge S0 13 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [G_coeff_0, G_coeff_1, G_coeff_2, G_coeff_3, G_coeff_4, G_coeff_5, G_coeff_6, G_coeff_7, G_coeff_8, G_coeff_9, G_coeff_10, G_coeff_11, G_coeff_12, S0_coeff_13, S0_coeff_12, S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1]
  simp [T1]
  decide

end LeanFormal.IUT.XiFPaper.S2565ProbeOptAdapted

end
