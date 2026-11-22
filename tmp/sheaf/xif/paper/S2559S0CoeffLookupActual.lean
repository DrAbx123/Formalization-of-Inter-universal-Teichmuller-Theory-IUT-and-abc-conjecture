import tmp.sheaf.xif.paper.S2558S0Part0Actual
import tmp.sheaf.xif.paper.S2558S0Part1Actual
import tmp.sheaf.xif.paper.S2558S0Part2Actual
import tmp.sheaf.xif.paper.S2558S0Part3Actual
import tmp.sheaf.xif.paper.S2558S0Part4Actual
import tmp.sheaf.xif.paper.S2558S0Part5Actual
import tmp.sheaf.xif.paper.S2558S0Part6Actual
import tmp.sheaf.xif.paper.S2558S0Part7Actual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2559S0CoeffLookupActual

open LeanFormal.IUT.XiFPaper.S2558S0Part0Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part1Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part2Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part3Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part4Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part5Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part6Actual
open LeanFormal.IUT.XiFPaper.S2558S0Part7Actual

def S0 : (ZMod 613)[X] := S0_0 + S0_1 + S0_2 + S0_3 + S0_4 + S0_5 + S0_6 + S0_7

lemma S0_coeff_0 : S0.coeff 0 = 39 := by
  rw [S0]
  have h1 : S0_1.coeff 0 = 0 := by decide
  have h2 : S0_2.coeff 0 = 0 := by decide
  have h3 : S0_3.coeff 0 = 0 := by decide
  have h4 : S0_4.coeff 0 = 0 := by decide
  have h5 : S0_5.coeff 0 = 0 := by decide
  have h6 : S0_6.coeff 0 = 0 := by decide
  have h7 : S0_7.coeff 0 = 0 := by decide
  simp only [Polynomial.coeff_add, h1, h2, h3, h4, h5, h6, h7]
  decide

lemma S0_coeff_1 : S0.coeff 1 = 281 := by
  rw [S0]
  have h1 : S0_1.coeff 1 = 0 := by simp [S0_1]
  have h2 : S0_2.coeff 1 = 0 := by simp [S0_2]
  have h3 : S0_3.coeff 1 = 0 := by simp [S0_3]
  have h4 : S0_4.coeff 1 = 0 := by simp [S0_4]
  have h5 : S0_5.coeff 1 = 0 := by simp [S0_5]
  have h6 : S0_6.coeff 1 = 0 := by simp [S0_6]
  have h7 : S0_7.coeff 1 = 0 := by simp [S0_7]
  simp only [Polynomial.coeff_add, h1, h2, h3, h4, h5, h6, h7]
  simp [S0_0]

end LeanFormal.IUT.XiFPaper.S2559S0CoeffLookupActual

end