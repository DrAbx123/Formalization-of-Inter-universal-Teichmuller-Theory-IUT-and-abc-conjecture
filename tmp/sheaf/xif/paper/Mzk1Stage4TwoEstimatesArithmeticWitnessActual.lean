import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual

/-! # Mzk1Stage4TwoEstimatesArithmeticWitnessActual (stage4 lane; unique filename)

A605 module: explicit arithmetic decomposition witnesses for the two-estimates numeric
data (Theorem 1.10 RHS and the q-degree width).  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesArithmeticWitnessActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- The Theorem 1.10 RHS decomposes as `(33/13) log 11 + 143769600`. -/
theorem theorem110RHS_decomp :
    theorem110RHS = (33 / 13 : Real) * Real.log 11 + 143769600 := by
  unfold theorem110RHS degD11 degF11 dMod eModStar
  norm_num

/-- The q-degree width of the 11a1 height instance is `(5/6) log 11`. -/
theorem degQ11_width : (1 / 6 : Real) * degQ11 = (5 / 6 : Real) * Real.log 11 := by
  unfold degQ11
  ring

/-- The large constant term: `20 e_mod^* l = 143769600`. -/
theorem constant_term_eq : (20 : Real) * (eModStar : Real) * 13 = 143769600 := by
  rw [eModStar_eq]
  norm_num

#check theorem110RHS_decomp
#check degQ11_width
#check constant_term_eq

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesArithmeticWitnessActual
end
