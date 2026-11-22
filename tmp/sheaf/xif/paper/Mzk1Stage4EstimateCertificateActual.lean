import tmp.sheaf.xif.paper.Mzk1Stage4HeightEstimateActual
import tmp.sheaf.xif.paper.Mzk1Stage4TwoEstimatesArithmeticWitnessActual

/-! # Mzk1Stage4EstimateCertificateActual (stage4 lane; unique filename)

A612 module: estimate certificate bundling the two-sided height estimate with the
arithmetic decomposition of the Theorem 1.10 right-hand side.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4EstimateCertificateActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesArithmeticWitnessActual

/-- The estimate certificate for the 11a1@l=13 data. -/
structure EstimateCertificate where
  /-- positivity of the height. -/
  height_pos : 0 < height11
  /-- height bounded by the hull constant. -/
  height_ub : height11 <= 11
  /-- height strictly below region volume. -/
  height_lt_region : height11 < regionVol11
  /-- the Theorem 1.10 RHS decomposition. -/
  rhs_decomp :
    theorem110RHS = (33 / 13 : Real) * Real.log 11 + 143769600

/-- Construct the estimate certificate. -/
noncomputable def estimateCertificate : EstimateCertificate where
  height_pos := heightEstimate11.lb
  height_ub := heightEstimate11.ub
  height_lt_region := height_le_region
  rhs_decomp := theorem110RHS_decomp

#check EstimateCertificate
#check estimateCertificate

end LeanFormal.IUT.XiFPaper.Mzk1Stage4EstimateCertificateActual
end
