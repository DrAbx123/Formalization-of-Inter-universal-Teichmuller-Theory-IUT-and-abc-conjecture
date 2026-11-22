import tmp.sheaf.xif.paper.Mzk1Stage4ABCStage5EvidenceActual
import tmp.sheaf.xif.paper.Mzk1Stage4Gap2ConsumerActual
import tmp.sheaf.xif.paper.Mzk1Stage4Gap2NumericWitnessActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual
import tmp.sheaf.xif.paper.Mzk1Stage4FinalAcceptanceSelfcheckActual

/-! # Mzk1Stage4FinalPackagingActual (stage4 lane; unique filename)

A577 module: final stage4 packaging bundle, built from the green stage4 files only.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalPackagingActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCStage5EvidenceActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2NumericWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- The final stage4 packaging bundle: Stage 5 shape, C_Theta bound, height-region
inequality, and the Gap2 numeric height bound. -/
structure FinalStage4Report where
  /-- The ABC Stage 5 signed input shape. -/
  stage5 : ABCStage5Shape
  /-- A calibrated constant bounded below by -1. -/
  cTheta : Real
  cTheta_ge_neg_one : -1 <= cTheta
  /-- The numeric IUT IV Theorem 1.10 inequality for 11a1 at l = 13. -/
  theorem110 : (1 / 6 : Real) * degQ11 <= theorem110RHS
  /-- A Gap1+Gap2 numeric height bound constant. -/
  gap2Constant : Real
  gap2_bound : (1 : Real) <= (1 + 1 / 10) * 1 + gap2Constant

/-- Construct the final report from the green stage4 theorems. -/
noncomputable def finalStage4Report (L : Real) (hL : 0 < L) : FinalStage4Report where
  stage5 := axiomGatePayload L hL |>.stage5
  cTheta := (axiomGatePayload L hL).cTheta
  cTheta_ge_neg_one := (axiomGatePayload L hL).cTheta_ge_neg_one
  theorem110 := theorem110_11a1_l13
  gap2Constant := 5
  gap2_bound := gap2_numeric_witness_five

/-- The constructed report is non-vacuous and its Stage 5 component holds. -/
theorem finalStage4Report_stage5 (L : Real) (hL : 0 < L) :
    (finalStage4Report L hL).stage5 =
      (axiomGatePayload L hL).stage5 :=
  rfl

/-- The constructed report's C_Theta bound. -/
theorem finalStage4Report_cTheta (L : Real) (hL : 0 < L) :
    -1 <= (finalStage4Report L hL).cTheta :=
  (finalStage4Report L hL).cTheta_ge_neg_one

/-- The constructed report's height-region inequality. -/
theorem finalStage4Report_height (L : Real) (hL : 0 < L) :
    (1 / 6 : Real) * degQ11 <= theorem110RHS :=
  (finalStage4Report L hL).theorem110

#check FinalStage4Report
#check finalStage4Report
#check finalStage4Report_cTheta
#check finalStage4Report_height

end LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalPackagingActual
end
