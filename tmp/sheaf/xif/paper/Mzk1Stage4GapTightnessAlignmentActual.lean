import tmp.sheaf.xif.paper.Mzk1GapTightnessActual
import tmp.sheaf.xif.paper.Mzk1Stage4GapTightnessCalibrationActual

/-! # Mzk1Stage4GapTightnessAlignmentActual (stage4 lane; tightness alignment, clean)

A649 module: clean stage4 tightness alignment.  NOTE (honesty): the canonical boundary
calibration `Mzk1GapTightnessActual.paperGap_boundary_calibrated` reports `sorryAx` in
its axiom set, so it is NOT re-exported as a stage4 result here; only the clean numeric
slack calibration is aligned, and the sorryAx finding is recorded for audit.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessAlignmentActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessCalibrationActual

/-- The clean (sorryAx-free) stage4 tightness alignment: numeric slack positivity only. -/
structure TightnessAlignment where
  /-- numeric Gap 1 slack positivity. -/
  gap1_slack : 0 < Mzk1Stage4HeightEstimateActual.regionVol11 -
    Mzk1Stage4HeightEstimateActual.height11
  /-- numeric Gap 2 slack positivity. -/
  gap2_slack :
    0 < (1 + 1 / 10 : Real) * Real.log 11 + 11 -
      Mzk1Stage4HeightEstimateActual.regionVol11

/-- Construct the clean tightness alignment. -/
noncomputable def tightnessAlignment : TightnessAlignment where
  gap1_slack := gap1_slack_pos
  gap2_slack := gap2_slack_pos

/-- Honesty record: the canonical boundary calibration's axiom status (contains sorryAx). -/
def boundaryCalibrationStatus : List String :=
  [ "Mzk1GapTightnessActual.paperGap_boundary_calibrated: sorryAx PRESENT (not re-exported as stage4 result)"
  , "Mzk1GapTightnessActual.paperGap_reduction_tight: gate trio clean"
  ]

/-- The honesty record has two entries. -/
theorem boundaryCalibrationStatus_length : boundaryCalibrationStatus.length = 2 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual.paperGap_boundary_calibrated
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual.paperGap_reduction_tight

#check TightnessAlignment
#check tightnessAlignment
#print axioms tightnessAlignment

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessAlignmentActual
end
