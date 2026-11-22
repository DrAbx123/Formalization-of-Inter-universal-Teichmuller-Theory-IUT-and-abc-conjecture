import tmp.sheaf.xif.paper.Mzk1Stage4GapTightnessCalibrationActual

/-! # Mzk1Stage4GapTightnessConsumerActual (stage4 lane; tightness consumer)

A646 module: consumer of the gap tightness calibration — the strict gap statements and
the calibrated slacks in one record.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessCalibrationActual

/-- The calibrated tightness record for the two numeric gaps. -/
structure GapTightnessRecord where
  /-- strict Gap 1 (height strictly below region volume). -/
  gap1_strict : Mzk1Stage4HeightEstimateActual.height11 < Mzk1Stage4HeightEstimateActual.regionVol11
  /-- positive Gap 1 slack. -/
  gap1_slack : 0 < Mzk1Stage4HeightEstimateActual.regionVol11 - Mzk1Stage4HeightEstimateActual.height11
  /-- positive Gap 2 slack. -/
  gap2_slack :
    0 < (1 + 1 / 10 : Real) * Real.log 11 + 11 -
      Mzk1Stage4HeightEstimateActual.regionVol11

/-- Construct the tightness record. -/
noncomputable def gapTightnessRecord : GapTightnessRecord where
  gap1_strict := Mzk1Stage4HeightEstimateActual.height_le_region
  gap1_slack := gap1_slack_pos
  gap2_slack := gap2_slack_pos

/-- Consumer: strict Gap 1 with calibrated slack. -/
theorem gapTightness_gap1 :
    Mzk1Stage4HeightEstimateActual.height11 < Mzk1Stage4HeightEstimateActual.regionVol11 ∧
      0 < Mzk1Stage4HeightEstimateActual.regionVol11 - Mzk1Stage4HeightEstimateActual.height11 :=
  ⟨gapTightnessRecord.gap1_strict, gapTightnessRecord.gap1_slack⟩

#check GapTightnessRecord
#check gapTightnessRecord
#check gapTightness_gap1

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessConsumerActual
end
