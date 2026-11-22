import tmp.sheaf.xif.paper.Mzk1Stage4GapInstancesNumericActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual

/-! # Mzk1Stage4GapTightnessCalibrationActual (stage4 lane; Gap tightness calibration)

A646 module: tightness/calibration of the two numeric gaps — explicit slack identities
and positivity, showing the instances are non-vacuous and calibrated to the paper
constants (l=13, e_mod^*=552960).  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessCalibrationActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapInstancesNumericActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- Gap 1 slack value: `regionVol - height = (7/6) log 11`. -/
theorem gap1_slack_value : regionVol11 - height11 = (7 / 6 : Real) * Real.log 11 := by
  unfold regionVol11 height11
  ring

/-- Gap 1 slack is positive. -/
theorem gap1_slack_pos : 0 < regionVol11 - height11 := by
  rw [gap1_slack_value]
  have h : (0 : Real) < Real.log 11 := Real.log_pos (by norm_num)
  positivity

/-- Gap 2 slack value: `(1.1) log 11 + 11 - 2 log 11 = 11 - 0.9 log 11`. -/
theorem gap2_slack_value :
    (1 + 1 / 10 : Real) * Real.log 11 + 11 - regionVol11 =
      11 - (9 / 10 : Real) * Real.log 11 := by
  unfold regionVol11
  ring

/-- Gap 2 slack is positive (since `log 11 < 11`). -/
theorem gap2_slack_pos :
    0 < (1 + 1 / 10 : Real) * Real.log 11 + 11 - regionVol11 := by
  rw [gap2_slack_value]
  have h : Real.log 11 < 11 := by
    have := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
    linarith
  linarith

/-- The Theorem 1.10 instance has positive slack. -/
theorem theorem110_slack_pos :
    (1 / 6 : Real) * degQ11 < theorem110RHS := by
  have hlog : Real.log 11 < 11 := by
    have := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
    linarith
  have hlog0 : (0 : Real) <= Real.log 11 := le_of_lt (Real.log_pos (by norm_num))
  unfold degQ11 theorem110RHS degD11 degF11 dMod eModStar
  norm_num
  have h1 : (1 / 6 : Real) * (5 * Real.log 11) < 10 := by
    nlinarith
  have h2 : (143769600 : Real) <= (33 / 13 : Real) * Real.log 11 + 143769600 := by
    nlinarith
  linarith

#check gap1_slack_value
#check gap1_slack_pos
#check gap2_slack_value
#check gap2_slack_pos
#check theorem110_slack_pos

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTightnessCalibrationActual
end
