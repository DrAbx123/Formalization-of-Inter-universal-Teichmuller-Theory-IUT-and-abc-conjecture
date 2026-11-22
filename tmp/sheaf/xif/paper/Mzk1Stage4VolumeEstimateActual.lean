import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4VolumeEstimateActual (stage4 lane; unique filename)

A611 module: substantive VOLUME estimates — explicit 1D closed-ball volumes and their
two-coordinate product in `toReal` form.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4VolumeEstimateActual

open MeasureTheory
open scoped ENNReal

/-- Volume of the unit closed ball in `ℝ` is `2`. -/
theorem volume_closedBall_one :
    volume (Metric.closedBall (0 : Real) 1) = (2 : ENNReal) := by
  rw [Real.volume_closedBall]
  norm_num

/-- Volume of the radius-2 closed ball in `ℝ` is `4`. -/
theorem volume_closedBall_two :
    volume (Metric.closedBall (0 : Real) 2) = (4 : ENNReal) := by
  rw [Real.volume_closedBall]
  norm_num

/-- Volume of the unit open ball in `ℝ` is `2`. -/
theorem volume_ball_one :
    volume (Metric.ball (0 : Real) 1) = (2 : ENNReal) := by
  rw [Real.volume_ball]
  norm_num

/-- The two-coordinate product volume in `toReal` form is `8`. -/
theorem two_coord_product_witness :
    (volume (Metric.closedBall (0 : Real) 1)).toReal *
        (volume (Metric.closedBall (0 : Real) 2)).toReal = 8 := by
  rw [volume_closedBall_one, volume_closedBall_two]
  norm_num

/-- The half-ball product is strictly smaller than the full-ball product (toReal). -/
theorem halfBall_product_lt :
    (volume (Metric.closedBall (0 : Real) (1 / 2))).toReal *
        (volume (Metric.closedBall (0 : Real) 1)).toReal <
      (volume (Metric.closedBall (0 : Real) 1)).toReal *
        (volume (Metric.closedBall (0 : Real) 2)).toReal := by
  rw [Real.volume_closedBall, Real.volume_closedBall]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  norm_num

#check volume_closedBall_one
#check volume_closedBall_two
#check volume_ball_one
#check two_coord_product_witness
#check halfBall_product_lt

end LeanFormal.IUT.XiFPaper.Mzk1Stage4VolumeEstimateActual
end
