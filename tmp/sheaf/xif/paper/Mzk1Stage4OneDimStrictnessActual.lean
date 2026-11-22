import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4OneDimStrictnessActual (stage4 lane; unique filename)

A578 module: stage4-lane 1D strictness of Haar volume — the half interval has strictly
smaller volume than the full interval.  This is the one-coordinate strictness feeding
the strict_measure / scaling-product chain.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessActual

open MeasureTheory
open scoped ENNReal

/-- 1D strictness: the half interval `(-r/2, r/2)` has strictly smaller volume than
the full interval `(-r, r)` for `r > 0`. -/
theorem volume_half_interval_lt {r : Real} (hr : 0 < r) :
    volume (Set.Ioo (-(r / 2)) (r / 2)) < volume (Set.Ioo (-r) r) := by
  rw [Real.volume_Ioo, Real.volume_Ioo]
  have h1 : r / 2 - -(r / 2) = r := by ring
  have h2 : r - -r = 2 * r := by ring
  rw [h1, h2]
  refine (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : Real) < 2 * r)).mpr ?_
  linarith

/-- The half interval's volume is `r`, the full interval's is `2r`. -/
theorem volume_half_interval_eq {r : Real} :
    volume (Set.Ioo (-(r / 2)) (r / 2)) = ENNReal.ofReal r :=
  by
  rw [Real.volume_Ioo]
  congr 1
  ring

/-- The full interval's volume is `2r`. -/
theorem volume_full_interval_eq {r : Real} :
    volume (Set.Ioo (-r) r) = ENNReal.ofReal (2 * r) :=
  by
  rw [Real.volume_Ioo]
  congr 1
  ring


/-- Open-ball version: `volume (ball 0 (r/2)) < volume (ball 0 r)` for `r > 0`. -/
theorem volume_ball_half_lt {r : Real} (hr : 0 < r) :
    volume (Metric.ball (0 : Real) (r / 2)) < volume (Metric.ball (0 : Real) r) := by
  rw [Real.volume_ball, Real.volume_ball]
  have h1 : 2 * (r / 2) = r := by ring
  rw [h1]
  refine (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : Real) < 2 * r)).mpr ?_
  linarith

/-- Closed-ball version: `volume (closedBall 0 (r/2)) < volume (closedBall 0 r)`. -/
theorem volume_closedBall_half_lt {r : Real} (hr : 0 < r) :
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r) := by
  rw [Real.volume_closedBall, Real.volume_closedBall]
  have h1 : 2 * (r / 2) = r := by ring
  rw [h1]
  refine (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : Real) < 2 * r)).mpr ?_
  linarith
#check volume_ball_half_lt
#check volume_closedBall_half_lt

#check volume_half_interval_lt
#check volume_half_interval_eq
#check volume_full_interval_eq

end LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessActual
end
