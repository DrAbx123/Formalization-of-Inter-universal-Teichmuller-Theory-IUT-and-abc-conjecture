import tmp.sheaf.xif.paper.Mzk1Stage4OneDimStrictnessActual
import tmp.sheaf.xif.paper.Mzk1Stage4ProductStrictnessActual

/-! # Mzk1Stage4OneDimStrictnessConsumerActual (stage4 lane; unique filename)

A582 module: consumer of the 1D strictness lemmas in the shape needed by the
strict_measure chain (one coordinate at a time), plus the two-factor product step.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessConsumerActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ProductStrictnessActual

/-- One-coordinate strictness for a single closed ball factor. -/
theorem oneDim_closedBall_strict {r : Real} (hr : 0 < r) :
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r) :=
  volume_closedBall_half_lt hr

/-- One-coordinate strictness for a single open ball factor. -/
theorem oneDim_ball_strict {r : Real} (hr : 0 < r) :
    volume (Metric.ball (0 : Real) (r / 2)) <
      volume (Metric.ball (0 : Real) r) :=
  volume_ball_half_lt hr

/-- A positive closed-ball volume (positive radius). -/
theorem closedBall_volume_pos {r : Real} (hr : 0 < r) :
    0 < volume (Metric.closedBall (0 : Real) r) := by
  rw [Real.volume_closedBall]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- Combining one strict 1D factor with non-strict positives, in `toReal` form
(the `NNReal`/`ENNReal` product strictness goes through `toReal` finiteness). -/
theorem oneDim_product_strict_toReal {r s : Real} (hr : 0 < r) (hs : 0 < s) :
    (volume (Metric.closedBall (0 : Real) (r / 2))).toReal *
        (volume (Metric.closedBall (0 : Real) (s / 2))).toReal <
      (volume (Metric.closedBall (0 : Real) r)).toReal *
        (volume (Metric.closedBall (0 : Real) s)).toReal := by
  rw [Real.volume_closedBall, Real.volume_closedBall,
    Real.volume_closedBall, Real.volume_closedBall]
  have hr0 : (0 : Real) ≤ 2 * (r / 2) := by linarith
  have hs0 : (0 : Real) ≤ 2 * (s / 2) := by linarith
  have hr1 : (0 : Real) ≤ 2 * r := by linarith
  have hs1 : (0 : Real) ≤ 2 * s := by linarith
  rw [ENNReal.toReal_ofReal hr0, ENNReal.toReal_ofReal hs0,
    ENNReal.toReal_ofReal hr1, ENNReal.toReal_ofReal hs1]
  have h2r : 2 * (r / 2) = r := by ring
  have h2s : 2 * (s / 2) = s := by ring
  rw [h2r, h2s]
  nlinarith
#check oneDim_closedBall_strict
#check oneDim_ball_strict
#check oneDim_product_strict_toReal

end LeanFormal.IUT.XiFPaper.Mzk1Stage4OneDimStrictnessConsumerActual
end
