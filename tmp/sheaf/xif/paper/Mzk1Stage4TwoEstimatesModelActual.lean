import tmp.sheaf.xif.paper.Mzk1Stage4HeightEstimateActual
import tmp.sheaf.xif.paper.Mzk1Stage4VolumeEstimateActual

/-! # Mzk1Stage4TwoEstimatesModelActual (stage4 lane; unique filename)

A612 module: a concrete numeric MODEL packaging both estimates: height/volume bounds
from HeightEstimate and explicit per-coordinate volumes from VolumeEstimate, with the
combined two-estimate inequality and the product-volume witness.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesModelActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4VolumeEstimateActual

/-- The two-estimates numeric model for 11a1@l=13. -/
structure TwoEstimatesModel where
  /-- the height value. -/
  height : Real
  /-- the region volume value. -/
  regionVol : Real
  height_pos : 0 < height
  height_le_hull : height <= 11
  regionVol_pos : 0 < regionVol
  regionVol_le_hull : regionVol <= 22
  height_lt_region : height < regionVol
  /-- the product-volume witness `2 * 4 = 8`. -/
  product_witness :
    (volume (Metric.closedBall (0 : Real) 1)).toReal *
        (volume (Metric.closedBall (0 : Real) 2)).toReal = 8

/-- Construct the model from the height estimate and the volume witness. -/
noncomputable def twoEstimatesModel11 : TwoEstimatesModel where
  height := height11
  regionVol := regionVol11
  height_pos := heightEstimate11.lb
  height_le_hull := heightEstimate11.ub
  regionVol_pos := by
    unfold regionVol11
    have h : (0 : Real) < Real.log 11 := Real.log_pos (by norm_num)
    linarith
  regionVol_le_hull := by
    unfold regionVol11
    have h : Real.log 11 < 11 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
      linarith
    linarith
  height_lt_region := height_le_region
  product_witness := two_coord_product_witness

/-- Consumer: the model's height is strictly below its region volume. -/
theorem model_height_lt_region (M : TwoEstimatesModel) : M.height < M.regionVol :=
  M.height_lt_region

/-- Consumer: the model's product-volume witness. -/
theorem model_product (M : TwoEstimatesModel) :
    (volume (Metric.closedBall (0 : Real) 1)).toReal *
        (volume (Metric.closedBall (0 : Real) 2)).toReal = 8 :=
  M.product_witness

#check TwoEstimatesModel
#check twoEstimatesModel11
#check model_height_lt_region
#check model_product

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TwoEstimatesModelActual
end
