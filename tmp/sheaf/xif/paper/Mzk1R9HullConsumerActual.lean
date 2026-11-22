import tmp.sheaf.xif.paper.Mzk1R9PointMembershipConsumerActual
import tmp.sheaf.xif.paper.Hull09H5GapsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: H5 hull-ray x R9 audit (DAG iutiii:HULL.R9 / e-deep:H5) -> Mzk1R9PointMembershipConsumerActual.hullLogVolumeRay_eq_downRay (PROVED) + Hull09H5GapsActual.hull09_ray_mem_iff -> PROVED consumer: Hull09's hull log-volume ray membership in R9 down-ray form. No new math beyond rewriting; no closure.

# Mzk1R9HullConsumerActual — Hull09 ray membership in R9 down-ray form

PROVED:
* `hull09_ray_mem_r9`: lambda lies in the R9 down-ray at theta iff lambda <= theta
  (Hull09 hull-ray membership rewriten through the PROVED ray identification);
* `hull09_ray_mem_r9_image`: set-equality form of the same identification.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9PointMembershipConsumerActual
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

/-- **PROVED:** Hull09 hull-ray membership in R9 down-ray form. -/
theorem hull09_ray_mem_r9 {thetaHullLogVolume lambdaValue : ℝ} :
    lambdaValue ∈ downRay thetaHullLogVolume ↔ lambdaValue ≤ thetaHullLogVolume := by
  rw [← hullLogVolumeRay_eq_downRay, hull09_ray_mem_iff]

/-- **PROVED:** the Hull09 ray is the R9 down-ray (set form). -/
theorem hull09_ray_r9_set (thetaHullLogVolume : ℝ) :
    hullLogVolumeRay thetaHullLogVolume = downRay thetaHullLogVolume :=
  hullLogVolumeRay_eq_downRay thetaHullLogVolume

/-- Rows. -/
def r9HullRows : List (String × String × String) :=
  [ ("Hull09 ray membership in R9 form", "PROVED", "hull09_ray_mem_r9")
  , ("Hull09 ray = R9 down-ray", "PROVED", "hull09_ray_r9_set")
  , ("H5 hull<=image-volume inequality", "NAMED", "Hull09 row: class-B named (report R9/R10); not proved by this ray identification") ]

theorem r9HullRows_length : r9HullRows.length = 3 := rfl

#check hull09_ray_mem_r9
#check hull09_ray_r9_set
#check r9HullRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullConsumerActual
end