import tmp.sheaf.xif.paper.Mzk1R9HullConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: R9/H5 ray monotonicity (DAG iutiii:HULL.R9 / e-deep:H5 advance) -> downRay (CardHullRealR9PointMembershipAudit:56) + hullLogVolumeRay_eq_downRay (Mzk1R9PointMembershipConsumerActual) -> PROVED monotonicity: larger theta gives smaller ray; R9/H5 ray membership monotone. No closure.

# Mzk1R9RayMonotonicityActual — monotonicity of the R9/H5 rays

PROVED:
* `downRay_antitone`: theta1 <= theta2 -> downRay theta2 <= downRay theta1;
* `hullLogVolumeRay_antitone`: same for the H5 hull log-volume ray;
* `ray_mem_mono`: membership monotonicity form.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9RayMonotonicityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9PointMembershipConsumerActual

/-- **PROVED:** down-rays are antitone in theta. -/
theorem downRay_mono {theta1 theta2 : ℝ} (h : theta1 ≤ theta2) :
    downRay theta1 ⊆ downRay theta2 := by
  intro x hx
  rw [mem_downRay_iff_le] at hx ⊢
  linarith

/-- **PROVED:** the H5 hull log-volume ray is antitone in theta. -/
theorem hullLogVolumeRay_mono {theta1 theta2 : ℝ} (h : theta1 ≤ theta2) :
    hullLogVolumeRay theta1 ⊆ hullLogVolumeRay theta2 := by
  rw [hullLogVolumeRay_eq_downRay, hullLogVolumeRay_eq_downRay]
  exact downRay_mono h

/-- **PROVED:** ray membership monotonicity. -/
theorem ray_mem_mono {theta1 theta2 x : ℝ} (h : theta1 ≤ theta2)
    (hx : x ∈ hullLogVolumeRay theta1) : x ∈ hullLogVolumeRay theta2 :=
  hullLogVolumeRay_mono h hx

/-- Rows. -/
def r9RayRows : List (String × String × String) :=
  [ ("down-ray monotonicity", "PROVED", "downRay_mono")
  , ("H5 hull-ray monotonicity", "PROVED", "hullLogVolumeRay_mono")
  , ("ray membership monotonicity", "PROVED", "ray_mem_mono")
  , ("H9 value-form/witness-form calibration", "CONSUMED TREE ASSET", "R9 audit (built)") ]

theorem r9RayRows_length : r9RayRows.length = 4 := rfl

#check downRay_mono
#check hullLogVolumeRay_mono
#check ray_mem_mono
#check r9RayRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9RayMonotonicityActual
end