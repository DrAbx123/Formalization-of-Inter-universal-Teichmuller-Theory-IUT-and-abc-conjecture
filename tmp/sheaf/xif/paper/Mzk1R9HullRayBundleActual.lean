import tmp.sheaf.xif.paper.Mzk1R9HullConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: R9/H5 ray bundle -> Mzk1R9HullConsumerActual (watchdog DONE EXIT=0) + downRay facts -> PROVED equality/membership/unboundedness bundle. No closure.

# Mzk1R9HullRayBundleActual — R9/H5 ray bundle

Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9HullConsumerActual

theorem r9Hull_ray_eq (theta : ℝ) :
    hullLogVolumeRay theta = downRay theta := hull09_ray_r9_set theta

theorem r9Hull_mem_iff {theta x : ℝ} :
    x ∈ hullLogVolumeRay theta ↔ x ≤ theta := hull09_ray_mem_r9

theorem downRay_unbounded (a : ℝ) (k : ℕ) :
    (a - ((k : ℝ) + 1)) ∈ downRay a := by
  rw [mem_downRay_iff_le]
  linarith

theorem r9Hull_bundle (theta : ℝ) :
    hullLogVolumeRay theta = downRay theta ∧
      (∀ x : ℝ, x ∈ hullLogVolumeRay theta ↔ x ≤ theta) ∧
      (∀ k : ℕ, (theta - ((k : ℝ) + 1)) ∈ downRay theta) :=
  ⟨r9Hull_ray_eq theta, fun x => r9Hull_mem_iff, fun k => downRay_unbounded theta k⟩

def r9HullBundleRows : List (String × String × String) :=
  [ ("ray equality", "PROVED", "r9Hull_ray_eq")
  , ("membership", "PROVED", "r9Hull_mem_iff")
  , ("unbounded below", "PROVED", "downRay_unbounded")
  , ("bundle", "PROVED", "r9Hull_bundle") ]

theorem r9HullBundleRows_length : r9HullBundleRows.length = 4 := rfl

#check r9Hull_bundle
#check downRay_unbounded
#check r9HullBundleRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleActual
end