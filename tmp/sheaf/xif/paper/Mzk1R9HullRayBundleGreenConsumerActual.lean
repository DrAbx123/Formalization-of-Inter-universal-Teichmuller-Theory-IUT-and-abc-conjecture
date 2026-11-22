import tmp.sheaf.xif.paper.Mzk1R9HullRayBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # R9 hull ray bundle green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleGreenConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleActual

theorem r9HullRayBundleGreen_bundle (theta : ℝ) :
    hullLogVolumeRay theta = downRay theta ∧
      (∀ x : ℝ, x ∈ hullLogVolumeRay theta ↔ x ≤ theta) :=
  r9Hull_bundle theta

theorem r9HullRayBundleGreen_unbounded (a : ℝ) (k : ℕ) :
    (a - ((k : ℝ) + 1)) ∈ downRay a := downRay_unbounded a k

def r9HullRayBundleGreenRows : List (String × String × String) :=
  [ ("ray bundle", "PROVED", "r9HullRayBundleGreen_bundle"),
    ("unboundedness", "PROVED", "r9HullRayBundleGreen_unbounded") ]

theorem r9HullRayBundleGreenRows_length : r9HullRayBundleGreenRows.length = 2 := rfl

#check r9HullRayBundleGreen_bundle
#check r9HullRayBundleGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleGreenConsumerActual
end