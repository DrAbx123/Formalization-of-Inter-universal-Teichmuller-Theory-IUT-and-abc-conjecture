import tmp.sheaf.xif.paper.Mzk1R9HullConsumerActual
import tmp.sheaf.xif.paper.Mzk1R9PointMembershipConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # R9/H5 basic facts bundle (green deps); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullBasicFactsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1R9HullConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1R9PointMembershipConsumerActual

theorem r9HullBasic_eq (theta : ℝ) : hullLogVolumeRay theta = downRay theta := hull09_ray_r9_set theta

theorem r9HullBasic_mem {theta x : ℝ} : x ∈ hullLogVolumeRay theta ↔ x ≤ theta := hull09_ray_mem_r9

theorem r9HullBasic_bundle (theta : ℝ) :
    hullLogVolumeRay theta = downRay theta ∧
      (∀ x : ℝ, x ∈ hullLogVolumeRay theta ↔ x ≤ theta) :=
  ⟨r9HullBasic_eq theta, fun x => r9HullBasic_mem⟩

def r9HullBasicRows : List (String × String × String) :=
  [ ("ray equality", "PROVED", "r9HullBasic_eq"),
    ("membership", "PROVED", "r9HullBasic_mem"),
    ("bundle", "PROVED", "r9HullBasic_bundle") ]

theorem r9HullBasicRows_length : r9HullBasicRows.length = 3 := rfl

#check r9HullBasic_bundle
#check r9HullBasicRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullBasicFactsActual
end