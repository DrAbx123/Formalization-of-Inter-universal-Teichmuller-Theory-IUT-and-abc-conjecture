import tmp.sheaf.xif.paper.Mzk1R9HullRayBundleActual
import tmp.sheaf.xif.paper.Mzk1R9HullRayLatticeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # R9 hull ray bundle deep consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleDeepConsumerActual

open LeanFormal.IUT

theorem r9RayDeep_bundle (theta a b : ℝ) :
    hullLogVolumeRay theta = downRay theta ∧
      downRay a ∩ downRay b = downRay (min a b) ∧
      downRay a ∪ downRay b = downRay (max a b) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleActual.r9Hull_ray_eq theta,
    LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual.r9Ray_inter a b,
    LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual.r9Ray_union a b⟩

theorem r9RayDeep_mono {a b : ℝ} (h : a ≤ b) : downRay a ⊆ downRay b :=
  LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual.r9Ray_mono h

def r9RayDeepRows : List (String × String × String) :=
  [ ("ray + lattice bundle", "PROVED", "r9RayDeep_bundle"),
    ("monotonicity", "PROVED", "r9RayDeep_mono") ]

theorem r9RayDeepRows_length : r9RayDeepRows.length = 2 := rfl

#check r9RayDeep_bundle
#check r9RayDeepRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullRayBundleDeepConsumerActual
end