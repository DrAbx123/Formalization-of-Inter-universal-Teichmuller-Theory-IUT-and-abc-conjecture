import tmp.sheaf.xif.paper.Mzk1R9HullRayLatticeActual
import tmp.sheaf.xif.paper.Mzk1R9HullBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # R9 hull ray lattice green bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeGreenActual

open LeanFormal.IUT

theorem r9HullLatticeGreen_bundle (a b : ℝ) :
    downRay a ∩ downRay b = downRay (min a b) ∧
      downRay a ∪ downRay b = downRay (max a b) ∧
      hullLogVolumeRay a = downRay a :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual.r9Ray_inter a b,
    LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeActual.r9Ray_union a b,
    LeanFormal.IUT.XiFPaper.Mzk1R9HullBasicFactsActual.r9HullBasic_eq a⟩

def r9HullLatticeGreenRows : List (String × String × String) :=
  [ ("intersection/union/ray equality bundle", "PROVED", "r9HullLatticeGreen_bundle") ]

theorem r9HullLatticeGreenRows_length : r9HullLatticeGreenRows.length = 1 := rfl

#check r9HullLatticeGreen_bundle
#check r9HullLatticeGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9HullRayLatticeGreenActual
end