import tmp.sheaf.xif.paper.Mzk1TreeR9HullRayActual
import tmp.sheaf.xif.paper.Mzk1TreeDownRayLatticeActual
import tmp.sheaf.xif.paper.Mzk1TreeR9RaySetActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullTreeR9BatchConsumerActual — tree R9/H5 batch consumer

A473: real Lean batch over the green tree R9/H5 ray files. No sorry/axioms;
no closure claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullTreeR9BatchConsumerActual

open LeanFormal.IUT

theorem treeR9Batch_rayEq (thetaHullLogVolume : ℝ) :
    hullLogVolumeRay thetaHullLogVolume = downRay thetaHullLogVolume :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_eq_downRay thetaHullLogVolume

theorem treeR9Batch_mem {theta x : ℝ} :
    x ∈ hullLogVolumeRay theta ↔ x ≤ theta :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual.tree_hullRay_mem_iff

theorem treeR9Batch_inter (a b : ℝ) :
    downRay a ∩ downRay b = downRay (min a b) :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeDownRayLatticeActual.downRay_inter a b

def treeR9BatchRows : List (String × String × String) :=
  [ ("ray equality", "PROVED", "treeR9Batch_rayEq"),
    ("membership", "PROVED", "treeR9Batch_mem"),
    ("intersection", "PROVED", "treeR9Batch_inter") ]

theorem treeR9BatchRows_length : treeR9BatchRows.length = 3 := rfl

#check treeR9Batch_rayEq
#check treeR9BatchRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullTreeR9BatchConsumerActual
end