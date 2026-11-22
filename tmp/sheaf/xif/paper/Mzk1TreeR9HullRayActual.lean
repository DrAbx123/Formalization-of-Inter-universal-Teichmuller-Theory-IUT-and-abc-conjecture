import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealR9PointMembershipAudit
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: tree-only R9/H5 ray identification -> CardHullRealR9PointMembershipAudit.downRay/mem_downRay_iff_le + HullDeterminantLogVolumeReduction.hullLogVolumeRay/mem_hullLogVolumeRay_iff -> PROVED: hull log-volume ray = R9 down-ray, membership form, antitone monotonicity. No named inputs; no closure.

# Mzk1TreeR9HullRayActual — tree-only R9/H5 ray facts

PROVED: ray equality, membership equivalence, antitone monotonicity.
CONSUMED TREE ASSETS: downRay (R9 audit:56), hullLogVolumeRay (HullDeterminant:501).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual

open LeanFormal.IUT

/-- **PROVED:** the H5 hull log-volume ray equals the R9 down-ray. -/
theorem tree_hullRay_eq_downRay (thetaHullLogVolume : ℝ) :
    hullLogVolumeRay thetaHullLogVolume = downRay thetaHullLogVolume := by
  ext x
  rw [mem_hullLogVolumeRay_iff, mem_downRay_iff_le]

/-- **PROVED:** membership form. -/
theorem tree_hullRay_mem_iff {theta x : ℝ} :
    x ∈ hullLogVolumeRay theta ↔ x ≤ theta := by
  rw [tree_hullRay_eq_downRay, mem_downRay_iff_le]

/-- **PROVED:** threshold monotonicity (larger threshold gives larger ray). -/
theorem tree_hullRay_mono {theta1 theta2 : ℝ} (h : theta1 ≤ theta2) :
    hullLogVolumeRay theta1 ⊆ hullLogVolumeRay theta2 := by
  intro x hx
  rw [tree_hullRay_mem_iff] at hx ⊢
  linarith

def treeR9HullRows : List (String × String × String) :=
  [ ("H5 ray = R9 down-ray", "PROVED", "tree_hullRay_eq_downRay")
  , ("membership", "PROVED", "tree_hullRay_mem_iff")
  , ("threshold monotonicity", "PROVED", "tree_hullRay_mono")
  , ("H5 hull<=image-volume", "NAMED", "Hull09 row; not formalized") ]

theorem treeR9HullRows_length : treeR9HullRows.length = 4 := rfl

#check tree_hullRay_eq_downRay
#check tree_hullRay_mono
#check treeR9HullRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeR9HullRayActual
end