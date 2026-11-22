import tmp.sheaf.xif.paper.Hull09H5GapsActual

/-!
  Mainline: H5 hull log-volume ray closure laws (real proofs from the Hull09 ray
  characterization).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullRayLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

/-- The hull log-volume ray is downward closed. -/
theorem hull09_ray_downward {theta lambda1 lambda2 : ℝ}
    (h12 : lambda1 ≤ lambda2)
    (h : lambda2 ∈ hullLogVolumeRay theta) :
    lambda1 ∈ hullLogVolumeRay theta := by
  rw [hull09_ray_mem_iff] at h ⊢
  linarith

/-- The hull log-volume itself lies on its ray. -/
theorem hull09_ray_self (theta : ℝ) :
    theta ∈ hullLogVolumeRay theta := by
  rw [hull09_ray_mem_iff]

/-- Membership characterization re-export at the ray level. -/
theorem hull09_ray_iff {theta lambda : ℝ} :
    lambda ∈ hullLogVolumeRay theta ↔ lambda ≤ theta :=
  hull09_ray_mem_iff

/-- The hull log-volume ray is monotone in its defining value. -/
theorem hull09_ray_mono_param {theta theta' lambda : ℝ}
    (h : theta ≤ theta') (hmem : lambda ∈ hullLogVolumeRay theta) :
    lambda ∈ hullLogVolumeRay theta' := by
  rw [hull09_ray_mem_iff] at hmem ⊢
  linarith
/-- The hull log-volume ray is exactly the down-set Iic(theta). -/
theorem hull09_ray_eq_Iic (theta : ℝ) :
    hullLogVolumeRay theta = Set.Iic theta := by
  ext lambda
  rw [hull09_ray_mem_iff]
  rfl
/-- The hull log-volume ray families are monotone in the defining value. -/
theorem hull09_ray_subset_of_le {theta theta' : ℝ} (h : theta ≤ theta') :
    hullLogVolumeRay theta ⊆ hullLogVolumeRay theta' := by
  intro lambda hlambda
  rw [hull09_ray_mem_iff] at hlambda ⊢
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1H5HullRayLawsActual