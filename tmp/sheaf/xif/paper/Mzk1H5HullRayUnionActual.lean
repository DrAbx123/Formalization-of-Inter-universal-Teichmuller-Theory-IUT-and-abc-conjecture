import tmp.sheaf.xif.paper.Hull09H5GapsActual

/-! Mainline: union law for hull log-volume rays (real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullRayUnionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

theorem hull09_ray_union {theta1 theta2 : ℝ} :
    hullLogVolumeRay theta1 ∪ hullLogVolumeRay theta2 =
      hullLogVolumeRay (max theta1 theta2) := by
  ext x
  rw [Set.mem_union, hull09_ray_mem_iff, hull09_ray_mem_iff, hull09_ray_mem_iff]
  constructor
  · rintro (h | h)
    · exact le_trans h (le_max_left _ _)
    · exact le_trans h (le_max_right _ _)
  · intro h
    rcases (le_max_iff.mp h) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2

end LeanFormal.IUT.XiFPaper.Mzk1H5HullRayUnionActual