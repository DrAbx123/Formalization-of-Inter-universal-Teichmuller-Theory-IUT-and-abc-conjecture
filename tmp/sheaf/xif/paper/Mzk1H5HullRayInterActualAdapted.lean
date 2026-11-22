import tmp.sheaf.xif.paper.Hull09H5GapsActual

/-! Mainline: intersection law for hull log-volume rays (real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullRayInterActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

theorem hull09_ray_inter {theta1 theta2 : ℝ} :
    hullLogVolumeRay theta1 ∩ hullLogVolumeRay theta2 =
      hullLogVolumeRay (min theta1 theta2) := by
  ext x
  rw [Set.mem_inter_iff, hull09_ray_mem_iff, hull09_ray_mem_iff, hull09_ray_mem_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_min h1 h2
  · intro h
    exact ⟨le_trans h (min_le_left _ _), le_trans h (min_le_right _ _)⟩

end LeanFormal.IUT.XiFPaper.Mzk1H5HullRayInterActualAdapted