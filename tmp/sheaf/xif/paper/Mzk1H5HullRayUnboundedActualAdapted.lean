import tmp.sheaf.xif.paper.Hull09H5GapsActual

/-! Mainline: hull log-volume rays are unbounded below (real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullRayUnboundedActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

theorem hull09_ray_not_bddBelow (theta : ℝ) :
    ¬ BddBelow (hullLogVolumeRay theta) := by
  intro hb
  obtain ⟨m, hm⟩ := hb
  have hmem : min theta (m - 1) ∈ hullLogVolumeRay theta := by
    rw [hull09_ray_mem_iff]
    exact min_le_left _ _
  have hle := hm hmem
  have hmin : min theta (m - 1) ≤ m - 1 := min_le_right _ _
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1H5HullRayUnboundedActualAdapted