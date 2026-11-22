import tmp.sheaf.xif.paper.Hull09H5GapsActual

/-! Mainline: ray partition laws for hull log-volume (real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullRayPartitionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull09H5GapsActual

theorem hull09_ray_disjoint_Ioi (theta : ℝ) :
    hullLogVolumeRay theta ∩ Set.Ioi theta = ∅ := by
  ext x
  rw [Set.mem_inter_iff, hull09_ray_mem_iff, Set.mem_Ioi, Set.mem_empty_iff_false]
  constructor
  · rintro ⟨h1, h2⟩
    exact (not_lt_of_ge h1) h2
  · intro h
    exact h.elim

theorem hull09_ray_union_Ioi (theta : ℝ) :
    hullLogVolumeRay theta ∪ Set.Ioi theta = Set.univ := by
  ext x
  rw [Set.mem_union, hull09_ray_mem_iff, Set.mem_Ioi, Set.mem_univ]
  exact le_or_lt x theta

end LeanFormal.IUT.XiFPaper.Mzk1H5HullRayPartitionActualAdapted