import Mathlib
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel

/-! # S3131 instantiation attempt: RegionRelativeToHullAndWeight (prior-art first) -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

namespace LeanFormal.IUT.XiFPaper.S3131RegionRelativeInstantiationAttemptActual

universe u

/-- EXACT OBLIGATION for (c): region volume is at most hull volume plus a constant. -/
def RegionRelativeToHullAndWeight {X : Type u} (W : IQHullLogVolumeInterface X)
    (region : Set X) : Prop :=
  ∃ D : Real, (W.logVolume region).toReal ≤ (W.logVolume W.hull).toReal + D

/-- PROVABLE instance: a region contained in the hull, with the hull volume finite,
satisfies the relative obligation with D = 0 (prior art: IQHullLogVolumeInterface.logVolume_mono). -/
theorem regionRelative_of_subset_hull {X : Type u} {W : IQHullLogVolumeInterface X}
    {region : Set X} (hsub : region ⊆ W.hull) (hfin : W.logVolume W.hull ≠ ⊤) :
    RegionRelativeToHullAndWeight W region := by
  refine ⟨0, ?_⟩
  have hle : W.logVolume region ≤ W.logVolume W.hull := W.logVolume_mono hsub
  have hto : (W.logVolume region).toReal ≤ (W.logVolume W.hull).toReal :=
    ENNReal.toReal_mono hfin hle
  linarith

#check RegionRelativeToHullAndWeight
#check iqCarrierModelLogVolume_region_eq
#check iqCarrierModelLogVolume_union_le

end LeanFormal.IUT.XiFPaper.S3131RegionRelativeInstantiationAttemptActual
end