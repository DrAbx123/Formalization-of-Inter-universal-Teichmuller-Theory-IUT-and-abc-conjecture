import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply

/-! # S3131 instantiation attempt: CardAMPLThetaBoundSupply vs our (c) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131CardAMPLInstantiationAttemptActual

universe u

/-- REUSE: the supply's real-form reduction law is available verbatim. -/
theorem cardAMPL_realVolume_le {X : Type u} {W : IQHullLogVolumeInterface X}
    (S : CardAMPLThetaBoundSupply W) : iqHullRealVolume W ≤ S.theta :=
  CardAMPLThetaBoundSupply.realVolume_le S

/-- EXACT REMAINING HYPOTHESIS for (c): a region-vs-(weight+hull) relative bound.
CardAMPLThetaBoundSupply supplies only the HULL upper bound (O3), not this. -/
def RegionRelativeToHullAndWeight {X : Type u} (W : IQHullLogVolumeInterface X)
    (region : Set X) : Prop :=
  ∃ D : Real, (W.logVolume region).toReal ≤ (W.logVolume W.hull).toReal + D

/-- The relative bound is the irreducible content of (c) beyond the hull term:
with any weight term added, (c) follows by linarith (bookkeeping only). -/
theorem relative_bound_gives_region_bound {X : Type u} {W : IQHullLogVolumeInterface X}
    {region : Set X} {weight : Real} {D : Real}
    (h : (W.logVolume region).toReal ≤ (W.logVolume W.hull).toReal + D)
    (hD : D ≤ weight + D) : (W.logVolume region).toReal ≤ (W.logVolume W.hull).toReal + weight + D :=
  by linarith

#check CardAMPLThetaBoundSupply.realVolume_le
#check CardAMPLThetaBoundSupply.ofReal_le_theta_of_imageSet_lower
#check CardAMPLThetaBoundSupply.exists_hull_eq_ofReal
#check CardAMPLThetaBoundSupply.of_realVolume_le

end LeanFormal.IUT.XiFPaper.S3131CardAMPLInstantiationAttemptActual
end