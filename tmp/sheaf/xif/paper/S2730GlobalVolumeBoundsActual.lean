import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2730GlobalVolumeBoundsActual

open LeanFormal.IUT
open LeanFormal.IUT.ABCBridge
open MeasureTheory

universe u

variable {X : Type u} (W : IQHullLogVolumeInterface X)
variable (point : Nat -> Nat -> Nat -> X)

/-- The generic global hweightvol statement for any IQ hull interface and point map. -/
def S2730Hweightvol : Prop :=
  forall a n c : Nat, IsABCTriple a n c ->
    arithmeticWeight (abcRationalPoint a c) <=
      (W.logVolume (normalizedComparisonRegion W point a n c)).toReal

/-- The normalized comparison region is the union of the scaled unit region and
the scaled point. -/
theorem S2730_region_eq_union (a n c : Nat) :
    normalizedComparisonRegion W point a n c =
      W.scaleShift '' W.unitRegion ∪ {W.scaleShift (point a n c)} :=
  Set.image_union

/-- Upper volume bound for the normalized comparison region, assuming
subadditivity of the log-volume. -/
theorem S2730_region_volume_le
    (hsub : forall S T : Set X, W.logVolume (S ∪ T) <= W.logVolume S + W.logVolume T)
    (a n c : Nat) :
    W.logVolume (normalizedComparisonRegion W point a n c) <=
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (point a n c)} := by
  rw [S2730_region_eq_union]
  exact hsub _ _

/-- Lower volume bound: the scaled unit region is contained in the normalized
comparison region. -/
theorem S2730_region_volume_ge (a n c : Nat) :
    W.logVolume (W.scaleShift '' W.unitRegion) <=
      W.logVolume (normalizedComparisonRegion W point a n c) := by
  apply W.logVolume_mono
  rw [S2730_region_eq_union]
  exact Set.subset_union_left

/-- A bound by the scaled unit region implies the full hweightvol statement. -/
theorem S2730_hweightvol_of_scaledUnitBound
    (h : forall a n c : Nat, IsABCTriple a n c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (W.logVolume (W.scaleShift '' W.unitRegion)).toReal) :
    S2730Hweightvol W point := by
  intro a n c habc
  refine le_trans (h a n c habc) (ENNReal.toReal_mono ?_ (S2730_region_volume_ge W point a n c))
  exact ENNReal.toReal_ne_top (by
    intro htop
    exact htop)

/-- hweightvol plus subadditivity gives the explicit upper bound by the scaled
unit-region volume and the point volume. -/
theorem S2730_hweightvol_imp_upper
    (hsub : forall S T : Set X, W.logVolume (S ∪ T) <= W.logVolume S + W.logVolume T)
    (h : S2730Hweightvol W point) :
    forall a n c : Nat, IsABCTriple a n c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (W.logVolume (W.scaleShift '' W.unitRegion) +
          W.logVolume {W.scaleShift (point a n c)}).toReal := by
  intro a n c habc
  refine le_trans (h a n c habc) (ENNReal.toReal_mono ?_ (S2730_region_volume_le W point hsub a n c))

#check S2730Hweightvol
#check S2730_region_eq_union
#check S2730_region_volume_le
#check S2730_region_volume_ge
#check S2730_hweightvol_of_scaledUnitBound
#check S2730_hweightvol_imp_upper

end LeanFormal.IUT.XiFPaper.S2730GlobalVolumeBoundsActual
end
