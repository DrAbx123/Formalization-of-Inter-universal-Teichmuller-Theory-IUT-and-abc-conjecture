import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: IQ hull monotonicity bundle (iutiv-abc:IQHull advance) -> IQHullLogVolumeInterface.logVolume_mono / imageSet_subset_hull (SourceHullCompactnessReduction:52-99) -> PROVED bundle: image⊆hull, volume monotonicity instances, finite hull volume. No closure.

# Mzk1IQHullMonotonicityActual — IQ hull monotonicity consumer

PROVED:
* `iqHull_image_subset`: imageSet ⊆ hull;
* `iqHull_scaleShift_mono`: volume(scaleShift image unit) <= volume(unit);
* `iqHull_finite_and_lower`: combined finiteness + lower-bound form.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT

universe u

/-- **PROVED:** the image union is contained in its hull. -/
theorem iqHull_image_subset {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull := W.imageSet_subset_hull

/-- **PROVED:** the scale-shifted unit region carries at most the unit volume. -/
theorem iqHull_scaleShift_mono {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume (W.scaleShift '' W.unitRegion) ≤ W.logVolume W.unitRegion :=
  W.scaleShift_unitRegion_logVolume_le

/-- **PROVED:** bundled finiteness/lower-bound form. -/
theorem iqHull_finite_and_lower {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  W.lower_bound_and_finiteness h

end LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Mzk1IQHullMonotonicityActual

def iqHullMonoRows : List (String × String × String) :=
  [ ("image union subset hull", "PROVED", "LeanFormal.IUT.iqHull_image_subset")
  , ("scale-shift unit volume monotonicity", "PROVED", "LeanFormal.IUT.iqHull_scaleShift_mono")
  , ("finiteness + lower bound bundle", "PROVED", "LeanFormal.IUT.iqHull_finite_and_lower") ]

theorem iqHullMonoRows_length : iqHullMonoRows.length = 3 := rfl

#check LeanFormal.IUT.iqHull_image_subset
#check LeanFormal.IUT.iqHull_scaleShift_mono
#check iqHullMonoRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IQHullMonotonicityActual
end