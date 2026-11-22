import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1HullFinitenessChainActual — A479 new finiteness/bound chains (H5 interface)

New conclusions from the interface fields and donor theorems of
`SourceHullCompactnessReduction.lean` (:59/:62/:73/:76/:80/:88/:95):

1. `imageSet_logVolume_lt_top`: the image-union log-volume is finite
   (image ⊆ hull and the hull volume is finite);
2. `hull_logVolume_le_unitRegion`: the hull log-volume is bounded by the unit
   region log-volume through the scale-shift inclusion and Haar normalization;
3. `scaleShift_unitRegion_lt_top`: the scaled unit region has finite
   log-volume.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullFinitenessChainActual

open LeanFormal.IUT

/-- Finiteness of the image-union log-volume. -/
theorem imageSet_logVolume_lt_top {X : Type*} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.imageSet < ⊤ :=
  lt_of_le_of_lt (IQHullLogVolumeInterface.imageSet_logVolume_le_hull W)
    (IQHullLogVolumeInterface.hull_logVolume_lt_top W)

/-- Hull log-volume is bounded by the unit-region log-volume. -/
theorem hull_logVolume_le_unitRegion {X : Type*} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull ≤ W.logVolume W.unitRegion :=
  le_trans (W.logVolume_mono W.hull_subset_scaleShift)
    W.scaleShift_unitRegion_logVolume_le

/-- Finiteness of the scaled unit-region log-volume. -/
theorem scaleShift_unitRegion_lt_top {X : Type*} (W : IQHullLogVolumeInterface X) :
    W.logVolume (W.scaleShift '' W.unitRegion) < ⊤ :=
  lt_of_le_of_lt W.scaleShift_unitRegion_logVolume_le
    W.unitRegion_logVolume_lt_top

#check imageSet_logVolume_lt_top
#check hull_logVolume_le_unitRegion

end LeanFormal.IUT.XiFPaper.Mzk1HullFinitenessChainActual
end