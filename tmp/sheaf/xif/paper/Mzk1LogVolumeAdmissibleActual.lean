import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

/-! # Mzk1LogVolumeAdmissibleActual — monotonicity/admissibility consumers for the hull log-volume

A523 small glue module (no new mathematics): consumes the paper-level hull/log-volume
interface (IQHullLogVolumeInterface of SourceHullCompactnessReduction) to expose the
monotonicity, admissibility (subsets of the hull are admissible and finite) and
normalization consequences used by the Corollary 3.12 closing argument.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeAdmissibleActual

open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

universe u

variable {X : Type u} (W : IQHullLogVolumeInterface X)

/-- Monotonicity of the hull log-volume under region inclusion. -/
theorem logVolume_mono_apply {S T : Set X} (h : S ⊆ T) :
    W.logVolume S ≤ W.logVolume T :=
  W.logVolume_mono h

/-- A region contained in the hull has log-volume bounded by the hull log-volume. -/
theorem region_logVolume_le_hull {S : Set X} (h : S ⊆ W.hull) :
    W.logVolume S ≤ W.logVolume W.hull :=
  W.logVolume_mono h

/-- Admissibility: a region contained in the finite hull has finite log-volume. -/
theorem admissible_region_logVolume_lt_top {S : Set X} (h : S ⊆ W.hull) :
    W.logVolume S < ⊤ :=
  lt_of_le_of_lt (region_logVolume_le_hull W h) (W.hull_logVolume_lt_top)

/-- The scaled unit region has finite log-volume (normalization half). -/
theorem scaleShift_image_logVolume_lt_top :
    W.logVolume (W.scaleShift '' W.unitRegion) < ⊤ :=
  lt_of_le_of_lt W.scaleShift_unitRegion_logVolume_le W.unitRegion_logVolume_lt_top

/-- The image union has finite log-volume (it lies in the hull). -/
theorem imageSet_logVolume_lt_top : W.logVolume W.imageSet < ⊤ :=
  lt_of_le_of_lt W.imageSet_logVolume_le_hull W.hull_logVolume_lt_top

/-- The two Corollary 3.12 conclusions from the ambient data, consumer form. -/
theorem lower_bound_and_finiteness_apply {lowerBound : ENNReal}
    (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  W.lower_bound_and_finiteness h

#check logVolume_mono_apply
#check region_logVolume_le_hull
#check admissible_region_logVolume_lt_top
#check scaleShift_image_logVolume_lt_top
#check imageSet_logVolume_lt_top
#check lower_bound_and_finiteness_apply

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeAdmissibleActual
end
