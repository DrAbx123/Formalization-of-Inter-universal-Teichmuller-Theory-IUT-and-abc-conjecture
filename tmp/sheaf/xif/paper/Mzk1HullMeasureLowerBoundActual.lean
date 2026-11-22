/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ComparisonConditionActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import Mathlib.Tactic

/-! # P7/#1: hull measure lower bound via unit region inclusion -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullMeasureLowerBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonConditionActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The actual unit region is contained in the theta-pilot hull. -/
theorem actualUnitRegion_subset_thetaPilotHull :
    actualUnitRegion C3 ⊆ thetaPilotHull C3 := by
  calc actualUnitRegion C3 ⊆ actualHolomorphicHull C3 (actualUnitRegion C3) :=
        actualUnitRegion_subset_hull C3
    _ = thetaPilotHull C3 := rfl

/-- Measure monotonicity: the hull measure is at least the unit-region measure. -/
theorem hull_measure_ge_unitRegion_measure :
    (actualC3LogShellTensorHaar C3) (actualUnitRegion C3) ≤
      (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) :=
  measure_mono (actualUnitRegion_subset_thetaPilotHull C3)

/-- Real-valued form of the lower bound: `mu(unitRegion) <= mu(hull)` (finite hull). -/
theorem hull_measure_toReal_ge_unitRegion
    (hfin : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤) :
    ((actualC3LogShellTensorHaar C3) (actualUnitRegion C3)).toReal ≤
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
  ENNReal.toReal_mono (ne_of_lt hfin) (hull_measure_ge_unitRegion_measure C3)

/-- **Sufficient condition via the unit region**: if `||q||` is at most the
unit-region measure and the hull measure is finite, the comparison holds. -/
theorem comparison_of_qnorm_le_unitRegion_measure
    (hfin : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤)
    (hμpos : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal)
    (hle : ‖P.line.C3.q.q‖ ≤
      ((actualC3LogShellTensorHaar C3) (actualUnitRegion C3)).toReal) :
    qThetaPilotLogVolumeComparison C3 P := by
  have hmono := hull_measure_toReal_ge_unitRegion C3 hfin
  exact comparison_of_qnorm_le_hull_measure C3 P hμpos (le_trans hle hmono)

/-- **Unconditional pattern**: if the unit region has measure at least 1 and
`||q|| < 1`, then the comparison holds. -/
theorem comparison_of_one_le_unitRegion_measure
    (hfin : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤)
    (hμpos : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal)
    (hunit : 1 ≤ ((actualC3LogShellTensorHaar C3) (actualUnitRegion C3)).toReal)
    (hqlt : ‖P.line.C3.q.q‖ < 1) :
    qThetaPilotLogVolumeComparison C3 P :=
  comparison_of_qnorm_le_unitRegion_measure C3 P hfin hμpos
    (le_trans (le_of_lt hqlt) hunit)

end LeanFormal.IUT.XiFPaper.Mzk1HullMeasureLowerBoundActual