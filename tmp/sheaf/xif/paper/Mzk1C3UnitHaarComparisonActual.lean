/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullMeasureLowerBoundActual
import tmp.sheaf.xif.paper.C3LambdaONormalizedScalarActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import Mathlib.Tactic

/-! # P7/#1: comparison via the concrete `c3UnitHaar` (actual unit-region Haar) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3UnitHaarComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LambdaONormalizedScalarActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonConditionActual
open LeanFormal.IUT.XiFPaper.Mzk1HullMeasureLowerBoundActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- `c3UnitHaar` is the actual Haar of the unit region. -/
theorem c3UnitHaar_eq_unitRegion_measure :
    c3UnitHaar C3 =
      (actualC3LogShellTensorHaar C3) (actualUnitRegion C3) := rfl

/-- Positive unit-region Haar implies positive hull Haar (via the subset). -/
theorem hull_measure_pos_of_unitRegion_pos
    (hunit : 0 < c3UnitHaar C3) :
    0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) := by
  rw [c3UnitHaar_eq_unitRegion_measure] at hunit
  exact lt_of_lt_of_le hunit (hull_measure_ge_unitRegion_measure C3)

/-- Hull Haar is finite (compact region). -/
theorem hull_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ := by
  rw [thetaPilotHull_eq_region]
  exact c3TensorRegion_measure_lt_top (C3 := C3)

/-- **Concrete condition**: `||q|| <= c3UnitHaar.toReal` implies the comparison. -/
theorem comparison_of_qnorm_le_c3UnitHaar
    (hunit : 0 < c3UnitHaar C3)
    (hle : ‖P.line.C3.q.q‖ ≤ (c3UnitHaar C3).toReal) :
    qThetaPilotLogVolumeComparison C3 P := by
  have hfin : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
    hull_measure_lt_top C3
  have hμpos : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (hull_measure_pos_of_unitRegion_pos C3 hunit))
      (ne_of_lt hfin)
  rw [c3UnitHaar_eq_unitRegion_measure] at hle
  exact comparison_of_qnorm_le_unitRegion_measure C3 P hfin hμpos hle

end LeanFormal.IUT.XiFPaper.Mzk1C3UnitHaarComparisonActual