/- Copyright (c) 2026 contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ComparisonSufficientActual
import tmp.sheaf.xif.paper.Mzk1ComparisonGeneralBranchesActual
import tmp.sheaf.xif.paper.Mzk1S3137ReadoutBridgeActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # P7/#1: explicit sufficient condition `||q|| <= mu(hull)` for the comparison -/

/-
| field | value |
|---|---|
| Status | PROVED explicit branch: `||q|| <= mu(theta hull)` (both positive) implies the qTheta comparison; this is exactly `A >= R` in the mu<1 branch |
| GAP | GAP-P7-GENERAL-CMP: no general proof; this is a sufficient condition with the concrete q norm |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonConditionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ReadoutBridgeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonSufficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonGeneralBranchesActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The actual C3 q norm is positive. -/
theorem qnorm_pos : 0 < ‖P.line.C3.q.q‖ := norm_pos_iff.mpr P.line.C3.q.q_ne_zero

/-- The q readout is `log ||q||`. -/
theorem qRead_eq_log_qnorm :
    qPilotLogVolumeReading P = Real.log ‖P.line.C3.q.q‖ :=
  qPilotLogVolumeReading_eq_log_norm P

/-- **Exact criterion**: with positive `||q||` and positive hull measure, the
comparison is equivalent to `||q|| <= mu(hull)`. -/
theorem comparison_iff_qnorm_le_hull_measure
    (hm : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) :
    qThetaPilotLogVolumeComparison C3 P ↔
      ‖P.line.C3.q.q‖ ≤ ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by
  rw [comparison_iff_qRead_le_log_measure, qRead_eq_log_qnorm P]
  exact (Real.log_le_log_iff (qnorm_pos P) hm)

/-- **Explicit sufficient condition**: `||q|| <= mu(hull)` implies the comparison. -/
theorem comparison_of_qnorm_le_hull_measure
    (hm : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal)
    (hle : ‖P.line.C3.q.q‖ ≤
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) :
    qThetaPilotLogVolumeComparison C3 P :=
  (comparison_iff_qnorm_le_hull_measure C3 P hm).mpr hle

/-- `A = -qRead` and `R = -thetaRead`; `A >= R` is exactly `||q|| <= mu(hull)`. -/
theorem A_ge_R_iff_qnorm_le_hull_measure
    (hm : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) :
    -(Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) ≤
        -qPilotLogVolumeReading P ↔
      ‖P.line.C3.q.q‖ ≤ ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by
  rw [qRead_eq_log_qnorm P]
  constructor <;> intro h
  · have h' : Real.log ‖P.line.C3.q.q‖ ≤ Real.log
        ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by linarith
    exact (Real.log_le_log_iff (qnorm_pos P) hm).mp h'
  · have h' : Real.log ‖P.line.C3.q.q‖ ≤ Real.log
        ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
      (Real.log_le_log_iff (qnorm_pos P) hm).mpr h
    linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonConditionActual