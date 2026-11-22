/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ComparisonSufficientActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # P7/#1: computable q-side lower bound A = -qRead = |log||q||| -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1QLowerBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- `A = -qRead = |log ||q|||` for the actual C3 q. -/
theorem A_eq_abs_log_qnorm :
    -qPilotLogVolumeReading P = |Real.log ‖P.line.C3.q.q‖| := by
  have h := qPilotLogVolumeReading_eq_neg_abs_qParameter P
  linarith

/-- `A > 0` (the actual q is contracting). -/
theorem A_pos : 0 < -qPilotLogVolumeReading P := by
  have h := P.signedQPilotLogVolume_neg
  unfold qPilotLogVolumeReading
  linarith

/-- Computable lower bound: if `||q|| <= c` for a positive `c`, then `A >= -log c`. -/
theorem A_ge_neg_log_of_qnorm_le {c : ℝ} (hcpos : 0 < c)
    (hqpos : 0 < ‖P.line.C3.q.q‖) (hqlt : ‖P.line.C3.q.q‖ < 1)
    (hle : ‖P.line.C3.q.q‖ ≤ c) :
    -Real.log c ≤ -qPilotLogVolumeReading P := by
  rw [A_eq_abs_log_qnorm]
  have hlog : Real.log ‖P.line.C3.q.q‖ ≤ Real.log c :=
    (Real.log_le_log_iff hqpos hcpos).mpr hle
  have hlogneg : Real.log ‖P.line.C3.q.q‖ < 0 := Real.log_neg hqpos hqlt
  rw [abs_of_neg hlogneg]
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1QLowerBoundActual