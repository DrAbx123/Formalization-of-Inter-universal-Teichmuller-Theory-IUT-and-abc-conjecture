/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-! # P7/#1: sufficient conditions for the qTheta comparison from S3137 readings -/

/-
| field | value |
|---|---|
| Status | PROVED sufficient conditions (not the general comparison): theta read >= 0, equivalently mu(hull) >= 1 |
| GAP | GAP-P7-GENERAL-CMP: general paper-normalization comparison still missing |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonSufficientActual

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

/-- If the theta readout is nonnegative, the q-pilot readout (<= 0) is below it. -/
theorem qThetaComparison_of_theta_nonneg
    (h : 0 ≤ thetaPilotHullLogVolumeReal C3) :
    qThetaPilotLogVolumeComparison C3 P := by
  unfold qThetaPilotLogVolumeComparison
  have hq : qPilotLogVolumeReading P ≤ 0 := qPilotLogVolumeReading_nonpos P
  linarith

/-- A concrete sufficient condition: the hull measure is at least 1. -/
theorem theta_read_nonneg_of_one_le_measure
    (h : 1 ≤ ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) :
    0 ≤ thetaPilotHullLogVolumeReal C3 := by
  unfold thetaPilotHullLogVolumeReal
  exact Real.log_nonneg h

/-- **Proved sufficient condition**: `mu(theta hull) >= 1` implies the comparison. -/
theorem qThetaComparison_of_one_le_hull_measure
    (h : 1 ≤ ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaComparison_of_theta_nonneg C3 P
    (theta_read_nonneg_of_one_le_measure C3 h)

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonSufficientActual