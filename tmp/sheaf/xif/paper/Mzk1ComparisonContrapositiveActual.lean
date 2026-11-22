/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ComparisonSufficientActual
import Mathlib.Tactic

/-! # P7/#1: further sufficient conditions and contrapositive for the qTheta comparison -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonContrapositiveActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonSufficientActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- If the theta readout is exactly zero, the comparison holds (q read <= 0). -/
theorem qThetaComparison_of_theta_eq_zero
    (hθ : thetaPilotHullLogVolumeReal C3 = 0) :
    qThetaPilotLogVolumeComparison C3 P := by
  unfold qThetaPilotLogVolumeComparison
  have hq : qPilotLogVolumeReading P ≤ 0 := qPilotLogVolumeReading_nonpos P
  linarith

/-- Contrapositive of the `mu >= 1` sufficient condition: if the comparison fails,
then the hull measure is `< 1`. -/
theorem hull_measure_lt_one_of_not_comparison
    (hnot : ¬ qThetaPilotLogVolumeComparison C3 P) :
    ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal < 1 := by
  by_contra hcon
  have hle : 1 ≤ ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
    le_of_not_gt hcon
  have hcomp : qThetaPilotLogVolumeComparison C3 P :=
    qThetaComparison_of_one_le_hull_measure C3 P hle
  exact hnot hcomp

/-- Equivalently, if the comparison fails then the theta readout is negative. -/
theorem theta_read_neg_of_not_comparison
    (hnot : ¬ qThetaPilotLogVolumeComparison C3 P) :
    thetaPilotHullLogVolumeReal C3 < 0 := by
  have hlt : thetaPilotHullLogVolumeReal C3 < qPilotLogVolumeReading P :=
    lt_of_not_ge hnot
  have hq : qPilotLogVolumeReading P ≤ 0 := qPilotLogVolumeReading_nonpos P
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonContrapositiveActual