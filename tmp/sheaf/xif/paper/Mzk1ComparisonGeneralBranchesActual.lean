/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ComparisonSufficientActual
import Mathlib.Tactic

/-! # P7/#1: exact branch characterization of the qTheta comparison -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonGeneralBranchesActual

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

/-- Exact characterization: the comparison is `qRead <= log (mu hull)`. -/
theorem comparison_iff_qRead_le_log_measure :
    qThetaPilotLogVolumeComparison C3 P ↔
      qPilotLogVolumeReading P ≤ Real.log
        ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by
  unfold qThetaPilotLogVolumeComparison thetaPilotHullLogVolumeReal
  rfl

/-- Signed `A = -qRead`, `R = -log(mu hull)` form: comparison is `R <= A`. -/
theorem comparison_iff_neg_log_le_neg_qRead :
    qThetaPilotLogVolumeComparison C3 P ↔
      -(Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) ≤
        -qPilotLogVolumeReading P := by
  rw [comparison_iff_qRead_le_log_measure]
  constructor <;> intro h <;> linarith

/-- Branch split for a successful comparison: either `mu >= 1` (trivial branch),
or `mu < 1` with the necessary condition `log(mu) >= qRead`. -/
theorem comparison_cases (h : qThetaPilotLogVolumeComparison C3 P) :
    (1 ≤ ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) ∨
      (((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal < 1 ∧
        qPilotLogVolumeReading P ≤ Real.log
          ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) := by
  rcases le_or_gt 1
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal with hle | hlt
  · exact Or.inl hle
  · refine Or.inr ⟨hlt, ?_⟩
    exact (comparison_iff_qRead_le_log_measure C3 P).mp h

/-- Necessary condition in the `mu < 1` branch: a failing log inequality implies
the comparison fails. -/
theorem not_comparison_of_log_measure_lt_qRead
    (h : Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal <
      qPilotLogVolumeReading P) :
    ¬ qThetaPilotLogVolumeComparison C3 P := by
  intro hc
  have hle := (comparison_iff_qRead_le_log_measure C3 P).mp hc
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonGeneralBranchesActual