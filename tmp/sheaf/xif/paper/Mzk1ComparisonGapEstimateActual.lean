/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ComparisonGeneralBranchesActual
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # P7/#1: comparison gap estimates in the mu < 1 branch -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonGapEstimateActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonGeneralBranchesActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The comparison gap `log(mu hull) - qRead`; the comparison is its nonnegativity. -/
noncomputable def comparisonGap : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal -
    qPilotLogVolumeReading P

theorem comparisonGap_def :
    comparisonGap C3 P =
      Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal -
        qPilotLogVolumeReading P := rfl

/-- The comparison holds iff the comparison gap is nonnegative. -/
theorem comparison_iff_gap_nonneg :
    qThetaPilotLogVolumeComparison C3 P ↔ 0 ≤ comparisonGap C3 P := by
  rw [comparison_iff_qRead_le_log_measure]
  unfold comparisonGap
  constructor <;> intro h <;> linarith

/-- Exact exponential characterization when the hull measure is positive:
comparison iff `exp(qRead) <= mu(hull)`. -/
theorem comparison_iff_exp_le_measure
    (hm : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal) :
    qThetaPilotLogVolumeComparison C3 P ↔
      Real.exp (qPilotLogVolumeReading P) ≤
        ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by
  rw [comparison_iff_qRead_le_log_measure, Real.le_log_iff_exp_le hm]

/-- In the `mu <= 1` branch the gap is at most `-qRead`. -/
theorem gap_le_neg_qRead_of_measure_le_one
    (hmpos : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal)
    (hm : ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal ≤ 1) :
    comparisonGap C3 P ≤ -qPilotLogVolumeReading P := by
  have hlog : Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal ≤ 0 :=
    Real.log_nonpos (le_of_lt hmpos) hm
  unfold comparisonGap
  linarith

/-- Under a successful comparison in the `mu < 1` branch: `0 <= gap <= -qRead` and `qRead < 0`. -/
theorem comparison_gap_bounds_of_measure_lt_one
    (hmpos : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal)
    (hm : ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal < 1)
    (hcomp : qThetaPilotLogVolumeComparison C3 P) :
    (0 ≤ comparisonGap C3 P) ∧
      (comparisonGap C3 P ≤ -qPilotLogVolumeReading P) ∧
        qPilotLogVolumeReading P < 0 := by
  have hlogneg : Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal < 0 :=
    Real.log_neg hmpos hm
  have hq : qPilotLogVolumeReading P ≤ Real.log
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
    (comparison_iff_qRead_le_log_measure C3 P).mp hcomp
  refine ⟨?_, ?_, ?_⟩
  · rw [comparison_iff_gap_nonneg] at hcomp; exact hcomp
  · unfold comparisonGap; linarith
  · linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonGapEstimateActual