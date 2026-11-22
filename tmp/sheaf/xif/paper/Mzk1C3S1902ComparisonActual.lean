/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902QuantityActual
import tmp.sheaf.xif.paper.Mzk1ComparisonConditionActual
import tmp.sheaf.xif.paper.QPilotObjectActual
import Mathlib.Tactic

/-! # P7/#1: comparison ⇔ ||q|| <= haarScale * product of local ball masses -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902ComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902QuantityActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonConditionActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
variable (D : C3S1902TransportData (T := T) C3)

theorem comparison_iff_qnorm_le_haarScale_mul_prod_ball :
    qThetaPilotLogVolumeComparison C3 P ↔
      ‖(P.line.C3.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) P.line.C3.place)‖ ≤ D.haarScale *
        ∏ b : Bad (nativePlaceSelection T),
          (rootExtensionHaar (T := T) b
            (Metric.closedBall (0 : rootNormedExtension (T := T) b)
              ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal := by
  have hμpos : 0 < ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal := by
    rw [hull_measure_toReal_eq_haarScale_mul_prod_ball T C3 D]
    exact mul_pos D.haarScale_pos (ballMassProduct_pos T)
  rw [comparison_iff_qnorm_le_hull_measure C3 P hμpos]
  rw [hull_measure_toReal_eq_haarScale_mul_prod_ball T C3 D]

theorem comparison_of_qnorm_le_haarScale_mul_prod_ball
    (hle : ‖(P.line.C3.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) P.line.C3.place)‖ ≤ D.haarScale *
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar (T := T) b
          (Metric.closedBall (0 : rootNormedExtension (T := T) b)
            ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal) :
    qThetaPilotLogVolumeComparison C3 P :=
  (comparison_iff_qnorm_le_haarScale_mul_prod_ball T C3 P D).mpr hle

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902ComparisonActual