/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902LowerBoundActual
import Mathlib.Tactic

/-! # P7/#1: comparison when the transport product is at least one and q is contracting -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902ConditionOneActual

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
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902QuantityActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902ComparisonActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1ComparisonConditionActual
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

/-- If the transport product `haarScale * prodb mu_b(ball_b)` is at least one and
`||q|| <= 1`, the comparison holds. -/
theorem comparison_of_one_le_haarScale_mul_prod
    (hprod : 1 ≤ D.haarScale *
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar (T := T) b
          (Metric.closedBall (0 : rootNormedExtension (T := T) b)
            ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal)
    (hq : ‖(P.line.C3.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) P.line.C3.place)‖ ≤ 1) :
    qThetaPilotLogVolumeComparison C3 P :=
  (comparison_iff_qnorm_le_haarScale_mul_prod_ball T C3 P D).mpr (le_trans hq hprod)

/-- If the transport scale is 1, the ball-mass product is at least one, and
`||q|| <= 1`, the comparison holds. -/
theorem comparison_of_haarScale_one_of_one_le_prod
    (hscale : D.haarScale = 1)
    (hprod : 1 ≤ ∏ b : Bad (nativePlaceSelection T),
      (rootExtensionHaar (T := T) b
        (Metric.closedBall (0 : rootNormedExtension (T := T) b)
          ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal)
    (hq : ‖(P.line.C3.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) P.line.C3.place)‖ ≤ 1) :
    qThetaPilotLogVolumeComparison C3 P := by
  refine comparison_of_one_le_haarScale_mul_prod T C3 P D ?_ hq
  rw [hscale, one_mul]
  exact hprod

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902ConditionOneActual