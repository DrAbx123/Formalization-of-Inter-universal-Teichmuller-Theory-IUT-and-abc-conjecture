/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902BridgeActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic

/-! # P7/#5: C3 hull measure = haarScale * product of local ball masses -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902QuantityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual
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
variable (D : C3S1902TransportData (T := T) C3)

/-- C3 hull Haar mass in terms of the transport scale and the S1902 local ball masses. -/
theorem hull_measure_toReal_eq_haarScale_mul_prod_ball :
    ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal =
      D.haarScale *
        ∏ b : Bad (nativePlaceSelection T),
          (rootExtensionHaar (T := T) b
            (Metric.closedBall (0 : rootNormedExtension (T := T) b)
              ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal := by
  rw [thetaPilotHull_eq_region]
  rw [D.haar_apply (actualC3LogShellTensorRegion C3)]
  rw [D.region_eq, productHaar_hull_eq_prod_ball T, ENNReal.toReal_prod]

/-- The S3137 raw theta read as `log haarScale + sum_b log mu_b(ball_b)`. -/
theorem thetaRead_eq_log_haarScale_add_sum_log_ball :
    thetaPilotHullLogVolumeReal C3 =
      Real.log D.haarScale +
        ∑ b : Bad (nativePlaceSelection T),
          Real.log (rootExtensionHaar (T := T) b
            (Metric.closedBall (0 : rootNormedExtension (T := T) b)
              ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal := by
  unfold thetaPilotHullLogVolumeReal
  rw [hull_measure_toReal_eq_haarScale_mul_prod_ball T C3 D]
  have hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (rootExtensionHaar (T := T) b
        (Metric.closedBall (0 : rootNormedExtension (T := T) b)
          ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal := by
    intro b; exact localBall_toReal_pos (T := T) b
  rw [Real.log_mul (ne_of_gt D.haarScale_pos) (ne_of_gt (Finset.prod_pos (fun b _ => hpos b)))]
  rw [Real.log_prod]
  intro b _; exact (hpos b).ne'

/-- The product of the S1902 local ball masses is positive. -/
theorem ballMassProduct_pos :
    0 < ∏ b : Bad (nativePlaceSelection T),
      (rootExtensionHaar (T := T) b
        (Metric.closedBall (0 : rootNormedExtension (T := T) b)
          ((rootImageRadius (T := T) b : NNReal) : ℝ))).toReal :=
  Finset.prod_pos fun b _ => localBall_toReal_pos (T := T) b

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902QuantityActual