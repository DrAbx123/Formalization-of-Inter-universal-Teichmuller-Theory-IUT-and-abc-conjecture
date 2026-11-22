/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902BallMassFormulaActual
import Mathlib.Tactic

/-! # P7/#1: comparison from the actual ball-mass product (no abstract lower bound) -/

/-
| field | value |
|---|---|
| Status | PROVED: `‖q‖ ≤ haarScale · (∏_b r_b^{d_b}) · (∏_b μ_b(O_b)).toReal` ⇒ comparison, using the actual S1915 local ball mass |
| GAP | `C3S1902TransportData` inhabitant still missing; no abstract `c`/`hprod`/norm-lower-bound inputs remain |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902LowerBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1PadicBallCeilActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902QuantityActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902ComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BallMassFormulaActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators NNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
variable (D : C3S1902TransportData (T := T) C3)

/-- **Comparison from the actual product of local ball masses** (route A). -/
theorem comparison_of_qnorm_le_haarScale_mul_ballMassProduct
    (hle : ‖P.line.C3.q.q‖ ≤ D.haarScale *
      ((∏ b : Bad (nativePlaceSelection T),
          (rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
        (∏ b : Bad (nativePlaceSelection T),
          rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)) :
    qThetaPilotLogVolumeComparison C3 P :=
  (comparison_iff_qnorm_le_haarScale_mul_ballMassProduct T C3 P D).mpr hle

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902LowerBoundActual