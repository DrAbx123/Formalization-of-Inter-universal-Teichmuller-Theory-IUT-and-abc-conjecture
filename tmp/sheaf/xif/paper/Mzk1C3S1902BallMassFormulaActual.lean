/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902ComparisonActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1PadicBallCeilActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-! # GAP-P7-BALL-MASS route A: actual ball-mass product and comparison -/

/-
| field | value |
|---|---|
| Status | PROVED from `s1915_local_measure`: `μ_b(B_b) = r_b^{d_b} μ_b(O_b)`; product mass `= (∏ r_b^{d_b}) * (∏ μ_b(O_b))`; comparison ⇔ `‖q‖ ≤ haarScale * (∏ r_b^{d_b}) * (∏ μ_b(O_b))` |
| GAP | transport data inhabitant (`C3S1902TransportData`) still not constructed; `s1915LocalDegree` vs `Module.finrank` identification not asserted |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902BallMassFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicBallCeilActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902QuantityActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902ComparisonActual
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

/-- Product of the actual local ball masses as a product of `ofReal` factors. -/
theorem ballMassProduct_eq :
    (∏ b : Bad (nativePlaceSelection T),
      rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : ℝ))) =
    ∏ b : Bad (nativePlaceSelection T),
      ENNReal.ofReal ((rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) :=
  Finset.prod_congr rfl fun b _ => rootExtension_ballMass_eq_radius_pow T b

/-- Real product mass: `(∏ μ_b(B_b)).toReal = (∏ r_b^{d_b}) * (∏ μ_b(O_b)).toReal`. -/
theorem ballMassProduct_toReal_eq :
    (∏ b : Bad (nativePlaceSelection T),
      rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : ℝ))).toReal =
      (∏ b : Bad (nativePlaceSelection T),
        (rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
      (∏ b : Bad (nativePlaceSelection T),
        rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      (ENNReal.ofReal ((rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal =
      (rootImageRadius T b : ℝ) ^ s1915LocalDegree T b *
        (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
    intro b
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (NNReal.coe_nonneg _) _)]
  rw [ballMassProduct_eq, ENNReal.toReal_prod,
    Finset.prod_congr rfl (fun b _ => hterm b),
    Finset.prod_mul_distrib, ENNReal.toReal_prod]

/-- The same as a product of real factors. -/
theorem ballMassProduct_toReal_prod_eq :
    (∏ b : Bad (nativePlaceSelection T),
      (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : ℝ))).toReal) =
      (∏ b : Bad (nativePlaceSelection T),
        (rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
      (∏ b : Bad (nativePlaceSelection T),
        rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
  rw [← ENNReal.toReal_prod, ballMassProduct_toReal_eq]

/-- **Comparison with the actual ball-mass product**: criterion in explicit form. -/
theorem comparison_iff_qnorm_le_haarScale_mul_ballMassProduct :
    qThetaPilotLogVolumeComparison C3 P ↔
      ‖P.line.C3.q.q‖ ≤ D.haarScale *
        ((∏ b : Bad (nativePlaceSelection T),
            (rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
          (∏ b : Bad (nativePlaceSelection T),
            rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) := by
  rw [comparison_iff_qnorm_le_haarScale_mul_prod_ball T C3 P D,
    ballMassProduct_toReal_prod_eq T]

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902BallMassFormulaActual