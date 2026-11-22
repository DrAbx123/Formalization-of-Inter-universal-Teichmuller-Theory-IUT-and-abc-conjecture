/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

/-! # GAP-P7-BALL-MASS: prime-power measure scaling (image form) and explicit ball mass -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PadicBallCeilActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open MeasureTheory
open scoped ENNReal BigOperators NNReal Pointwise

universe u

section RootExtension

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- **(A2)** Actual local ball mass: `μ_b(B_b) = r_b^{d_b} · μ_b(O_b)`
(`s1915_local_measure`). -/
theorem rootExtension_ballMass_eq_radius_pow
    (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : ℝ)) =
      ENNReal.ofReal ((rootImageRadius T b : ℝ) ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) :=
  s1915_local_measure T b

/-- The same with the explicit radius `r_b = p_b^(-c_b/(2l))`. -/
theorem rootExtension_ballMass_eq_p_rpow
    (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : ℝ)) =
      ENNReal.ofReal
        (Real.rpow (qVFamTensorP T b : ℝ)
          (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : ℝ))) ^
          s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  rw [rootExtension_ballMass_eq_radius_pow T b, rootImageRadius_eq_p_rpow]
end RootExtension

end LeanFormal.IUT.XiFPaper.Mzk1PadicBallCeilActual