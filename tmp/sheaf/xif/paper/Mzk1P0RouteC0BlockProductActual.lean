/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0RootDetHaarActual
import tmp.sheaf.xif.paper.Mzk1P3ProductLogRatioActual
import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import Mathlib.Tactic
/-! # P0.6 #1: block identity -> product normalized-log difference -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0BlockProductActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0RootDetHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductLogRatioActual
open MeasureTheory
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
theorem c0QLattice_log_eq
    (h : RootExtensionHaarDetScaling T b)
    (hO0 : rootExtensionHaar T b (c0UnitBall T b) ≠ 0)
    (hOtop : rootExtensionHaar T b (c0UnitBall T b) ≠ ⊤) :
    Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal =
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
        Real.log ‖c0QHat T b‖ +
      Real.log (rootExtensionHaar T b (c0UnitBall T b)).toReal := by
  rw [c0QLattice_haar_eq T b h]
  rw [ENNReal.toReal_mul]
  have hnorm : ENNReal.toReal
      (ENNReal.ofReal (‖c0QHat T b‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))) =
      ‖c0QHat T b‖ ^ Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    ENNReal.toReal_ofReal (by positivity)
  rw [hnorm]
  rw [Real.log_mul (by positivity)
    (ENNReal.toReal_pos hO0 hOtop).ne']
  rw [Real.log_pow]
  ring
/-- Product normalized-log difference equals the sum of dimension-weighted qhat logs. -/
theorem c0Product_normalizedLog_sub
    (h : RootExtensionHaarDetScaling T b)
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (c0UnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (c0UnitBall T b) ≠ ⊤)
    (hU0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hUtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    rootExtensionProductNormalizedLog T
        (Set.pi Set.univ (fun b => c0QLattice T b)) -
      rootExtensionProductNormalizedLog T
        (Set.pi Set.univ (fun b => c0UnitBall T b)) =
      ∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
          Real.log ‖c0QHat T b‖ := by
  rw [productNormalizedLog_sub T
    (fun b => c0QLattice T b) (fun b => c0UnitBall T b)
    hQ0 hQtop hO0 hOtop hU0 hUtop]
  apply Finset.sum_congr rfl
  intro b _
  have hlocal := c0QLattice_log_eq T b h (hO0 b) (hOtop b)
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0BlockProductActual
end
