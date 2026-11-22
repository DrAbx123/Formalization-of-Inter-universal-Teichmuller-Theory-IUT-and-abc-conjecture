/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic
/-! # qVFam default-vs-normalized norm bridge: value-level proof

Both norms are evaluated by their exact absNorm^exponent formulas; the bridge
is then `absNorm^(-nu/d) = (absNorm^(-nu))^(1/d)`, with no S45. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.Mzk1QVFamNormBridgeValueActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Normalized norm value from the donor normalized formula. -/
theorem qVFamNormalizedNorm_eq_absNorm_rpow :
    qVFamNormalizedNorm T b =
      (absNorm (qVFamTensorPlace T b)) ^
        (-(nu (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) : ℝ) /
          (d (qVFamTensorPlace T b) : ℝ)) := by
  have h := generalNormalizedNormFormula (F := T.arithmetic.F)
    (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b)
    (qVFamNormalizedGenerator_ne_zero T b)
  simpa [qVFamNormalizedNorm, qVFamNormalizedGenerator, CommonPrimeCompletion,
    NormalizedCompletion, qVFamTensorPlaces, qVFamTensorPlace, d] using h
/-- Default norm value from the default completion norm formula and `nu` sign. -/
theorem qVFamDefaultNorm_eq_absNorm_rpow :
    qVFamDefaultNorm T b =
      (absNorm (qVFamTensorPlace T b)) ^
        (-(nu (qVFamTensorPlace T b) (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q) : ℝ)) := by
  have hx : (qVFamily T b).q ≠ 0 := (qVFamily T b).q_ne_zero
  have h := norm_eq_absNorm_zpow (F := T.arithmetic.F)
    (qVFamTensorPlace T b) ((qVFamily T b).q) hx
  have hv : Valued.v (toC (qVFamTensorPlace T b)
      (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q)) ≠ 0 :=
    valuation_ne_zero_of_ne_zero (qVFamTensorPlace T b)
      (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q)
      (by simpa using hx)
  have hlog : WithZero.log (Valued.v (toC (qVFamTensorPlace T b)
      (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q))) =
      Multiplicative.toAdd (WithZero.unzero hv) := by
    conv_lhs => rw [← WithZero.coe_unzero hv]
    rfl
  have hnu : nu (qVFamTensorPlace T b)
      (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q) =
      -Multiplicative.toAdd (WithZero.unzero hv) := by
    unfold nu
    rw [hlog]
  have hval : Multiplicative.toAdd (WithZero.unzero hv) =
      -nu (qVFamTensorPlace T b)
        (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q) := by
    rw [hnu]; ring
  change ‖(qVFamily T b).q‖ = absNorm (qVFamTensorPlace T b) ^ (-(nu (qVFamTensorPlace T b) (show NormalizedCompletion (qVFamTensorPlace T b) from (qVFamily T b).q) : ℝ))
  rw [h, hval]
/-- **The bridge**: qVFamNormalizedNorm = qVFamDefaultNorm^(1/d). -/
theorem qVFamNormalizedNorm_eq_defaultNorm_rpow :
    qVFamNormalizedNorm T b = (qVFamDefaultNorm T b) ^
      (1 / (d (qVFamTensorPlace T b) : ℝ)) := by
  rw [qVFamNormalizedNorm_eq_absNorm_rpow T b,
    qVFamDefaultNorm_eq_absNorm_rpow T b]
  simp only [qVFamNormalizedGenerator]
  rw [← Real.rpow_mul (le_of_lt (absNorm_pos (qVFamTensorPlace T b)))]
  congr 1
  ring_nf
end LeanFormal.IUT.XiFPaper.Mzk1QVFamNormBridgeValueActual
end