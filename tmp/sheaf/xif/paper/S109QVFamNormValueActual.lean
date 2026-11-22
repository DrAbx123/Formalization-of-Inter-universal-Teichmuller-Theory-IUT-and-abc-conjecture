import tmp.sheaf.xif.paper.S92NormRatioUnifiedActual
import tmp.sheaf.xif.paper.S64DependentThetaHullActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S109: actual values of the qVFamily default and normalized norms

The default norm is the valuation norm of the actual qVFamily q:

  ||q||_default = residueNormBase(place) ^ (-exponent(q)).

The normalized norm is the spectral norm of the same q:

  ||q||_normalized = p ^ (-c_norm).

Therefore

  qVFamNormRatio
    = p ^ (-c_norm) / residueNormBase ^ (-exponent).

This is the exact value formula.  Equality to one is equivalent to
c_norm * log p = exponent * log residueNormBase, which is recorded as an exact
condition, not asserted.  The correction is then written exactly in terms of
these valuation quantities.  No fake equality.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S109QVFamNormValueActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.XiFPaper.S64DependentThetaHullActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact default-norm value from the actual valuation formula. -/
theorem qVFamDefaultNorm_eq_residueNormBase_zpow
    (b : Bad (nativePlaceSelection T)) :
    qVFamDefaultNorm T b =
      residueNormBase (qVFamTensorPlace T b) ^
        (-(qVFamily T b).exponent) := by
  unfold qVFamDefaultNorm
  exact qNorm_eq_residueNormBase_zpow (qVFamily T b)

/-- Exact normalized-norm value from the spectral normalization identity. -/
theorem qVFamNormalizedNorm_eq_p_zpow_neg_coefficient
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormalizedNorm T b =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) := by
  unfold qVFamNormalizedNorm
  exact qVFamNormalizedGenerator_norm T b

/-- Exact ratio value: quotient of the two p-power expressions. -/
theorem qVFamNormRatio_eq_p_zpow_div_residue_zpow
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormRatio T b =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) /
        residueNormBase (qVFamTensorPlace T b) ^
          (-(qVFamily T b).exponent) := by
  unfold qVFamNormRatio
  rw [qVFamNormalizedNorm_eq_p_zpow_neg_coefficient,
    qVFamDefaultNorm_eq_residueNormBase_zpow]

/-- Exact logarithm of the ratio in valuation/coefficient terms. -/
theorem log_qVFamNormRatio_eq_valuation
    (b : Bad (nativePlaceSelection T)) :
    Real.log (qVFamNormRatio T b) =
      ((qVFamily T b).exponent : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)) -
        qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) := by
  have h := qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio T b
  have hlocal : localLogMagnitude (qVFamily T b) =
      ((qVFamily T b).exponent : Real) *
        Real.log (residueNormBase (qVFamTensorPlace T b)) :=
    localLogMagnitude_eq_exponent_mul_log (qVFamily T b)
  linarith

/-- Exact condition for the norm ratio to be one, in valuation/coefficient
form. -/
theorem qVFamNormRatio_eq_one_iff_valuation_eq
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormRatio T b = 1 ↔
      qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) =
        ((qVFamily T b).exponent : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  constructor
  · intro h
    have hlog := log_qVFamNormRatio_eq_valuation T b
    rw [h, Real.log_one] at hlog
    linarith
  · intro hval
    have hlog := log_qVFamNormRatio_eq_valuation T b
    rw [hval, sub_self] at hlog
    rcases Real.log_eq_zero.mp hlog with h0 | h1 | hneg
    · linarith [qVFamNormRatio_pos T b]
    · exact h1
    · linarith [qVFamNormRatio_pos T b]

/-- The exact correction in valuation/coefficient form. -/
theorem qVFamNormRatioCorrection_eq_valuation :
    qVFamNormRatioCorrection T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (((qVFamily T b).exponent : Real) *
              Real.log (residueNormBase (qVFamTensorPlace T b)) -
            qVFamNormalizedCoefficient T b *
              Real.log (qVFamTensorP T b : Real)) := by
  unfold qVFamNormRatioCorrection
  apply Finset.sum_congr rfl
  intro b _
  rw [log_qVFamNormRatio_eq_valuation]

/-- Exact norm-ratio value condition (nonzero norm ratio). -/
def QVFamNormRatioValueCondition : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real) =
      ((qVFamily T b).exponent : Real) *
        Real.log (residueNormBase (qVFamTensorPlace T b))

end LeanFormal.IUT.XiFPaper.S109QVFamNormValueActual

end
