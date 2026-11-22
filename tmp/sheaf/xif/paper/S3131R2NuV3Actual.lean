import Mathlib.Algebra.Group.TypeTags.Basic
import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

noncomputable section
open scoped BigOperators WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

namespace LeanFormal.IUT.XiFPaper.S3131R2NuV3Actual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem S3131Nu_qVFamNormalizedGenerator_eq_exponent :
    completionValuationExponent (qVFamTensorPlace T b).maximalIdeal
      (Units.mk0 (qVFamNormalizedGenerator T b)
        (qVFamNormalizedGenerator_ne_zero T b)) = (qVFamily T b).exponent := by
  unfold completionValuationExponent FinitePlaceQCandidate.exponent
  rw [completionValuationAdd_eq_log]
  congr 1
  have hunit : ((Units.mk0 (qVFamNormalizedGenerator T b)
      (qVFamNormalizedGenerator_ne_zero T b) :
        (Completion (qVFamTensorPlace T b))ˣ) :
      Completion (qVFamTensorPlace T b)) = (qVFamily T b).q := by
    rw [Units.val_mk0]
    rfl
  rw [hunit]
  have hq : Valued.v ((qVFamily T b).q :
      Completion (qVFamTensorPlace T b)) ≠ 0 :=
    (qVFamily T b).valuation_ne_zero
  have h1 : WithZero.exp (Multiplicative.toAdd (WithZero.unzero hq)) =
      Valued.v ((qVFamily T b).q : Completion (qVFamTensorPlace T b)) := by
    unfold WithZero.exp
    rw [ofAdd_toAdd, WithZero.coe_unzero hq]
  rw [← h1, WithZero.log_exp]

#check S3131Nu_qVFamNormalizedGenerator_eq_exponent

end LeanFormal.IUT.XiFPaper.S3131R2NuV3Actual
end