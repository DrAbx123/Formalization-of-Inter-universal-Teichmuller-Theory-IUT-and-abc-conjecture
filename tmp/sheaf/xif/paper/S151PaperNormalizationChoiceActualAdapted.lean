import tmp.sheaf.xif.paper.S145NormRatioCorrectionZeroActual

/-!
# S151: normalization choice for the paper q-pilot coefficient

The spectral coefficient c_norm is NOT the paper-normalized coefficient.  The
actual paper-normalized coefficient is

  paperNormalizedCoefficient
    = order * log(residueNormBase F-place) / log p.

Under the rational-prime log obstruction it absorbs the rational degree:

  paperNormalizedCoefficient = order * rationalDegree = exponent * rationalDegree.

The current spectral coefficient instead satisfies

  c_norm = paperNormalizedCoefficient - log(qVFamNormRatio)/log p,

so the spectral gap is exactly the paper-coefficient gap times log p.  Therefore
the needed normalization is the paperNormalizedCoefficient (or equivalently a
normalized norm whose coefficient absorbs the rational degree), not the
spectral normalized coefficient.  Choosing it makes the paper-normalized gap
zero.  This is a normalization choice, not a proof that the spectral coefficient
was already paper-normalized.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S151PaperNormalizationChoiceActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionControlActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignActual
open LeanFormal.IUT.XiFPaper.BadPlaceCorrectionSignAttackActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedTargetBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullScalarBridgeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.S121QVFamSpectralValuationActual
open LeanFormal.IUT.XiFPaper.S134ActualPaperTargetCorrectionActual
open LeanFormal.IUT.XiFPaper.S137PaperTargetCorrectionStatusActual
open LeanFormal.IUT.XiFPaper.S145NormRatioCorrectionZeroActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The paper-normalized coefficient absorbs the rational degree under the
actual rational-prime log obstruction. -/
theorem paperNormalizedCoefficient_eq_order_mul_rationalDegree
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    paperNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) *
        qVFamTensorRationalDegree T b := by
  have hbase :=
    (qVFamTensorRationalPrimeLogObstruction_iff_baseLog_eq T b).mp hobs
  unfold qVFamTensorRationalBaseNorm at hbase
  have hlog_res := log_qVFamTensorPlace_eq_rationalDegree_mul_baseLog T b
  unfold qVFamTensorRationalBaseNorm at hlog_res
  have hlogp : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  unfold paperNormalizedCoefficient
  rw [hlog_res, hbase]
  field_simp [hlogp]
  ring

/-- The paper-normalized coefficient also equals exponent * rationalDegree. -/
theorem paperNormalizedCoefficient_eq_exponent_mul_rationalDegree
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    paperNormalizedCoefficient T b =
      ((qVFamily T b).exponent : Real) *
        qVFamTensorRationalDegree T b := by
  rw [paperNormalizedCoefficient_eq_order_mul_rationalDegree T hobs,
    qOrder_cast_eq_exponent_cast (qVFamily T b)]

/-- Paper-normalized spectral gap: exactly zero under the obstruction. -/
noncomputable def paperNormalizedSpectralGap
    (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b -
    paperNormalizedCoefficient T b

/-- Choosing the paper-normalized coefficient makes the gap zero. -/
theorem paperNormalizedSpectralGap_eq_zero
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    paperNormalizedSpectralGap T b = 0 := by
  unfold paperNormalizedSpectralGap
  rw [paperNormalizedCoefficient_eq_exponent_mul_rationalDegree T hobs]
  ring

/-- Current spectral gap equals the paper-normalized coefficient gap times
log p. -/
theorem normRatioSpectralGap_eq_paperCoefficient_gap
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    normRatioSpectralGap T b =
      (paperNormalizedCoefficient T b -
          qVFamNormalizedCoefficient T b) *
        Real.log (qVFamTensorP T b : Real) := by
  have hpaper :=
    paperNormalizedCoefficient_eq_exponent_mul_rationalDegree T hobs
  unfold normRatioSpectralGap
  rw [hpaper]
  ring

/-- Actual nonzero gap criterion: if the paper-normalized coefficient differs
from the spectral coefficient, the spectral gap is nonzero. -/
theorem normRatioSpectralGap_ne_zero_of_paperCoefficient_ne_cNorm
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hne : paperNormalizedCoefficient T b ≠ qVFamNormalizedCoefficient T b) :
    normRatioSpectralGap T b ≠ 0 := by
  have hlogp : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  rw [normRatioSpectralGap_eq_paperCoefficient_gap T hobs]
  exact mul_ne_zero (sub_ne_zero.mpr hne) hlogp

/-- The needed normalization: paperNormalizedCoefficient, not the spectral
normalized coefficient.  This definition is the paper coefficient as an
explicit normalization choice. -/
noncomputable def paperNormalizedCoefficientChoice
    (b : Bad (nativePlaceSelection T)) : Real :=
  paperNormalizedCoefficient T b

/-- With the paper normalization choice, the gap is zero under the obstruction. -/
theorem paperNormalizedCoefficientChoice_gap_zero
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b -
        paperNormalizedCoefficientChoice T b = 0 := by
  unfold paperNormalizedCoefficientChoice
  rw [paperNormalizedCoefficient_eq_exponent_mul_rationalDegree T hobs]
  ring

end LeanFormal.IUT.XiFPaper.S151PaperNormalizationChoiceActualAdapted

end
