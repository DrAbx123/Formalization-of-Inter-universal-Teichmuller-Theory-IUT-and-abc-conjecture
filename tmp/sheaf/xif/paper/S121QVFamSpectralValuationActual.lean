import tmp.sheaf.xif.paper.S120QVFamWeightedValuationConditionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual

/-!
# S121: spectral coefficient versus exponent * rationalDegree

The actual spectral coefficient is defined through the normalized norm, not by
the valuation exponent.  Under the rational-prime log obstruction we derive the
exact formula

  c_norm = exponent * rationalDegree - log(qVFamNormRatio)/log p,

hence

  c_norm = exponent * rationalDegree <-> qVFamNormRatio = 1.

The last equality is exactly the unproved norm-instance equality.  We also
record the separate order-coefficient definition and show that it cannot equal
exponent * rationalDegree unless the rational residue degree is one; this is a
real counterexample for that separate definition, not for the spectral one.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S121QVFamSpectralValuationActual

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
open LeanFormal.IUT.XiFPaper.S118QVFamNormRatioValueActual
open LeanFormal.IUT.XiFPaper.S109QVFamNormValueActual
open LeanFormal.IUT.XiFPaper.S92NormRatioUnifiedActual
open LeanFormal.IUT.XiFPaper.S120QVFamWeightedValuationConditionActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact formula: under the rational-prime log obstruction, the spectral
coefficient is exponent * rationalDegree minus log(norm ratio)/log p. -/
theorem qVFamNormalizedCoefficient_eq_exponent_mul_degree_sub_logRatio
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    qVFamNormalizedCoefficient T b =
      ((qVFamily T b).exponent : Real) *
          qVFamTensorRationalDegree T b -
        Real.log (qVFamNormRatio T b) /
          Real.log (qVFamTensorP T b : Real) := by
  have hbase :=
    (qVFamTensorRationalPrimeLogObstruction_iff_baseLog_eq T b).mp hobs
  unfold qVFamTensorRationalBaseNorm at hbase
  have hdeg : (localResidueDegree (k := ℚ) (qVFamTensorPlace T b) : Real) =
      qVFamTensorRationalDegree T b := rfl
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  have h := log_qVFamNormRatio_eq_localResidueDegree (T := T) (b := b)
  rw [← hbase, hdeg] at h
  rw [eq_sub_iff_add_eq, div_eq_mul_inv]
  field_simp [hlog]
  nlinarith [h]

/-- Equality to exponent * rationalDegree is exactly the norm-ratio equality. -/
theorem qVFamNormalizedCoefficient_eq_exponent_mul_degree_iff
    (hobs : qVFamTensorRationalPrimeLogObstruction T b) :
    qVFamNormalizedCoefficient T b =
        ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b ↔
      qVFamNormRatio T b = 1 := by
  have hformula :=
    qVFamNormalizedCoefficient_eq_exponent_mul_degree_sub_logRatio T hobs
  constructor
  · intro h
    have hlog : Real.log (qVFamNormRatio T b) = 0 := by
      have hdiv : Real.log (qVFamNormRatio T b) /
          Real.log (qVFamTensorP T b : Real) = 0 := by
        linarith
      have hlogp : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one
        · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
        · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
      exact (div_eq_zero_iff.mp hdiv).resolve_right hlogp
    rcases Real.log_eq_zero.mp hlog with h0 | h1 | hneg
    · exfalso
      exact (qVFamNormRatio_pos T b).ne' h0
    · exact h1
    · exfalso
      nlinarith [qVFamNormRatio_pos T b, hneg]
  · intro h
    rw [hformula, h, Real.log_one, zero_div, sub_zero]

/-- Failure criterion: a non-one norm ratio forces the spectral coefficient to
differ from exponent * rationalDegree. -/
theorem qVFamNormalizedCoefficient_ne_exponent_mul_degree_of_ratio_ne_one
    (hobs : qVFamTensorRationalPrimeLogObstruction T b)
    (hratio : qVFamNormRatio T b ≠ 1) :
    qVFamNormalizedCoefficient T b ≠
      ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b := by
  intro h
  exact hratio ((qVFamNormalizedCoefficient_eq_exponent_mul_degree_iff
    T hobs).mp h)

/-- The separate order-coefficient definition is literally the order. -/
theorem orderCoefficient_eq_order
    (b : Bad (nativePlaceSelection T)) :
    LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) :=
  rfl

/-- For the separate order-coefficient, the formula c = order * rationalDegree
fails whenever rationalDegree != 1. -/
theorem orderCoefficient_ne_order_mul_degree_of_degree_ne_one
    (hdeg : qVFamTensorRationalDegree T b ≠ 1) :
    LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b ≠
      ((qVFamily T b).order : Real) * qVFamTensorRationalDegree T b := by
  rw [orderCoefficient_eq_order T b]
  intro h
  have horder_pos : 0 < ((qVFamily T b).order : Real) := by
    exact_mod_cast (FinitePlaceQCandidate.order_pos (qVFamily T b))
  have hmul : ((qVFamily T b).order : Real) *
      qVFamTensorRationalDegree T b = ((qVFamily T b).order : Real) := by
    linarith
  have hdeg_one : ((qVFamTensorRationalDegree T b : Real) = 1) :=
    mul_left_cancel₀ (ne_of_gt horder_pos) (by simpa [mul_comm] using hmul)
  exact hdeg (by exact_mod_cast hdeg_one)

end LeanFormal.IUT.XiFPaper.S121QVFamSpectralValuationActual

end
