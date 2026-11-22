import tmp.sheaf.xif.paper.S118QVFamNormRatioValueActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual

/-!
# S120: weighted valuation condition for the qVFamily norm ratio

The actual spectral coefficient is defined by

  c_norm = -logb_p ||q||_normalized,

not by the exponent/degree formula.  It is therefore not equal to the order or
to exponent * degree by definition.  This file records the exact reduction:

under the actual rational-prime log obstruction (log p = log rational base),

  QVFamNormRatioWeightedValuationCondition
    <-> c_norm = exponent * rationalDegree
    <-> c_norm = order * rationalDegree.

If one uses the separate order-coefficient definition c = order, the condition
fails whenever the rational residue degree is not one.  No spectral equality is
assumed and no ratio=1 is fabricated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S120QVFamWeightedValuationConditionActual

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
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual definitional formula of the spectral coefficient. -/
theorem qVFamNormalizedCoefficient_eq_neg_logb_norm
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormalizedCoefficient T b =
      -Real.logb (qVFamTensorP T b : Real)
        ‖qVFamNormalizedGenerator T b‖ :=
  rfl

/-- Under the actual rational-prime log obstruction, the weighted valuation
condition is exactly c_norm = exponent * rationalDegree. -/
theorem weightedValuationCondition_iff_coefficient_eq_exponent_mul_degree
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b) :
    QVFamNormRatioWeightedValuationCondition T ↔
      ∀ b : Bad (nativePlaceSelection T),
        qVFamNormalizedCoefficient T b =
          ((qVFamily T b).exponent : Real) *
            qVFamTensorRationalDegree T b := by
  constructor
  · intro h b
    have hb := h b
    have hbase :=
      (qVFamTensorRationalPrimeLogObstruction_iff_baseLog_eq T b).mp (hobs b)
    unfold qVFamTensorRationalBaseNorm at hbase
    have hdeg : (localResidueDegree (k := ℚ) (qVFamTensorPlace T b) : Real) =
        qVFamTensorRationalDegree T b := rfl
    have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
      · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
    rw [← hbase, hdeg] at hb
    apply mul_right_cancel₀ hlog
    calc
      qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real)
          = ((qVFamily T b).exponent : Real) *
              (qVFamTensorRationalDegree T b *
                Real.log (qVFamTensorP T b : Real)) := hb
      _ = (((qVFamily T b).exponent : Real) *
            qVFamTensorRationalDegree T b) *
          Real.log (qVFamTensorP T b : Real) := by ring
  · intro h b
    have hbase :=
      (qVFamTensorRationalPrimeLogObstruction_iff_baseLog_eq T b).mp (hobs b)
    unfold qVFamTensorRationalBaseNorm at hbase
    have hdeg : (localResidueDegree (k := ℚ) (qVFamTensorPlace T b) : Real) =
        qVFamTensorRationalDegree T b := rfl
    rw [← hbase, hdeg]
    rw [h b]
    ring

/-- Conditional actual reduction: if the spectral coefficient is exactly
exponent * rationalDegree, the weighted valuation condition holds. -/
theorem weightedValuationCondition_of_coefficient_eq_exponent_mul_degree
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b)
    (hc : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedCoefficient T b =
        ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b) :
    QVFamNormRatioWeightedValuationCondition T :=
  (weightedValuationCondition_iff_coefficient_eq_exponent_mul_degree T hobs).mpr hc

/-- Failure criterion: if at some bad place the spectral coefficient differs
from exponent * rationalDegree, the weighted valuation condition fails. -/
theorem not_weightedValuationCondition_of_coefficient_ne_exponent_mul_degree
    (hobs : ∀ b : Bad (nativePlaceSelection T),
      qVFamTensorRationalPrimeLogObstruction T b)
    (hb : ∃ b : Bad (nativePlaceSelection T),
      qVFamNormalizedCoefficient T b ≠
        ((qVFamily T b).exponent : Real) * qVFamTensorRationalDegree T b) :
    ¬ QVFamNormRatioWeightedValuationCondition T := by
  intro h
  rcases hb with ⟨b, hbne⟩
  exact hbne ((weightedValuationCondition_iff_coefficient_eq_exponent_mul_degree
    T hobs).mp h b)

end LeanFormal.IUT.XiFPaper.S120QVFamWeightedValuationConditionActual

end
