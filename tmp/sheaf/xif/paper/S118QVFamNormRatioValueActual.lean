import tmp.sheaf.xif.paper.S109QVFamNormValueActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S118: p-adic/valuation form of the qVFamily norm-ratio condition

The exact ratio is a quotient of a p-power and a residue-norm-base power:

  qVFamNormRatio = p ^ (-c_norm)
    / residueNormBase(qVFamTensorPlace) ^ (-exponent(q)).

Using the actual residue-base factor relation

  residueNormBase(place)
    = residueNormBase(comap_Q place) ^ localResidueDegree(place),

this becomes a quotient of p ^ (-c_norm) by
  (rational residue base) ^ (localResidueDegree * (-exponent)).

The equality-to-one condition is therefore the exact weighted valuation relation

  c_norm * log p
    = exponent * localResidueDegree * log(rational residue base).

No assertion that this relation holds; no fake ratio=1.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S118QVFamNormRatioValueActual

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
open LeanFormal.IUT.XiFPaper.S109QVFamNormValueActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual residue-base factor relation at the qVFamily tensor place. -/
theorem qVFamTensorPlace_residueNormBase_eq_lower_pow
    (b : Bad (nativePlaceSelection T)) :
    residueNormBase (qVFamTensorPlace T b) =
      residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)) ^
        localResidueDegree (k := ℚ) (qVFamTensorPlace T b) := by
  exact residueNormBase_eq_lower_pow (k := ℚ) (qVFamTensorPlace T b)

/-- Exact p-power/rational-residue-base expression for the ratio. -/
theorem qVFamNormRatio_eq_p_div_rationalBase
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormRatio T b =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) /
        (residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)) ^
          localResidueDegree (k := ℚ) (qVFamTensorPlace T b)) ^
          (-(qVFamily T b).exponent) := by
  rw [qVFamNormRatio_eq_p_zpow_div_residue_zpow,
    qVFamTensorPlace_residueNormBase_eq_lower_pow]

/-- Exact logarithmic form in p, rational residue base and local residue
degree. -/
theorem log_qVFamNormRatio_eq_localResidueDegree :
    Real.log (qVFamNormRatio T b) =
      ((qVFamily T b).exponent : Real) *
          ((localResidueDegree (k := ℚ) (qVFamTensorPlace T b) : Real) *
            Real.log (residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)))) -
        qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) := by
  rw [log_qVFamNormRatio_eq_valuation,
    qVFamTensorPlace_residueNormBase_eq_lower_pow, Real.log_pow]

/-- The exact weighted valuation condition for ratio one. -/
theorem qVFamNormRatio_eq_one_iff_localResidueDegree :
    qVFamNormRatio T b = 1 ↔
      qVFamNormalizedCoefficient T b *
          Real.log (qVFamTensorP T b : Real) =
        ((qVFamily T b).exponent : Real) *
          ((localResidueDegree (k := ℚ) (qVFamTensorPlace T b) : Real) *
            Real.log (residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)))) := by
  rw [qVFamNormRatio_eq_one_iff_valuation_eq,
    qVFamTensorPlace_residueNormBase_eq_lower_pow, Real.log_pow]

/-- The actual weighted valuation condition, as a named proposition. -/
def QVFamNormRatioWeightedValuationCondition : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real) =
      ((qVFamily T b).exponent : Real) *
        ((localResidueDegree (k := ℚ) (qVFamTensorPlace T b) : Real) *
          Real.log (residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b))))

end LeanFormal.IUT.XiFPaper.S118QVFamNormRatioValueActual

end
