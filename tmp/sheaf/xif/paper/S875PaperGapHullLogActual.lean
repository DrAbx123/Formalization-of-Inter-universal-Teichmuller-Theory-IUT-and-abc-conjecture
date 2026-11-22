import tmp.sheaf.xif.paper.S822PadicDetHullActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S875PaperGapHullLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S822PadicDetHullActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact single field: completion scaling data at cRoot = order/(2l). -/
def S875HullLogDatum : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b))

/-- From the exact scaling data, S822's lambda-O hull formula gives the paper
root intrinsic log -order/(2l) * log p. -/
theorem paperLeastLambdaOHullLog_eq_neg_order_div
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperLeastLambdaOHullLog (l := l) T b Measure.addHaar =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold paperLeastLambdaOHullLog
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  change arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
      Measure.addHaar (lambdaOSet (l := l) T b (paperRootCoefficientFamily T b)) = _
  rw [normalizedLogVolume_lambdaOSet (l := l) T b Measure.addHaar data]
  unfold hullLogFunctional
  congr 1
  simp [paperRootCoefficientFamily, qVFamPaperRootCoefficient, Finset.sum_const,
    Finset.card_univ, qVFamTensorV, nsmul_eq_mul]

/-- The S873 hull-log equality field, conditional on the exact single datum. -/
theorem s875_hullLog_eq_root_of_data
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperLeastLambdaOHullLog (l := l) T b Measure.addHaar =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) :=
  paperLeastLambdaOHullLog_eq_neg_order_div (l := l) T b data

/-- Exact minimal proposition. -/
theorem s875HullLogDatum_iff :
    S875HullLogDatum (l := l) T b ↔
      Nonempty (ArithmeticTuplePureFractionalScalingData
        (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S875PaperGapHullLogActual

end
