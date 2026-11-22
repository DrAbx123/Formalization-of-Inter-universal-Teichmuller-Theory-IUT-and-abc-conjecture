import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S797PaperOrderRegionContainmentActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S801PaperHullLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S797PaperOrderRegionContainmentActual
open LeanFormal.IUT.XiFPaper.S775PaperOrderQPilotCorrectionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The least lambda-O paper hull equals the paper-order qPilot region. -/
theorem paperLeastLambdaOHull_eq_paperQPilotRegion :
    paperLeastLambdaOHull (l := l) T b = paperQPilotRegionPaperOrder T b := by
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  rfl

/-- Measure/log of the least hull. -/
noncomputable def paperHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperLeastLambdaOHull (l := l) T b)

/-- Measure/log of the paper-order qPilot region. -/
noncomputable def paperQPilotRegionLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperQPilotRegionPaperOrder T b)

theorem paperHullLog_eq_paperQPilotRegionLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    paperHullLog T b mu = paperQPilotRegionLog T b mu := by
  unfold paperHullLog paperQPilotRegionLog
  rw [paperLeastLambdaOHull_eq_paperQPilotRegion (l := l) T b]

/-- Exact formula data at the paper root coefficient. -/
structure PaperHullLogFormulaData
    (b : Bad (nativePlaceSelection T)) where
  data : ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)

theorem paperQPilotRegionLog_eq_paperQPilotLog_of_data
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (D : PaperHullLogFormulaData (l := l) T b) :
    paperQPilotRegionLog T b mu = paperQPilotLogPaperOrder (l := l) T b := by
  unfold paperQPilotRegionLog paperQPilotRegionPaperOrder paperQPilotLogPaperOrder
  change arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
      ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
          (paperRootCoefficientFamily T b) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple :
          Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b)) =
    -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
      Real.log (qVFamTensorP T b : Real))
  rw [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu D.data]

/-- Conditional paper-order log inequality from the exact hull-log formula data. -/
theorem paperQPilotLogPaperOrder_le_paperHullLog_of_data
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (D : PaperHullLogFormulaData (l := l) T b) :
    paperQPilotLogPaperOrder (l := l) T b ≤ paperHullLog T b mu := by
  rw [paperHullLog_eq_paperQPilotRegionLog]
  rw [paperQPilotRegionLog_eq_paperQPilotLog_of_data (l := l) T b mu D]

/-- Exact minimal condition for S785's paper-order log inequality. -/
def PaperHullLogFormulaRequired : Prop :=
  Nonempty (PaperHullLogFormulaData (l := l) T b)

end LeanFormal.IUT.XiFPaper.S801PaperHullLogActual

end
