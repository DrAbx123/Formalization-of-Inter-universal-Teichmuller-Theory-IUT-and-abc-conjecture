import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
/-! # Paper root-theta coefficient order/(2l): hull object and exact formula gap
The paper coefficient is qVFamPaperRootCoefficient = order(qVFamily)/(2l).  The
root theta hull is rebuilt with this coefficient.  Its normalized-log formula
requires exact ArithmeticTuplePureFractionalScalingData at that coefficient and
the hull equality to the minimal fractional-lattice scaled region; the exact gap
is recorded and not asserted.  With the gap, the paper Theta side is expressed
directly by the paper coefficient, without the c_norm bridge.  No inequality. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotBaseChange
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
/-- The paper root theta coefficient family at b: order(qVFamily)/(2l). -/
noncomputable def paperRootCoefficientFamily
    (b : Bad (nativePlaceSelection T)) : qVFamTensorV → Real :=
  fun _ => qVFamPaperRootCoefficient T b
/-- The actual paper-coefficient root theta hull at b. -/
noncomputable def paperRootThetaHull
    (b : Bad (nativePlaceSelection T)) : Set (qVFamTensorBlock T b) :=
  rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b)
/-- The paper-coefficient normalized root hull log at b. -/
noncomputable def paperRootThetaHullLog
    (b : Bad (nativePlaceSelection T)) (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] : Real :=
  rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (paperRootCoefficientFamily T b)
/-- The paper-coefficient formula scalar at b. -/
noncomputable def paperRootThetaFormulaLog
    (b : Bad (nativePlaceSelection T)) : Real :=
  -((∑ _ : qVFamTensorV, qVFamPaperRootCoefficient T b) *
    Real.log (qVFamTensorP T b : Real))
/-- Exact minimal paper-hull gap at b. -/
structure PaperRootHullFormulaGap
    (b : Bad (nativePlaceSelection T)) where
  data : ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)
  hull_eq : paperRootThetaHull T b =
    ((arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b) *
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b))
/-- Conditional formula from the exact paper-hull gap. -/
theorem paperRootThetaHullLog_eq_formula_of_gap
    (b : Bad (nativePlaceSelection T)) (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] (G : PaperRootHullFormulaGap T b) :
    paperRootThetaHullLog T b mu = paperRootThetaFormulaLog T b := by
  unfold paperRootThetaHullLog paperRootThetaFormulaLog paperRootCoefficientFamily
    rootThetaHullLog
  change arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (paperRootThetaHull T b) = paperRootThetaFormulaLog T b
  rw [G.hull_eq]
  rw [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (c := paperRootCoefficientFamily T b) G.data]
  rfl
/-- Weighted paper-coefficient Theta hull scalar. -/
noncomputable def paperRootThetaHullScalar : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperRootThetaHullLog T b Measure.addHaar
/-- Weighted paper-coefficient formula scalar. -/
noncomputable def paperRootThetaFormulaScalar : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperRootThetaFormulaLog T b
/-- Global conditional equality from the exact hull gap at every bad place. -/
theorem paperRootThetaHullScalar_eq_formula_of_gap
    (G : ∀ b : Bad (nativePlaceSelection T), PaperRootHullFormulaGap T b) :
    paperRootThetaHullScalar T = paperRootThetaFormulaScalar T := by
  unfold paperRootThetaHullScalar paperRootThetaFormulaScalar
  apply Finset.sum_congr rfl
  intro b _
  rw [paperRootThetaHullLog_eq_formula_of_gap T b Measure.addHaar (G b)]
end LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
