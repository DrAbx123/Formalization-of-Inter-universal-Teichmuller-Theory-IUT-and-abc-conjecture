import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Corrected hull-first paper carrier: least lambda*O hull, not closure of
the union of theta regions. -/
noncomputable def paperHullFirstCarrierCorrected : Set (qVFamTensorBlock T b) :=
  paperLeastLambdaOHull (l := l) T b

theorem paperHullFirstCarrierCorrected_eq_lambdaORegion :
    paperHullFirstCarrierCorrected (l := l) T b =
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b) :=
  paperLeastLambdaOHull_eq_minimal (l := l) T b

theorem paperHullFirstCarrierCorrected_subset_oldUnion :
    paperHullFirstCarrierCorrected (l := l) T b ⊆
      paperRootThetaHull (l := l) T b :=
  paperLeastLambdaOHull_subset_old_unionHull (l := l) T b

/-- Exact reverse-gap: corrected least hull equals old union/closure only
when closure adds nothing. -/
def S810LeastEqualsOldUnion : Prop :=
  paperRootThetaHull (l := l) T b =
    paperHullFirstCarrierCorrected (l := l) T b

/-- The qPilot region at the one-label is the lambda*O region at the paper
root coefficient. -/
noncomputable def paperQPilotRegionCorrected : Set (qVFamTensorBlock T b) :=
  paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b)

theorem paperQPilotRegionCorrected_eq_least :
    paperQPilotRegionCorrected (l := l) T b =
      paperHullFirstCarrierCorrected (l := l) T b :=
  (paperLeastLambdaOHull_eq_minimal (l := l) T b).symm

theorem paperQPilotRegionCorrected_subset_least :
    paperQPilotRegionCorrected (l := l) T b ⊆
      paperHullFirstCarrierCorrected (l := l) T b :=
  (paperQPilotRegionCorrected_eq_least (l := l) T b).le

/-- Exact log bridge: normalized log of the least hull needs the actual pure
fractional scaling data at paperRootCoefficientFamily. -/
def S810HullLogDataRequired : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b))

/-- Conditional formula-level log of the corrected least hull. -/
noncomputable def paperHullFirstLogCorrected
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (paperHullFirstCarrierCorrected (l := l) T b)

end LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual

end
