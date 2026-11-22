import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S926GlobalIntegrationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b)

/-- Per-b R-side log: model hull. -/
noncomputable def perBModelLog (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple (mu b)
    (modelHull (l := l) T b)

/-- Per-b S-side log: paper multiradial hull with supplied Ind images. -/
noncomputable def perBPaperSLog (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple (mu b)
    (paperSHull (l := l) T b (D b))

/-- Per-b inequality from S922, under the geometric boundedness side condition. -/
theorem perB_le_perB
    (hD : ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (D b)) :
    ∀ b : Bad (nativePlaceSelection T),
      perBModelLog (l := l) T mu b ≤ perBPaperSLog (l := l) T mu D b := by
  intro b
  exact modelHullLog_le_paperSHullLog (l := l) T b (mu b) (D b) (hD b)

/-- Weighted global R-side log. -/
noncomputable def globalModelLog : Real :=
  S919GlobalWeightedInequalityActual.weightedPaperV (l := l) T
    (perBModelLog (l := l) T mu)

/-- Weighted global S-side log. -/
noncomputable def globalPaperSLog : Real :=
  S919GlobalWeightedInequalityActual.weightedPaperV (l := l) T
    (perBPaperSLog (l := l) T mu D)

/-- Global weighted inequality from S922 + S919 weighted monotonicity. -/
theorem globalModelLog_le_globalPaperSLog
    (hD : ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (D b)) :
    globalModelLog (l := l) T mu ≤
      globalPaperSLog (l := l) T mu D := by
  unfold globalModelLog globalPaperSLog
  exact S919GlobalWeightedInequalityActual.weightedPaperV_mono (l := l) T
    (perB_le_perB (l := l) T mu D hD)

/-- Exact side conditions of S926. -/
def S926SideConditions : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    S922IndImageBounded (l := l) T b (D b)

/-- Alternative exact side condition: finiteness of each paper S hull. -/
def S926FinitenessSideConditions : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    S922PaperSHullFinite (l := l) T b (mu b) (D b)

theorem globalModelLog_le_globalPaperSLog_of_finite
    (hfin : S926FinitenessSideConditions (l := l) T mu D) :
    globalModelLog (l := l) T mu ≤
      globalPaperSLog (l := l) T mu D := by
  unfold globalModelLog globalPaperSLog
  apply S919GlobalWeightedInequalityActual.weightedPaperV_mono (l := l) T
  intro b
  exact modelHullLog_le_paperSHullLog_of_finite (l := l) T b (mu b) (D b) (hfin b)

end LeanFormal.IUT.XiFPaper.S926GlobalIntegrationActual
end