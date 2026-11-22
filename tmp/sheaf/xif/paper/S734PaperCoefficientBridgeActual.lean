import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S734PaperCoefficientBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

def PaperRootThetaLogBridgeCondition (b : Bad (nativePlaceSelection T)) : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
    ((qVFamily T b).order : Real)

theorem paperRootThetaLogBridgeCondition_iff_correction_zero
    (b : Bad (nativePlaceSelection T)) :
    PaperRootThetaLogBridgeCondition T b ↔ normalizedOrderCorrection T b = 0 := by
  unfold PaperRootThetaLogBridgeCondition normalizedOrderCorrection
  constructor <;> intro h <;> linarith

theorem rootHalfCoefficient_eq_paperRootCoefficientFamily
    (b : Bad (nativePlaceSelection T))
    (h : PaperRootThetaLogBridgeCondition T b) :
    rootHalfCoefficient (l := l) T b = paperRootCoefficientFamily T b := by
  funext i
  unfold rootHalfCoefficient rootNormCoefficient paperRootCoefficientFamily
    qVFamPaperRootCoefficient qVFamNormalizedCoefficientFamily
  rw [h]

theorem paperRootThetaHull_eq_perBThetaHull
    (b : Bad (nativePlaceSelection T))
    (h : PaperRootThetaLogBridgeCondition T b) :
    paperRootThetaHull T b =
      RootHullContainmentInequalityActual.rootThetaHull (l := l)
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) := by
  unfold paperRootThetaHull
  rw [← rootHalfCoefficient_eq_paperRootCoefficientFamily T b h]

theorem paperRootThetaHullLog_eq_perBThetaHullLog
    (b : Bad (nativePlaceSelection T))
    (h : PaperRootThetaLogBridgeCondition T b) :
    paperRootThetaHullLog T b Measure.addHaar = perBThetaHullLog T b := by
  unfold paperRootThetaHullLog perBThetaHullLog
  rw [← rootHalfCoefficient_eq_paperRootCoefficientFamily T b h]

end LeanFormal.IUT.XiFPaper.S734PaperCoefficientBridgeActual
end