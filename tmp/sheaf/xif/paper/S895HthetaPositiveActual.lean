import tmp.sheaf.xif.paper.S888HqHthetaActual
import tmp.sheaf.xif.paper.S810LeastHullPaperCarrierActual
import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S895HthetaPositiveActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
open LeanFormal.IUT.XiFPaper.S876CorrectedGlobalTargetActual
open LeanFormal.IUT.XiFPaper.S888HqHthetaActual
open LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual
open LeanFormal.IUT.XiFPaper.S734PaperCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

theorem perBThetaHullLog_eq_leastHullLog_of_bridges
    (b : Bad (nativePlaceSelection T))
    (hcn : qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real))
    (hleast : S810LeastEqualsOldUnion T b) :
    PaperLevelXiFTargetProofActual.perBThetaHullLog T b =
      paperLeastLambdaOHullLog (l := l) T b Measure.addHaar := by
  have hpaper : BadPlacePaperRootThetaHullActual.paperRootThetaHullLog
      (l := l) T b Measure.addHaar =
      paperLeastLambdaOHullLog (l := l) T b Measure.addHaar := by
    unfold BadPlacePaperRootThetaHullActual.paperRootThetaHullLog
    unfold paperLeastLambdaOHullLog
    change arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
      qVFamTensorTuple Measure.addHaar
        (BadPlacePaperRootThetaHullActual.paperRootThetaHull T b) =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple Measure.addHaar
        (paperLeastLambdaOHull (l := l) T b)
    have hset : BadPlacePaperRootThetaHullActual.paperRootThetaHull T b =
        paperLeastLambdaOHull (l := l) T b := by
      simpa [S810LeastEqualsOldUnion, paperHullFirstCarrierCorrected] using hleast
    rw [hset]
  exact (paperRootThetaHullLog_eq_perBThetaHullLog T b hcn).symm.trans hpaper

theorem thetaHullScalar_eq_leastHullWeighted_of_bridges
    (hcn : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real))
    (hleast : ∀ b : Bad (nativePlaceSelection T),
      S810LeastEqualsOldUnion T b) :
    S860GlobalCor312AuditActual.thetaHullScalar T =
      paperLeastHullWeightedLog T := by
  unfold S860GlobalCor312AuditActual.thetaHullScalar
  unfold PaperLevelXiFTargetProofActual.globalThetaHullLog
  unfold paperLeastHullWeightedLog
  apply Finset.sum_congr rfl
  intro b _
  rw [perBThetaHullLog_eq_leastHullLog_of_bridges T b (hcn b) (hleast b)]

/-- S810 old-hull = least-hull, together with c_norm=order at every b, proves
the corrected Htheta (no extra 2l). -/
theorem hthetaNoTwoL_of_bridges
    (hcn : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real))
    (hleast : ∀ b : Bad (nativePlaceSelection T),
      S810LeastEqualsOldUnion T b) :
    HthetaNoTwoL T :=
  thetaHullScalar_eq_leastHullWeighted_of_bridges T hcn hleast

end LeanFormal.IUT.XiFPaper.S895HthetaPositiveActual
end