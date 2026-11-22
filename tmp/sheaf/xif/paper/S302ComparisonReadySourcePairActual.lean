import tmp.sheaf.xif.paper.S301GlobalThetaHullLogActual
import tmp.sheaf.xif.paper.S232QPilotHaarTransportActual

/-!
# S302: comparison-ready Theta/qPilot source pair

This file puts the actual Theta-side weighted theta-hull log object from S301
and the actual qPilot-side object with classical log / multiradial image /
transported Haar and mu_log from S232 into one pair.  The shared indexing is the
same bad-place family, and the shared weights are nativeBadLocalWeight.

Only the pair object and field compatibility formulas are constructed.  No
inequality and no comparison result is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S302ComparisonReadySourcePairActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S301GlobalThetaHullLogActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S178QPilotObjectFullActual
open LeanFormal.IUT.XiFPaper.S232QPilotHaarTransportActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry T b))]

/-- Actual Theta-side object used in the pair. -/
noncomputable def thetaSideOfPair : GlobalSourceThetaHullLogObject T :=
  globalSourceThetaHullLogObject T

/-- Actual qPilot-side object used in the pair. -/
noncomputable def qPilotSideOfPair : QPilotHaarTransportActual T :=
  qPilotHaarTransportActual T

/-- qPilot classical log is the same weighted order*log p sum used on the
Theta-side indexing. -/
theorem qPilotClassicalLog_eq_weighted_order_sum :
    QPilotClassicalLog T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (((qVFamily T b).order : Real) *
            Real.log (qVFamTensorP T b : Real)) :=
  rfl

/-- Comparison-ready source pair. -/
structure ComparisonReadySourcePair where
  badIndex : Type
  badIndex_eq : badIndex = Bad (nativePlaceSelection T)
  theta : GlobalSourceThetaHullLogObject T
  theta_eq : theta = thetaSideOfPair T
  thetaWeightedNormalizedLog : Real
  thetaWeightedNormalizedLog_eq :
    thetaWeightedNormalizedLog = theta.weightedNormalizedLog
  thetaWeightedNormalizedLog_formula :
    thetaWeightedNormalizedLog = globalSourceHullNormalizedLog T
  thetaRootCoefficient : Real
  thetaRootCoefficient_eq :
    thetaRootCoefficient = theta.weightedRootCoefficient
  thetaRootCoefficient_formula :
    thetaRootCoefficient = globalSourceHullS13RootCoefficient T
  qPilot : QPilotHaarTransportActual T
  qPilot_eq : qPilot = qPilotSideOfPair T
  qPilotClassicalLog : Real
  qPilotClassicalLog_eq : qPilotClassicalLog = qPilot.classicalLog
  qPilotClassicalLog_formula :
    qPilotClassicalLog = QPilotClassicalLog T
  qPilotImagePoint : QPilotMultiradialCarrier T
  qPilotImagePoint_eq : qPilotImagePoint = qPilot.imagePoint
  qPilotImageHaar : Measure (QPilotMultiradialCarrier T)
  qPilotImageHaar_eq : qPilotImageHaar = qPilot.transportedImageHaar
  qPilotImageMuLog : ENNReal
  qPilotImageMuLog_eq : qPilotImageMuLog = qPilot.transportedImageMuLog
  sharedWeight_formula : qPilotClassicalLog =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        (((qVFamily T b).order : Real) *
          Real.log (qVFamTensorP T b : Real))

/-- Actual comparison-ready source pair constructor. -/
noncomputable def comparisonReadySourcePair : ComparisonReadySourcePair T where
  badIndex := Bad (nativePlaceSelection T)
  badIndex_eq := rfl
  theta := thetaSideOfPair T
  theta_eq := rfl
  thetaWeightedNormalizedLog := (thetaSideOfPair T).weightedNormalizedLog
  thetaWeightedNormalizedLog_eq := rfl
  thetaWeightedNormalizedLog_formula :=
    (thetaSideOfPair T).weightedNormalizedLog_eq
  thetaRootCoefficient := (thetaSideOfPair T).weightedRootCoefficient
  thetaRootCoefficient_eq := rfl
  thetaRootCoefficient_formula :=
    (thetaSideOfPair T).weightedRootCoefficient_eq
  qPilot := qPilotSideOfPair T
  qPilot_eq := rfl
  qPilotClassicalLog := (qPilotSideOfPair T).classicalLog
  qPilotClassicalLog_eq := rfl
  qPilotClassicalLog_formula := (qPilotSideOfPair T).classicalLog_eq
  qPilotImagePoint := (qPilotSideOfPair T).imagePoint
  qPilotImagePoint_eq := rfl
  qPilotImageHaar := (qPilotSideOfPair T).transportedImageHaar
  qPilotImageHaar_eq := rfl
  qPilotImageMuLog := (qPilotSideOfPair T).transportedImageMuLog
  qPilotImageMuLog_eq := rfl
  sharedWeight_formula := qPilotClassicalLog_eq_weighted_order_sum T

/-- Field compatibility: both sides use the same bad index and the same native
weights; the qPilot image is the S172 image point. -/
theorem comparisonReadySourcePair_compatibility :
    (comparisonReadySourcePair T).badIndex = Bad (nativePlaceSelection T) ∧
      (comparisonReadySourcePair T).qPilotImagePoint =
        QPilotMultiradialImagePoint (l := l) T ∧
      (comparisonReadySourcePair T).thetaWeightedNormalizedLog =
        globalSourceHullNormalizedLog T := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (comparisonReadySourcePair T).qPilotImagePoint_eq.trans
      (comparisonReadySourcePair T).qPilot.imagePoint_eq
  · exact (comparisonReadySourcePair T).thetaWeightedNormalizedLog_formula

end LeanFormal.IUT.XiFPaper.S302ComparisonReadySourcePairActual

end
