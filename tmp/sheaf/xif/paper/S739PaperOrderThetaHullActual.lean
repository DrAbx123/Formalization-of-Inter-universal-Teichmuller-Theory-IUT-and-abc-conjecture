import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S739PaperOrderThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Paper-order Θ hull log at b: coefficient order(q_v)/(2l), not the
spectral supply coefficient. -/
noncomputable def paperPerBThetaHullLogPaperOrder : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- The paper root coefficient family is exactly order(q_v)/(2l). -/
theorem paperRootCoefficientFamily_eq_order_div
    (i : qVFamTensorV) :
    paperRootCoefficientFamily T b i =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  rfl

/-- Exact minimal bridge: if the normalized generator supply coefficient is
the paper order, then the S716 spectral hull log equals the paper-order hull
log. -/
theorem paperPerBThetaHullLog_eq_paperOrder_of_supply_eq_order
    (h : QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real)) :
    paperPerBThetaHullLog T b = paperPerBThetaHullLogPaperOrder (l := l) T b := by
  unfold paperPerBThetaHullLog perBThetaHullLog paperPerBThetaHullLogPaperOrder
    paperRootThetaHullLog rootNormHull rootHalfCoefficient paperRootCoefficientFamily
  rw [show (fun _ : qVFamTensorV =>
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
          (2 * (l.value : Real))) =
      (fun _ : qVFamTensorV =>
        ((qVFamily T b).order : Real) / (2 * (l.value : Real))) by
    funext i
    rw [h]]

/-- Exact coefficient bridge proposition. -/
def PaperOrderCoefficientBridge : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
    ((qVFamily T b).order : Real)

/-- Conditional passage from the spectral hull log to the paper-order hull
log. -/
theorem paperOrderThetaHullLog_of_bridge
    (h : PaperOrderCoefficientBridge (l := l) T b) :
    paperPerBThetaHullLog T b = paperPerBThetaHullLogPaperOrder (l := l) T b :=
  paperPerBThetaHullLog_eq_paperOrder_of_supply_eq_order (l := l) T b h

end LeanFormal.IUT.XiFPaper.S739PaperOrderThetaHullActual

end
