import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S735CoefficientNamespaceAuditActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S734PaperCoefficientBridgeActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The paper-faithful normalized coefficient is the order. -/
theorem actual_coefficient_is_order_rfl :
    QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) := rfl

/-- S734's bridge condition is exactly equality of the spectral generator-supply
coefficient with the paper order coefficient. -/
theorem s734_condition_iff_namespace_equality :
    PaperRootThetaLogBridgeCondition T b ↔
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
        QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b := by
  unfold PaperRootThetaLogBridgeCondition
  rw [actual_coefficient_is_order_rfl]

theorem s734_condition_of_namespace_equality
    (h : QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b) :
    PaperRootThetaLogBridgeCondition T b :=
  (s734_condition_iff_namespace_equality T b).mpr h

/-- The exact gap between the spectral supply coefficient and the paper order. -/
def S735SpectralVsPaperOrderGap : Prop :=
  QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
    ((qVFamily T b).order : Real)

theorem s734_condition_iff_spectral_gap :
    PaperRootThetaLogBridgeCondition T b ↔ S735SpectralVsPaperOrderGap T b :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S735CoefficientNamespaceAuditActualAdapted
end