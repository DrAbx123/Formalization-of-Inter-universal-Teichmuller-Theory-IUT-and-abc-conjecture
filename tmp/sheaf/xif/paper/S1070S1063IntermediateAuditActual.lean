import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual

-- S1070 audit: S1063 is an INTERMEDIATE (c_norm) model, not paper-level.
-- Its coefficient equality paperRootCoefficientFamily = rootHalfCoefficient
-- requires c_norm = order (S734 bridge); it is NOT unconditional.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1070S1063IntermediateAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S734PaperCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- INTERMEDIATE normalized model per-b inequality (c_norm/(2l) hull). -/
theorem s1070NormalizedModelPerB :
    perBQPilotLog (l := l) T b ≤ perBThetaHullLog (l := l) T b :=
  perBQPilotLog_le_perBThetaHullLog (l := l) T b

/-- Exact paper-level coefficient bridge required to upgrade S1063. -/
def S1070S1063PaperLevelBridge : Prop :=
  PaperRootThetaLogBridgeCondition (l := l) T b

theorem s1070PaperCoeff_eq_rootHalf_of_bridge
    (h : S1070S1063PaperLevelBridge (l := l) T b) :
    paperRootCoefficientFamily T b =
      rootHalfCoefficient T b :=
  (rootHalfCoefficient_eq_paperRootCoefficientFamily T b h).symm

/-- S1063 is paper-level only under this exact bridge. -/
def S1070S1063PaperLevelRequired : Prop :=
  S1070S1063PaperLevelBridge (l := l) T b

#check s1070NormalizedModelPerB
#check s1070PaperCoeff_eq_rootHalf_of_bridge
#check S1070S1063PaperLevelRequired

end LeanFormal.IUT.XiFPaper.S1070S1063IntermediateAuditActual

end