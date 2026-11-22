import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual

-- S775: corrected paper target with qPilot coefficient order/(2l).
-- The S716/S706 qPilot uses c_norm=order and is 2l times too large.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S775PaperOrderQPilotCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S734PaperCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Corrected paper qPilot coefficient: order/(2l). -/
noncomputable def paperQPilotCoefficientPaperOrder : qVFamTensorV → Real :=
  fun _ : qVFamTensorV => ((qVFamily T b).order : Real) / (2 * (l.value : Real))

/-- Corrected paper qPilot log: - sum_b order/(2l) * log p. -/
noncomputable def paperQPilotLogPaperOrder : Real :=
  -((∑ _ : qVFamTensorV, paperQPilotCoefficientPaperOrder (l := l) T b ()) *
    Real.log (qVFamTensorP T b : Real))

/-- Actual paper-order Theta hull log (coefficient order/(2l)). -/
noncomputable def paperThetaHullLogPaperOrder : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- Corrected paper target, using paper-order qPilot. -/
def PaperTargetPaperOrder : Prop :=
  paperQPilotLogPaperOrder (l := l) T b ≤ paperThetaHullLogPaperOrder (l := l) T b

/-- Exact 2l factor gap of the current S716/S706 qPilot target. -/
def PerBQPilotTwoLFactorGap : Prop :=
  perBQPilotLog T b = (2 * (l.value : Real)) * paperQPilotLogPaperOrder (l := l) T b

/-- Exact theta-side bridge: spectral root hull log = paper-order hull log. -/
def PaperThetaHullBridge : Prop :=
  perBThetaHullLog T b = paperThetaHullLogPaperOrder (l := l) T b

def PaperThetaHullBridgeRequired : Prop :=
  PaperThetaHullBridge (l := l) T b

/-- Coefficient bridge condition used by S734/S739. -/
def PaperOrderCoefficientBridge : Prop :=
  qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real)

theorem PaperOrderCoefficientBridge_iff_correction_zero :
    PaperOrderCoefficientBridge (l := l) T b ↔ normalizedOrderCorrection T b = 0 :=
  paperRootThetaLogBridgeCondition_iff_correction_zero (l := l) T b

#check paperQPilotLogPaperOrder
#check paperThetaHullLogPaperOrder
#check PaperTargetPaperOrder
#check PerBQPilotTwoLFactorGap
#check PaperThetaHullBridge

end LeanFormal.IUT.XiFPaper.S775PaperOrderQPilotCorrectionActual

end