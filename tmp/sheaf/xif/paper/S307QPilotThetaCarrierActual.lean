import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import tmp.sheaf.xif.paper.QSideRootLValuedBridgeActual
import tmp.sheaf.xif.paper.PaperThetaSideObjectActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
/-! # S307: qPilot image in the RootL carrier and exact Theta-carrier gap
qVFamToRootL maps qVFamTensorBlock to the RootL-valued carrier
qVFamTensorBlock ⊗ RootL, NOT to rootTensorBlock (the ThetaSideObject carrier).
This file constructs the actual qPilot point/image/measure in the RootL-valued
carrier and records the exact carrier-alignment gap with ThetaSideObject.  No
fake equivalence or inequality. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S307QPilotThetaCarrierActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.QSideRootLValuedBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

instance qVFamTensorBlockMeasurable : MeasurableSpace (qVFamTensorBlock T b) :=
  borel (qVFamTensorBlock T b)

instance qVFamTensorBlockBorel : BorelSpace (qVFamTensorBlock T b) := ⟨rfl⟩

/-- Actual qPilot point in the qVFam one-factor block. -/
noncomputable def qPilotBlockPoint : qVFamTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
    (fun _ => ((qVFamily T b).q : CommonPrimeCompletion
      (qVFamTensorPlaces T b () ())))
/-- Actual qPilot image point in the RootL-valued carrier. -/
noncomputable def qPilotRootLImagePoint : RootLValuedCarrier T b :=
  qVFamToRootL T b (qPilotBlockPoint T b)
/-- Actual qPilot image set in the RootL-valued carrier. -/
noncomputable def qPilotRootLImageSet : Set (RootLValuedCarrier T b) :=
  {qPilotRootLImagePoint T b}
/-- ThetaSideObject is on rootTensorBlock, by definition. -/
abbrev ThetaSideCarrier : Type := rootTensorBlock T b
/-- Exact missing carrier alignment: a Qp-linear equivalence between the
RootL-valued qPilot carrier and the ThetaSideObject rootTensorBlock carrier. -/
def QPilotThetaCarrierAlignmentGap : Prop :=
  Nonempty (RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
    rootTensorBlock T b)
/-- The alignment is not asserted. -/
def QPilotThetaCarrierAlignmentGapRequired : Prop :=
  QPilotThetaCarrierAlignmentGap T b
end LeanFormal.IUT.XiFPaper.S307QPilotThetaCarrierActual
