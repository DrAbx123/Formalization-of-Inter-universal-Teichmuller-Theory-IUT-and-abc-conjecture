import tmp.sheaf.xif.paper.S307QPilotThetaCarrierActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
/-! # S312: qPilot one-factor base change to the Theta rootTensorBlock carrier
The qVFam block is the one-factor p-adic tensor of rootBase = sourceRootField.
Using the one-factor TensorProduct equivalence (subsingletonEquiv), it is
linearly equivalent to rootBase.  Extending scalars rootBase -> RootL and
transporting through the one-factor identification rootTensorBlock ~= RootL
puts the actual qPilot point in the same rootTensorBlock carrier as
ThetaSideObject.  No Qp-tensor comparison, no fake. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual
open LeanFormal.IUT.XiFPaper.S307QPilotThetaCarrierActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- One-factor linear equivalence qVFam block ~= rootBase. -/
noncomputable def qVFamBlockLinearEquiv :
    qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] (rootBase T b) :=
  @PiTensorProduct.subsingletonEquiv Unit ℚ_[qVFamTensorP T b] _
    (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
    (fun _ => inferInstance) (fun _ => inferInstance) inferInstance ()
/-- Actual base-change map qVFam block -> rootTensorBlock (one-factor case). -/
noncomputable def qPilotBlockToRootTensor :
    qVFamTensorBlock T b → rootTensorBlock T b :=
  fun x => (blockLinearEquiv T b).symm
    (algebraMap (rootBase T b) (rootNormedExtension T b)
      (qVFamBlockLinearEquiv T b x))
/-- qPilot image in RootL via algebraMap after the one-factor equivalence. -/
noncomputable def qPilotImageInL : rootNormedExtension T b :=
  algebraMap (rootBase T b) (rootNormedExtension T b)
    (qVFamBlockLinearEquiv T b (qPilotBlockPoint T b))

/-- Compatibility: the RootL image is exactly the algebraMap of the
qVFamBlockLinearEquiv image of the qPilot block point. -/
theorem qPilotImageInL_eq :
    qPilotImageInL T b =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        (qVFamBlockLinearEquiv T b (qPilotBlockPoint T b)) := rfl

/-- The actual qPilot image point in the same rootTensorBlock carrier as Theta. -/
noncomputable def qPilotImageInThetaCarrier : rootTensorBlock T b :=
  qPilotBlockToRootTensor T b (qPilotBlockPoint T b)

/-- Compatibility in the Theta carrier: the image is the one-factor
transport of qPilotImageInL. -/
theorem qPilotImageInThetaCarrier_eq :
    qPilotImageInThetaCarrier T b =
      (blockLinearEquiv T b).symm (qPilotImageInL T b) := rfl
/-- The image set in the Theta carrier. -/
noncomputable def qPilotImageInThetaCarrierSet : Set (rootTensorBlock T b) :=
  {qPilotImageInThetaCarrier T b}
/-- The transported qPilot measure in the Theta carrier. -/
noncomputable def qPilotTransportedThetaMeasure : Measure (rootTensorBlock T b) :=
  Measure.map (qPilotBlockToRootTensor T b)
    (Measure.addHaar : Measure (qVFamTensorBlock T b))
/-- The transported qPilot mu_log in the Theta carrier. -/
noncomputable def qPilotTransportedThetaMuLog : ENNReal :=
  haarLogVolume (qPilotTransportedThetaMeasure T b)
    (qPilotImageInThetaCarrierSet T b)
/-- ThetaSideObject uses exactly this rootTensorBlock carrier. -/
theorem thetaSideObject_carrier_eq : ThetaSideCarrier (T := T) b = rootTensorBlock T b := rfl
end LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
