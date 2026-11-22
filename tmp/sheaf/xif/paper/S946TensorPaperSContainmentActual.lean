import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual
import tmp.sheaf.xif.paper.S921RQpilotPaperRegionPositivityActual

/-! # S946: qPilot tensor-packet image containment

`paperTensorS` is exactly the actual union `thetaImageIndUnion`.  The
containment of the qPilot image is therefore exactly the pointwise tensor
image condition; no closure, empty set, or fake map is used.  The qPilot
region and paperTensorS are both nonempty (actual witnesses). -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S946TensorPaperSContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact pointwise tensor-image condition, equivalent to the set containment. -/
def S946TensorPointwiseImageCondition : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotPaperRegion (l := l) T b →
      qVFamToLValued (l := l) T b x ∈ thetaImageIndUnion (l := l) T b

theorem s946QPilotContainment_iff_pointwise :
    qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorS (l := l) T b ↔
      S946TensorPointwiseImageCondition (l := l) T b := by
  unfold qPilotPaperImageInLValued paperTensorS S946TensorPointwiseImageCondition
  constructor
  · rintro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h x hx

/-- Exact minimal preimage form of the containment. -/
def S946TensorPreimageRequired : Prop :=
  qPilotPaperRegion (l := l) T b ⊆ qVFamToLValued (l := l) T b ⁻¹'
    (paperTensorS (l := l) T b)

theorem s946QPilotContainment_iff_preimage :
    qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorS (l := l) T b ↔
      S946TensorPreimageRequired (l := l) T b := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h hx

theorem qPilotPaperImageInLValued_nonempty :
    (qPilotPaperImageInLValued (l := l) T b).Nonempty :=
  ⟨qVFamToLValued (l := l) T b 0,
    ⟨0, s921R_zero_mem (l := l) T b, rfl⟩⟩

end LeanFormal.IUT.XiFPaper.S946TensorPaperSContainmentActual

end
