import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual

/-! # qside rootTensorBlock to RootLValuedCarrier

This file constructs the actual Qp-linear base-change map from the qside
one-factor tensor block over RootL into the RootLValued carrier, and proves
the root theta image lands in rootThetaImageRootL.  It does NOT assert a
linear equivalence: qVFamTensorBlock is a one-factor tensor over the local
completion K0, so RootLValuedCarrier has Qp-dimension dim(K0)*dim(RootL),
while rootTensorBlock has Qp-dimension dim(RootL).  The equivalence would
require dim(K0)=1 and is recorded as an exact missing proposition.

No fake equivalence, no inequality. -/

noncomputable section
open scoped TensorProduct BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QSideRootLValuedBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual base-change linear map from the qside block to the RootL-valued carrier. -/
noncomputable def qsideToRootLValued :
    rootTensorBlock T b →ₗ[ℚ_[(qVFamTensorP T b)]] RootLValuedCarrier T b :=
  ((TensorProduct.mk ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)
    (RootL T b)) (1 : qVFamTensorBlock T b)).comp
    (blockLinearEquiv T b).toLinearMap

/-- The qside root theta image maps to the RootL root theta image. -/
theorem qsideToRootLValued_rootThetaImage (j : SignedLabel l.value) :
    qsideToRootLValued T b (rootTensorThetaImage T b j) =
      rootThetaToRootL (l := l) T b j := by
  unfold qsideToRootLValued rootThetaToRootL
  rw [LinearMap.comp_apply]
  change ((TensorProduct.mk ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)
      (RootL T b)) (1 : qVFamTensorBlock T b))
      ((blockLinearEquiv T b) (rootTensorThetaImage T b j)) =
    TensorProduct.tmul ℚ_[(qVFamTensorP T b)] (1 : qVFamTensorBlock T b)
      (rootNormedThetaValueInL T b j : RootL T b)
  rw [blockLinearEquiv_rootTensorThetaImage T b j]
  rfl

/-- The qside positive-label image is contained in rootThetaImageRootL. -/
theorem qsideToRootLValued_thetaImage_subset :
    qsideToRootLValued T b ''
      (Set.range (rootTensorThetaImage T b)) ⊆
        rootThetaImageRootL (l := l) T b := by
  rintro y ⟨x, ⟨j, rfl⟩, rfl⟩
  exact ⟨j, (qsideToRootLValued_rootThetaImage (l := l) T b j).symm⟩

/-- Exact missing property for a linear equivalence between the two carriers. -/
def QSideRootLValuedEquivRequired : Prop :=
  Nonempty (rootTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] RootLValuedCarrier T b)

end LeanFormal.IUT.XiFPaper.QSideRootLValuedBridgeActual

end
