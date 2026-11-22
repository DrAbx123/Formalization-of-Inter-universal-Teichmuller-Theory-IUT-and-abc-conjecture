import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual
import Mathlib.LinearAlgebra.TensorProduct.Associator

-- S311: rebuild the L-valued carrier as base extension over K0 = rootBase,
-- not ⊗_Qp.  qVFamTensorBlock is one-factor ≅ rootBase, so the carrier is
-- K0 ⊗_{K0} RootL ≅ RootL; it is linearly equivalent to rootTensorBlock by
-- blockLinearEquiv.  The old Qp-tensor carrier is not used here.

noncomputable section
open scoped TensorProduct BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S311RootLValuedK0CarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperThetaSideObjectActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Correct base extension over K0 = rootBase.
abbrev RootLValuedCarrierK0 : Type :=
  TensorProduct (rootBase T b) (rootBase T b) (rootL T b)

noncomputable def carrierK0EquivRootL :
    RootLValuedCarrierK0 T b ≃ₗ[rootBase T b] (rootL T b) :=
  TensorProduct.lid (rootBase T b) (rootL T b)

noncomputable def carrierK0EquivRootTensor :
    RootLValuedCarrierK0 T b ≃ₗ[ℚ_[qVFamTensorP T b]] rootTensorBlock T b :=
  (carrierK0EquivRootL T b).restrictScalars ℚ_[qVFamTensorP T b] |>.trans
    (blockLinearEquiv T b).symm

noncomputable def qVFamToCarrierK0 :
    qVFamTensorBlock T b → RootLValuedCarrierK0 T b :=
  fun x => TensorProduct.tmul (rootBase T b) (qVFamBlockLinearEquiv T b x) (1 : rootL T b)

theorem qVFamToCarrierK0_compat (x : qVFamTensorBlock T b) :
    carrierK0EquivRootTensor T b (qVFamToCarrierK0 T b x) =
      (blockLinearEquiv T b).symm
        (algebraMap (rootBase T b) (rootL T b) (qVFamBlockLinearEquiv T b x)) := by
  rfl

#check RootLValuedCarrierK0
#check carrierK0EquivRootL
#check carrierK0EquivRootTensor
#check qVFamToCarrierK0
#check qVFamToCarrierK0_compat

end LeanFormal.IUT.XiFPaper.S311RootLValuedK0CarrierActual

end