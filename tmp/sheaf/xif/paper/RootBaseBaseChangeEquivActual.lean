import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual
import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual

/-! # rootBase base-change equivalence to RootLValued carrier

qVFamBlockLinearEquiv identifies qVFamTensorBlock with rootBase.  We induce the
rootBase-module structure on qVFamTensorBlock through that equivalence, form
TensorProduct rootBase qVFamTensorBlock RootL, identify it with RootL by the
one-factor/base-change equivalence, and compose with blockLinearEquiv to get
rootTensorBlock ≃ RootLValuedCarrierRootBase.  No Qp tensor comparison, no fake.

No inequality. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.RootBaseBaseChangeEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Induced rootBase-module structure on the qVFam block via the one-factor identification. -/
noncomputable instance qVFamBlockModuleRootBase :
    Module (rootBase T b) (qVFamTensorBlock T b) where
  smul a x := (qVFamBlockLinearEquiv T b).symm
    (a * (qVFamBlockLinearEquiv T b x))
  one_smul x := by simp
  mul_smul a c x := by
    simp [mul_assoc]
  smul_zero a := by simp
  smul_add a x y := by simp
  add_smul a c x := by simp [add_mul]
  zero_smul x := by simp

/-- The one-factor linear equivalence qVFamBlock ≃ rootBase, now rootBase-linear. -/
noncomputable def qVFamBlockRootBaseEquiv :
    qVFamTensorBlock T b ≃ₗ[rootBase T b] rootBase T b where
  toFun := qVFamBlockLinearEquiv T b
  invFun := (qVFamBlockLinearEquiv T b).symm
  left_inv := fun x => (qVFamBlockLinearEquiv T b).symm_apply_apply x
  right_inv := fun x => (qVFamBlockLinearEquiv T b).apply_symm_apply x
  map_add' := fun x y => (qVFamBlockLinearEquiv T b).map_add x y
  map_smul' := fun a x => rfl

/-- The rootBase base-change carrier. -/
abbrev RootLValuedCarrierRootBase : Type :=
  TensorProduct (rootBase T b) (qVFamTensorBlock T b) (RootL T b)

/-- Base-change identification TensorProduct rootBase qVFamTensorBlock RootL ≃ RootL. -/
noncomputable def tensorBaseChangeEquiv :
    RootLValuedCarrierRootBase T b ≃ₗ[rootBase T b] RootL T b :=
  (TensorProduct.congr (qVFamBlockRootBaseEquiv T b)
    (LinearEquiv.refl (rootBase T b) (RootL T b))).trans
    (TensorProduct.lid (rootBase T b) (RootL T b))

/-- Actual Qp-linear equivalence rootTensorBlock ≃ RootLValuedCarrierRootBase. -/
noncomputable def rootTensorBlockEquivRootBase :
    rootTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] RootLValuedCarrierRootBase T b :=
  (blockLinearEquiv T b).trans
    ((tensorBaseChangeEquiv T b).symm.restrictScalars ℚ_[(qVFamTensorP T b)])

end LeanFormal.IUT.XiFPaper.RootBaseBaseChangeEquivActual

end
