import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

-- S222: FinalLValued carrier rebased on the actual finite/complete
-- rootNormedExtension, not on the algebraic closure.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev RootL : Type := rootNormedExtension T b

abbrev RootLValuedCarrier : Type :=
  TensorProduct ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) (RootL T b)

noncomputable def qVFamToRootL :
    qVFamTensorBlock T b → RootLValuedCarrier T b :=
  fun x => TensorProduct.tmul ℚ_[qVFamTensorP T b] x (1 : RootL T b)

noncomputable def rootLUnitMulEquiv (u : (RootL T b)ˣ) :
    RootL T b ≃ₗ[ℚ_[qVFamTensorP T b]] RootL T b where
  toFun x := (u : RootL T b) * x
  invFun x := ((u⁻¹ : (RootL T b)ˣ) : RootL T b) * x
  map_add' x y := by ring
  map_smul' a x := by simp [mul_smul_comm]
  left_inv x := by simp
  right_inv x := by simp

noncomputable def rootLInd1 :
    RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      RootLValuedCarrier T b := LinearEquiv.refl _ _

noncomputable def rootLInd2 (u : (RootL T b)ˣ) :
    RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      RootLValuedCarrier T b :=
  TensorProduct.congr (LinearEquiv.refl _ _) (rootLUnitMulEquiv T b u)

noncomputable def rootLInd3 (u : (RootL T b)ˣ) (m : Nat) :
    RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      RootLValuedCarrier T b :=
  rootLInd2 T b (u ^ m)

noncomputable def rootThetaToRootL (j : SignedLabel l.value) :
    RootLValuedCarrier T b :=
  TensorProduct.tmul ℚ_[qVFamTensorP T b] (1 : qVFamTensorBlock T b)
    (rootNormedThetaValueInL (l := l) T b j : RootL T b)

noncomputable def rootThetaImageRootL : Set (RootLValuedCarrier T b) :=
  Set.range (rootThetaToRootL (l := l) T b)

structure RootLValuedTensorPacketActual where
  qVFamMap : qVFamTensorBlock T b → RootLValuedCarrier T b
  ind1 : RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] RootLValuedCarrier T b
  ind2 : (RootL T b)ˣ → RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] RootLValuedCarrier T b
  ind3 : (RootL T b)ˣ → Nat → RootLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] RootLValuedCarrier T b
  rootThetaMap : SignedLabel l.value → RootLValuedCarrier T b

noncomputable def rootLValuedTensorPacket :
    RootLValuedTensorPacketActual T b where
  qVFamMap := qVFamToRootL T b
  ind1 := rootLInd1 T b
  ind2 := fun u => rootLInd2 T b u
  ind3 := fun u m => rootLInd3 T b u m
  rootThetaMap := rootThetaToRootL T b

#check RootL
#check RootLValuedCarrier
#check qVFamToRootL
#check rootLInd1
#check rootLInd2
#check rootLInd3
#check rootThetaToRootL
#check rootThetaImageRootL
#check rootLValuedTensorPacket

-- Actual complete/finite/proper/measurable instances on the rebased L.
instance rootLCompleteSpace : CompleteSpace (RootL T b) :=
  rootNormedExtensionComplete (l := l) T b

instance rootLMeasurableSpace : MeasurableSpace (RootL T b) := borel _

instance rootLFiniteDimensionalQp :
    FiniteDimensional ℚ_[qVFamTensorP T b] (RootL T b) :=
  rootNormedExtensionFiniteDimensionalQp (T := T) (b := b)

instance rootLProperSpace : ProperSpace (RootL T b) := by
  exact @FiniteDimensional.proper ℚ_[qVFamTensorP T b] inferInstance (RootL T b)
    inferInstance inferInstance inferInstance
    (rootNormedExtensionFiniteDimensionalQp (T := T) (b := b))
#check rootLCompleteSpace
#check rootLFiniteDimensionalQp
end LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual

end