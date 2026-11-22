import tmp.sheaf.xif.paper.PaperRootThetaPacketActionsActual
import tmp.sheaf.xif.paper.PaperC3SourceQHullRelationActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

-- S188: actual base-change L-valued final tensor carrier.
-- Base: qVFamTensorBlock T b over Qp; L = algebraic closure of the
-- completion at the qVFamily place; carrier = qVFamTensorBlock ⊗_{Qp} L.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaPacketActionsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def finalLGeometry :
    CompletionValuedSourceGeometry (l := l) (K := T.arithmetic.F)
      (p := qVFamTensorP T b) PUnit.{1} where
  place := fun _ => qVFamTensorPlaces T b () ()
  qUnit := fun _ => sourceQVFamilyUnit (l := l) T b
  thetaPacket := sourceThetaPacketFromQ (l := l) T b
  thetaPacket_q_eq := fun _ => sourceThetaPacketFromQ_q (l := l) T b

abbrev FinalL (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  RootExtension (G := finalLGeometry T b) PUnit.unit

abbrev FinalLValuedCarrier (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=
  TensorProduct ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) (FinalL T b)

noncomputable def qVFamToLValued :
    qVFamTensorBlock T b → FinalLValuedCarrier T b :=
  fun x => TensorProduct.tmul ℚ_[qVFamTensorP T b] x (1 : FinalL T b)

noncomputable def finalLUnitMulEquiv (u : (FinalL T b)ˣ) :
    FinalL T b ≃ₗ[ℚ_[qVFamTensorP T b]] FinalL T b where
  toFun x := (u : FinalL T b) * x
  invFun x := ((u⁻¹ : (FinalL T b)ˣ) : FinalL T b) * x
  map_add' x y := by ring
  map_smul' a x := by simp [mul_smul_comm]
  left_inv x := by simp
  right_inv x := by simp

noncomputable def ind1LValued :
    FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      FinalLValuedCarrier T b :=
  LinearEquiv.refl _ _

noncomputable def ind2LValued (u : (FinalL T b)ˣ) :
    FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      FinalLValuedCarrier T b :=
  TensorProduct.congr (LinearEquiv.refl _ _) (finalLUnitMulEquiv (l := l) T b u)

noncomputable def ind3LValued (u : (FinalL T b)ˣ) (m : Nat) :
    FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      FinalLValuedCarrier T b :=
  ind2LValued (l := l) T b (u ^ m)

noncomputable def rootThetaToLValued (x : RootThetaCarrier (G := finalLGeometry T b)) :
    FinalLValuedCarrier T b :=
  TensorProduct.tmul ℚ_[qVFamTensorP T b] (1 : qVFamTensorBlock T b)
    ((x PUnit.unit : (RootExtension (G := finalLGeometry T b) PUnit.unit)ˣ) :
      FinalL T b)

#check FinalLValuedCarrier
#check qVFamToLValued
#check ind1LValued
#check ind2LValued
#check ind3LValued
#check rootThetaToLValued

-- Actual root theta image in the L-valued base-change carrier.
noncomputable def rootThetaImageInLValued :
    Set (FinalLValuedCarrier T b) :=
  Set.range (fun j : SignedLabel l.value =>
    rootThetaToLValued T b (paperRootThetaImagePoint (G := finalLGeometry T b) j))

noncomputable def ind2ImageInLValued (u : (FinalL T b)ˣ) :
    Set (FinalLValuedCarrier T b) :=
  (ind2LValued T b u).toLinearMap.toFun '' rootThetaImageInLValued T b

-- Actual final L-valued tensor packet package.
structure FinalLValuedTensorPacketActual where
  qVFamMap : qVFamTensorBlock T b → FinalLValuedCarrier T b
  ind1 : FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] FinalLValuedCarrier T b
  ind2 : (FinalL T b)ˣ → FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] FinalLValuedCarrier T b
  ind3 : (FinalL T b)ˣ → Nat → FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] FinalLValuedCarrier T b
  rootThetaMap : RootThetaCarrier (G := finalLGeometry T b) → FinalLValuedCarrier T b

noncomputable def finalLValuedTensorPacket :
    FinalLValuedTensorPacketActual T b where
  qVFamMap := qVFamToLValued T b
  ind1 := ind1LValued T b
  ind2 := fun u => ind2LValued T b u
  ind3 := fun u m => ind3LValued T b u m
  rootThetaMap := rootThetaToLValued T b

#check rootThetaImageInLValued
#check ind2ImageInLValued
#check FinalLValuedTensorPacketActual
#check finalLValuedTensorPacket
end LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual

end