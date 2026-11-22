import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual

-- S196: verify that the FinalLValued tensor is genuinely one-factor and that
-- its Ind1 action is the actual paper action on a singleton index packet.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperFinalLInd1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- The actual final tensor index is qVFamTensorV = Unit.
theorem finalTensorIndex_isSingleton : Subsingleton (qVFamTensorV) := inferInstance

theorem finalTensorIndex_card : Fintype.card qVFamTensorV = 1 := by
  simp [qVFamTensorV]

theorem finalLValued_oneFactor : qVFamTensorV = Unit := rfl

-- Ind1 on the one-factor carrier is identity; this is the actual paper
-- action on a singleton index packet (the only reindexing is trivial).
theorem ind1LValued_eq_refl :
    ind1LValued (l := l) T b =
      LinearEquiv.refl ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b) := rfl

noncomputable def paperInd1ActionOnSingleton :
    FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] FinalLValuedCarrier T b :=
  ind1LValued (l := l) T b

theorem paperInd1ActionOnSingleton_eq_refl :
    paperInd1ActionOnSingleton T b =
      LinearEquiv.refl ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b) :=
  ind1LValued_eq_refl T b

theorem paperInd1ActionOnSingleton_apply
    (x : FinalLValuedCarrier T b) :
    paperInd1ActionOnSingleton T b x = x :=
  rfl

-- Exact gap for a multi-factor/dependent paper Ind1 packet.  The current
-- carrier has a singleton tensor index; a nontrivial dependent reindexing
-- action is not constructed here.
structure PaperInd1MultiFactorGap where
  index : Type
  packet : Type
  reindex : (index ≃ index) → packet ≃ packet
  rootMap : RootThetaCarrier (G := finalLGeometry T b) → packet

def PaperInd1MultiFactorGapRequired : Prop :=
  Nonempty (PaperInd1MultiFactorGap T b)

#check finalTensorIndex_isSingleton
#check finalTensorIndex_card
#check finalLValued_oneFactor
#check ind1LValued_eq_refl
#check paperInd1ActionOnSingleton
#check paperInd1ActionOnSingleton_eq_refl
#check PaperInd1MultiFactorGap

end LeanFormal.IUT.XiFPaper.PaperFinalLInd1Actual

end