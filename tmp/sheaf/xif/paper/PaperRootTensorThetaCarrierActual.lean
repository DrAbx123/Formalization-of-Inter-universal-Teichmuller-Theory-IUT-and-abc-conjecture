import tmp.sheaf.xif.paper.RootTensorHaarTransportActual

-- S299: qside rootTensorBlock is the final L-valued theta carrier.
-- No RootLValuedCarrier equivalence is asserted; blockLinearEquiv ≃ L is used.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.PaperRootTensorThetaCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def rootTensorThetaImageSetFinal : Set (rootTensorBlock T b) :=
  blockThetaImageSetTheta T b

noncomputable def lMulLinearEquiv (u : (rootNormedExtension T b)ˣ) :
    rootNormedExtension T b ≃ₗ[ℚ_[qVFamTensorP T b]] rootNormedExtension T b where
  toFun x := (u : rootNormedExtension T b) * x
  invFun x := ((u⁻¹ : (rootNormedExtension T b)ˣ) : rootNormedExtension T b) * x
  map_add' x y := by ring
  map_smul' a x := by simp [mul_smul_comm]
  left_inv x := by simp
  right_inv x := by simp

noncomputable def ind1RootTensor : rootTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] rootTensorBlock T b :=
  LinearEquiv.refl _ _

noncomputable def ind2RootTensor (u : (rootNormedExtension T b)ˣ) :
    rootTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] rootTensorBlock T b :=
  (blockLinearEquiv T b).trans ((lMulLinearEquiv T b u).trans (blockLinearEquiv T b).symm)

noncomputable def ind3RootTensor (u : (rootNormedExtension T b)ˣ) (m : Nat) :
    rootTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] rootTensorBlock T b :=
  ind2RootTensor T b (u ^ m)

noncomputable def rootTensorThetaInd1Image : Set (rootTensorBlock T b) :=
  (ind1RootTensor T b).toLinearMap.toFun '' rootTensorThetaImageSetFinal T b

noncomputable def rootTensorThetaInd2Image (u : (rootNormedExtension T b)ˣ) :
    Set (rootTensorBlock T b) :=
  (ind2RootTensor T b u).toLinearMap.toFun '' rootTensorThetaImageSetFinal T b

noncomputable def rootTensorThetaInd3Image (u : (rootNormedExtension T b)ˣ) (m : Nat) :
    Set (rootTensorBlock T b) :=
  (ind3RootTensor T b u m).toLinearMap.toFun '' rootTensorThetaImageSetFinal T b

noncomputable def rootTensorThetaIndUnion : Set (rootTensorBlock T b) :=
  rootTensorThetaImageSetFinal T b ∪ rootTensorThetaInd1Image T b ∪
    (Set.iUnion (fun u : (rootNormedExtension T b)ˣ => rootTensorThetaInd2Image T b u)) ∪
    (Set.iUnion (fun u : (rootNormedExtension T b)ˣ =>
      Set.iUnion (fun m : Nat => rootTensorThetaInd3Image T b u m)))

-- Actual qside field-unit lambda-O hull, Haar, and measure/log objects.
noncomputable def rootTensorFieldUnitLambdaOHull : Set (rootTensorBlock T b) :=
  blockThetaScaledHull T b

noncomputable def rootTensorHaar : Measure (rootTensorBlock T b) := blockHaar T b

noncomputable def rootTensorUnitBallMeasure : ENNReal := blockHaar T b (blockUnitBall T b)

theorem rootTensorUnitBallMeasure_eq_one : rootTensorUnitBallMeasure T b = 1 := by
  unfold rootTensorUnitBallMeasure
  exact blockUnitBall_measure T b

theorem rootTensorThetaImage_subset_IndUnion :
    rootTensorThetaImageSetFinal T b ⊆ rootTensorThetaIndUnion T b :=
  fun x hx => Or.inl (Or.inl (Or.inl hx))

theorem rootTensorThetaImage_subset_scaledHull :
    rootTensorThetaImageSetFinal T b ⊆ rootTensorFieldUnitLambdaOHull T b := by
  intro x hx
  change x ∈ blockThetaImageSetTheta T b ∪
    ⋃ j : ThetaLabel (l := l), blockScaledRegion T b
      (rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)
  exact Or.inl hx

#check rootTensorThetaImageSetFinal
#check ind1RootTensor
#check ind2RootTensor
#check ind3RootTensor
#check rootTensorThetaIndUnion
#check rootTensorFieldUnitLambdaOHull
#check rootTensorHaar
#check rootTensorUnitBallMeasure_eq_one
#check rootTensorThetaImage_subset_IndUnion
#check rootTensorThetaImage_subset_scaledHull

end LeanFormal.IUT.XiFPaper.PaperRootTensorThetaCarrierActual

end