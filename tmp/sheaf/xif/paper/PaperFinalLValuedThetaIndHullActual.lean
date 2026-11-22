import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual

-- S199: actual root Theta image union under Ind1/2/3 on the L-valued
-- base-change packet, and the field-unit lambda-O scaling hull.
-- Objects only; no inequality.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev Carrier : Type := FinalLValuedCarrier T b

noncomputable def ind1Image : Set (Carrier T b) :=
  (ind1LValued T b).toLinearMap.toFun '' rootThetaImageInLValued T b

noncomputable def ind2Image (u : (FinalL T b)ˣ) : Set (Carrier T b) :=
  (ind2LValued T b u).toLinearMap.toFun '' rootThetaImageInLValued T b

noncomputable def ind3Image (u : (FinalL T b)ˣ) (m : Nat) : Set (Carrier T b) :=
  (ind3LValued T b u m).toLinearMap.toFun '' rootThetaImageInLValued T b

-- Actual union of the root Theta image under Ind1, Ind2 (all field units)
-- and Ind3 (all field units and upper-semi shifts).
noncomputable def thetaImageIndUnion : Set (Carrier T b) :=
  rootThetaImageInLValued T b ∪ ind1Image T b ∪
    (Set.iUnion (fun u : (FinalL T b)ˣ => ind2Image T b u)) ∪
    (Set.iUnion (fun u : (FinalL T b)ˣ =>
      Set.iUnion (fun m : Nat => ind3Image T b u m)))

-- Actual field-unit lambda-O scaling hull of the Ind union (union over all
-- field-unit scalings; not the unit ball and not a closure).
noncomputable def fieldUnitLambdaOHull : Set (Carrier T b) :=
  Set.iUnion (fun u : (FinalL T b)ˣ =>
    (ind2LValued T b u).toLinearMap.toFun '' thetaImageIndUnion T b)

theorem rootThetaImage_subset_indUnion :
    rootThetaImageInLValued T b ⊆ thetaImageIndUnion T b :=
  fun x hx => Or.inl (Or.inl (Or.inl hx))

theorem ind1Image_subset_indUnion :
    ind1Image T b ⊆ thetaImageIndUnion T b :=
  fun x hx => Or.inl (Or.inl (Or.inr hx))

#check ind1Image
#check ind2Image
#check ind3Image
#check thetaImageIndUnion
#check fieldUnitLambdaOHull
#check rootThetaImage_subset_indUnion

end LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual

end