import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

-- S293: migrate the theta/Ind/hull objects to the RootL finite complete carrier;
-- no algebraic-closure FinalL carrier is used.  qside rootTensorBlock is the
-- comparison/hull target.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.PaperRootLThetaMigratedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev Carrier : Type := RootLValuedCarrier T b

noncomputable def RootLThetaImage : Set (Carrier T b) :=
  Set.range (rootThetaToRootL (l := l) T b)

noncomputable def rootLInd1Image : Set (Carrier T b) :=
  (rootLInd1 T b).toLinearMap.toFun '' RootLThetaImage T b

noncomputable def rootLInd2Image (u : (RootL T b)ˣ) : Set (Carrier T b) :=
  (rootLInd2 T b u).toLinearMap.toFun '' RootLThetaImage T b

noncomputable def rootLInd3Image (u : (RootL T b)ˣ) (m : Nat) : Set (Carrier T b) :=
  (rootLInd3 T b u m).toLinearMap.toFun '' RootLThetaImage T b

noncomputable def RootLThetaIndUnion : Set (Carrier T b) :=
  RootLThetaImage T b ∪ rootLInd1Image T b ∪
    (Set.iUnion (fun u : (RootL T b)ˣ => rootLInd2Image T b u)) ∪
    (Set.iUnion (fun u : (RootL T b)ˣ =>
      Set.iUnion (fun m : Nat => rootLInd3Image T b u m)))

noncomputable def RootLFieldUnitLambdaOHull : Set (Carrier T b) :=
  Set.iUnion (fun u : (RootL T b)ˣ =>
    (rootLInd2 T b u).toLinearMap.toFun '' RootLThetaIndUnion T b)

theorem RootLThetaImage_subset_IndUnion :
    RootLThetaImage T b ⊆ RootLThetaIndUnion T b :=
  fun x hx => Or.inl (Or.inl (Or.inl hx))

-- qside root tensor block target (no Haar asserted; exact object map gap).
abbrev RootTensorBlock : Type := rootTensorBlock T b

structure RootLHaarGap where
  measurableSpace : MeasurableSpace (Carrier T b)
  haar : @Measure (Carrier T b) measurableSpace
  measurableHull : Prop
  hullPositiveFinite : Prop

def RootLHaarGapRequired : Prop := Nonempty (RootLHaarGap T b)
#check RootLThetaImage
#check RootLThetaIndUnion
#check RootLFieldUnitLambdaOHull
#check RootLThetaImage_subset_IndUnion
#check RootLHaarGapRequired

end LeanFormal.IUT.XiFPaper.PaperRootLThetaMigratedActual

end