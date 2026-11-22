import tmp.sheaf.xif.paper.S956TensorPacketLogVolumeExactActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
/-! # S957: corrected qPilot containment in the paper tensor closure
paperTensorS is only the point-set union thetaImageIndUnion.  The qPilot
region is the whole F(cRoot)O region, so requiring its image in the union is
too strong.  The paper object is the closure/hull.  This file defines the
closure using S956 topology data and records the exact density input; no union
containment is claimed. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData (l := l) T b)
/-- Paper tensor hull: closure of the actual theta+Ind union, using the exact
S956 topology on the fixed carrier. -/
noncomputable def paperTensorHull : Set (FinalLValuedCarrier T b) := by
  letI := D.topologicalSpace
  exact closure (thetaImageIndUnion (l := l) T b)
/-- Exact density input: every qPilot image point lies in the closure of the
theta+Ind union.  This replaces the too-strong union containment. -/
def S957ThetaImageDenseInQPilot : Prop :=
  qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorHull (l := l) T b D
/-- Conditional closure containment, with no union containment. -/
theorem qPilotPaperImage_subset_paperTensorHull
    (h : S957ThetaImageDenseInQPilot (l := l) T b D) :
    qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorHull (l := l) T b D :=
  h
/-- Exact minimal missing density theorem, pointwise form. -/
def S957ThetaAccumulatesQPilot : Prop :=
  ∀ x : qVFamTensorBlock T b, x ∈ qPilotPaperRegion (l := l) T b →
    qVFamToLValued (l := l) T b x ∈ paperTensorHull (l := l) T b D
theorem s957ThetaAccumulatesQPilot_iff :
    S957ThetaAccumulatesQPilot (l := l) T b D ↔
      S957ThetaImageDenseInQPilot (l := l) T b D := by
  unfold S957ThetaAccumulatesQPilot S957ThetaImageDenseInQPilot
    qPilotPaperImageInLValued
  constructor
  · rintro h y ⟨x, hx, rfl⟩
    exact h x hx
  · rintro h x hx
    exact h ⟨x, hx, rfl⟩
end LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
