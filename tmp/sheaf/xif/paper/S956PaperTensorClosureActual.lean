import tmp.sheaf.xif.paper.S946TensorPaperSContainmentActual

/-! # S956: paper tensor hull = closure(thetaIndUnion)

`paperTensorS = thetaImageIndUnion` is only a point-set union; the paper
object is its hull.  Under a supplied topology on FinalLValuedCarrier, define
`paperTensorHull := closure thetaImageIndUnion`, prove the actual theta/Ind
images land in it, and reduce qPilot hull containment to the exact
neighbourhood approximation condition.  The union containment of S946 is not
asserted.  No fake topology or empty set is used. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S956PaperTensorClosureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S946TensorPaperSContainmentActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable [TopologicalSpace (FinalLValuedCarrier T b)]

/-- Paper tensor hull: closure of the actual theta+Ind1/2/3 image union. -/
noncomputable def paperTensorHull : Set (FinalLValuedCarrier T b) :=
  closure (thetaImageIndUnion (l := l) T b)

theorem rootThetaImage_subset_paperTensorHull :
    rootThetaImageInLValued (l := l) T b ⊆ paperTensorHull (l := l) T b :=
  fun x hx => subset_closure (rootThetaImage_subset_indUnion (l := l) T b hx)

theorem ind1Image_subset_paperTensorHull :
    ind1Image (l := l) T b ⊆ paperTensorHull (l := l) T b :=
  fun x hx => subset_closure (ind1Image_subset_indUnion (l := l) T b hx)

theorem ind2Image_subset_paperTensorHull (u : (FinalL T b)ˣ) :
    ind2Image (l := l) T b u ⊆ paperTensorHull (l := l) T b := by
  intro x hx
  exact subset_closure (ind2Image_subset_paperTensorS (l := l) T b u hx)

theorem ind3Image_subset_paperTensorHull (u : (FinalL T b)ˣ) (m : Nat) :
    ind3Image (l := l) T b u m ⊆ paperTensorHull (l := l) T b := by
  intro x hx
  exact subset_closure (ind3Image_subset_paperTensorS (l := l) T b u m hx)

/-- Exact paper hull containment of the qPilot tensor image. -/
def S956QPilotHullContainment : Prop :=
  qPilotPaperImageInLValued (l := l) T b ⊆ paperTensorHull (l := l) T b

/-- Exact minimal neighbourhood approximation condition, equivalent to hull
containment.  It says each qPilot image point is approximated by theta/Ind
image points; it does not assert union containment. -/
def S956QPilotApproximationCondition : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ qPilotPaperRegion (l := l) T b →
      ∀ U : Set (FinalLValuedCarrier T b), U ∈ 𝓝 (qVFamToLValued (l := l) T b x) →
        (U ∩ thetaImageIndUnion (l := l) T b).Nonempty

theorem s956QPilotHullContainment_iff_approximation :
    S956QPilotHullContainment (l := l) T b ↔
      S956QPilotApproximationCondition (l := l) T b := by
  unfold S956QPilotHullContainment S956QPilotApproximationCondition paperTensorHull
    qPilotPaperImageInLValued
  constructor
  · rintro h x hx U hU
    exact (mem_closure_iff_nhds.mp (h ⟨x, hx, rfl⟩)) U hU
  · rintro h y ⟨x, hx, rfl⟩
    exact mem_closure_iff_nhds.mpr (h x hx)

theorem qPilotPaperImageInLValued_nonempty_hull :
    (qPilotPaperImageInLValued (l := l) T b).Nonempty :=
  qPilotPaperImageInLValued_nonempty (l := l) T b

end LeanFormal.IUT.XiFPaper.S956PaperTensorClosureActual

end
