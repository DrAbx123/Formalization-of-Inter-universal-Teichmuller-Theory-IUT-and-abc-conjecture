import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S908ORExpansionContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u v
variable {X : Type u} {ι : Type v}

/-- Abstract OR-expansion data: the qPilot branch is one of the expanded OR
possibilities B_i, and the theta hull contains all of them. -/
structure ORExpansionData (X : Type u) (ι : Type v) where
  A : Set X
  B : Set X
  branches : ι → Set X
  or_expansion : A ∩ B ⊆ A ∩ (⋃ i, branches i)
  qPilot : Set X
  thetaHull : Set X
  qPilot_subset_branches : qPilot ⊆ (⋃ i, branches i)
  branches_subset_hull : (⋃ i, branches i) ⊆ thetaHull

/-- General OR-expansion comparison for any monotone log-volume. -/
theorem orExpansion_comparison
    (φ : Set X → Real) (hmono : ∀ {S T : Set X}, S ⊆ T → φ S ≤ φ T)
    (D : ORExpansionData X ι) :
    φ D.qPilot ≤ φ D.thetaHull :=
  hmono (D.qPilot_subset_branches.trans D.branches_subset_hull)

universe w
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Actual OR-expansion data from S793/S800/S805: qPilot is the j=1 branch,
and the nonzero theta hull is the closure of all nonzero branches. -/
noncomputable def paperORExpansionData :
    ORExpansionData (qVFamTensorBlock T b) (NonzeroLabel (l := l)) where
  A := Set.univ
  B := ⋃ j : NonzeroLabel (l := l),
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) j.1
  branches := fun j : NonzeroLabel (l := l) =>
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) j.1
  or_expansion := by
    intro x hx
    exact ⟨trivial, hx.2⟩
  qPilot := qPilotPaperRegion (l := l) T b
  thetaHull := paperRootThetaHullNonzero (l := l) T b
  qPilot_subset_branches := by
    rw [qPilotPaperRegion_eq_rootThetaRegion_one (l := l) T b]
    exact Set.subset_iUnion
      (fun j : NonzeroLabel (l := l) =>
        rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
          (paperRootCoefficientFamily (l := l) T b) j.1)
      ⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩
  branches_subset_hull := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    unfold paperRootThetaHullNonzero rootThetaHullNonzero rootThetaImageSetNonzero
    exact subset_closure (Set.mem_iUnion.mpr ⟨j, hj⟩)

/-- Actual containment qPilot ⊆ nonzero theta hull. -/
theorem paperQPilot_subset_nonzeroHull :
    qPilotPaperRegion (l := l) T b ⊆ paperRootThetaHullNonzero (l := l) T b :=
  qPilotPaperRegion_subset_nonzeroHull (l := l) T b

/-- Actual OR-expansion comparison with normalized log-volume, conditional only
on positivity of the qPilot measure and finiteness of the hull measure. -/
theorem paperORExpansionLogComparison
    (hpos : 0 < mu (qPilotPaperRegion (l := l) T b))
    (hfin : mu (paperRootThetaHullNonzero (l := l) T b) < ⊤) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (qPilotPaperRegion (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (paperRootThetaHullNonzero (l := l) T b) :=
  arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (paperQPilot_subset_nonzeroHull (l := l) T b) hpos hfin

end LeanFormal.IUT.XiFPaper.S908ORExpansionContainmentActual

end
