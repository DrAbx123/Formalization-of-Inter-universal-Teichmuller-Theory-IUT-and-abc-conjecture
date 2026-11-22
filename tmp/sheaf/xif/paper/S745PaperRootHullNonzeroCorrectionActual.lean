import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.RootHullClosednessActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S745PaperRootHullNonzeroCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.RootHullClosednessActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :
    0 ≤ paperRootCoefficientFamily T b i := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  positivity

/-- Corrected paper root theta hull: only nonzero labels (paper labels 0<j<l). -/
noncomputable def paperRootThetaHullNonzero : Set (qVFamTensorBlock T b) :=
  rootThetaHullNZ (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b)

theorem paperRootThetaHullNonzero_subset_closure_minimal :
    paperRootThetaHullNonzero T b ⊆
      closure (rootMinimalRegion (l := l) (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily T b) (oneLabel l)) := by
  unfold paperRootThetaHullNonzero
  apply closure_minimal
  · exact rootThetaImageSetNZ_subset_minimal (l := l)
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)
      (paperRootCoefficientFamily_nonneg (l := l) T b) (oneLabel l)
      (gaussExponent_oneLabel l)
  · exact isClosed_closure

theorem closure_minimal_subset_paperRootThetaHullNonzero :
    closure (rootMinimalRegion (l := l) (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperRootCoefficientFamily T b) (oneLabel l)) ⊆
      paperRootThetaHullNonzero T b := by
  unfold paperRootThetaHullNonzero
  apply closure_minimal
  · intro x hx
    exact rootMinimalRegion_subset_hullNZ (l := l) (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperRootCoefficientFamily T b) (oneLabel l)
      (gaussExponent_oneLabel l) hx
  · exact isClosed_closure

theorem paperRootThetaHullNonzero_eq_closure_minimal :
    paperRootThetaHullNonzero T b =
      closure (rootMinimalRegion (l := l) (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily T b) (oneLabel l)) :=
  Set.Subset.antisymm
    (paperRootThetaHullNonzero_subset_closure_minimal (l := l) T b)
    (closure_minimal_subset_paperRootThetaHullNonzero (l := l) T b)

/-- Exact closedness gap for the corrected nonzero hull. -/
def PaperRootHullNonzeroClosedGap : Prop :=
  IsClosed (rootMinimalRegion (l := l) (qVFamTensorPlaces T b)
    qVFamTensorTuple (paperRootCoefficientFamily T b) (oneLabel l))

theorem paperRootThetaHullNonzero_eq_minimal_of_closed
    (hclosed : PaperRootHullNonzeroClosedGap (l := l) T b) :
    paperRootThetaHullNonzero T b =
      rootMinimalRegion (l := l) (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily T b) (oneLabel l) := by
  rw [paperRootThetaHullNonzero_eq_closure_minimal]
  exact IsClosed.closure_eq hclosed

/-- Corrected paper nonzero hull log. -/
noncomputable def paperRootThetaHullLogNonzero
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperRootThetaHullNonzero T b)

theorem paperRootThetaHullLogNonzero_eq_formula_of_gap
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b))
    (hclosed : PaperRootHullNonzeroClosedGap (l := l) T b) :
    paperRootThetaHullLogNonzero (l := l) T b mu =
      -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold paperRootThetaHullLogNonzero
  rw [paperRootThetaHullNonzero_eq_minimal_of_closed (l := l) T b hclosed]
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu data

/-- Audit: the old zero-inclusive hull contains the j = 0 region. -/
theorem zero_region_subset_old_paperRootThetaHull :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b) 0 ⊆ paperRootThetaHull T b := by
  intro x hx
  unfold paperRootThetaHull rootThetaHull rootThetaImageSet
  exact subset_closure (Set.mem_iUnion.mpr ⟨0, hx⟩)

end LeanFormal.IUT.XiFPaper.S745PaperRootHullNonzeroCorrectionActual

end
