import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
/-! # S920: finiteness of S = paperRootThetaHullNonzero
Each nonzero paper region is contained in O_hol (same nonnegative-coefficient
calculation), O_hol is compact (S854), so S, being a closed subset of O_hol,
has finite Haar measure.  Only inequalities/containment; no equality/scaling. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S920SHullFinitenessActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
abbrev s920O : Set (qVFamTensorBlock T b) :=
  arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple
/-- Every paper nonzero-label theta region is contained in O_hol. -/
theorem s920PaperRegion_subset_O (j : SignedLabel l.value) :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) j ⊆ s920O (l := l) T b := by
  intro x hx
  unfold rootThetaRegion at hx
  have hnonneg : ∀ i : qVFamTensorV,
      0 <= (gaussExponent j.1).toNat * paperRootCoefficientFamily (l := l) T b i := by
    intro i
    exact mul_nonneg (Nat.cast_nonneg _)
      (paperRootCoefficientFamily_nonneg (l := l) T b i)
  have hle : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun i => (gaussExponent j.1).toNat *
          paperRootCoefficientFamily (l := l) T b i) <=
      arithmeticTupleValuationIntegerLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleFractionalLattice_le_valuationInteger
      (qVFamTensorPlaces T b) qVFamTensorTuple hnonneg
  have hmul : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun i => (gaussExponent j.1).toNat *
          paperRootCoefficientFamily (l := l) T b i) *
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple <=
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
    calc
      _ <= arithmeticTupleValuationIntegerLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple *
          arithmeticTupleHolomorphicLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple := mul_le_mul' hle le_rfl
      _ = _ := arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
  rw [show s920O (l := l) T b =
      (arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :
          Set (qVFamTensorBlock T b)) by
    unfold s920O
    exact (coefficient_arithmeticTupleHolomorphicLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple).symm]
  exact hmul hx
/-- S is a closed subset of O_hol. -/
theorem s920SHull_subset_O :
    paperRootThetaHullNonzero (l := l) T b ⊆ s920O (l := l) T b := by
  intro x hx
  unfold paperRootThetaHullNonzero at hx
  revert hx
  unfold rootThetaHullNonzero
  apply closure_minimal
  · intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨j, hj⟩
    exact s920PaperRegion_subset_O (l := l) T b j.1 hj
  · exact (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed
/-- Finiteness of the S measure. -/
theorem s920SHull_measure_lt_top :
    mu (paperRootThetaHullNonzero (l := l) T b) < ⊤ :=
  lt_of_le_of_lt (measure_mono (s920SHull_subset_O (l := l) T b))
    ((measure_arithmeticTupleCanonicalRegions_pos_lt_top
      (qVFamTensorPlaces T b) qVFamTensorTuple mu).2.2)
end LeanFormal.IUT.XiFPaper.S920SHullFinitenessActual
