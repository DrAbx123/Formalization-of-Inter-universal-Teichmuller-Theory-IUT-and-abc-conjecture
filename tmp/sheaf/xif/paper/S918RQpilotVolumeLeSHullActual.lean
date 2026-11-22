import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.S806PaperRootHullNonzeroGapsActual

/-! # S918: V(R) <= V(S) from containment, positivity and finiteness

Only an inequality.  R = qPilotPaperRegion, S = paperRootThetaHullNonzero.
No equality V(R)=... and no hull-log equality is asserted.  Finiteness of S
uses the containment S <= canonicalUnitReference for nonnegative paper root
coefficients. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Every nonzero paper root theta region is contained in O_hol. -/
theorem s918PaperRootRegion_subset_holomorphic
    (j : {j : SignedLabel l.value // j.1 ≠ 0}) :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) j.1 ⊆
      arithmeticTupleCanonicalUnitReference
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
  intro x hx
  unfold rootThetaRegion at hx
  have hcoeff_nonneg : ∀ i : qVFamTensorV,
      0 <= ((gaussExponent j.1.1).toNat : Real) *
        paperRootCoefficientFamily (l := l) T b i := by
    intro i
    exact mul_nonneg (Nat.cast_nonneg _)
      (S779RootHullNonzeroFixActual.paperRootCoefficientFamily_nonneg (l := l) T b i)
  have hle : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun i => ((gaussExponent j.1.1).toNat : Real) *
          paperRootCoefficientFamily (l := l) T b i) <=
      arithmeticTupleValuationIntegerLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleFractionalLattice_le_valuationInteger
      (qVFamTensorPlaces T b) qVFamTensorTuple hcoeff_nonneg
  have hmul : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun i => ((gaussExponent j.1.1).toNat : Real) *
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
  rw [← coefficient_arithmeticTupleHolomorphicLattice
    (qVFamTensorPlaces T b) qVFamTensorTuple]
  exact hmul hx

/-- S = paperRootThetaHullNonzero is contained in canonicalUnitReference. -/
theorem s918S_subset_holomorphic :
    s914S (l := l) T b ⊆
      arithmeticTupleCanonicalUnitReference
        (qVFamTensorPlaces T b) qVFamTensorTuple := by
  unfold s914S paperRootThetaHullNonzero rootThetaHullNonzero rootThetaImageSetNonzero
  apply closure_minimal
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact s918PaperRootRegion_subset_holomorphic (l := l) T b j hj
  · exact (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed

/-- Exact requested positivity of the paper-order R measure.  The available
S778 positivity is at the spectral root-half coefficient; using it for the
paper-order R would require the forbidden spectral/order identification. -/
def S918RMeasurePosRequired : Prop :=
  0 < mu (s914R (l := l) T b)

/-- Positivity of the S measure from R positivity and R ⊆ S. -/
theorem s918S_measure_pos
    (hR : S918RMeasurePosRequired (l := l) T b mu) :
    0 < mu (s914S (l := l) T b) :=
  lt_of_lt_of_le hR (measure_mono (s914R_subset_S (l := l) T b))

/-- Finiteness of the S measure from S ⊆ canonicalUnitReference. -/
theorem s918S_measure_lt_top : mu (s914S (l := l) T b) < ⊤ :=
  lt_of_le_of_lt (measure_mono (s918S_subset_holomorphic (l := l) T b))
    ((isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.measure_lt_top)

/-- Main inequality: V(R) <= V(S), conditional only on R positivity.
No equality is asserted. -/
theorem s918V_R_le_V_S
    (hR : S918RMeasurePosRequired (l := l) T b mu) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  s914MuLogComparison (l := l) T b mu hR
    (s918S_measure_lt_top (l := l) T b mu)

end LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual

end
