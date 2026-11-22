import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S747ZeroLabelHullAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

def zeroSignedLabel : SignedLabel l.value :=
  ⟨0, by
    constructor
    · have hstar : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      exact neg_nonpos.mpr hstar
    · have hstar : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      exact hstar⟩

theorem rootThetaRegion_zero :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) zeroSignedLabel =
      arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple := by
  unfold rootThetaRegion
  have hc : (fun i : qVFamTensorV =>
      (gaussExponent (zeroSignedLabel (l := l)).1).toNat *
        rootHalfCoefficient (l := l) T b i) = fun _ => 0 := by
    funext i
    simp [zeroSignedLabel]
  rw [hc, arithmeticTupleFractionalLattice_zero]
  change ((arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
    Set (qVFamTensorBlock T b)) =
    arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple
  rw [(rootNormScalingData (l := l) T b).integerTensor_mul_holomorphic]
  exact coefficient_arithmeticTupleHolomorphicLattice
    (qVFamTensorPlaces T b) qVFamTensorTuple

theorem holomorphic_subset_rootThetaHull :
    arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple ⊆
      rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) := by
  intro x hx
  apply subset_closure
  apply Set.mem_iUnion.mpr
  exact ⟨zeroSignedLabel (l := l), by rw [rootThetaRegion_zero]; exact hx⟩

theorem rootThetaImageSet_subset_holomorphic :
    rootThetaImageSet (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) ⊆
      arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  exact rootThetaRegion_subset_holomorphic (l := l) T b j hj

theorem rootThetaHull_eq_closure_holomorphic :
    rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) =
      closure (arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple) := by
  apply le_antisymm
  · exact closure_mono (rootThetaImageSet_subset_holomorphic T b)
  · exact closure_minimal (holomorphic_subset_rootThetaHull T b) isClosed_closure

theorem rootThetaHullLog_eq_log_closure_holomorphic
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootHalfCoefficient (l := l) T b) =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (closure (arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple)) := by
  unfold rootThetaHullLog
  rw [rootThetaHull_eq_closure_holomorphic]

end LeanFormal.IUT.XiFPaper.S747ZeroLabelHullAuditActual
end