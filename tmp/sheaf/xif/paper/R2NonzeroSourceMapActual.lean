/- R2 nonzero-label hull: actual source-map containment
`urNonzeroLabelHull ⊆ arithmeticTupleHolomorphicHull (possibleImages)`.

Uses the actual ceiling generator urCeilGenerator (norm p^{-urCeilC}), the actual
action family p6Phi (contains LinearEquiv.refl), and urLabelOneRegion_eq_ceilRegion.
No root/completion datum; no equality of volumes.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaHullNonzeroActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullLowerActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.S2144RootMinimalClosedActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Pointwise
namespace LeanFormal.IUT.XiFPaper.R2NonzeroSourceMapActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.S2144RootMinimalClosedActual
open MeasureTheory
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

theorem urCeilRegion_eq_pureGenerator_smul :
    thetaTensorScaledRegion (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => urCeilC (l := l) T b) =
      arithmeticTupleFractionalPureGenerator (qVFamTensorPlaces T b) qVFamTensorTuple
          (fun _ => urCeilGenerator (l := l) T b) •
        arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple := by
  unfold thetaTensorScaledRegion
  rw [arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    (data := urCeilData (l := l) T b)]
  rfl

theorem urCeilPossibleImages_eq :
    arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple ()
        (urCeilGenerator (l := l) T b) {LinearEquiv.refl ℚ_[qVFamTensorP T b]
          (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)} =
      thetaTensorScaledRegion (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => urCeilC (l := l) T b) := by
  rw [urCeilRegion_eq_pureGenerator_smul]
  ext x
  constructor
  · rintro ⟨φ, hφ, y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hφ
    subst hφ
    refine ⟨y, hy, ?_⟩
    simp [arithmeticTupleTprod, arithmeticTupleFractionalPureGenerator]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨LinearEquiv.refl _ _, by simp, y, hy, ?_⟩
    simp [arithmeticTupleTprod, arithmeticTupleFractionalPureGenerator]

/-- R2 source-map containment from the actual ceiling generator and the actual action
family containing the identity. -/
theorem urNonzeroLabelHull_subset_holomorphicHull
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((j : Unit) → CommonPrimeCompletion (qVFamTensorPlace T b))) :
    urNonzeroLabelHull (l := l) T b ⊆
      arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e
        (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple ()
          (urCeilGenerator (l := l) T b)
          {LinearEquiv.refl ℚ_[qVFamTensorP T b]
            (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)}) := by
  have hclosed : IsClosed (thetaTensorScaledRegion (p := qVFamTensorP T b)
      (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => urCeilC (l := l) T b)) :=
    s2144_isClosed_rootMinimalRegion_of_data (p := qVFamTensorP T b)
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
      (c := fun _ => urCeilC (l := l) T b) (urCeilData (l := l) T b)
  have hreg : urNonzeroLabelHull (l := l) T b =
      thetaTensorScaledRegion (p := qVFamTensorP T b)
        (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => urCeilC (l := l) T b) := by
    rw [urNonzeroLabelHull_eq_closure_region_one]
    rw [urNonzeroLabelImageSet_eq_region_one]
    rw [urLabelOneRegion_eq_ceilRegion]
    exact hclosed.closure_eq
  rw [hreg, urCeilPossibleImages_eq]
  exact subset_arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e _

#print axioms urNonzeroLabelHull_subset_holomorphicHull
end LeanFormal.IUT.XiFPaper.R2NonzeroSourceMapActual