import tmp.sheaf.xif.paper.Node09P5NormalizedRegionActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Node09P5HullInequalityActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
/-- The label-0 theta region is the holomorphic unit lattice. -/
theorem qVFamThetaTensorRegion_zero_eq_holomorphic :
    qVFamThetaTensorRegion T b (LeanFormal.IUT.Theorem311Source.OriginalInput.zeroSignedLabel (l := l)) =
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Set (qVFamTensorBlock T b)) := by
  unfold qVFamThetaTensorRegion thetaTensorScaledRegion
  have hcoef : qVFamThetaTensorCoefficient T b (zeroSignedLabel (l := l)) =
      fun _ => (0 : Real) := by
    funext i
    simp [qVFamThetaTensorCoefficient, LeanFormal.IUT.Theorem311Source.OriginalInput.zeroSignedLabel_val, gaussExponent_zero]
  rw [hcoef, arithmeticTupleFractionalLattice_zero]
  change (((arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b) qVFamTensorTuple) *
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple) :
        Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b)) =
    (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Set (qVFamTensorBlock T b))
  exact congrArg
    (fun S : Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b) =>
      (S : Set (qVFamTensorBlock T b)))
    (arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
      (p := qVFamTensorP T b) (qVFamTensorPlaces T b) qVFamTensorTuple)
/-- The holomorphic unit lattice is contained in the qVFam theta hull. -/
theorem qVFamHolomorphicLattice_subset_thetaHull :
    (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
        Set (qVFamTensorBlock T b)) ⊆ qVFamLocalThetaHull T b := by
  intro x hx
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨zeroSignedLabel (l := l), ?_⟩
  rwa [qVFamThetaTensorRegion_zero_eq_holomorphic]
#check qVFamThetaTensorRegion_zero_eq_holomorphic
#check qVFamHolomorphicLattice_subset_thetaHull
end LeanFormal.IUT.XiFPaper.Node09P5HullInequalityActual
end