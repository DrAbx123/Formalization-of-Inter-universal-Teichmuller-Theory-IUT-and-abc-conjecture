import tmp.sheaf.xif.paper.Node09P5HullInequalityActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09P5ThetaHullNonemptyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Node09P5HullInequalityActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
theorem qVFamLocalThetaHull_nonempty :
    (qVFamLocalThetaHull T b).Nonempty := by
  refine ⟨0, ?_⟩
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨zeroSignedLabel (l := l), ?_⟩
  rw [qVFamThetaTensorRegion_zero_eq_holomorphic]
  exact (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple).zero_mem
end LeanFormal.IUT.XiFPaper.Node09P5ThetaHullNonemptyActual
