/- U-L actual packet family: actual tensor witness, actual q, the actual Phi
action family, and the actual packet hull. -/
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPacketFamilyActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
/-- The actual tensor-core witness of the qVFamily tensor block at `b`. -/
noncomputable def ulPacketTensorWitness :
    TensorCoreWitness (qVFamTensorPlaces T b) qVFamTensorTuple :=
  tensorCoreWitness (qVFamTensorPlaces T b) qVFamTensorTuple
/-- Actual packet hull from the actual tensor decomposition, the actual
distinguished q, and the actual Phi action family.

Index note: the qVFamily tensor index is `qVFamTensorV = Unit`, i.e. the actual
one-factor arithmetic tensor block at the fixed bad place `b` (its single
completion factor is `CommonPrimeCompletion (qVFamTensorPlace T b)`); the
distinguished slot `()` is the actual index of that one factor, not a toy
carrier. -/
noncomputable def ulActualPacketHull : Set (qVFamTensorBlock T b) := by
  let W := ulPacketTensorWitness T b
  letI : Fintype W.J := W.fintype
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (W.E j) := W.finite
  letI : ∀ j, ProperSpace (W.E j) :=
    fun j => FiniteDimensional.proper ℚ_[qVFamTensorP T b] (W.E j)
  exact arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple
    W.equiv
    (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple
      () (qVFamily T b).q (p6Phi (qVFamTensorPlaces T b) qVFamTensorTuple))
/-- Every actual theta possible image is in the actual packet hull. -/
theorem ulPossibleImages_subset_packetHull :
    arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple
      () (qVFamily T b).q (p6Phi (qVFamTensorPlaces T b) qVFamTensorTuple) ⊆
      ulActualPacketHull T b := by
  let W := ulPacketTensorWitness T b
  letI : Fintype W.J := W.fintype
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (W.E j) := W.finite
  letI : ∀ j, ProperSpace (W.E j) :=
    fun j => FiniteDimensional.proper ℚ_[qVFamTensorP T b] (W.E j)
  unfold ulActualPacketHull
  exact subset_arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple
    W.equiv _
#print axioms ulPacketTensorWitness
#print axioms ulPossibleImages_subset_packetHull
end LeanFormal.IUT.XiFPaper.Mzk1ULPacketFamilyActual
end
