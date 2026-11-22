/- U-L actual per-packet value on the real qVFamily tensor block, built from the
accepted per-packet `V_a` (Mzk1ULPacketVActual.packetV) with the actual
tensor-core field product and an actual nonzero distinguished representative.

Route compliance: the distinguished representative `ϖ` of route §5.2.2 is the
split-Tate / value-group `θ`-pilot supplied by the U-R root carrier (kurt,
`F_b = IntermediateField.adjoin K_b {hodgeTwoLthRoot}`).  A completion
`2l`-th root does not exist (`S342QVFamilyRootImpossibleActual`), so this file
does NOT assert a completion root: `varpi` is an explicit actual element of the
distinguished slot, and the C1 negative term is `-localNormOrder p varpi`. -/
import tmp.sheaf.xif.paper.Mzk1ULPacketFamilyActual
import tmp.sheaf.xif.paper.Mzk1ULPacketVActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPacketHullActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
/-- The actual exceptional index set of the qVFamily packet: the unique tensor
place when its shell ramification exponent exceeds `p - 2`.  This is a
definition, not a hypothesis. -/
noncomputable def ulQVFamPacketExceptional : Finset qVFamTensorV :=
  Finset.univ.filter (fun i =>
    qVFamTensorP T b - 2 < logShellRamificationExponent
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b))
/-- Outside the defined exceptional set the shell exponent is `≤ p - 2`. -/
theorem ulQVFamPacketExceptional_small_outside
    (i : qVFamTensorV) (hi : i ∉ ulQVFamPacketExceptional T b) :
    logShellRamificationExponent
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
        (p := qVFamTensorP T b) ≤ qVFamTensorP T b - 2 := by
  by_contra hle
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Nat.lt_of_not_le hle⟩)
/-- The actual per-packet value `V_a` on the actual qVFamily tensor block, for
an actual nonzero distinguished representative `varpi` (from the split-Tate /
root carrier) and the actual lattice-preserving action family. -/
noncomputable def ulQVFamPacketV
    (varpi : CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
    (Phi : Set (qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] qVFamTensorBlock T b)) :
    Real := by
  let W := ulPacketTensorWitness T b
  letI : Fintype W.J := W.fintype
  letI : Finite W.J := Finite.of_fintype W.J
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (W.E j) := W.finite
  letI : ∀ j, ProperSpace (W.E j) :=
    fun j => FiniteDimensional.proper ℚ_[qVFamTensorP T b] (W.E j)
  exact packetV (qVFamTensorPlaces T b) qVFamTensorTuple W.equiv () varpi Phi
/-- C1 for the actual qVFamily packet: `V_a ≤ B_a` with the actual distinguished
representative and the defined exceptional set. -/
theorem ulQVFamPacketV_le_paperBound
    (varpi : CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
    (hvarpi : varpi ≠ 0)
    (Phi : Set (qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] qVFamTensorBlock T b))
    (hPhi_ne : Phi.Nonempty)
    (hPhi : ∀ phi ∈ Phi, ∀ u ∈ arithmeticTupleUnitLogLattice (qVFamTensorPlaces T b) qVFamTensorTuple,
      phi u ∈ arithmeticTupleUnitLogLattice (qVFamTensorPlaces T b) qVFamTensorTuple) :
    ulQVFamPacketV T b varpi Phi ≤
      packetB (qVFamTensorPlaces T b) qVFamTensorTuple ()
        varpi (ulQVFamPacketExceptional T b) := by
  let W := ulPacketTensorWitness T b
  letI : Fintype W.J := W.fintype
  letI : Finite W.J := Finite.of_fintype W.J
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (W.E j) := W.finite
  letI : ∀ j, ProperSpace (W.E j) :=
    fun j => FiniteDimensional.proper ℚ_[qVFamTensorP T b] (W.E j)
  unfold ulQVFamPacketV
  exact packetV_le_packetB (qVFamTensorPlaces T b) qVFamTensorTuple W.equiv ()
    varpi hvarpi Phi hPhi_ne hPhi (ulQVFamPacketExceptional T b)
    (fun i hi => ulQVFamPacketExceptional_small_outside T b i hi)
#print axioms ulQVFamPacketExceptional_small_outside
#print axioms ulQVFamPacketV_le_paperBound
end LeanFormal.IUT.XiFPaper.Mzk1ULPacketHullActual
end
