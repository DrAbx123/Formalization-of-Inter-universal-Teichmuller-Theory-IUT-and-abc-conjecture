/- U-L per-packet value on the actual tensor-core field product: the accepted
`packetV` instantiated at the actual field-product witness. -/
import tmp.sheaf.xif.paper.Mzk1ULPacketVActual
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPacketHull2Actual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- The per-packet value `V_a` on the actual tensor-core field-product witness
and an actual nonzero Kummer representative. -/
noncomputable def ulPacketVOfWitness
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)) : Real := by
  let W := tensorCoreWitness places tuple
  letI : Fintype W.J := W.fintype
  letI : Finite W.J := Finite.of_fintype W.J
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[p] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[p] (W.E j) := W.finite
  letI : ∀ j, ProperSpace (W.E j) :=
    fun j => FiniteDimensional.proper ℚ_[p] (W.E j)
  exact packetV places tuple W.equiv istar varpi Phi
/-- C1 on the actual field-product packet value: the paper bound with the actual
Kummer representative and the actual exceptional set. -/
theorem ulPacketVOfWitness_le_paperBound
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hPhi_ne : Phi.Nonempty)
    (hPhi : ∀ phi ∈ Phi, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      phi u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    ulPacketVOfWitness places tuple istar varpi Phi ≤
      packetB places tuple istar varpi exceptional := by
  let W := tensorCoreWitness places tuple
  letI : Fintype W.J := W.fintype
  letI : Finite W.J := Finite.of_fintype W.J
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[p] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[p] (W.E j) := W.finite
  letI : ∀ j, ProperSpace (W.E j) :=
    fun j => FiniteDimensional.proper ℚ_[p] (W.E j)
  unfold ulPacketVOfWitness
  exact packetV_le_packetB places tuple W.equiv istar varpi hvarpi Phi hPhi_ne hPhi
    exceptional small_outside
#print axioms ulPacketVOfWitness_le_paperBound
end LeanFormal.IUT.XiFPaper.Mzk1ULPacketHull2Actual
end
