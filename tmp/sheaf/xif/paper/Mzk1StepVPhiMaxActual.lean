import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1StepVPhiMaxActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace

universe u v
variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- Step-V `Φmax`: the set of all `ℚ_[p]`-linear automorphisms of the actual
tensor tuple block preserving the actual unit log-lattice.  This is exactly
the class of indeterminacy actions for which Step V is stated. -/
def stepVPhiMax :
    Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple) :=
  {φ | ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
    φ u ∈ arithmeticTupleUnitLogLattice places tuple}

/-- The identity automorphism preserves the lattice. -/
theorem identity_mem_stepVPhiMax :
    (LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)) ∈
      stepVPhiMax places tuple := by
  intro u hu
  simpa using hu

/-- `Φmax` is nonempty; the identity is an actual member, not a free
`Nonempty` inhabitant. -/
theorem stepVPhiMax_nonempty : (stepVPhiMax places tuple).Nonempty :=
  ⟨LinearEquiv.refl _ _, identity_mem_stepVPhiMax places tuple⟩

/-- A supplied family of actual Ind1/Ind2 automorphisms is contained in
`Φmax`; this is the exact condition Step V needs. -/
def StepVPhiMaxContains
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)) : Prop :=
  Φ ⊆ stepVPhiMax places tuple

/-- The actual Ind1/Ind2 action families are not constructed in the current
tree; this records the exact missing input for Step V. -/
structure StepVActualInd1Ind2Action where
  ind1 : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  ind2 : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  ind1_mem : StepVPhiMaxContains places tuple ind1
  ind2_mem : StepVPhiMaxContains places tuple ind2

def StepVActualInd1Ind2ActionRequired : Prop :=
  Nonempty (StepVActualInd1Ind2Action places tuple)

#print axioms identity_mem_stepVPhiMax
#print axioms stepVPhiMax_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1StepVPhiMaxActual