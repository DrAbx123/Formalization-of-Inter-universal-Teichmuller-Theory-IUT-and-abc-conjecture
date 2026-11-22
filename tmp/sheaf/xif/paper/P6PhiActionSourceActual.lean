/- P6 Phi action source: actual source arrows preserving the unit log lattice. -/
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
namespace LeanFormal.IUT.XiFPaper.P6PhiActionSourceActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι -> Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
/-- Actual source arrows for the Phi action family: linear automorphisms of the
tensor block together with the proof that they preserve the unit log lattice. -/
structure P6PhiSource where
  arrows : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  preserves : ∀ phi ∈ arrows, ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple ->
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
/-- The source action family is a subset of the actual lattice-preserving family. -/
theorem p6PhiSource_subset (S : P6PhiSource places tuple) :
    S.arrows ⊆ p6Phi places tuple :=
  fun phi hphi => S.preserves phi hphi
#print axioms p6PhiSource_subset
end LeanFormal.IUT.XiFPaper.P6PhiActionSourceActual
end