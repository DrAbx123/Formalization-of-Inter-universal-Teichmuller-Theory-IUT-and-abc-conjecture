import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionSourceActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι -> Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- Actual source action family data: the lattice-preserving linear equivalences
and the identity action. -/
structure PhiActionSourceData where
  Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  Phi_eq : Phi = p6Phi places tuple
  id_mem : (LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)) ∈ Phi
  preserves : ∀ phi ∈ Phi, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
/-- Actual inhabitant of the source action family data. -/
noncomputable def phiActionSourceData : PhiActionSourceData places tuple where
  Phi := p6Phi places tuple
  Phi_eq := rfl
  id_mem := by
    intro u hu
    simpa using hu
  preserves := by
    intro phi hphi u hu
    exact hphi u hu
#print axioms phiActionSourceData
end LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionSourceActual
end