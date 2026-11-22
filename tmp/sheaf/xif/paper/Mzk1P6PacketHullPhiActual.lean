/- P6 generic PacketHullData Phi data (small). -/
import tmp.sheaf.xif.paper.Mzk1P6PacketHullGenericActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullPhiActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (places : Unit -> Unit -> FinitePlaceAtPrime K p) (tuple : Unit -> Unit)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type u} [Finite J] {E : J -> Type u}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
theorem genericPacketHullData_Phi_nonempty
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    (packetHullDataGeneric places tuple e).Phi.Nonempty :=
  (packetHullDataGeneric places tuple e).hPhi_ne
theorem genericPacketHullData_Phi_stable
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j))
    (phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]] ArithmeticTensorTupleBlock places tuple)
    (hphi : phi ∈ (packetHullDataGeneric places tuple e).Phi)
    (u : ArithmeticTensorTupleBlock places tuple)
    (hu : u ∈ arithmeticTupleUnitLogLattice places tuple) :
    phi u ∈ arithmeticTupleUnitLogLattice places tuple :=
  (packetHullDataGeneric places tuple e).hPhi phi hphi u hu
#print axioms genericPacketHullData_Phi_stable
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullPhiActual
