/- P6 generic PacketHullData nonempty (small). -/
import tmp.sheaf.xif.paper.Mzk1P6PacketHullGenericActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullNonemptyActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (places : Unit -> Unit -> FinitePlaceAtPrime K p) (tuple : Unit -> Unit)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type u} [Finite J] {E : J -> Type u}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
theorem genericPacketHullData_nonempty
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    Nonempty (PacketHullData places tuple (J := J) (E := E)) :=
  packetHullDataGeneric_nonempty places tuple e
#print axioms genericPacketHullData_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullNonemptyActual
