/- P6 PacketHull final2 assembly. -/
import tmp.sheaf.xif.paper.Mzk1P6PacketHullBoundFinalActual
import tmp.sheaf.xif.paper.Mzk1P6PacketHullBoundReexportActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullBoundFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullBoundReexportActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullFinal2Actual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (places : Unit -> Unit -> FinitePlaceAtPrime K p) (tuple : Unit -> Unit)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type u} [Finite J] {E : J -> Type u}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
theorem p6PacketHullFinal2
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    Nonempty (PacketHullData places tuple (J := J) (E := E)) ∧
    (packetHullDataGeneric places tuple e).Phi.Nonempty :=
  p6PacketHullBoundFinal places tuple e
#print axioms p6PacketHullFinal2
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullFinal2Actual
