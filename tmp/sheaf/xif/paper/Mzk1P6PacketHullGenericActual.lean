/- Generic P6 PacketHullData constructor from an actual field-product equivalence. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
noncomputable section
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (places : Unit -> Unit -> FinitePlaceAtPrime K p) (tuple : Unit -> Unit)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type u} [Finite J] {E : J -> Type u}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
noncomputable def packetHullDataGeneric
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    PacketHullData places tuple (J := J) (E := E) where
  mu := MeasureTheory.Measure.addHaar
  inst := inferInstance
  e := e
  istar := Unit.unit
  varpi := 1
  hvarpi := one_ne_zero
  Phi := {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple ->
    phi u ∈ arithmeticTupleUnitLogLattice places tuple}
  hPhi_ne := ⟨LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple), by
    intro u hu; simpa using hu⟩
  hPhi := by intro phi hphi u hu; exact hphi u hu
  exceptional := Finset.univ
  small_outside := by intro i hi; exact absurd (Finset.mem_univ i) hi
theorem packetHullDataGeneric_nonempty
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    Nonempty (PacketHullData places tuple (J := J) (E := E)) :=
  ⟨packetHullDataGeneric places tuple e⟩
#print axioms packetHullDataGeneric
#print axioms packetHullDataGeneric_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
