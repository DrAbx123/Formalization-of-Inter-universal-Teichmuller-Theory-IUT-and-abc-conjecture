/- P6 PackageHull final: bound + Phi stability consumer. -/
import tmp.sheaf.xif.paper.Mzk1P6PacketHullBoundActual
import tmp.sheaf.xif.paper.Mzk1P6PacketHullPhiActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullPhiActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullFinalActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (places : Unit -> Unit -> FinitePlaceAtPrime K p) (tuple : Unit -> Unit)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type u} [Finite J] {E : J -> Type u}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
theorem p6PacketHullFinal
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    (packetHullDataGeneric places tuple e).Phi.Nonempty ∧
    arithmeticTupleNormalizedLogVolume places tuple MeasureTheory.Measure.addHaar
      (packetHull (places := places) (tuple := tuple)
        (packetHullDataGeneric places tuple e)) ≤
      (-LocalFieldLogarithm.localNormOrder p
          (packetHullDataGeneric places tuple e).varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ (packetHullDataGeneric places tuple e).exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real))) := by
  exact ⟨genericPacketHullData_Phi_nonempty places tuple e,
    genericPacketHull_bound places tuple e⟩
#print axioms p6PacketHullFinal
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullFinalActual
