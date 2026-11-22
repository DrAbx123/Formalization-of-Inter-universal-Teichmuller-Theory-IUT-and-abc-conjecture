/- P6 PacketHull final reexport. -/
import tmp.sheaf.xif.paper.Mzk1P6PacketHullBoundActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullGenericActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullBoundActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullBoundReexportActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (places : Unit -> Unit -> FinitePlaceAtPrime K p) (tuple : Unit -> Unit)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type u} [Finite J] {E : J -> Type u}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
theorem p6PacketHullBoundReexport
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    arithmeticTupleNormalizedLogVolume places tuple MeasureTheory.Measure.addHaar
      (packetHull (places := places) (tuple := tuple)
        (packetHullDataGeneric places tuple e)) ≤
      (-LocalFieldLogarithm.localNormOrder p
          (packetHullDataGeneric places tuple e).varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ (packetHullDataGeneric places tuple e).exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  genericPacketHull_bound places tuple e
#print axioms p6PacketHullBoundReexport
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullBoundReexportActual
