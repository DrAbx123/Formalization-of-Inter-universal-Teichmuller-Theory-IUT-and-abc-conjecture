/- U-L: P6 pre-independent upper C1 on the actual packet.
Reuses actual root-parameter weight, Phi source/hull, StepV weighted average,
and the actual packet-hull Box bound; no hCor312. -/
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionSourceActual
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6ULPacketUpperActual

theorem uL_root_parameter_weight {p : Nat} {K : Type*} [NormedField K]
    (X : LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.DistinguishedScalarData p K) :
    LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.ord (K := K) p
        (LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.theta X.alpha X.j) =
      ((X.j : Real) ^ 2 / (2 * (X.l : Real))) *
        LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.ord (K := K) p X.q :=
  Mzk1P6RootParameterWeightActual.rootParameterWeight_eq_ord_varpi X

theorem uL_weighted_average
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.Icc 1 n,
          LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
            (2 * (n : Real) + 1) D Q S T j) ≤
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
          4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) :=
  Mzk1P6StepVAveragesActual.p6_stepVAverages_ivInequality n hn D Q S T hD hS hT

theorem uL_packet_hull_box
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (D : PacketHullData places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu] :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
      (packetHull (places := places) (tuple := tuple) D) ≤
      (-LocalFieldLogarithm.localNormOrder p D.varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ D.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  packetHull_normalizedLogVolume_le_box (places := places) (tuple := tuple) D

#print axioms uL_root_parameter_weight
#print axioms uL_weighted_average
#print axioms uL_packet_hull_box
end LeanFormal.IUT.XiFPaper.Mzk1P6ULPacketUpperActual
end
