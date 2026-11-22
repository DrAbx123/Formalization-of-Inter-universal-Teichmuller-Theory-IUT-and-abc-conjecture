import tmp.sheaf.xif.paper.Mzk1P6StepVESupportFinalAct
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVESupportFinalAct

namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundConsumerActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- Consumer of the accepted StepV hull bound, for any actual field-product
decomposition `e` of the tensor block. -/
theorem p6_stepV_bound_consumer
    {J : Type (max u v)} [Fintype J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hPhi_ne : Phi.Nonempty)
    (hPhi : ∀ phi ∈ Phi, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      phi u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    arithmeticTupleNormalizedLogVolume places tuple MeasureTheory.Measure.addHaar
        (arithmeticTupleHolomorphicHull places tuple e
          (arithmeticTupleStepVPossibleImages places tuple istar varpi Phi)) ≤
      (-localNormOrder p varpi +
          ∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i) + 1) *
        Real.log (p : Real) +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound places tuple
    MeasureTheory.Measure.addHaar e istar varpi hvarpi Phi hPhi_ne hPhi exceptional small_outside

#print axioms p6_stepV_bound_consumer

end LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundConsumerActual
end