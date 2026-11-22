/- P6 IV/display assembly: Thm 1.10 final display packaged with the actual
StepV hull bound consumer. -/
import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import Mathlib.Tactic
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundConsumerActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayAssemblyActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι -> Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- P6 IV/display assembly: exact Thm 1.10 final display and the actual
StepV hull bound, from the accepted P6 display and StepV consumers. -/
theorem p6_iv_display_assembly
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    {J : Type (max u v)} [Fintype J] {E : J -> Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j))
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hPhi_ne : Phi.Nonempty)
    (hPhi : ∀ phi ∈ Phi, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      phi u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional ->
      logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    (thm110Lhs T ≤ thm110Rhs T) ∧
      arithmeticTupleNormalizedLogVolume places tuple MeasureTheory.Measure.addHaar
          (arithmeticTupleHolomorphicHull places tuple e
            (arithmeticTupleStepVPossibleImages places tuple istar varpi Phi)) ≤
        (-localNormOrder p varpi +
            ∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i) + 1) *
          Real.log (p : Real) +
          ∑ i ∈ exceptional, (3 + Real.log
            (logShellRamificationExponent
              (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  ⟨p6_thm110_display T hl hd hS hE hCor312,
    p6_stepV_bound_consumer places tuple e istar varpi hvarpi Phi hPhi_ne hPhi
      exceptional small_outside⟩
#print axioms p6_iv_display_assembly
end LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayAssemblyActual
end