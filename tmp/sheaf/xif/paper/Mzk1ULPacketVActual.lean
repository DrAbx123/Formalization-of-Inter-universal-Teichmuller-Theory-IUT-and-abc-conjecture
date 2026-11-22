import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundConsumerActual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type (max u v)} [Fintype J] {E : J → Type (max u v)}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
/-- Actual per-packet normalized log-volume `V_a`. -/
noncomputable def packetV
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)) : Real :=
  arithmeticTupleNormalizedLogVolume places tuple MeasureTheory.Measure.addHaar
    (arithmeticTupleHolomorphicHull places tuple e
      (arithmeticTupleStepVPossibleImages places tuple istar varpi Phi))
/-- Actual per-packet paper bound `B_a` (C1 formula). -/
noncomputable def packetB
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) : Real :=
  (-localNormOrder p varpi +
      ∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i) + 1) *
      Real.log (p : Real) +
    ∑ i ∈ exceptional, (3 + Real.log
      (logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real))
/-- Actual U-L packet bound: `V_a <= B_a`, from the accepted StepV consumer.

The distinguished representative `varpi` is an actual nonzero element of the
distinguished completion slot.  For the `θ`-pilot `ϖ = θ_j` the representative
lives in the split Tate / value-group carrier built by the U-R root carrier
(kurt): a completion `2l`-th root does not exist
(`S342QVFamilyRootImpossibleActual`), so no completion `DistinguishedScalarData`
is asserted here.  Once kurt's carrier provides `ϖ`, this theorem applies
verbatim. -/
theorem packetV_le_packetB
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
    packetV places tuple e istar varpi Phi ≤
      packetB places tuple istar varpi exceptional :=
  p6_stepV_bound_consumer places tuple e istar varpi hvarpi Phi hPhi_ne hPhi
    exceptional small_outside
variable {istar : ι}
/-- The actual exceptional index set: places where the shell ramification
exponent exceeds `p - 2`.  This is a definition, not a hypothesis. -/
noncomputable def packetExceptional : Finset ι :=
  Finset.univ.filter (fun i =>
    p - 2 < logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))
/-- Outside the defined exceptional set the shell exponent is `≤ p - 2`. -/
theorem packetExceptional_small_outside
    (i : ι) (hi : i ∉ packetExceptional (p := p) places tuple) :
    logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2 := by
  by_contra hle
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Nat.lt_of_not_le hle⟩)
#print axioms packetV_le_packetB
#print axioms packetExceptional_small_outside
end LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
end
