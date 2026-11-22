import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic
/-! IUT IV Prop 1.4(iii) → Box (11), using the actual LeanFormal tensor proof.

This re-exports `LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTuple_stepV_normalizedLogVolume_le_paperBound`,
whose proof already constructs the actual different generators, the tensor container and the
component volume estimate, without importing the Iut library. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxFormalActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p) (tuple : (i : ι) -> V i)
/-- The paper's Box (11) bound for the actual tensor block. -/
theorem prop14iii_box_formal [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hPhi : forall phi, (phi ∈ Phi) -> forall u, (u ∈ arithmeticTupleUnitLogLattice places tuple) ->
      phi u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : forall i, i ∉ exceptional ->
      LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2)
    {S : Set (ArithmeticTensorTupleBlock places tuple)} (hSpos : 0 < mu S)
    (hS : forall s, (s ∈ S) -> exists phi, (phi ∈ Phi) ∧ exists x, (x ∈ arithmeticTupleCanonicalUnitReference places tuple) ∧
      s = phi (arithmeticTupleTprod places tuple (Function.update 1 istar varpi) * x)) :
    arithmeticTupleNormalizedLogVolume places tuple mu S ≤
      (-LocalFieldLogarithm.localNormOrder p varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalDifferent places tuple i) +
          1) * Real.log p +
        ∑ i ∈ exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  arithmeticTuple_stepV_normalizedLogVolume_le_paperBound places tuple mu istar varpi
    hvarpi Phi hPhi exceptional small_outside hSpos hS
end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxFormalActual
end
