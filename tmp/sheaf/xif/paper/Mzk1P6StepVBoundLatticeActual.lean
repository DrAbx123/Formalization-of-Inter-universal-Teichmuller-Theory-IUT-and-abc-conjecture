/- P6 StepV bound from the actual tensor-core field-product witness (isolated). -/
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 8000000
noncomputable section
open scoped BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundLatticeActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
abbrev p6P (X : N8NativeInput l) : Nat := (completionRationalPrime (nativeFPlaceOverBad X)).val
abbrev p6Place (X : N8NativeInput l) : FinitePlaceAtPrime X.S.arithmetic.F (p6P X) :=
  ⟨nativeFPlaceOverBad X, rfl⟩
abbrev p6Places (X : N8NativeInput l) : PUnit -> PUnit -> FinitePlaceAtPrime X.S.arithmetic.F (p6P X) :=
  fun _ _ => p6Place X
abbrev p6Tuple (X : N8NativeInput l) : PUnit -> PUnit := fun _ => PUnit.unit
abbrev P6Block (X : N8NativeInput l) : Type :=
  ArithmeticTensorTupleBlock (K := X.S.arithmetic.F) (p := p6P X) (p6Places X) (p6Tuple X)
local instance p6BlockMeasurableSpace (X : N8NativeInput l) : MeasurableSpace (P6Block X) := borel _
local instance p6BlockBorelSpace (X : N8NativeInput l) : BorelSpace (P6Block X) := ⟨rfl⟩
noncomputable def p6Witness (X : N8NativeInput l) :
    TensorCoreWitness (p := p6P X) (p6Places X) (p6Tuple X) :=
  tensorCoreWitness (p := p6P X) (p6Places X) (p6Tuple X)
theorem p6_stepV_bound (X : N8NativeInput l) :
    arithmeticTupleNormalizedLogVolume (p := p6P X) (p6Places X) (p6Tuple X)
        MeasureTheory.Measure.addHaar
        (arithmeticTupleHolomorphicHull (p := p6P X) (p6Places X) (p6Tuple X)
          (p6Witness X).equiv
          (arithmeticTupleStepVPossibleImages (p := p6P X) (p6Places X) (p6Tuple X)
            PUnit.unit (nativeQActual X).q
            {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X) ->
              phi u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X)})) ≤
      (-LocalFieldLogarithm.localNormOrder (p6P X) (nativeQActual X).q +
          ∑ i, LocalFieldLogarithm.localNormOrder (p6P X)
            (arithmeticTupleLocalDifferent (p6Places X) (p6Tuple X) i) + 1) * Real.log (p6P X) +
        ∑ i ∈ (Finset.univ : Finset PUnit), (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (p6Places X i (p6Tuple X i))) (p := p6P X) : Real)) := by
  let W := p6Witness X
  letI : Fintype W.J := W.fintype
  letI (j : W.J) : NontriviallyNormedField (W.E j) := W.field j
  letI (j : W.J) : NormedAlgebra ℚ_[p6P X] (W.E j) := W.alg j
  letI (j : W.J) : FiniteDimensional ℚ_[p6P X] (W.E j) := W.finite j
  letI (j : W.J) : ProperSpace (W.E j) := FiniteDimensional.proper ℚ_[p6P X] (W.E j)
  exact arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound
    (p := p6P X) (places := p6Places X) (tuple := p6Tuple X)
    (μ := MeasureTheory.Measure.addHaar) (e := W.equiv)
    PUnit.unit (nativeQActual X).q (nativeQActual X).q_ne_zero
    {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X) ->
      phi u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X)}
    ⟨LinearEquiv.refl ℚ_[p6P X] (P6Block X), by intro u hu; simpa using hu⟩
    (by intro phi hphi u hu; exact hphi u hu)
    Finset.univ (by intro i hi; exact absurd (Finset.mem_univ i) hi)
#print axioms p6_stepV_bound
end LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundLatticeActual
