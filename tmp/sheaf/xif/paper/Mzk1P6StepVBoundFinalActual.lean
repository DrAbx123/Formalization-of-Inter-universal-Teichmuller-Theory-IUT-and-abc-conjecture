/- P6 StepV bound from isolated source fields + actual witness. -/
import tmp.sheaf.xif.paper.Mzk1P6SourceFieldsActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundFinalActual
variable {l : LeanFormal.IUT.PrimeGeFive} (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l)
theorem p6_stepV_bound (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) :
    arithmeticTupleNormalizedLogVolume (p := p6P X) (p6Places X) (p6Tuple X)
        MeasureTheory.Measure.addHaar
        (arithmeticTupleHolomorphicHull (p := p6P X) (p6Places X) (p6Tuple X)
          (p6Witness X).equiv
          (arithmeticTupleStepVPossibleImages (p := p6P X) (p6Places X) (p6Tuple X)
            Unit.unit (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q
            {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X) ->
              phi u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X)})) ≤
      (-LocalFieldLogarithm.localNormOrder (p6P X) (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q +
          ∑ i, LocalFieldLogarithm.localNormOrder (p6P X)
            (arithmeticTupleLocalDifferent (p6Places X) (p6Tuple X) i) + 1) * Real.log (p6P X) +
        ∑ i ∈ (Finset.univ : Finset Unit), (3 + Real.log
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
    Unit.unit (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q_ne_zero
    {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X) ->
      phi u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X)}
    ⟨LinearEquiv.refl ℚ_[p6P X] (P6Block X), by intro u hu; simpa using hu⟩
    (by intro phi hphi u hu; exact hphi u hu)
    Finset.univ (by intro i hi; exact absurd (Finset.mem_univ i) hi)
#print axioms p6_stepV_bound
end LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundFinalActual
