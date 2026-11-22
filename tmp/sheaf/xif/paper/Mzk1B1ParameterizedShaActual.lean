import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

/-! # B1 parameterized assembly / coordinatewise zero-measure -/

namespace LeanFormal.IUT.XiFPaper.Mzk1B1ParameterizedShaActual

open MeasureTheory

/-- Coordinatewise zero measure for a finite family of zero-singleton measures. -/
theorem b1_coordinatewise_zero {ι α : Type*} [MeasurableSpace α]
    (μ : ι → Measure α) [forall i, MeasureTheory.NullSingletonClass (μ i)]
    (x : ι → α) :
    forall i, μ i {x i} = 0 :=
  fun i => MeasureTheory.measure_singleton (x i)

/-- B1 parameterized assembly: the range of a finite family has measure zero. -/
theorem b1_finite_range_zero {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.NullSingletonClass μ] (x : ι → α) :
    μ (Set.range x) = 0 :=
  Set.Countable.measure_zero (Set.countable_range x) μ

#print axioms b1_coordinatewise_zero
#print axioms b1_finite_range_zero

end LeanFormal.IUT.XiFPaper.Mzk1B1ParameterizedShaActual
