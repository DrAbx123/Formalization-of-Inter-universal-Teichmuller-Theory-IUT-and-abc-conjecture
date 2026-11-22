import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi single-point null measure V2

Generic B1 supplement with the current Mathlib `NullSingletonClass` API. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullV2Actual

theorem single_point_null {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.NullSingletonClass μ] (x : X) :
    μ ({x} : Set X) = 0 :=
  MeasureTheory.measure_singleton x

theorem finite_set_null {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.NullSingletonClass μ]
    (s : Finset X) : μ ((s : Set X)) = 0 :=
  s.measure_zero μ

end LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullV2Actual

end
