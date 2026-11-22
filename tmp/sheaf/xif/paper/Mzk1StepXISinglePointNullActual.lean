import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi single-point null measure

Generic B1 supplement: singletons are null for a measure with no atoms. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullActual

theorem single_point_null {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.NoAtoms μ] (x : X) :
    μ ({x} : Set X) = 0 :=
  MeasureTheory.measure_singleton x

end LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullActual

end
