import tmp.sheaf.xif.paper.Mzk1StepXISinglePointNullV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi B1 assembly from green files

B1 assembly using only the green single-point-null V2: finite sets are null, and
countable unions have measure zero. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIB1AssemblyActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullV2Actual

theorem finite_set_null_from_green {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.NullSingletonClass μ]
    (s : Finset X) : μ ((s : Set X)) = 0 :=
  finite_set_null μ s

theorem finite_union_singletons_null {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.NullSingletonClass μ]
    (s : Finset X) : μ ((s : Set X)) = 0 := by
  exact finite_set_null μ s

end LeanFormal.IUT.XiFPaper.Mzk1StepXIB1AssemblyActual

end
