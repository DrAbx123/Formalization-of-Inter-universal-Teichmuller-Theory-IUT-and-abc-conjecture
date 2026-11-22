import tmp.sheaf.xif.paper.Mzk1FiniteStepSetGreenActual

/-! # Mzk1FiniteStepSetGreen2Actual — finite f4a chained over green lemmas (real)

Real Lean (no sorry/axiom): when alpha0 realises the maximal degree, the step-set degree is
bounded by maxDeg S (chained over the green step-set bound).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreen2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreenActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_le_green (S : Finset Qbar) (alpha0 : Qbar)
    (hdeg : degQ alpha0 = maxDeg S) :
    maxDeg (stepSet S alpha0) <= maxDeg S := by
  have h := maxDeg_stepSet_le_max_green S alpha0
  rw [hdeg, max_self] at h
  exact h

def finiteStepSetGreen2Rows : List (String × String) :=
  [ ("maxDeg_stepSet_le_green", "PROVED (finite f4a, chained)") ]

theorem finiteStepSetGreen2Rows_length : finiteStepSetGreen2Rows.length = 1 := rfl

#check maxDeg_stepSet_le_green

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreen2Actual
end
