import tmp.sheaf.xif.paper.Mzk1FiniteStepSetMaxDegActual

/-! # Mzk1FiniteStepSetMaxDeg2Actual — finite f4a (real)

Real Lean (no sorry/axiom): the maximal degree of the paper's step set is bounded by the
maximal degree of S, when alpha0 realizes the maximal degree.  This is the finite-level f4a
statement of the Problem C nested induction.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDeg2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDegActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_le (S : Finset Qbar) (alpha0 : Qbar)
    (hdeg : degQ alpha0 = maxDeg S) :
    maxDeg (stepSet S alpha0) <= maxDeg S := by
  have h : maxDeg S <= degQ alpha0 := le_of_eq hdeg.symm
  exact maxDeg_stepSet_le_of_maxDeg_le S alpha0 h

/-- Consumer: with maxDeg bound, the step set stays within the max degree class. -/
theorem maxDeg_stepSet_le_consumer (S : Finset Qbar) (alpha0 : Qbar)
    (halpha0 : alpha0 ∈ S) (hdeg : degQ alpha0 = maxDeg S) :
    maxDeg (stepSet S alpha0) <= maxDeg S :=
  maxDeg_stepSet_le S alpha0 hdeg

def finiteStepSetMaxDeg2Rows : List (String × String) :=
  [ ("maxDeg_stepSet_le", "PROVED (finite f4a)"),
    ("maxDeg_stepSet_le_consumer", "PROVED") ]

theorem finiteStepSetMaxDeg2Rows_length : finiteStepSetMaxDeg2Rows.length = 2 := rfl

#check maxDeg_stepSet_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDeg2Actual
end
