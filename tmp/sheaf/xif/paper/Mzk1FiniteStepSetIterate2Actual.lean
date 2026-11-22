import tmp.sheaf.xif.paper.Mzk1FiniteStepSetIterateActual

/-! # Mzk1FiniteStepSetIterate2Actual — iterated bound at max degree (real)

Real Lean (no sorry/axiom): when alpha0 realises the maximal degree, iterating the step set
never raises the maximal degree above maxDeg S.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterate2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterateActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_iterate_le_maxDeg (S : Finset Qbar) (alpha0 : Qbar)
    (hdeg : degQ alpha0 = maxDeg S) (n : Nat) :
    maxDeg (Nat.iterate (fun T => stepSet T alpha0) n S) <= maxDeg S := by
  have h : maxDeg S <= degQ alpha0 := le_of_eq hdeg.symm
  have hb := maxDeg_stepSet_iterate_le S alpha0 h n
  rw [hdeg] at hb
  exact hb

def finiteStepSetIterate2Rows : List (String × String) :=
  [ ("maxDeg_stepSet_iterate_le_maxDeg", "PROVED") ]

theorem finiteStepSetIterate2Rows_length : finiteStepSetIterate2Rows.length = 1 := rfl

#check maxDeg_stepSet_iterate_le_maxDeg

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterate2Actual
end
