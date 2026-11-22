import tmp.sheaf.xif.paper.Mzk1FiniteStepSetMaxDeg3Actual

/-! # Mzk1FiniteStepSetIterate3Actual — unconditional iterated bound (real)

Real Lean (no sorry/axiom): every iterate of the paper's step-set operator has maximal degree
bounded by max (maxDeg S) (degQ alpha0).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterate3Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDeg3Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_iterate_le_max (S : Finset Qbar) (alpha0 : Qbar) (n : Nat) :
    maxDeg (Nat.iterate (fun T => stepSet T alpha0) n S)
      <= max (maxDeg S) (degQ alpha0) := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
      show maxDeg (stepSet (Nat.iterate (fun T => stepSet T alpha0) n S) alpha0)
        <= max (maxDeg S) (degQ alpha0)
      exact le_trans (maxDeg_stepSet_le_max _ alpha0)
        (max_le ih (le_max_right _ _))

def finiteStepSetIterate3Rows : List (String × String) :=
  [ ("maxDeg_stepSet_iterate_le_max", "PROVED (unconditional induction)") ]

theorem finiteStepSetIterate3Rows_length : finiteStepSetIterate3Rows.length = 1 := rfl

#check maxDeg_stepSet_iterate_le_max

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterate3Actual
end
