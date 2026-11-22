import tmp.sheaf.xif.paper.Mzk1FiniteStepSetMaxDegActual

/-! # Mzk1FiniteStepSetIterateActual — iterated step-set degree bound (real)

Real Lean (no sorry/axiom): if maxDeg S <= degQ alpha0, then every iterate of the paper's
step-set operator keeps maximal degree <= degQ alpha0.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterateActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDegActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_iterate_le (S : Finset Qbar) (alpha0 : Qbar)
    (h : maxDeg S <= degQ alpha0) (n : Nat) :
    maxDeg (Nat.iterate (fun T => stepSet T alpha0) n S) <= degQ alpha0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
      show maxDeg (stepSet (Nat.iterate (fun T => stepSet T alpha0) n S) alpha0) <= degQ alpha0
      exact maxDeg_stepSet_le_of_maxDeg_le _ alpha0 ih

def finiteStepSetIterateRows : List (String × String) :=
  [ ("maxDeg_stepSet_iterate_le", "PROVED (induction on iterations)") ]

theorem finiteStepSetIterateRows_length : finiteStepSetIterateRows.length = 1 := rfl

#check maxDeg_stepSet_iterate_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetIterateActual
end
