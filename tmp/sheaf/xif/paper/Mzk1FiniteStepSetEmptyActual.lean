import tmp.sheaf.xif.paper.Mzk1FiniteStepSetGreenActual
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureEmptyActual

/-! # Mzk1FiniteStepSetEmptyActual — empty-set step degree bound (real)

Real Lean (no sorry/axiom): the step set of the empty set has maximal degree at most
degQ alpha0 (in particular at most max 1 (degQ alpha0)).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetEmptyActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreenActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEmptyActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_empty_le (alpha0 : Qbar) :
    maxDeg (stepSet (∅ : Finset Qbar) alpha0) <= degQ alpha0 := by
  have hmax0 : maxDeg (∅ : Finset Qbar) = 0 := by
    unfold maxDeg
    simp
  have h := maxDeg_stepSet_le_max_green (∅ : Finset Qbar) alpha0
  rw [hmax0, Nat.zero_max] at h
  exact h

theorem maxDeg_stepSet_empty_le_one (alpha0 : Qbar) :
    maxDeg (stepSet (∅ : Finset Qbar) alpha0) <= max 1 (degQ alpha0) :=
  le_trans (maxDeg_stepSet_empty_le alpha0) (le_max_right _ _)

def finiteStepSetEmptyRows : List (String × String) :=
  [ ("maxDeg_stepSet_empty_le", "PROVED"), ("maxDeg_stepSet_empty_le_one", "PROVED") ]

theorem finiteStepSetEmptyRows_length : finiteStepSetEmptyRows.length = 2 := rfl

#check maxDeg_stepSet_empty_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetEmptyActual
end
