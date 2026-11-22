import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImageActual
import tmp.sheaf.xif.paper.Mzk1FiniteConjBoundActual

/-! # Mzk1FiniteStepSetMaxDeg3Actual — unconditional finite step-set bound (real)

Real Lean (no sorry/axiom): the maximal degree of the paper's step set is always bounded by
max (maxDeg S) (degQ alpha0) — no relative assumption needed.  Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDeg3Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteConjBoundActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_le_max (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (stepSet S alpha0) <= max (maxDeg S) (degQ alpha0) := by
  unfold stepSet
  rw [maxDeg_union]
  apply max_le
  · apply maxDeg_image_le
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxC
    · have hxle : degQ x <= maxDeg S := by
        unfold maxDeg
        exact Finset.le_sup hxS
      exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) (le_trans hxle (le_max_left _ _))
    · exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x)
        (le_trans (degQ_le_of_mem_conjSet alpha0 x hxC) (le_max_right _ _))
  · apply maxDeg_image_le
    intro xi hxi
    have hroot := aeval_derivative_eq_zero_of_mem_critSet hxi
    exact le_trans (le_of_lt (degQ_critValue_lt alpha0 xi hroot)) (le_max_right _ _)

def finiteStepSetMaxDeg3Rows : List (String × String) :=
  [ ("maxDeg_stepSet_le_max", "PROVED (unconditional)") ]

theorem finiteStepSetMaxDeg3Rows_length : finiteStepSetMaxDeg3Rows.length = 1 := rfl

#check maxDeg_stepSet_le_max

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDeg3Actual
end
