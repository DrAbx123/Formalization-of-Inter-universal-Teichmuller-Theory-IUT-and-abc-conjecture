import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImageActual
import tmp.sheaf.xif.paper.Mzk1FiniteConjBoundActual

/-! # Mzk1FiniteStepSetMaxDegActual — finite step-set degree bound (real)

Real Lean (no sorry/axiom): if the maximal degree of S is at most degQ alpha0, then the
paper's step set S' = f0(S ∪ conjugates) ∪ f0(critical points) has maximal degree at most
degQ alpha0.  Uses the PROVED degQ_aeval_le, the conjugate bound (minpoly divisibility) and
degQ_critValue_lt.  This is a genuine finite-level ingredient of f4a.  Registry 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDegActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteConjBoundActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_stepSet_le_of_maxDeg_le (S : Finset Qbar) (alpha0 : Qbar)
    (h : maxDeg S <= degQ alpha0) :
    maxDeg (stepSet S alpha0) <= degQ alpha0 := by
  unfold stepSet
  rw [maxDeg_union]
  apply max_le
  · apply maxDeg_image_le
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxC
    · have hxle : degQ x <= maxDeg S := by
        unfold maxDeg
        exact Finset.le_sup hxS
      exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) (le_trans hxle h)
    · exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) (degQ_le_of_mem_conjSet alpha0 x hxC)
  · apply maxDeg_image_le
    intro xi hxi
    have hroot := aeval_derivative_eq_zero_of_mem_critSet hxi
    exact le_of_lt (degQ_critValue_lt alpha0 xi hroot)

def finiteStepSetMaxDegRows : List (String × String) :=
  [ ("maxDeg_stepSet_le_of_maxDeg_le", "PROVED (aeval/conj/crit bounds)") ]

theorem finiteStepSetMaxDegRows_length : finiteStepSetMaxDegRows.length = 1 := rfl

#check maxDeg_stepSet_le_of_maxDeg_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMaxDegActual
end
