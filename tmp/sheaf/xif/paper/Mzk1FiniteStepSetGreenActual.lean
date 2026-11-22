import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImageActual
import tmp.sheaf.xif.paper.Mzk1FiniteConjBoundActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetGreenActual — step-set degree bound chained over green lemmas

Real Lean (no sorry/axiom): unconditional bound maxDeg (stepSet S alpha0) <=
max (maxDeg S) (degQ alpha0), chained from the PROVED maxDeg_image_le (green),
degQ_aeval_le and degQ_critValue_lt (green).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreenActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_union_green (S T : Finset Qbar) :
    maxDeg (S ∪ T) = max (maxDeg S) (maxDeg T) := by
  unfold maxDeg
  rw [Finset.sup_union]

theorem maxDeg_stepSet_le_max_green (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (stepSet S alpha0) <= max (maxDeg S) (degQ alpha0) := by
  unfold stepSet
  rw [maxDeg_union_green]
  apply max_le
  · apply maxDeg_image_le
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxC
    · have hxle : degQ x <= maxDeg S := by
        unfold maxDeg
        exact Finset.le_sup hxS
      exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) (le_trans hxle (le_max_left _ _))
    · have hroot : aeval x (minpoly ℚ alpha0) = 0 := mem_conjSet_iff.mp hxC
      have hdvd : minpoly ℚ x ∣ minpoly ℚ alpha0 := minpoly.dvd ℚ x hroot
      have hne : minpoly ℚ alpha0 ≠ 0 := minpoly.ne_zero (isIntegral_Qbar alpha0)
      have hle : degQ x <= degQ alpha0 := Polynomial.natDegree_le_of_dvd hdvd hne
      exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) (le_trans hle (le_max_right _ _))
  · apply maxDeg_image_le
    intro xi hxi
    have hroot := aeval_derivative_eq_zero_of_mem_critSet hxi
    exact le_trans (le_of_lt (degQ_critValue_lt alpha0 xi hroot)) (le_max_right _ _)

def finiteStepSetGreenRows : List (String × String) :=
  [ ("maxDeg_stepSet_le_max_green", "PROVED (chained green lemmas)") ]

theorem finiteStepSetGreenRows_length : finiteStepSetGreenRows.length = 1 := rfl

#check maxDeg_stepSet_le_max_green

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetGreenActual
end
