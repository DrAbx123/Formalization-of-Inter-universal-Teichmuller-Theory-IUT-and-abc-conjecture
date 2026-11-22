import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi bad part / log / normalized scaling pieces

Algebraic pieces of the scaling comparison: bad inverse, logarithmic scale, and
normalized scale, with their basic identities. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartLogNormalizedActual

def badPart (c : Real) : Real := c⁻¹

def logScale (c : Real) : Real := Real.log c

def normalizedScale (c : Real) : Real := c / Real.log c

theorem badPart_mul_cancel {c : Real} (hc : c ≠ 0) : badPart c * c = 1 := by
  unfold badPart
  field_simp

theorem normalizedScale_eq (c : Real) :
    normalizedScale c = c / logScale c := rfl

theorem logScale_exp (x : Real) : logScale (Real.exp x) = x := by
  unfold logScale
  exact Real.log_exp x

theorem logScale_pos {c : Real} (hc : 1 < c) : 0 < logScale c := by
  unfold logScale
  exact Real.log_pos hc

end LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartLogNormalizedActual

end
