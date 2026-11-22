import tmp.sheaf.xif.paper.Mzk1StepXIBadPartLogNormalizedActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi badPart arithmetic identities

Multiplicative and inverse identities for the bad inverse scaling factor. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartArithmeticActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartLogNormalizedActual

theorem badPart_mul {c d : Real} (hc : c ≠ 0) (hd : d ≠ 0) :
    badPart (c * d) = badPart c * badPart d := by
  unfold badPart
  field_simp

theorem badPart_inv {c : Real} (hc : c ≠ 0) : badPart c⁻¹ = c := by
  unfold badPart
  field_simp

theorem badPart_pos {c : Real} (hc : 0 < c) : 0 < badPart c := by
  unfold badPart
  positivity

theorem normalizedScale_mul_log {c : Real} (hc : Real.log c ≠ 0) :
    normalizedScale c * logScale c = c := by
  unfold normalizedScale logScale
  field_simp

end LeanFormal.IUT.XiFPaper.Mzk1StepXIBadPartArithmeticActual

end
