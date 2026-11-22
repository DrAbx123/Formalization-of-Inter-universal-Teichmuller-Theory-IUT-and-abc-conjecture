/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1BadPartLogScalingQpilotActual — bad-part log/normalized scaling (A661)

Logarithmic scaling laws for the bad-part candidate scaling `λ = a+b+c+1`:
`log(‖λ‖·R) = log‖λ‖ + log R` (R > 0) and the normalized form
`log((‖λ‖·R)/R) = log‖λ‖`; these are the per-coordinate logarithmic increments of
the scaled hull radius. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadPartLogScalingQpilotActual

/-- Log of the scaled positive radius is the sum of the log-norm and the log-radius. -/
theorem log_norm_mul_pos {lam R : Real} (hlam : lam ≠ 0) (hR : 0 < R) :
    Real.log (‖lam‖ * R) = Real.log ‖lam‖ + Real.log R := by
  rw [Real.log_mul (norm_ne_zero_iff.mpr hlam) (ne_of_gt hR)]

/-- Normalized form: `log((‖λ‖·R)/R) = log‖λ‖`. -/
theorem log_normalized_scale {lam R : Real} (hlam : lam ≠ 0) (hR : 0 < R) :
    Real.log ((‖lam‖ * R) / R) = Real.log ‖lam‖ := by
  rw [mul_div_cancel_right₀ _ (ne_of_gt hR)]

/-- The logarithmic increment is additive over the scaling element. -/
theorem log_scale_increment {lam1 lam2 R : Real}
    (h1 : lam1 ≠ 0) (h2 : lam2 ≠ 0) (hR : 0 < R) :
    Real.log (‖lam1 * lam2‖ * R) =
      Real.log ‖lam1‖ + Real.log ‖lam2‖ + Real.log R := by
  rw [norm_mul, Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr h1)
    (norm_ne_zero_iff.mpr h2)) (ne_of_gt hR), Real.log_mul
    (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]

/-- Rows for the bad-part log/normalized scaling. -/
def badPartLogRows : List (String × String) :=
  [ ("log(‖λ‖R) = log‖λ‖ + log R", "PROVED"),
    ("normalized log = log‖λ‖", "PROVED"),
    ("additive incremental law", "PROVED") ]

theorem badPartLogRows_length : badPartLogRows.length = 3 := rfl

#check log_norm_mul_pos
#check log_normalized_scale
#check log_scale_increment
#check badPartLogRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BadPartLogScalingQpilotActual
end
