/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1Gap2ArithmeticQpilotActual — Gap2 arithmeticization (A681)

Arithmetic consequences of the Gap-2 shape: ratio form for positive weight, log
form for positive slack, and the minimal additive constant `v − (1+ε)w − θ`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticQpilotActual

/-- Gap-2 ratio form: for positive weight, `(v − θ − D)/w ≤ 1+ε`. -/
theorem gap2_arith_ratio {v w theta D epsilon : Real} (hw : 0 < w)
    (h : v ≤ (1 + epsilon) * w + theta + D) :
    (v - theta - D) / w ≤ 1 + epsilon := by
  rw [div_le_iff₀ hw]
  linarith

/-- Gap-2 log form: for positive slack, `log(v − θ − D) ≤ log(1+ε) + log w`. -/
theorem gap2_arith_log {v w theta D epsilon : Real} (hw : 0 < w)
    (hslack : 0 < v - theta - D) (heps : 0 < 1 + epsilon)
    (h : v ≤ (1 + epsilon) * w + theta + D) :
    Real.log (v - theta - D) ≤ Real.log (1 + epsilon) + Real.log w := by
  have hle : v - theta - D ≤ (1 + epsilon) * w := by linarith
  calc Real.log (v - theta - D) ≤ Real.log ((1 + epsilon) * w) :=
        Real.log_le_log hslack hle
    _ = Real.log (1 + epsilon) + Real.log w :=
        Real.log_mul (ne_of_gt heps) (ne_of_gt hw)

/-- The minimal additive constant `v − (1+ε)w − θ` always works. -/
theorem gap2_minimal_D (v w theta epsilon : Real) :
    ∃ D : Real, v ≤ (1 + epsilon) * w + theta + D :=
  ⟨v - (1 + epsilon) * w - theta, by linarith⟩

/-- Any additive constant is at least the minimal one. -/
theorem gap2_minimal_D_is_min {v w theta D epsilon : Real}
    (h : v ≤ (1 + epsilon) * w + theta + D) :
    v - (1 + epsilon) * w - theta ≤ D := by
  linarith

/-- Gap-2 arithmetic rows. -/
def gap2ArithmeticRows : List (String × String) :=
  [ ("ratio form", "PROVED"),
    ("log form", "PROVED"),
    ("minimal D exists", "PROVED"),
    ("minimal D is minimal", "PROVED") ]

theorem gap2ArithmeticRows_length : gap2ArithmeticRows.length = 4 := rfl

#check gap2_arith_ratio
#check gap2_arith_log
#check gap2_minimal_D_is_min
#check gap2ArithmeticRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticQpilotActual
end
