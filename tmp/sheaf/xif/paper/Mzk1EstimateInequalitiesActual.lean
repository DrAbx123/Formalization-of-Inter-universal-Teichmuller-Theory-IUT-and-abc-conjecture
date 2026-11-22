import Mathlib

/-!
# Mzk1EstimateInequalitiesActual — elementary estimate inequalities (genuine)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Genuine rational inequalities used in log-volume/height-volume estimate bookkeeping. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1EstimateInequalitiesActual

/-- Squares are nonnegative (genuine). -/
theorem square_nonneg_bookkeeping (x : ℚ) : 0 ≤ x ^ 2 := sq_nonneg x

/-- 2ab <= a^2 + b^2 (genuine, from (a-b)^2 >= 0). -/
theorem two_mul_le_sq_add_sq (a b : ℚ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- ab <= (a^2 + b^2)/2 (genuine). -/
theorem mul_le_half_sq_add_sq (a b : ℚ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [two_mul_le_sq_add_sq a b]

/-- (a+b)^2 <= 2(a^2+b^2) (genuine). -/
theorem sq_add_le_two_sq_add_sq (a b : ℚ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [two_mul_le_sq_add_sq a b]

end LeanFormal.IUT.XiFPaper.Mzk1EstimateInequalitiesActual
