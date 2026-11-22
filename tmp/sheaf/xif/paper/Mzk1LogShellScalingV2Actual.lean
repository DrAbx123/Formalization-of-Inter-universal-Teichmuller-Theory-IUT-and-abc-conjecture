import Mathlib

/-!
# Mzk1LogShellScalingV2Actual — scaling action of ℕ on ℚ (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Natural-number scaling action on rationals: multiplicativity/one/monotonicity (real algebra). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellScalingV2Actual

/-- Scaling by a natural number on ℚ. -/
def scale (n : ℕ) (x : ℚ) : ℚ := n * x

/-- Genuine theorem: scaling is multiplicative. -/
theorem scale_mul (m n : ℕ) (x : ℚ) : scale (m * n) x = scale m (scale n x) := by
  unfold scale
  push_cast
  ring

/-- Genuine theorem: scaling by one is the identity. -/
theorem scale_one (x : ℚ) : scale 1 x = x := by
  unfold scale
  ring

/-- Genuine theorem: scaling by a nonnegative rational preserves order. -/
theorem scale_monotone (n : ℕ) : Monotone (scale n) := by
  intro a b hab
  unfold scale
  exact mul_le_mul_of_nonneg_left hab (by positivity)

end LeanFormal.IUT.XiFPaper.Mzk1LogShellScalingV2Actual
