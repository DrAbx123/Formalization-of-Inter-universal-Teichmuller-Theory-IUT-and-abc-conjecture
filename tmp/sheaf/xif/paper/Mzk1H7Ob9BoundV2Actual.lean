import Mathlib

/-!
# Mzk1H7Ob9BoundV2Actual — two-sided bounds with real composition theorems

Status: PENDING-VERIFY. No sorry, no axiom.
Two-sided rational bounds: transitivity, addition, and nonnegative scaling (real order proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H7Ob9BoundV2Actual

/-- Two-sided bound: lo ≤ x ≤ hi. -/
def TwoSidedBound (lo hi x : ℚ) : Prop := lo ≤ x ∧ x ≤ hi

/-- Genuine theorem: bounds compose by transitivity in the value. -/
theorem twoSidedBound_trans {lo hi x y : ℚ} (hx : TwoSidedBound lo hi x)
    (hxy : x ≤ y) (hy : y ≤ hi) : TwoSidedBound lo hi y :=
  ⟨le_trans hx.1 hxy, hy⟩

/-- Genuine theorem: two-sided bounds add. -/
theorem twoSidedBound_add {lo1 hi1 x1 lo2 hi2 x2 : ℚ}
    (h1 : TwoSidedBound lo1 hi1 x1) (h2 : TwoSidedBound lo2 hi2 x2) :
    TwoSidedBound (lo1 + lo2) (hi1 + hi2) (x1 + x2) :=
  ⟨add_le_add h1.1 h2.1, add_le_add h1.2 h2.2⟩

/-- Genuine theorem: nonnegative scaling preserves two-sided bounds. -/
theorem twoSidedBound_smul {lo hi x : ℚ} (h : TwoSidedBound lo hi x)
    {c : ℚ} (hc : 0 ≤ c) : TwoSidedBound (c * lo) (c * hi) (c * x) :=
  ⟨mul_le_mul_of_nonneg_left h.1 hc, mul_le_mul_of_nonneg_left h.2 hc⟩

end LeanFormal.IUT.XiFPaper.Mzk1H7Ob9BoundV2Actual
