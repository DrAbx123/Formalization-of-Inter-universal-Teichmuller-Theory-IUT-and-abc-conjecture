/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#1: elementary arithmetic for the comparison-gap interface -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonGapArithmeticActual

/-- The comparison `qRead <= thetaRead` is equivalent to a nonnegative gap. -/
theorem le_iff_zero_le_sub {q θ : ℝ} : q ≤ θ ↔ 0 ≤ θ - q := by
  constructor <;> intro h <;> linarith

/-- It is also equivalent to the signed inequality `-θ <= -q`. -/
theorem le_iff_neg_le_neg {q θ : ℝ} : q ≤ θ ↔ -θ ≤ -q := by
  constructor <;> intro h <;> linarith

/-- The `M = A - R` form: `-A <= -R` iff `0 <= A - R`. -/
theorem neg_le_neg_iff_zero_le {A R : ℝ} : -A ≤ -R ↔ 0 ≤ A - R := by
  constructor <;> intro h <;> linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonGapArithmeticActual