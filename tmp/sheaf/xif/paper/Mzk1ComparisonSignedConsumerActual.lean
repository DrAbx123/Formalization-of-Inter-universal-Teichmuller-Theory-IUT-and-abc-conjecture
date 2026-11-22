/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#1: signed consumer of the q/theta comparison -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonSignedConsumerActual

/-- `q <= θ` with `q = -A`, `θ = -R` gives the signed inequality `-A <= -R`. -/
theorem signed_of_comparison {q θ A R : ℝ}
    (h : q ≤ θ) (hq : q = -A) (hθ : θ = -R) : -A ≤ -R := by
  linarith

/-- The same comparison gives `M = A - R >= 0`. -/
theorem M_nonneg_of_comparison {q θ A R : ℝ}
    (h : q ≤ θ) (hq : q = -A) (hθ : θ = -R) : 0 ≤ A - R := by
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonSignedConsumerActual