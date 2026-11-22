/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GeneralComparisonInterfaceActual
import Mathlib.Tactic

/-! # P7/#1: consumer of the general comparison in `M = A - R` form -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GeneralComparisonConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1GeneralComparisonInterfaceActual

/-- If the general comparison holds with `q = -A`, `theta = -R`, then `M >= 0`. -/
theorem generalComparison_imp_M_nonneg {q θ A R : ℝ}
    (h : GeneralQThetaComparison q θ) (hq : q = -A) (hθ : θ = -R) :
    0 ≤ A - R := by
  unfold GeneralQThetaComparison at h
  linarith

/-- Contrapositive form: if `M < 0`, the general comparison fails. -/
theorem not_comparison_of_M_neg {q θ A R : ℝ}
    (hq : q = -A) (hθ : θ = -R) (hM : A - R < 0) :
    ¬ GeneralQThetaComparison q θ := by
  intro h
  have := generalComparison_imp_M_nonneg h hq hθ
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1GeneralComparisonConsumerActual