/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#1: general qTheta comparison named interface (GAP; no proof claimed) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeneralComparisonInterfaceActual

/-- Named general comparison: q-pilot reading ≤ theta-pilot reading.  This is the
missing paper-normalization comparison (#1); it is a Prop, not an assumption of a structure. -/
def GeneralQThetaComparison (qRead θRead : ℝ) : Prop :=
  qRead ≤ θRead

theorem GeneralQThetaComparison_iff (q θ : ℝ) :
    GeneralQThetaComparison q θ ↔ q ≤ θ := Iff.rfl

/-- Conditional consumer: no proof of the comparison is claimed. -/
theorem generalComparison_apply {q θ : ℝ} (h : GeneralQThetaComparison q θ) : q ≤ θ := h

end LeanFormal.IUT.XiFPaper.Mzk1GeneralComparisonInterfaceActual