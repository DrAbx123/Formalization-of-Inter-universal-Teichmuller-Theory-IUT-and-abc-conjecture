/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P6/P7: quantitative target chain arithmetic -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1QuantitativeTargetChainActual

/-- `M = A - R`; `M >= 0` iff `A >= R`. -/
theorem M_nonneg_iff_A_ge_R {A R : ℝ} : 0 ≤ A - R ↔ R ≤ A := by
  constructor <;> intro h <;> linarith

/-- With `R = -log μ` and `A = |log q|`: `M >= 0` iff `-A <= log μ`. -/
theorem M_nonneg_iff_neg_le_log {A logmu : ℝ} : 0 ≤ A - (-logmu) ↔ -A ≤ logmu := by
  constructor <;> intro h <;> linarith

/-- Signed form: `-A <= -R` iff `M >= 0`. -/
theorem signed_iff_M_nonneg {A R : ℝ} : -A ≤ -R ↔ 0 ≤ A - R := by
  constructor <;> intro h <;> linarith

end LeanFormal.IUT.XiFPaper.Mzk1QuantitativeTargetChainActual