/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: signed-target arithmetic for Cor 3.12 -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedArithmeticActual

/-- The target `M >= 0` in signed form: `-A <= -R`. -/
theorem targetSigned_iff_M_nonneg {A R : ℝ} : -A ≤ -R ↔ 0 ≤ A - R := by
  constructor <;> intro h <;> linarith

/-- `M = A - R` nonnegative iff `R <= A`. -/
theorem M_nonneg_iff_R_le_A {A R : ℝ} : 0 ≤ A - R ↔ R ≤ A := by
  constructor <;> intro h <;> linarith

/-- The signed q/theta comparison `qRead <= thetaRead` is `M >= 0` when
`qRead = -A`, `thetaRead = -R`. -/
theorem comparison_iff_M_nonneg {q θ A R : ℝ}
    (hq : q = -A) (hθ : θ = -R) : q ≤ θ ↔ 0 ≤ A - R := by
  rw [hq, hθ, targetSigned_iff_M_nonneg]

end LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedArithmeticActual