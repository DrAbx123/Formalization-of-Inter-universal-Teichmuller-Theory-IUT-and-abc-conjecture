/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P6/P7: nonnegativity of the quantitative target M = A - R -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1QuantitativeTargetNonnegActual

/-- If `A >= 0` and `R <= 0`, then `M = A - R >= 0`. -/
theorem M_nonneg_of_A_nonneg_R_nonpos {A R : ℝ}
    (hA : 0 ≤ A) (hR : R ≤ 0) : 0 ≤ A - R := by linarith

/-- If `R <= 0` and `M = A - R`, then `A <= M`. -/
theorem A_le_M_of_R_nonpos {A R M : ℝ}
    (hR : R ≤ 0) (hM : M = A - R) : A ≤ M := by linarith

/-- If `0 <= A - R` and `A <= 0`, then `R <= 0`. -/
theorem R_nonpos_of_M_nonneg_A_nonpos {A R : ℝ}
    (hM : 0 ≤ A - R) (hA : A ≤ 0) : R ≤ 0 := by linarith

end LeanFormal.IUT.XiFPaper.Mzk1QuantitativeTargetNonnegActual