/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P6: arithmetic of the paper normalization `logQ/(2l)` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperLogQArithActual

/-- The paper normalization factor. -/
noncomputable def paperQAbsLogArith (l : ℕ) (logQ : ℝ) : ℝ :=
  logQ / (2 * (l : ℝ))

/-- Multiplying the normalized value by `2l` recovers `logQ` (l ≠ 0). -/
theorem two_l_mul_paperQAbsLogArith {l : ℕ} (hl : (l : ℝ) ≠ 0) (logQ : ℝ) :
    2 * (l : ℝ) * paperQAbsLogArith l logQ = logQ := by
  unfold paperQAbsLogArith
  field_simp [hl]

/-- The canonical logQ `2l*x` normalizes back to `x`. -/
theorem paperQAbsLogArith_two_l_mul {l : ℕ} (hl : (l : ℝ) ≠ 0) (x : ℝ) :
    paperQAbsLogArith l (2 * (l : ℝ) * x) = x := by
  unfold paperQAbsLogArith
  field_simp [hl]

end LeanFormal.IUT.XiFPaper.Mzk1PaperLogQArithActual