/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/NORM-ARCH-C: comparison arithmetic for q-side vs arch-side factors -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchFactorComparisonActual

/-- For `l >= 1`, the q-side factor is strictly less than the arch factor 1. -/
theorem qSideFactor_lt_one {l : ℕ} (hl : 1 ≤ l) :
    (1 : ℝ) / (2 * (l : ℝ)) < 1 := by
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  rw [div_lt_one (by positivity)]
  have : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  linarith

/-- For `l >= 1`, the q-side factor is nonzero. -/
theorem qSideFactor_ne_zero {l : ℕ} (hl : 1 ≤ l) :
    (1 : ℝ) / (2 * (l : ℝ)) ≠ 0 := by
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  positivity

end LeanFormal.IUT.XiFPaper.Mzk1ArchFactorComparisonActual