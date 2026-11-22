/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/NORM-ARCH-C: product arithmetic of the q-side and arch-side factors -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchFactorProductActual

/-- The q-side factor `1/(2l)` cancels the `2l` scaling. -/
theorem qSideFactor_mul_two (l : ℕ) (hl : (l : ℝ) ≠ 0) :
    (1 / (2 * (l : ℝ))) * (2 * (l : ℝ)) = 1 := by
  field_simp [hl]

/-- The q-side factor equals the rational arch factor `1` iff `l = 1/2` (as a real). -/
theorem qSideFactor_eq_one_iff {l : ℕ} (hl : (l : ℝ) ≠ 0) :
    (1 / (2 * (l : ℝ))) = 1 ↔ (l : ℝ) = 1 / 2 := by
  constructor
  · intro h
    have h2 : (2 * (l : ℝ)) ≠ 0 := by positivity
    field_simp [hl] at h
    linarith
  · intro h
    rw [h]
    norm_num
end LeanFormal.IUT.XiFPaper.Mzk1ArchFactorProductActual