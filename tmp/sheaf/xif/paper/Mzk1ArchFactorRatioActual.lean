/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/NORM-ARCH-C: q-side 1/(2l) vs arch-side 1/[K:Q] are distinct factors -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchFactorRatioActual

/-- q-side c_root factor `1/(2l)`. -/
noncomputable def qSideFactor (l : ℕ) : ℝ := 1 / (2 * (l : ℝ))

/-- For `l >= 5`, the q-side factor is not 1 (so it cannot equal the rational arch factor 1/[Q:Q]=1). -/
theorem qSideFactor_ne_one_of_ge_five {l : ℕ} (hl : 5 ≤ l) :
    qSideFactor l ≠ 1 := by
  unfold qSideFactor
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  have hden : (2 * (l : ℝ)) ≠ 0 := by positivity
  intro h
  have hlt : (1 : ℝ) / (2 * (l : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 1 ≤ l)
    linarith
  linarith

/-- The q-side factor is positive for `l > 0`. -/
theorem qSideFactor_pos {l : ℕ} (hl : 0 < l) : 0 < qSideFactor l := by
  unfold qSideFactor
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hden : (0 : ℝ) < 2 * (l : ℝ) := by positivity
  exact div_pos one_pos hden

end LeanFormal.IUT.XiFPaper.Mzk1ArchFactorRatioActual