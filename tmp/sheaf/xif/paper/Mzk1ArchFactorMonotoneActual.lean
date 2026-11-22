/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/NORM-ARCH-C: monotonicity of the q-side factor `1/(2l)` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchFactorMonotoneActual

/-- The q-side factor is antitone on positive naturals. -/
theorem qSideFactor_antitone {l m : ℕ} (hl : 1 ≤ l) (hlm : l ≤ m) :
    (1 : ℝ) / (2 * (m : ℝ)) ≤ 1 / (2 * (l : ℝ)) := by
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlm' : (l : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1ArchFactorMonotoneActual