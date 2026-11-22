/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#7: arithmetic of the hull bound constant `(1/4) l (log d + log f)` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1HullBoundConstantActual

/-- The hull upper-bound main term. -/
noncomputable def hullBoundMain (l d f : ℝ) : ℝ := (1 / 4) * l * (Real.log d + Real.log f)

theorem hullBoundMain_def (l d f : ℝ) :
    hullBoundMain l d f = (1 / 4) * l * (Real.log d + Real.log f) := rfl

/-- The main term is nonnegative for `l >= 0`, `d >= 1`, `f >= 1`. -/
theorem hullBoundMain_nonneg {l d f : ℝ} (hl : 0 ≤ l) (hd : 1 ≤ d) (hf : 1 ≤ f) :
    0 ≤ hullBoundMain l d f := by
  unfold hullBoundMain
  have hd0 : 0 ≤ Real.log d := Real.log_nonneg hd
  have hf0 : 0 ≤ Real.log f := Real.log_nonneg hf
  positivity

end LeanFormal.IUT.XiFPaper.Mzk1HullBoundConstantActual