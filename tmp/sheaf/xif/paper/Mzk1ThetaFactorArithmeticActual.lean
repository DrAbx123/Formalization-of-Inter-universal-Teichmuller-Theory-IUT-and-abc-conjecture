/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: arithmetic of raw = dim * normalized and p-scaling, dimension ≠ 0 -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaFactorArithmeticActual

/-- If `raw = dim * norm` then `norm = raw / dim`. -/
theorem norm_eq_raw_div_dim {raw dim norm : ℝ} (hdim : dim ≠ 0)
    (h : raw = dim * norm) : norm = raw / dim := by
  rw [h]
  field_simp

/-- p-shift arithmetic: `(raw - dim*logp)/dim = raw/dim - logp`. -/
theorem normalized_shift {raw dim logp : ℝ} (hdim : dim ≠ 0) :
    (raw - dim * logp) / dim = raw / dim - logp := by
  field_simp [hdim]

/-- Raw p-shift from the normalized one: `norm -> norm - logp` implies `raw -> raw - dim*logp`. -/
theorem raw_shift_of_normalized {raw dim norm logp : ℝ} (hdim : dim ≠ 0)
    (h : raw = dim * norm) :
    raw - dim * logp = dim * (norm - logp) := by
  rw [h]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1ThetaFactorArithmeticActual