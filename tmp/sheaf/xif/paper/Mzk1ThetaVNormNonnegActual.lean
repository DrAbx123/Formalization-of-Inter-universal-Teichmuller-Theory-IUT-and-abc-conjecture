/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: nonnegativity propagation raw -> normalized -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVNormNonnegActual

/-- If `raw >= 0` and `dim > 0`, then `raw/dim >= 0`. -/
theorem raw_div_dim_nonneg {raw dim : ℝ} (hraw : 0 ≤ raw) (hdim : 0 < dim) :
    0 ≤ raw / dim := div_nonneg hraw (le_of_lt hdim)

/-- If `raw = dim * norm`, `dim > 0`, `raw >= 0`, then `norm >= 0`. -/
theorem norm_nonneg_of_raw_nonneg {raw dim norm : ℝ}
    (h : raw = dim * norm) (hdim : 0 < dim) (hraw : 0 ≤ raw) : 0 ≤ norm := by
  rw [h] at hraw
  by_contra hcon
  have hlt : norm < 0 := not_le.mp hcon
  have hmulneg : dim * norm < 0 := mul_neg_of_pos_of_neg hdim hlt
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1ThetaVNormNonnegActual