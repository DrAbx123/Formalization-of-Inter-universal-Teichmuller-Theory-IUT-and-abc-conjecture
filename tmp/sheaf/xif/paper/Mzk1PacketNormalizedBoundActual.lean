/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: packet-normalized bound arithmetic -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedBoundActual

/-- If `norm = raw / dim` then `raw = dim * norm` (dim ≠ 0). -/
theorem raw_eq_dim_mul_of_norm_eq_div {raw dim norm : ℝ} (hdim : dim ≠ 0)
    (h : norm = raw / dim) : raw = dim * norm := by
  rw [h]
  field_simp

/-- If `raw = dim * norm` and `dim > 0`, then `norm < 0` when `raw < 0`. -/
theorem norm_neg_of_raw_neg {raw dim norm : ℝ}
    (hdim : 0 < dim) (h : raw = dim * norm) (hraw : raw < 0) : norm < 0 := by
  rw [h] at hraw
  by_contra hcon
  push_neg at hcon
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedBoundActual