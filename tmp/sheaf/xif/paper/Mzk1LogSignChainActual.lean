/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7: sign chain for logs used by the raw theta readout -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1LogSignChainActual

/-- `0 < μ < 1` gives `log μ <= 0`. -/
theorem log_nonpos_of_lt_one {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) : Real.log μ ≤ 0 :=
  Real.log_nonpos (le_of_lt h0) (le_of_lt h1)

/-- `1 < μ` gives `0 <= log μ`. -/
theorem log_nonneg_of_one_lt {μ : ℝ} (h : 1 < μ) : 0 ≤ Real.log μ :=
  Real.log_nonneg (le_of_lt h)

/-- `0 < μ < 1` gives `-log μ > 0`. -/
theorem neg_log_pos_of_lt_one {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) :
    0 < -Real.log μ := neg_pos.mpr (Real.log_neg h0 h1)

end LeanFormal.IUT.XiFPaper.Mzk1LogSignChainActual