/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: elementary facts about the raw theta readout `log μ` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRawReadoutArithmeticActual

/-- If `0 < μ < 1`, the raw theta readout is negative. -/
theorem raw_log_neg {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) :
    Real.log μ < 0 := Real.log_neg h0 h1

/-- The paper-normalized candidate `log μ / dim` is negative when `log μ < 0` and `dim > 0`. -/
theorem raw_div_dim_neg {μ dim : ℝ} (h0 : 0 < μ) (h1 : μ < 1) (hdim : 0 < dim) :
    Real.log μ / dim < 0 := div_neg_of_neg_of_pos (raw_log_neg h0 h1) hdim

end LeanFormal.IUT.XiFPaper.Mzk1ThetaRawReadoutArithmeticActual