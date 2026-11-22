/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: sign equivalences for the raw theta readout `log μ` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1RawThetaLogSignActual

/-- For `0 < μ`, `log μ <= 0` iff `μ <= 1`. -/
theorem log_nonpos_iff {μ : ℝ} (h0 : 0 < μ) : Real.log μ ≤ 0 ↔ μ ≤ 1 := by
  constructor
  · intro h
    have hlog : Real.log μ ≤ Real.log 1 := by simpa using h
    exact (Real.log_le_log_iff h0 one_pos).mp hlog
  · intro h
    exact Real.log_nonpos (le_of_lt h0) h

/-- For `0 < μ`, `0 <= log μ` iff `1 <= μ`. -/
theorem log_nonneg_iff {μ : ℝ} (h0 : 0 < μ) : 0 ≤ Real.log μ ↔ 1 ≤ μ := by
  constructor
  · intro h
    have hlog : Real.log 1 ≤ Real.log μ := by simpa using h
    exact (Real.log_le_log_iff one_pos h0).mp hlog
  · intro h
    exact Real.log_nonneg h

end LeanFormal.IUT.XiFPaper.Mzk1RawThetaLogSignActual