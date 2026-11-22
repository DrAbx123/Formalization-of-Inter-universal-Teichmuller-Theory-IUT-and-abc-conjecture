/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: bounds for the raw theta readout `log μ` -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1RawThetaReadoutBoundsActual

/-- If `0 < μ <= 1`, the raw readout is nonpositive. -/
theorem raw_log_nonpos {μ : ℝ} (h0 : 0 < μ) (h1 : μ ≤ 1) :
    Real.log μ ≤ 0 := Real.log_nonpos (le_of_lt h0) h1

/-- If `μ = 1`, the raw readout is zero. -/
theorem raw_log_eq_zero {μ : ℝ} (h : μ = 1) : Real.log μ = 0 := by
  rw [h, Real.log_one]

/-- If `0 < μ`, the raw readout is strictly negative iff `μ < 1`. -/
theorem raw_log_neg_iff {μ : ℝ} (h0 : 0 < μ) : Real.log μ < 0 ↔ μ < 1 := by
  constructor
  · intro h
    by_contra hcon
    have hle : 1 ≤ μ := le_of_not_gt hcon
    have : 0 ≤ Real.log μ := Real.log_nonneg hle
    linarith
  · intro h
    exact Real.log_neg h0 h

end LeanFormal.IUT.XiFPaper.Mzk1RawThetaReadoutBoundsActual