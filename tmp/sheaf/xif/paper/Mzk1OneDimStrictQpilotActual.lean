/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1OneDimStrictQpilotActual — 1D ball strictness (qpilot lane)

A578: one-dimensional strictness lemmas: for `0 ≤ r < R` the closed ball of
radius `r` is a proper subset of the closed ball of radius `R`, and its Lebesgue
measure is strictly smaller. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1OneDimStrictQpilotActual

open MeasureTheory
open scoped ENNReal

/-- Proper-subset strictness of 1D closed balls. -/
theorem oneDim_strict_subset {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    Metric.closedBall (0 : Real) r ⊂ Metric.closedBall (0 : Real) R := by
  constructor
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    linarith
  · intro hsub
    have hRmem : (R : Real) ∈ Metric.closedBall (0 : Real) R := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : Real) ≤ R)]
    have hRmem' := hsub hRmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : Real) ≤ R)] at hRmem'
    exact absurd hRmem' (not_le.mpr hrR)

/-- Strict measure increase of 1D closed balls. -/
theorem oneDim_volume_strict {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    volume (Metric.closedBall (0 : Real) r) <
      volume (Metric.closedBall (0 : Real) R) := by
  rw [Real.volume_closedBall, Real.volume_closedBall]
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : Real) < 2 * R)).mpr
  linarith

/-- Monotone (non-strict) version. -/
theorem oneDim_volume_mono {r R : Real} (h : r ≤ R) :
    volume (Metric.closedBall (0 : Real) r) ≤ volume (Metric.closedBall (0 : Real) R) :=
  measure_mono (Metric.closedBall_subset_closedBall h)

#check oneDim_strict_subset
#check oneDim_volume_strict

end LeanFormal.IUT.XiFPaper.Mzk1OneDimStrictQpilotActual
end
