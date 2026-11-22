/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Cor 3.12: log-volume monotonicity facts -/

namespace LeanFormal.IUT.XiFPaper.LogVolumeMonotoneActual

theorem log_nonneg_of_one_le {x : ℝ} (h : 1 ≤ x) : 0 ≤ Real.log x := Real.log_nonneg h

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_lt_log_of_pos {x y : ℝ} (hx : 0 < x) (h : x < y) :
    Real.log x < Real.log y := Real.log_lt_log hx h

theorem log_le_zero_of_pos_le_one {x : ℝ} (hx : 0 < x) (h : x ≤ 1) :
    Real.log x ≤ 0 := Real.log_nonpos hx.le h

theorem log_one' : Real.log 1 = 0 := Real.log_one

theorem log_eq_zero_iff {x : ℝ} (hx : 0 < x) : Real.log x = 0 ↔ x = 1 := 
  Real.log_eq_zero.trans (or_iff_left (ne_of_gt hx))

end LeanFormal.IUT.XiFPaper.LogVolumeMonotoneActual
