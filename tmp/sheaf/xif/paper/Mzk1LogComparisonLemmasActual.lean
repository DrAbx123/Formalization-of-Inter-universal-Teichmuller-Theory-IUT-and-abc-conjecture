/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # IUT IV / Cor 3.12: logarithmic comparison lemmas (paper-layer arithmetic) -/

namespace LeanFormal.IUT.XiFPaper.LogComparisonLemmasActual

theorem log_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x * y) = Real.log x + Real.log y := 
  Real.log_mul hx.ne' hy.ne'

theorem log_le_log_of_pos {x y : ℝ} (hx : 0 < x) (h : x ≤ y) :
    Real.log x ≤ Real.log y := Real.log_le_log hx h

theorem log_inv_of_pos {x : ℝ} (hx : 0 < x) : Real.log x⁻¹ = -Real.log x := 
  Real.log_inv x

theorem log_div_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x / y) = Real.log x - Real.log y := Real.log_div hx.ne' hy.ne'

theorem log_zpow_of_pos {x : ℝ} (hx : 0 < x) (n : ℤ) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := Real.log_zpow hx n

theorem log_pow_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := by
  rw [← Real.log_pow]
  rfl

theorem log_pos_of_one_lt {x : ℝ} (h : 1 < x) : 0 < Real.log x := Real.log_pos h

theorem log_nonpos_of_pos_le_one {x : ℝ} (hx : 0 < x) (h : x ≤ 1) : Real.log x ≤ 0 :=
  Real.log_nonpos hx.le h

end LeanFormal.IUT.XiFPaper.LogComparisonLemmasActual
