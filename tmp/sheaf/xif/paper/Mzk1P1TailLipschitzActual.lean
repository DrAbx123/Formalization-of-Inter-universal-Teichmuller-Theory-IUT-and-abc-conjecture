/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries
import Mathlib.Tactic

/-! # P1 tail Lipschitz: termwise difference bound -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P1TailLipschitzActual
open LeanFormal.IUT

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Termwise difference of the x-kernel: the difference factors as
`(a-b)(1-ab)/((1-a)^2(1-b)^2)`, hence is bounded by `‖a-b‖` when both
denominators have norm one and `‖ab‖ ≤ 1`. -/
theorem xTerm_diff_norm_le (a b : K)
    (ha : ‖1 - a‖ = 1) (hb : ‖1 - b‖ = 1) (hab : ‖a * b‖ ≤ 1) :
    ‖a / (1 - a) ^ 2 - b / (1 - b) ^ 2‖ ≤ ‖a - b‖ := by
  have h1a : 1 - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  have h1b : 1 - b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb
    norm_num at hb
  have hfac : a / (1 - a) ^ 2 - b / (1 - b) ^ 2 =
      (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := by
    field_simp [h1a, h1b]
    ring
  have hnum : ‖1 - a * b‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : K) (-(a * b))
    calc
      ‖1 - a * b‖ = ‖1 + (-(a * b))‖ := by ring_nf
      _ ≤ max ‖(1 : K)‖ ‖a * b‖ := by simpa using h
      _ = 1 := by rw [norm_one, max_eq_left hab]
  have hden : ‖(1 - a) ^ 2 * (1 - b) ^ 2‖ = 1 := by
    rw [norm_mul, norm_pow, norm_pow, ha, hb]
    norm_num
  rw [hfac, norm_div, norm_mul, hden]
  rw [div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hnum

end LeanFormal.IUT.XiFPaper.Mzk1P1TailLipschitzActual
