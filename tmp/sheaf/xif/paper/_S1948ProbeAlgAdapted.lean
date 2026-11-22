import Mathlib

example (D n m L l : ℝ) (hD : D ≠ 0) (hl : l ≠ 0) :
    (D * n) * ((-(m * L) / D) / (2 * l)) = -((n * m) / (2 * l)) * L := by
  field_simp [hD, hl]
  ring

example (D n m L l : ℝ) (hD : D ≠ 0) (hl : l ≠ 0) :
    (D * n) * ((-(m * L) / D) / (2 * l)) = -((n * m) / (2 * l)) * L := by
  rw [div_div]
  field_simp [hD, hl]
  ring

example (D n m L l : ℝ) (hD : D ≠ 0) (hl : l ≠ 0) :
    (D * n) * ((-(m * L) / D) / (2 * l)) = -((n * m) / (2 * l)) * L := by
  rw [show (-(m * L) / D) = -(m*L)/D from rfl]
  rw [div_div, mul_div_assoc']
  field_simp [hD, hl]
  ring
