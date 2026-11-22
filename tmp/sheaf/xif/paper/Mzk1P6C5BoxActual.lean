import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6C5BoxActual
/-- C5: from the actual Step-V Box and `-M <= H`, with `M=Q/(2l)`,
    derive the first Box coefficient bound. -/
theorem c5_box_first {l D Q S T : Real}
    (hl : 0 < l)
    (hbox : -Q / (2 * l) ≤ (l + 5) / 4 * D - (l + 1) / 24 * Q + S + (l + 5) * T) :
    ((l + 4) * (l - 3)) / (24 * l) * Q ≤ (l + 5) / 4 * D + S + (l + 5) * T := by
  have h : (l + 1) / 24 * Q - Q / (2 * l) ≤ (l + 5) / 4 * D + S + (l + 5) * T := by
    linarith
  have heq : (l + 1) / 24 * Q - Q / (2 * l) =
      ((l + 4) * (l - 3)) / (24 * l) * Q := by
    field_simp [hl.ne']
    ring
  rwa [heq] at h
/-- C5 final coefficient form for `l >= 7`. -/
theorem c5_box_final {l D Q S T : Real} (hl : 7 ≤ l)
    (hD0 : 0 ≤ D) (hS0 : 0 ≤ S) (hT0 : 0 ≤ T) :
    l * (l + 5) / ((l + 4) * (l - 3)) * D +
        4 * l / ((l + 4) * (l - 3)) * S +
        4 * l * (l + 5) / ((l + 4) * (l - 3)) * T
      ≤ (1 + 7 / l) * D + (5 / l) * S + 8 * T := by
  have hl0 : 0 < l := by linarith
  have hden : 0 < (l + 4) * (l - 3) := by nlinarith
  have hD : l * (l + 5) / ((l + 4) * (l - 3)) ≤ 1 + 7 / l := by
    rw [div_le_iff hden]
    field_simp [hl0.ne']
    nlinarith
  have hS : 4 * l / ((l + 4) * (l - 3)) ≤ 5 / l := by
    rw [div_le_iff hden]
    field_simp [hl0.ne']
    nlinarith
  have hT : 4 * l * (l + 5) / ((l + 4) * (l - 3)) ≤ 8 := by
    rw [div_le_iff hden]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hD hD0, mul_le_mul_of_nonneg_right hS hS0, mul_le_mul_of_nonneg_right hT hT0]
#print axioms c5_box_final
end LeanFormal.IUT.XiFPaper.Mzk1P6C5BoxActual
end