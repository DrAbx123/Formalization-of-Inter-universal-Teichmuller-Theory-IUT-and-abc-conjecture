import Mathlib.Tactic

/-! # Gap2 arithmeticization (theta absorbed into weight) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticizationShaActual

/-- Arithmeticization: if theta is bounded by `K * w`, the Gap2 theta term can be
absorbed into the weight coefficient. -/
theorem gap2_theta_absorbed_into_weight
    {v w theta D epsilon K : Real} (hw : 0 ≤ w)
    (htheta : theta ≤ K * w)
    (hgap2 : v ≤ (1 + epsilon) * w + theta + D) :
    v ≤ (1 + epsilon + K) * w + D := by
  nlinarith

/-- Gap2 in normal form: `v ≤ (1+ε)w + θ + D` iff `v - θ ≤ (1+ε)w + D`. -/
theorem gap2_normal_form {v w theta D epsilon : Real} :
    (v ≤ (1 + epsilon) * w + theta + D) ↔
    (v - theta ≤ (1 + epsilon) * w + D) := by
  constructor <;> intro h <;> linarith

#print axioms gap2_theta_absorbed_into_weight
#print axioms gap2_normal_form

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticizationShaActual
