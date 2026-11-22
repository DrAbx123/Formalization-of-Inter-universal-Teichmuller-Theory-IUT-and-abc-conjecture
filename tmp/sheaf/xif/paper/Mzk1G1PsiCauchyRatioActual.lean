/- B1 analytic h (kurt): pure real-arithmetic ratio bound used by the analytic h
producer to turn a value bound and a derivative lower bound into a ratio bound.
Default heartbeats.
-/
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyRatioActual

/-- Ratio bound: numerator bound and positive denominator lower bound give a ratio
bound in the real numbers. -/
theorem div_le_div_of_bounds {a A L B : ℝ} (ha : a ≤ A) (hL : 0 < L) (hB : L ≤ B)
    (hA : 0 ≤ A) :
    a / B ≤ A / L := by
  have hBpos : 0 < B := lt_of_lt_of_le hL hB
  have h1 : a / B ≤ A / B := by
    exact div_le_div_of_nonneg_right ha hBpos.le
  have h2 : A / B ≤ A / L := by
    apply div_le_div_of_nonneg_left hA hL hB
  exact h1.trans h2

/-- Squared ratio bound (avoids square roots in the analytic h estimates). -/
theorem div_sq_le_div_sq_of_bounds {a A L B : ℝ} (ha : a ≤ A) (hL : 0 < L) (hB : L ≤ B)
    (hA : 0 ≤ A) (ha0 : 0 ≤ a) :
    (a / B) ^ 2 ≤ (A / L) ^ 2 := by
  have hBpos : 0 < B := lt_of_lt_of_le hL hB
  have hratio : 0 ≤ a / B := div_nonneg ha0 hBpos.le
  have hAoverL : 0 ≤ A / L := div_nonneg hA hL.le
  exact sq_le_sq' (by linarith [div_le_div_of_bounds ha hL hB hA]) (div_le_div_of_bounds ha hL hB hA)

#print axioms div_le_div_of_bounds
#print axioms div_sq_le_div_sq_of_bounds

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyRatioActual
end