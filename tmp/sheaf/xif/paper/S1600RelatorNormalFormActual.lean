import tmp.sheaf.xif.paper.S1599SmulXSubActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
theorem s1600ψᵤ_zero : ψᵤ 0 = 0 := by
  simp [ψᵤ, WeierstrassCurve.ψ_zero]
theorem s1600ψᵤ_one : ψᵤ 1 = 1 := by
  simp [ψᵤ, WeierstrassCurve.ψ_one]
theorem s1600RelatorNormalForm (n m : ℤ) :
    ψᵤ (n + m) * ψᵤ (n - m) =
      ψᵤ (n + 1) * ψᵤ (n - 1) * ψᵤ m ^ 2
        - ψᵤ (m + 1) * ψᵤ (m - 1) * ψᵤ n ^ 2 := by
  have h := s1599IsEllipticNet_ψᵤ n m 1 0
  rw [IsEllipticNet.rel] at h
  simp only [s1600ψᵤ_zero, s1600ψᵤ_one, mul_one, mul_zero, add_zero] at h
  linear_combination h
theorem smulX_sub_smulX (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n =
      ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq m hm, smulX_eq n hn, sub_sub_sub_cancel_left, div_sub_div]
  · field_simp [polyToField_ψ_ne_zero n hn, polyToField_ψ_ne_zero m hm]
    have hn1 : ψᵤ (1 + n) = ψᵤ (n + 1) := by congr 1; ring
    have hnm1 : ψᵤ (-1 + n) = ψᵤ (n - 1) := by congr 1; ring
    have hm1 : ψᵤ (1 + m) = ψᵤ (m + 1) := by congr 1; ring
    have hmm1 : ψᵤ (-1 + m) = ψᵤ (m - 1) := by congr 1; ring
    rw [show ψᵤ (n + 1) * ψᵤ (n - 1) * ψᵤ m ^ 2 -
        ψᵤ n ^ 2 * ψᵤ (m + 1) * ψᵤ (m - 1) =
          ψᵤ (n + 1) * ψᵤ (n - 1) * ψᵤ m ^ 2 -
            ψᵤ (m + 1) * ψᵤ (m - 1) * ψᵤ n ^ 2 by ring]
    rw [← s1600RelatorNormalForm]
  all_goals exact pow_ne_zero _ (polyToField_ψ_ne_zero _ (by assumption))
end WeierstrassCurve.Universal
end
