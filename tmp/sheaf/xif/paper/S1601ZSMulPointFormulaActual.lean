import tmp.sheaf.xif.paper.S1600RelatorNormalFormActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
theorem smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  rw [smulX_eq 2 (by norm_num)]
  simp only [show (2 + 1 : ℤ) = 3 by norm_num,
    show (2 - 1 : ℤ) = 1 by norm_num, s1600ψᵤ_one, mul_one]
theorem smulX_neg (n : ℤ) : smulX (-n) = smulX n := by
  rw [smulX_def, smulX_def]
  simp [WeierstrassCurve.φ_neg, WeierstrassCurve.ψ_neg,
    map_neg (polyToField), map_pow (polyToField), neg_sq]
theorem smulX_sub_sub_smulX_add (m n : ℤ)
    (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) =
      ψᵤ (2 * n) * ψᵤ (2 * m) /
        (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX (n - m) (n + m) sub_ne add_ne]
  ring_nf
end WeierstrassCurve.Universal
end
