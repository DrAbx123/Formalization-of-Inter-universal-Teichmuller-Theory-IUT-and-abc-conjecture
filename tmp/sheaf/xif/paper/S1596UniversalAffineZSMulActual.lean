import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1569AffineRecursionNonzeroActual
import tmp.sheaf.xif.paper.S1577CuspPsiEvalActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
abbrev ψᵤ (n : ℤ) : Field := polyToField (curve.toAffine.ψ n)
theorem smulX_one : smulX 1 = polyToField (C Polynomial.X) := by
  simp [smulX, WeierstrassCurve.φ_one, WeierstrassCurve.ψ_one]
theorem smulY_one : smulY 1 = polyToField Polynomial.X := by
  simp [smulY, WeierstrassCurve.ω_one, WeierstrassCurve.ψ_one]
theorem smulX_eq (n : ℤ) (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, WeierstrassCurve.φ, map_sub (polyToField),
    sub_div, map_mul (polyToField), map_pow (polyToField),
    mul_div_cancel_right₀, map_mul (polyToField)]
  exact pow_ne_zero _ (polyToField_ψ_ne_zero n hn)
end WeierstrassCurve.Universal

end
