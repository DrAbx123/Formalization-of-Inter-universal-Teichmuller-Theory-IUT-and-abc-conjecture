import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic.General

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CharZero K]

/-- The c4 formula for the general Tate curve from a1 = 1, a2 = a3 = 0. -/
theorem tateCurve_c4_eq (q : K) :
    (TateCurve.weierstrassCurve K q).c₄ = 1 - 48 * TateCurve.a4 K q :=
  TateCurve.canonical_c₄ q

/-- The c6 formula for the general Tate curve from a1 = 1, a2 = a3 = 0. -/
theorem tateCurve_c6_eq (q : K) :
    (TateCurve.weierstrassCurve K q).c₆ =
      -1 + 72 * TateCurve.a4 K q - 864 * TateCurve.a6 K q :=
  TateCurve.canonical_c₆ q

/-- Algebraic Tate discriminant identity:
Delta = (c4^3 - c6^2) / 1728 for the general Tate curve. -/
theorem tateCurve_delta_eq_c4_c6 (q : K) :
    (TateCurve.weierstrassCurve K q).Δ =
      ((TateCurve.weierstrassCurve K q).c₄ ^ 3 -
        (TateCurve.weierstrassCurve K q).c₆ ^ 2) / 1728 := by
  have h1728 : (1728 : K) ≠ 0 := by norm_num
  rw [eq_div_iff h1728, mul_comm]
  exact (TateCurve.weierstrassCurve K q).c_relation

end
end LeanFormal.IUT.PAdicAnalytic.General
