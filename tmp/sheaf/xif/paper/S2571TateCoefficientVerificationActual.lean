import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT Polynomial

namespace LeanFormal.IUT.XiFPaper.S2571TateCoefficientVerificationActual

variable {K : Type*} [NormedField K] [CharZero K]

theorem S2571_tate_coefficients (q : K) :
    TateCurve.weierstrassCurve K q =
      WeierstrassCurve.mk 1 0 0 (TateCurve.a4 K q) (TateCurve.a6 K q) := rfl

theorem S2571_tate_equation_is_nodal_limit (q : K) :
    (TateCurve.weierstrassCurve K q).a₁ = 1 ∧
    (TateCurve.weierstrassCurve K q).a₂ = 0 ∧
    (TateCurve.weierstrassCurve K q).a₃ = 0 ∧
    (TateCurve.weierstrassCurve K q).a₄ = TateCurve.a4 K q ∧
    (TateCurve.weierstrassCurve K q).a₆ = TateCurve.a6 K q := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def S2571NodalCubic (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨1, 0, 0, 0, 0⟩

theorem S2571_nodal_tangent :
    splitReductionPolynomial (S2571NodalCubic (ZMod 2)) =
      (Polynomial.X ^ 2 + Polynomial.X : (ZMod 2)[X]) := by
  ext k
  simp [splitReductionPolynomial, S2571NodalCubic, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]

#check S2571_tate_coefficients
#check S2571_tate_equation_is_nodal_limit
#check S2571_nodal_tangent
#print axioms S2571_tate_coefficients
end LeanFormal.IUT.XiFPaper.S2571TateCoefficientVerificationActual
end