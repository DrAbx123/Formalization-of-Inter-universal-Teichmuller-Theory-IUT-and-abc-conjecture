import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import Mathlib.Algebra.MvPolynomial.CommRing
/-! # S1523: minimal actual universal curve and universal division tuple -/
noncomputable section
open Polynomial
namespace WeierstrassCurve
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff
namespace Universal
open MvPolynomial (X)
def curve : WeierstrassCurve (MvPolynomial Coeff ℤ) where
  a₁ := X Coeff.A₁
  a₂ := X Coeff.A₂
  a₃ := X Coeff.A₃
  a₄ := X Coeff.A₄
  a₆ := X Coeff.A₆
abbrev Poly : Type := Polynomial (Polynomial (MvPolynomial Coeff ℤ))
def smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
@[simp] theorem smulPoly_apply_zero (n : ℤ) : smulPoly n 0 = curve.φ n := rfl
@[simp] theorem smulPoly_apply_one (n : ℤ) : smulPoly n 1 = curve.ω n := rfl
@[simp] theorem smulPoly_apply_two (n : ℤ) : smulPoly n 2 = curve.ψ n := rfl
end Universal
end WeierstrassCurve
#print axioms WeierstrassCurve.Universal.curve
#print axioms WeierstrassCurve.Universal.smulPoly
end
