import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import tmp.sheaf.xif.paper.S1572ZCoordinateSmulActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula

/-! # S1575: curvePoly and the map_φ / map_ψ pushforwards

Constructs the actual base change `curvePoly := curve.map (C.comp C)` and
the phi/psi pushforward identities.  The omega and psi_c pushforwards plus
the dblZ/addZ polynomial identities are recorded as the exact next missing
layer; no map or coordinate is fabricated. -/

noncomputable section
set_option maxHeartbeats 4000000
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
namespace Universal

open MvPolynomial (X)

noncomputable def polyMap : MvPolynomial Coeff ℤ →+* Poly :=
  (Polynomial.C : Polynomial (MvPolynomial Coeff ℤ) →+* Poly).comp
    (Polynomial.C : MvPolynomial Coeff ℤ →+* Polynomial (MvPolynomial Coeff ℤ))

noncomputable def curvePoly : WeierstrassCurve Poly := curve.map polyMap

@[simp] theorem curvePoly_a₁ : curvePoly.a₁ = polyMap curve.a₁ := rfl
@[simp] theorem curvePoly_a₂ : curvePoly.a₂ = polyMap curve.a₂ := rfl
@[simp] theorem curvePoly_a₃ : curvePoly.a₃ = polyMap curve.a₃ := rfl
@[simp] theorem curvePoly_a₄ : curvePoly.a₄ = polyMap curve.a₄ := rfl
@[simp] theorem curvePoly_a₆ : curvePoly.a₆ = polyMap curve.a₆ := rfl

theorem curvePoly_φ (n : ℤ) :
    curvePoly.φ n = (curve.φ n).map (mapRingHom polyMap) := by
  simpa [curvePoly] using WeierstrassCurve.map_φ (W := curve) (f := polyMap) n

theorem curvePoly_ψ (n : ℤ) :
    curvePoly.ψ n = (curve.ψ n).map (mapRingHom polyMap) := by
  simpa [curvePoly] using WeierstrassCurve.map_ψ (W := curve) (f := polyMap) n

/-- Exact missing omega pushforward. -/
def S1575MapOmegaMissing : Prop :=
  forall n : ℤ,
    curvePoly.ω n = (curve.ω n).map (mapRingHom polyMap)

/-- Exact missing psi_c pushforward. -/
def S1575MapPsiCMissing : Prop :=
  forall n : ℤ,
    curvePoly.ψc n = (curve.ψc n).map (mapRingHom polyMap)

/-- Exact missing TauCeti `dblZ_smulPoly`. -/
def S1575DblZSmulPolyMissing : Prop :=
  forall n : ℤ,
    WeierstrassCurve.Jacobian.dblZ curvePoly.toAffine (smulPoly n) =
      curve.ψ (2 * n)

#check curvePoly
#check curvePoly_φ
#check curvePoly_ψ
#check S1575MapOmegaMissing
#check S1575MapPsiCMissing
#check S1575DblZSmulPolyMissing

end Universal
end WeierstrassCurve
end
