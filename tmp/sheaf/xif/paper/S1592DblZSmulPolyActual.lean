import tmp.sheaf.xif.paper.S1575CurvePolyMapActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
/-! # S1592: dblZ_smulPoly
TauCeti route: omega_spec + psi_mul_psic + smulPoly unfolding + ring. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1592DblZSmulPolyActual
open WeierstrassCurve.Universal
theorem s1592DblZSmulPoly : S1575DblZSmulPolyMissing := by
  intro n
  have key : 2 * curve.ω n + curvePoly.a₁ * curve.φ n * curve.ψ n
      + curvePoly.a₃ * curve.ψ n ^ 3 = curve.ψc n := by
    simpa [curvePoly, polyMap] using (WeierstrassCurve.ω_spec (W := curve) n)
  rw [← WeierstrassCurve.ψ_mul_ψc, ← key]
  simp only [WeierstrassCurve.Jacobian.dblZ, smulPoly,
    WeierstrassCurve.Jacobian.negY_eq, fin3_def_ext]
  ring
theorem s1592IsEllipticNet_psi_comm {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) : IsEllipticNet W.ψ := by
  rw [show W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) from rfl]
  exact IsEllipticNet.normEDS _ _ _
def S1592AddZSmulPoly : Prop :=
  ∀ m n : ℤ,
    WeierstrassCurve.Jacobian.addZ (smulPoly m) (smulPoly n) =
      curve.ψ (n + m) * curve.ψ (n - m)
theorem s1592AddZSmulPoly : S1592AddZSmulPoly := by
  intro m n
  have key := (s1592IsEllipticNet_psi_comm (R := MvPolynomial Coeff ℤ) curve).isEllipticSequence n m 1
  simp only [IsEllipticNet.rel, add_zero, ψ_one] at key
  symm
  rw [← sub_eq_zero, ← key, WeierstrassCurve.Jacobian.addZ]
  simp only [smulPoly, fin3_def_ext, WeierstrassCurve.φ]
  ring
end LeanFormal.IUT.XiFPaper.S1592DblZSmulPolyActual
end
