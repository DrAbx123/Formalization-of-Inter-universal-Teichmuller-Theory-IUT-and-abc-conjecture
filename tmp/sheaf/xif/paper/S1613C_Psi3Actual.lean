import tmp.sheaf.xif.paper.S1612ZSMulPointFinalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1613C_Psi3Actual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal

/-- C_Ψ₃: Ψ₃ through the Weierstrass polynomial. -/
theorem s1613_C_Ψ₃ {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - Affine.polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * Affine.polynomialX W - CC W.a₁ ^ 2 * Affine.polynomial W := by
  simp_rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, Affine.polynomial,
    Affine.polynomialX, WeierstrassCurve.ψ₂, Affine.polynomialY,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, CC]
  simp only [map_ofNat, C_add, C_sub, C_mul, C_pow]
  ring


/-- Ψ₂Sq in the universal field is ψ₂². -/
theorem s1613_polyToField_Ψ₂Sq :
    polyToField (C curve.Ψ₂Sq) = polyToField (curve.toAffine.ψ 2) ^ 2 := by
  rw [WeierstrassCurve.ψ_two, polyToField_apply, polyToField_apply, ← map_pow]
  exact (congrArg (algebraMap Ring Field)
    (Affine.CoordinateRing.mk_ψ₂_sq curve.toAffine)).symm

end LeanFormal.IUT.XiFPaper.S1613C_Psi3Actual
end