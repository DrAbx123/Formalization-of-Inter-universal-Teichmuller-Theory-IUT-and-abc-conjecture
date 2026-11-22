import tmp.sheaf.xif.paper.S1597UniversalAffineFullActual
import tmp.sheaf.xif.paper.S1577CuspPsiEvalActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
theorem s1598PolyToField_CC (a : MvPolynomial Coeff ℤ) :
    polyToField (CC a) = algebraMap (MvPolynomial Coeff ℤ) Field a := by
  rw [polyToField_apply]
  change algebraMap Ring Field
      (AdjoinRoot.mk curve.toAffine.polynomial (Polynomial.C (Polynomial.C a))) = _
  rw [AdjoinRoot.mk_C]
  rw [← AdjoinRoot.algebraMap_eq]
  rw [Polynomial.C_eq_algebraMap a]
  rw [← IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ)
    (Polynomial (MvPolynomial Coeff ℤ)) Ring a]
  rw [← IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ) Ring Field a]
theorem s1598SmulY_neg (n : ℤ) (h0 : n ≠ 0) :
    smulY (-n) =
      (curve.map (algebraMap (MvPolynomial Coeff ℤ) Field)).toAffine.negY
        (smulX n) (smulY n) := by
  simp only [smulY, smulX, WeierstrassCurve.ψ_neg, S1597UniversalOmegaNeg,
    Affine.negY, map_add (polyToField), map_neg (polyToField),
    map_mul (polyToField), map_pow (polyToField)]
  have h1 : polyToField (CC curve.a₁) =
      (curve.map (algebraMap (MvPolynomial Coeff ℤ) Field)).toAffine.a₁ := by
    rw [WeierstrassCurve.map_a₁]
    exact s1598PolyToField_CC curve.a₁
  have h3 : polyToField (CC curve.a₃) =
      (curve.map (algebraMap (MvPolynomial Coeff ℤ) Field)).toAffine.a₃ := by
    rw [WeierstrassCurve.map_a₃]
    exact s1598PolyToField_CC curve.a₃
  rw [h1, h3]
  field_simp [polyToField_ψ_ne_zero n h0]
  ring
end WeierstrassCurve.Universal

end
