import tmp.sheaf.xif.paper.S1618ZSMulPointFinalActual
import tmp.sheaf.xif.paper.S1602PhiNeZeroActual
import tmp.sheaf.xif.paper.S1598PolyToFieldCCActual
import tmp.sheaf.xif.paper.S1606SlopeDoublingActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1618ZSMulPointFinalActual
theorem s1619PolyToField_polyMap (a : MvPolynomial Coeff ℤ) :
    polyToField (polyMap a) = algebraMap (MvPolynomial Coeff ℤ) Field a := by
  simpa [polyMap] using s1598PolyToField_CC a
theorem s1619PointedCurve_eq_baseChange :
    pointedCurve = curve.baseChange Field := by
  ext <;>
    simp [pointedCurve, curvePoly, WeierstrassCurve.map,
      s1619PolyToField_polyMap]
theorem s1619Equation :
    pointedCurve.toAffine.Equation (smulX 1) (smulY 1) := by
  rw [s1619PointedCurve_eq_baseChange, smulX_one, smulY_one,
    ← universalX_eq_polyToField, ← universalY_eq_polyToField]
  exact universal_equation
theorem s1619PolynomialY_ne_zero :
    2 * smulY 1 + pointedCurve.toAffine.a₁ * smulX 1 +
      pointedCurve.toAffine.a₃ ≠ 0 := by
  have h := s1606_smulY_one_sub_negY
  simp only [Affine.negY] at h
  have h2 : 2 * smulY 1 + pointedCurve.toAffine.a₁ * smulX 1 +
      pointedCurve.toAffine.a₃ = ψᵤ 2 := by
    linear_combination h
  rw [h2]
  exact polyToField_ψ_ne_zero 2 (by norm_num)
theorem s1619Nonsingular :
    pointedCurve.toAffine.Nonsingular (smulX 1) (smulY 1) :=
  (Affine.nonsingular_iff' (W := pointedCurve.toAffine)
    (smulX 1) (smulY 1)).mpr
    ⟨s1619Equation, Or.inr s1619PolynomialY_ne_zero⟩
noncomputable def s1619Point : (pointedCurve.toAffine).Point :=
  Affine.Point.some (smulX 1) (smulY 1) s1619Nonsingular
def s1619PointLayer : S1618PointLayerRequired where
  point := s1619Point
  xCoord_eq := by
    simp [s1619Point, Affine.Point.xCoord_some]
  yCoord_eq := by
    simp [s1619Point, Affine.Point.yCoord_some]
end LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
end
