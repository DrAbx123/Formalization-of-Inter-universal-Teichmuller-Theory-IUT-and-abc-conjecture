import tmp.sheaf.xif.paper.S1923UniversalA
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Universal

open Coeff
open MvPolynomial (X)

lemma polyToField_C (a : Polynomial (MvPolynomial Coeff ℤ)) :
    polyToField (Polynomial.C a) = algebraMap (Polynomial (MvPolynomial Coeff ℤ)) Universal.Field a := by
  rw [polyToField_apply, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]
  exact (IsScalarTower.algebraMap_apply (Polynomial (MvPolynomial Coeff ℤ)) Universal.Ring Universal.Field a).symm

lemma x_eq : polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ))) =
    algebraMap (Polynomial (MvPolynomial Coeff ℤ)) Universal.Field Polynomial.X :=
  polyToField_C _

lemma evalEval_polyToField_hom :
    (Polynomial.evalEvalRingHom (polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ))))
      (polyToField Polynomial.X)).comp
      (mapRingHom (mapRingHom (algebraMap (MvPolynomial Coeff ℤ) Universal.Field))) = polyToField := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
    change Polynomial.evalEval (polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ))))
      (polyToField Polynomial.X)
      (Polynomial.C (Polynomial.map (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) a)) =
        polyToField (Polynomial.C a)
    rw [Polynomial.evalEval_C, polyToField_C, Polynomial.eval_map]
    exact Polynomial.eval₂_algebraMap_X a (IsScalarTower.toAlgHom (MvPolynomial Coeff ℤ) (Polynomial (MvPolynomial Coeff ℤ)) Universal.Field)
  · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
    change Polynomial.evalEval (polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ))))
      (polyToField Polynomial.X) Polynomial.X = polyToField Polynomial.X
    rw [Polynomial.evalEval_X]

lemma evalEval_polyToField (p : Poly) :
    Polynomial.evalEval (polyToField (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ))))
      (polyToField Polynomial.X)
      (p.map (mapRingHom (algebraMap (MvPolynomial Coeff ℤ) Universal.Field))) = polyToField p :=
  congrFun (congrArg DFunLike.coe evalEval_polyToField_hom) p

lemma equation_point : pointedCurve.toAffine.Equation (polyToField (Polynomial.C Polynomial.X)) (polyToField Polynomial.X) := by
  change Polynomial.evalEval (polyToField (Polynomial.C Polynomial.X)) (polyToField Polynomial.X)
    ((curve.map (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)).toAffine.polynomial) = 0
  rw [Affine.map_polynomial, evalEval_polyToField, polyToField_polynomial]

def Affine.point : pointedCurve.toAffine.Point :=
  .mk equation_point

end Universal
end WeierstrassCurve
