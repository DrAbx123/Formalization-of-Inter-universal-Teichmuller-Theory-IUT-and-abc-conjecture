import tmp.sheaf.xif.paper.S1530UniversalRingFieldActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.AdjoinRoot

/-! # S1533: universal point equation via a CommRing-base coordinate-ring lemma -/

noncomputable section
open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
namespace Universal
open MvPolynomial (X)

/-- CommRing-base version of S1467 algHom_mk_eq_evalEval. -/
theorem algHom_mk_eq_evalEval_comm {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve.Affine R) (f : W.CoordinateRing →ₐ[R] A) (p : R[X][Y]) :
    f (Affine.CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap R A))).evalEval
        (f (AdjoinRoot.of W.polynomial X)) (f (AdjoinRoot.root W.polynomial)) := by
  rw [← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X]
  let g : R[X][Y] →ₐ[R] A :=
    f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars R)
  change g p = _
  have hg : g = aevalAeval (g (C X)) (g Y) :=
    ((aevalAevalEquiv R A).apply_symm_apply g).symm
  rw [hg]
  let _ := Polynomial.algebra R A
  rw [aevalAevalEquiv_apply_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have halg : algebraMap R[X] A[X] = mapRingHom (algebraMap R A) := rfl
  rw [halg]
  simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]

/-- CommRing-base version of S1467 equation_of_algHom. -/
theorem equation_of_algHom_comm {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve.Affine R) (f : W.CoordinateRing →ₐ[R] A) :
    (W⁄A).Equation (f (AdjoinRoot.of W.polynomial X)) (f (AdjoinRoot.root W.polynomial)) := by
  change (W.map (algebraMap R A)).Equation _ _
  rw [Equation, map_polynomial,
    ← algHom_mk_eq_evalEval_comm W f W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- Algebra map from the universal coordinate ring to its fraction field, as an
R-algebra hom. -/
noncomputable def universalAlgebraHom :
    curve.toAffine.CoordinateRing →ₐ[MvPolynomial Coeff ℤ] Field :=
  IsScalarTower.toAlgHom (MvPolynomial Coeff ℤ) Ring Field

/-- The universal point satisfies the base-changed Weierstrass equation. -/
theorem universal_equation :
    (curve.baseChange Field).toAffine.Equation universalX universalY := by
  have h := equation_of_algHom_comm (W := curve.toAffine)
    (A := Field) (f := universalAlgebraHom)
  convert h using 2
  · rfl
  · rfl

end Universal
end WeierstrassCurve
end