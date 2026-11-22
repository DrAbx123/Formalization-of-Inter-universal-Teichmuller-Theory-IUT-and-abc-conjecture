import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff
  deriving DecidableEq

namespace Universal

open Coeff
open MvPolynomial (X)

def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma curve_Δ_ne_zero : curve.Δ ≠ 0 :=
  ne_of_apply_ne (MvPolynomial.eval (Coeff.rec 0 0 0 0 1)) <| by
    simp [Δ, b₂, b₄, b₆, b₈, curve]

abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
protected abbrev Ring : Type := curve.CoordinateRing
protected abbrev Field : Type := FractionRing Universal.Ring

def polyToField : Poly →+* Universal.Field :=
  (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

@[simp] lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_ring_injective : Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Ring) := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial Coeff ℤ) (MvPolynomial Coeff ℤ)[X] Universal.Ring,
    AdjoinRoot.algebraMap_eq]
  have hdeg : curve.polynomial.degree ≠ 0 := by
    rw [Affine.degree_polynomial]
    norm_num
  exact (AdjoinRoot.of.injective_of_degree_ne_zero hdeg).comp Polynomial.C_injective

lemma algebraMap_field_injective : Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial Coeff ℤ) Universal.Ring Universal.Field]
  exact (IsFractionRing.injective Universal.Ring Universal.Field).comp algebraMap_ring_injective

abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field

instance : pointedCurve.IsElliptic where
  isUnit := by
    change IsUnit (curve.map (algebraMap (MvPolynomial Coeff ℤ) Universal.Field)).Δ
    rw [map_Δ]
    exact (map_ne_zero_iff _ algebraMap_field_injective).mpr curve_Δ_ne_zero |>.isUnit

end Universal

end WeierstrassCurve
