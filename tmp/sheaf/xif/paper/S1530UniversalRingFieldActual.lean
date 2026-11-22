import tmp.sheaf.xif.paper.S1523UniversalCurveActual
import Mathlib.RingTheory.Localization.FractionRing

/-! # S1530: universal coordinate ring, fraction field, and type alignment -/

noncomputable section
open Polynomial
namespace WeierstrassCurve
namespace Universal
open MvPolynomial (X)

/-- The universal coordinate ring. -/
abbrev Ring : Type := curve.toAffine.CoordinateRing

/-- The universal fraction field. -/
abbrev Field : Type := FractionRing Ring

/-- Type alignment: the bivariate polynomial ring Poly is the one-variable
AdjoinRoot input over the univariate polynomial base. -/
def polyToRing : Poly →+* Ring :=
  AdjoinRoot.mk curve.toAffine.polynomial

/-- The same map into the fraction field. -/
def polyToField : Poly →+* Field :=
  (algebraMap Ring Field).comp polyToRing

theorem polyToField_apply (p : Poly) :
    polyToField p = algebraMap Ring Field (polyToRing p) := rfl

/-- Universal X coordinate. -/
def universalX : Field :=
  algebraMap Ring Field (Affine.CoordinateRing.mk curve.toAffine (C Polynomial.X))

/-- Universal Y coordinate. -/
def universalY : Field :=
  algebraMap Ring Field (Affine.CoordinateRing.mk curve Polynomial.X)

/-- X coordinate is the image of the polynomial X under polyToField. -/
theorem universalX_eq_polyToField :
    universalX = polyToField (C Polynomial.X) := rfl

/-- Y coordinate is the image of the polynomial Y under polyToField. -/
theorem universalY_eq_polyToField :
    universalY = polyToField Polynomial.X := rfl

/-- The defining polynomial of the universal curve is zero in its coordinate
ring. -/
theorem curvePolynomial_eq_zero :
    AdjoinRoot.mk curve.toAffine.polynomial curve.toAffine.polynomial = 0 :=
  AdjoinRoot.mk_self

end Universal
end WeierstrassCurve
end