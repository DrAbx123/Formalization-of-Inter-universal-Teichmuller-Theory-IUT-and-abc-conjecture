import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import tmp.sheaf.xif.paper.S2789E37OrbicurveSignActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open WeierstrassCurve
open LeanFormal.IUT
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual

universe u

variable (K : Type u) [Field K] [DecidableEq K]

/-- The affine origin (0,0) of E37: y^2 + y = x^3 - x. -/
noncomputable def E37AffineOrigin : (S2801E37Curve K).toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 0 0 (by
    rw [WeierstrassCurve.Affine.nonsingular_zero]
    constructor
    · rfl
    · left
      norm_num [S2801E37Curve])

/-- The same point as a projective point via the actual projective/affine equivalence. -/
noncomputable def E37ProjectiveOrigin : (S2801E37Curve K).toProjective.Point :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (S2801E37Curve K).toProjective).symm (E37AffineOrigin K)

theorem E37ProjectiveOrigin_ne_zero :
    (E37ProjectiveOrigin K) ≠ 0 := by
  intro h
  have h' := congrArg
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (S2801E37Curve K).toProjective) h
  simp only [E37ProjectiveOrigin, AddEquiv.apply_symm_apply, map_zero] at h'
  change WeierstrassCurve.Affine.Point.some 0 0 _ = 0 at h'
  cases h'


abbrev S2813Base (K : Type u) [Field K] : Iut.SchemeOverField K :=
  Over.mk (𝟙 (Spec (CommRingCat.of K)))

/-- Interface for the missing comparison: F-points of the representable fiber
(morphisms from the base scheme) surject onto the Weierstrass projective points. -/
structure S2813CurvePointRealization (K : Type u) [Field K] [DecidableEq K]
    (X : Iut.SchemeOverField K)
    (C : PuncturedEllipticCurve K) where
  pointMap : (S2813Base K ⟶ X) → C.curve.toProjective.Point
  surjective : Function.Surjective pointMap

#check S2813CurvePointRealization

#check E37AffineOrigin
#check E37ProjectiveOrigin
#check E37ProjectiveOrigin_ne_zero
#print axioms E37ProjectiveOrigin_ne_zero

end LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
end
