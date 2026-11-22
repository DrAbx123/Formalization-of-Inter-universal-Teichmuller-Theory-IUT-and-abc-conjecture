import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import tmp.sheaf.xif.paper.S517EtThSpecialTwoTorsionGapActual

-- S617: the minimal actual item is the origin point of any Weierstrass
-- special fiber.  Point reduction and componentOf remain exact.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S617SpecialFiberOriginActual

open WeierstrassCurve

universe u
variable {R : Type u} [CommRing R]

-- Actual origin: the point at infinity of the projective special fiber.
noncomputable def specialFiberOrigin (W : WeierstrassCurve R) :
    W.toProjective.Point :=
  WeierstrassCurve.Projective.Point.zero

theorem specialFiberOrigin_eq_zero (W : WeierstrassCurve R) :
    specialFiberOrigin W = WeierstrassCurve.Projective.Point.zero := rfl

structure SpecialFiberOriginData (W : WeierstrassCurve R) where
  origin : W.toProjective.Point
  origin_eq : origin = WeierstrassCurve.Projective.Point.zero

noncomputable def specialFiberOriginData (W : WeierstrassCurve R) :
    SpecialFiberOriginData W where
  origin := specialFiberOrigin W
  origin_eq := specialFiberOrigin_eq_zero W

-- Exact minimal remaining API: componentOf and point reduction.
structure SpecialFiberComponentGap (W : WeierstrassCurve R) where
  componentType : Type u
  componentOf : W.toProjective.Point → componentType
  originComponent : componentType
  reductionMap : W.toProjective.Point → W.toProjective.Point
  reduction_origin : reductionMap WeierstrassCurve.Projective.Point.zero = WeierstrassCurve.Projective.Point.zero

#check specialFiberOrigin
#check specialFiberOriginData
#check specialFiberOrigin_eq_zero
#check SpecialFiberComponentGap

end LeanFormal.IUT.XiFPaper.S617SpecialFiberOriginActual

end