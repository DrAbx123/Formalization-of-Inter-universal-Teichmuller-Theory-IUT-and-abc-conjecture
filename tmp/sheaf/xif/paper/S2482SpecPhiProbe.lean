import tmp.sheaf.xif.paper.S2482UnderlyingSquareActual

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2482SpecPhiProbe
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual
open CategoryTheory AlgebraicGeometry

theorem S2482AffineOver_left :
    S2482AffineOver.left = S2482AffineScheme := rfl

noncomputable def S2482Phi (η : S2482Orbicurve.Hom S2482Orbicurve) :
    S2482CoordinateRing →+* S2482CoordinateRing :=
  (Spec.homEquiv (S := CommRingCat.of S2482CoordinateRing)
    (R := CommRingCat.of S2482CoordinateRing)
    (S2482Underlying η).left).hom

#check S2482AffineOver_left
#check S2482Phi
end LeanFormal.IUT.XiFPaper.S2482SpecPhiProbe
end