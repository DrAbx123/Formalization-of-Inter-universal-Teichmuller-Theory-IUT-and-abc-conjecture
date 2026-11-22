import tmp.sheaf.xif.paper.S2354TwoTorsionPointsActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual
open LeanFormal.IUT.XiFPaper.S2353TwoTorsionEquationActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual

namespace TestOrder3

universe u
variable {R : Type u} [Field R]
variable (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

#check WeierstrassCurve.Affine.Point.instAddCommGroup
#synth AddCommGroup (WeierstrassCurve.Affine.Point W.toAffine)

end TestOrder3
