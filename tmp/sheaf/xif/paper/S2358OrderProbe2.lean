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

namespace TestOrder2

universe u
variable {R : Type u} [Field R]
variable (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

example : Nonempty (AddCommGroup W.Point) := ⟨inferInstance⟩

theorem test (h2 : (2 : R) ≠ 0) (x : R)
    (hx : W.twoTorsionPolynomial.toPoly.eval x = 0) :
    (2 : Nat) • S2354Point W h2 x hx = 0 := by
  letI : AddCommGroup W.toAffine.Point := inferInstanceAs (AddCommGroup W.Point)
  let P : W.toAffine.Point := S2354Point W h2 x hx
  have hPP : P = -P := by
    simp only [P, S2354Point, WeierstrassCurve.Affine.Point.mk]
    rw [WeierstrassCurve.Affine.Point.neg_def]
    simp only [WeierstrassCurve.Affine.Point.neg]
    sorry
  sorry

end TestOrder2
