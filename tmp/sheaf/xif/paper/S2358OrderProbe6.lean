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

namespace TestOrder6

universe u
variable {R : Type u} [Field R] [DecidableEq R]
variable (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

theorem test (h2 : (2 : R) ≠ 0) (x : R)
    (hx : W.twoTorsionPolynomial.toPoly.eval x = 0) :
    (2 : Nat) • S2354Point W h2 x hx = 0 := by
  letI : AddCommGroup W.toAffine.Point := inferInstance
  let P : W.toAffine.Point := S2354Point W h2 x hx
  have hy : W.toAffine.negY x (S2337Y W x) = S2337Y W x := by
    unfold WeierstrassCurve.Affine.negY S2337Y
    field_simp [h2]
    ring
  have hPP : P = -P := by
    simp only [P, S2354Point, WeierstrassCurve.Affine.Point.mk]
    rw [WeierstrassCurve.Affine.Point.neg_def]
    simp only [WeierstrassCurve.Affine.Point.neg]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨trivial, hy⟩
  have hsum : P + P = 0 := add_eq_zero_iff_eq_neg.mpr hPP
  simpa [two_nsmul] using hsum

end TestOrder6
