import tmp.sheaf.xif.paper.S1544LTorsionKernelFieldActual
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitMultiplicativeCurve
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
/-! # S1587: Gaussian CM endomorphism — actual curve type mismatch
The S1280 Gaussian curve is the base change of y^2 + xy = x^3 + 5 (a1=1,
a6=5), not y^2 = x^3 - x.  The proposed CM map (x,y) -> (-x, i y) preserves
y^2 = x^3 - x, but not the actual Gaussian Weierstrass equation.  Therefore the
CM endomorphism and its mod-l matrix J are not constructed from this map; the
exact first missing is an actual CM endomorphism of the actual Gaussian curve
(if one exists) or a proof that the target curve is a different model.  No fake
CM map is used. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
namespace LeanFormal.IUT.XiFPaper.S1587GaussianCMEndomorphismActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1544LTorsionKernelFieldActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
variable {l : PrimeGeFive}
theorem S1587GaussianCurve_a₁ :
    (GaussianCurve (l := l)).curve.a₁ = (1 : (S1280Arithmetic l).F) := by
  change (concreteSplitPuncturedCurve.baseChange (S1280Arithmetic l).F).curve.a₁ = 1
  simp [concreteSplitPuncturedCurve, concreteSplitCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁]
theorem S1587GaussianCurve_a₆ :
    (GaussianCurve (l := l)).curve.a₆ = (5 : (S1280Arithmetic l).F) := by
  change (concreteSplitPuncturedCurve.baseChange (S1280Arithmetic l).F).curve.a₆ = 5
  simp [concreteSplitPuncturedCurve, concreteSplitCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆]
theorem S1587GaussianCurve_not_y2_x3_sub_x :
    (GaussianCurve (l := l)).curve ≠ curveY2EqX3SubX.baseChange (S1280Arithmetic l).F := by
  intro h
  have h1 := congrArg (fun W : WeierstrassCurve (S1280Arithmetic l).F => W.a₁) h
  rw [S1587GaussianCurve_a₁] at h1
  simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, curveY2EqX3SubX] at h1
end LeanFormal.IUT.XiFPaper.S1587GaussianCMEndomorphismActual
end
