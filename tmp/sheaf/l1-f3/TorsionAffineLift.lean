import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# L1-F3 F3.a sublemmas (a2)/(a3): affine lift of nonzero torsion

For a nonzero projective point on a Weierstrass curve over a field, the affine
lift is nonzero, and therefore is an affine point some x y h; in particular the
x-coordinate is available. No division-polynomial input is needed.
-/

open LeanFormal.IUT
open WeierstrassCurve

namespace LeanFormal.IUT.L1F3.TorsionAffineLift

universe u

variable {K : Type u} [Field K]

/-- Nonzero projective point has nonzero affine lift. -/
theorem toAffineLift_ne_zero_of_ne_zero
    (W : WeierstrassCurve K)
    (P : W.toProjective.Point) (hP : P ≠ 0) :
    P.toAffineLift ≠ 0 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  intro h
  apply hP
  apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv W.toProjective).injective
  rw [h, WeierstrassCurve.Projective.Point.toAffineLift_zero]

/-- Every nonzero projective point has an explicit affine representative
some x y h, in particular an x-coordinate. -/
theorem exists_affineLift_some_of_ne_zero
    (W : WeierstrassCurve K)
    (P : W.toProjective.Point) (hP : P ≠ 0) :
    ∃ (x y : K) (h : W.toAffine.Nonsingular x y),
      P.toAffineLift = WeierstrassCurve.Affine.Point.some x y h := by
  classical
  letI : DecidableEq K := Classical.decEq K
  have hne : P.toAffineLift ≠ 0 :=
    toAffineLift_ne_zero_of_ne_zero W P hP
  cases hlift : P.toAffineLift with
  | zero => exact (hne hlift).elim
  | some x y h => exact ⟨x, y, h, hlift⟩

/-- Nonzero l-torsion point of the actual source curve has an explicit affine
lift some x y h. -/
theorem torsion_exists_affineLift_some
    (X : PuncturedEllipticCurve K) (l : PrimeGeFive)
    (P : X.LTorsion l)
    (hP : (P : X.AlgebraicClosurePoint) ≠ 0) :
    ∃ (x y : AlgebraicClosure K)
      (h : (X.curve.toAffine.baseChange (AlgebraicClosure K)).Nonsingular x y),
      ((P : X.AlgebraicClosurePoint).toAffineLift =
        WeierstrassCurve.Affine.Point.some x y h) :=
  exists_affineLift_some_of_ne_zero
    (X.curve.baseChange (AlgebraicClosure K))
    (P : X.AlgebraicClosurePoint) hP

end LeanFormal.IUT.L1F3.TorsionAffineLift
