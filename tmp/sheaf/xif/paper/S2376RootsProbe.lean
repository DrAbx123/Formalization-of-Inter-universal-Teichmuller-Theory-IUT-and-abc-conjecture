import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open WeierstrassCurve Polynomial

namespace TestThreeRoots

universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

theorem three_roots (h2 : (2 : R) ≠ 0) :
    ∃ x1 x2 x3 : AlgebraicClosure R,
      x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 := by
  let φ : R →+* AlgebraicClosure R := algebraMap R _
  let P : Cubic R := W.twoTorsionPolynomial
  have ha : P.a ≠ 0 := by
    simp only [P, WeierstrassCurve.twoTorsionPolynomial]
    norm_num [h2]
  have hP : (P.toPoly.map φ).Splits := IsAlgClosed.splits _
  obtain ⟨x, y, z, hxyz⟩ := (Cubic.splits_iff_roots_eq_three (P := P) (φ := φ) ha).mp hP
  have hd : P.discr ≠ 0 := by
    exact W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr h2)
  have hne := (Cubic.discr_ne_zero_iff_roots_ne (P := P) (φ := φ) ha hxyz).mp hd
  exact ⟨x, y, z, hne⟩

end TestThreeRoots
