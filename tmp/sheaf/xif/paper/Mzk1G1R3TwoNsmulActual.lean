/- R3 milestone M1 (Lead approved): the doubling step for the 5-division x-coordinate chain.
REUSE (Mathlib `AlgebraicGeometry.EllipticCurve.Affine.Point`): `Point`, `Point.add`,
`add_self_of_Y_ne`, `nonsingular_add`; division polynomials from `DivisionPolynomial.Basic`.
DEDUP: no doubling wrapper existed in our tree. -/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulActual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Doubling as a group-law identity: `(2 : ℤ) • P = P + P`. -/
theorem two_smul_eq_add (P : W.Point) : (2 : ℤ) • P = P + P := by
  change ((2 : ℕ) : ℤ) • P = P + P
  rw [natCast_zsmul, two_nsmul]

/-- **M1 doubling step**: for a nonsingular affine point `P = (x, y)` that is not
2-torsion (`y ≠ -y - a₁x - a₃`), the double `2 • P` equals the sum `P + P` computed by
Mathlib's addition law (`add_self_of_Y_ne` gives the `nonsingular_add` representative).
The comparison with `Φ 2 / ΨSq 2` is the next milestone. -/
theorem two_nsmul_some_eq {x y : F} (hns : W.Nonsingular x y)
    (hy : y ≠ W.negY x y) :
    (2 : ℤ) • Point.some x y hns = Point.some x y hns + Point.some x y hns := by
  exact two_smul_eq_add W _

/-- Explicit `nonsingular_add` representative of the double (Mathlib `add_self_of_Y_ne`). -/
theorem two_nsmul_some_eq_add_self {x y : F} (hns : W.Nonsingular x y)
    (hy : y ≠ W.negY x y) :
    (2 : ℤ) • Point.some x y hns =
      Point.some _ _ (nonsingular_add hns hns fun hxy => hy hxy.right) := by
  rw [two_smul_eq_add]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := W) hy

#print axioms two_smul_eq_add
#print axioms two_nsmul_some_eq
#print axioms two_nsmul_some_eq_add_self
end LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulActual