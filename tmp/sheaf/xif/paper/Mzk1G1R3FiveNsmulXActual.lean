/- R3 milestone M3a (Lead 01:xx): `5P = 4P + P` coordinates via Mathlib's addition law.
Independent of the M2 Legendre identity. REUSE: `Point.add_some`/`Point.add_of_Y_ne`
(`WeierstrassCurve.Affine.Point`), `W.addX`/`W.addY`/`W.slope`; group-law lemmas
`mul_zsmul`, `add_zsmul`, `one_zsmul`. DEDUP: no n=5 coordinate wrapper existed. -/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3FiveNsmulXActual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- `4 • P = 2 • (2 • P)` (iteration of doubling). -/
theorem four_smul_eq_two_smul_two (P : W.Point) :
    (4 : ℤ) • P = (2 : ℤ) • ((2 : ℤ) • P) := by
  rw [show (4 : ℤ) = 2 * 2 from by norm_num, mul_zsmul]

/-- `5 • P = 4 • P + P`. -/
theorem five_smul_eq_four_smul_add (P : W.Point) :
    (5 : ℤ) • P = (4 : ℤ) • P + P := by
  rw [show (5 : ℤ) = 4 + 1 from by norm_num, add_zsmul, one_zsmul]

/-- **M3a**: if `4P = (x₄, y₄)` and `(x₄, y₄) + (x, y)` is not a vertical cancellation,
then `5P` has the addition-law coordinates `addX x₄ x (slope x₄ x y₄ y)` and
`addY x₄ x y₄ (slope x₄ x y₄ y)`. -/
theorem five_smul_some_eq {x y x₄ y₄ : F} (hns : W.Nonsingular x y)
    (hns₄ : W.Nonsingular x₄ y₄)
    (h4 : (4 : ℤ) • Point.some x y hns = Point.some x₄ y₄ hns₄)
    (hxy : ¬(x₄ = x ∧ y₄ = W.negY x y)) :
    (5 : ℤ) • Point.some x y hns =
      Point.some (W.addX x₄ x (W.slope x₄ x y₄ y)) (W.addY x₄ x y₄ (W.slope x₄ x y₄ y))
        (nonsingular_add hns₄ hns hxy) := by
  rw [five_smul_eq_four_smul_add, h4]
  exact Point.add_some hxy

#print axioms four_smul_eq_two_smul_two
#print axioms five_smul_eq_four_smul_add
#print axioms five_smul_some_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1R3FiveNsmulXActual
