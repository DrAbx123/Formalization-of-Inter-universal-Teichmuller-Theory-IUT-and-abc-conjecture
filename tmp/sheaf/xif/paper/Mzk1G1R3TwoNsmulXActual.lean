/- R3 milestone M2a: the x-coordinate of `2 • P` in terms of Mathlib's addition formulas.
REUSE: `Mzk1G1R3TwoNsmulActual.{two_smul_eq_add, two_nsmul_some_eq_add_self}` (this lane),
`WeierstrassCurve.Affine.Point.add_self_of_Y_ne`, `WeierstrassCurve.Affine.nonsingular_add`,
`W.addX`, `W.addY`, `W.slope` (Mathlib). DEDUP: no coordinate-level doubling formula existed.
-/
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulActual
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulXActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulActual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- **M2a**: the double of a nonsingular affine point `(x, y)` that is not 2-torsion is the
point with Mathlib's addition coordinates `addX x x (slope x x y y)` and
`addY x x y (slope x x y y)`. -/
theorem two_nsmul_some_x {x y : F} (hns : W.Nonsingular x y) (hy : y ≠ W.negY x y) :
    (2 : ℤ) • Point.some x y hns =
      Point.some (W.addX x x (W.slope x x y y)) (W.addY x x y (W.slope x x y y))
        (nonsingular_add hns hns fun hxy => hy hxy.right) := by
  exact two_nsmul_some_eq_add_self (W := W) hns hy

#print axioms two_nsmul_some_x
end LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulXActual