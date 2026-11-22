/- R3 milestone M2b (exact forms; Lead/grace ruled out the naive `ψ₄/ψ₂³` bridge): the
EXACT doubling slope and y-coordinate formulas in terms of Mathlib's `slope`/`addX`/`addY`.
REUSE: `Mzk1G1R3TwoNsmulXActual.two_nsmul_some_x` (full coordinate equality),
`WeierstrassCurve.Affine.{slope_of_Y_ne, addX, addY, negY, negAddY}` (Mathlib).
DEDUP: no exact-form expansion existed in the tree. -/
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulXActual
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulYActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulXActual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- The exact doubling slope (no guessing of division-polynomial relations). -/
theorem two_nsmul_slope_eq {x y : F} (hy : y ≠ W.negY x y) :
    W.slope x x y y =
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (y - W.negY x y) :=
  W.slope_of_Y_ne rfl hy

/-- The exact doubling y-coordinate, expanded through `addY = negY (addX) (negAddY)`. -/
theorem two_nsmul_addY_eq {x y : F} (hy : y ≠ W.negY x y) :
    W.addY x x y (W.slope x x y y) =
      -(W.slope x x y y * (W.addX x x (W.slope x x y y) - x) + y)
        - W.a₁ * W.addX x x (W.slope x x y y) - W.a₃ := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, mul_zero, zero_mul, add_zero]

/-- The doubling slope in the `-polynomialX / polynomialY` form (Mathlib exact identity). -/
theorem two_nsmul_slope_eq_evalEval {x y : F} (hy : y ≠ W.negY x y) :
    W.slope x x y y =
      -W.polynomialX.evalEval x y / W.polynomialY.evalEval x y :=
  W.slope_of_Y_ne_eq_evalEval rfl hy

#print axioms two_nsmul_slope_eq
#print axioms two_nsmul_addY_eq
#print axioms two_nsmul_slope_eq_evalEval
end LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulYActual