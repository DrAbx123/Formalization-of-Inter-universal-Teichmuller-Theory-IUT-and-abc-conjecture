import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

example {x y : K} (h : W.Nonsingular x y)
    (hy : y ≠ W.negY x y) (lam : K) (hlam : lam = W.slope x x y y) :
    wCoord W (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) =
      -(2 * y + W.a₁ * x + W.a₃) -
        (W.a₁ + 2 * lam) * (W.addX x x lam - x) := by
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  simp only [wCoord_some, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY]
  rw [hlam]
  ring

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
