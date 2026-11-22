import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

theorem wCoord_add_of_X_ne {u v x y : K}
    (hA : W.Nonsingular u v) (hP : W.Nonsingular x y) (hux : u ≠ x) :
    wCoord W (WeierstrassCurve.Affine.Point.some u v hA +
        WeierstrassCurve.Affine.Point.some x y hP) =
      (wCoord W (WeierstrassCurve.Affine.Point.some x y hP) *
          (u - W.addX u x (W.slope u x v y)) -
        wCoord W (WeierstrassCurve.Affine.Point.some u v hA) *
          (x - W.addX u x (W.slope u x v y))) / (x - u) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hux, wCoord_some]
  have h := WeierstrassCurve.Affine.addY_sub_negY_addY (W := W.toAffine) v y hux
  dsimp only at h
  have hw : 2 * W.addY u x v (W.slope u x v y) + W.a₁ * W.addX u x (W.slope u x v y) + W.a₃ =
      W.addY u x v (W.slope u x v y) -
        W.negY (W.addX u x (W.slope u x v y)) (W.addY u x v (W.slope u x v y)) := by
    rw [WeierstrassCurve.Affine.negY]; ring
  rw [hw, h]
  simp only [wCoord_some, WeierstrassCurve.Affine.negY]
  ring

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
