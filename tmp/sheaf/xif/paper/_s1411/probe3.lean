import tmp.sheaf.xif.paper.S1373ZeroCriterionActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

open Polynomial WeierstrassCurve

universe u

example {F : Type u} [Field F] {W : WeierstrassCurve.Affine F} {x y : F} {hns : W.Nonsingular x y} {n : ℤ}
    (X Y : F) (Z : F) :
    (![X, -W.toJacobian.negY ![X, Y, Z], -Z] : Fin 3 → F) =
      (-1 : F) • W.toJacobian.neg (![X, Y, Z] : Fin 3 → F) := by
  funext i
  fin_cases i <;>
    simp [WeierstrassCurve.Jacobian.neg, WeierstrassCurve.Jacobian.negY]

#check @WeierstrassCurve.Jacobian.nonsingular_smul
#check @WeierstrassCurve.Jacobian.nonsingular_neg
#check WeierstrassCurve.Jacobian.PointClass
#check @WeierstrassCurve.Jacobian.PointClass

example {F : Type u} [Field F] {W : WeierstrassCurve.Affine F} {x y : F} {hns : W.Nonsingular x y} {n : ℤ} :
    True := by trivial
