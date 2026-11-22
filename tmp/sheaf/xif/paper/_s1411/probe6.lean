import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Jacobian

example {F : Type*} [Field F] (P : Fin 3 → F) : ((-1 : F) • P) 0 = P 0 := by
  simp [WeierstrassCurve.Jacobian.smul_fin3]

example {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} (X Y Z : F) :
    (![X, -W.toJacobian.negY ![X, Y, Z], -Z] : Fin 3 → F) =
      (-1 : F) • W.toJacobian.neg (![X, Y, Z] : Fin 3 → F) := by
  funext i
  fin_cases i <;>
    simp [WeierstrassCurve.Jacobian.neg, WeierstrassCurve.Jacobian.negY]
