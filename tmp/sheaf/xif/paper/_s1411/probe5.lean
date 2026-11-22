import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

open Polynomial WeierstrassCurve

example {F : Type*} [Field F] (P : Fin 3 → F) :
    ((-1 : F) • P) 0 = (-1 : F) ^ 2 * P 0 := by
  simp [WeierstrassCurve.Jacobian.smul_fin3]

example {F : Type*} [Field F] (P : Fin 3 → F) :
    ((-1 : F) • P) 0 = P 0 := by
  simp

example {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} (X Y Z : F) :
    (((-1 : F) • W.toJacobian.neg (![X, Y, Z] : Fin 3 → F)) 0) = X := by
  simp [WeierstrassCurve.Jacobian.neg, WeierstrassCurve.Jacobian.negY]

example {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} (X Y Z : F) :
    (![X, -W.toJacobian.negY ![X, Y, Z], -Z] : Fin 3 → F) =
      (-1 : F) • W.toJacobian.neg (![X, Y, Z] : Fin 3 → F) := by
  funext i
  fin_cases i <;>
    simp [WeierstrassCurve.Jacobian.neg, WeierstrassCurve.Jacobian.negY]
