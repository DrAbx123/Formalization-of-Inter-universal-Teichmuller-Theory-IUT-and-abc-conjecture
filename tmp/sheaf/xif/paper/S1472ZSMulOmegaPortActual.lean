import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import tmp.sheaf.xif.paper.S1411ZSMulBridgeActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice

/-! # S1472: minimal ZSMul / bivariate omega layer

Mathlib v4.32.2 has bivariate ψ and φ but no bivariate ω and no
`zsmul_eq_smulEval`.  S1410 ports the actual bivariate ω and its evaluation
laws.  This file adds the minimal `smulEval` triple using the actual
`φ`, `ω`, `ψ`, proves its n=0/n=1 values and the n=0/n=1 point-bridge, and
records the exact first fields for the general bridge.  No fake bridge. -/

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

namespace LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual

open WeierstrassCurve WeierstrassCurve.Jacobian
open scoped WeierstrassCurve.Jacobian

universe u

/-- The TauCeti triple `(φ_n, ω_n, ψ_n)` evaluated at an affine point. -/
noncomputable def smulEval {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) (x y : F) (n : ℤ) : Fin 3 → F :=
  ![evalEval x y (W.φ n), evalEval x y (W.ω n), evalEval x y (W.ψ n)]

@[simp] theorem smulEval_apply_zero {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) (x y : F) (n : ℤ) :
    smulEval W x y n 0 = evalEval x y (W.φ n) := rfl

@[simp] theorem smulEval_apply_one {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) (x y : F) (n : ℤ) :
    smulEval W x y n 1 = evalEval x y (W.ω n) := rfl

@[simp] theorem smulEval_apply_two {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) (x y : F) (n : ℤ) :
    smulEval W x y n 2 = evalEval x y (W.ψ n) := rfl

/-- The actual base value `(1, 1, 0)` for `n = 0`. -/
theorem smulEval_zero {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) (x y : F) :
    smulEval W x y 0 = ![1, 1, 0] := by
  funext i
  fin_cases i <;>
    simp [smulEval, WeierstrassCurve.φ_zero, WeierstrassCurve.ω_zero,
      WeierstrassCurve.ψ_zero]

/-- The actual base value `(x, y, 1)` for `n = 1`. -/
theorem smulEval_one {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) (x y : F) :
    smulEval W x y 1 = ![x, y, 1] := by
  funext i
  fin_cases i <;>
    simp [smulEval, WeierstrassCurve.φ_one, WeierstrassCurve.ω_one,
      WeierstrassCurve.ψ_one, Polynomial.evalEval_C, Polynomial.evalEval_X]

/-- The point-bridge at a fixed `n`: the Jacobian class of `n • P` is the
class of the actual `(φ_n, ω_n, ψ_n)` triple. -/
def ZSMulEqSmulEvalAt {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) {x y : F}
    (hns : W.Nonsingular x y) (n : ℤ) : Prop :=
  (n • (WeierstrassCurve.Affine.Point.some x y hns).toJacobian).point =
    ⟦smulEval W x y n⟧

/-- The full bridge `zsmul_eq_smulEval`, stated on the actual integral
`ω` from S1410. -/
def ZSMulEqSmulEval {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  ∀ (x y : F) (hns : W.Nonsingular x y) (n : ℤ),
    (n • (WeierstrassCurve.Affine.Point.some x y hns).toJacobian).point =
      ⟦smulEval W x y n⟧

/-- The bridge at `n = 0`, actual. -/
theorem zsmulEqSmulEvalAt_zero {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) {x y : F} (hns : W.Nonsingular x y) :
    ZSMulEqSmulEvalAt W hns 0 := by
  rw [ZSMulEqSmulEvalAt, zero_zsmul, smulEval_zero]
  exact WeierstrassCurve.Jacobian.Point.zero_point

/-- The bridge at `n = 1`, actual. -/
theorem zsmulEqSmulEvalAt_one {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) {x y : F} (hns : W.Nonsingular x y) :
    ZSMulEqSmulEvalAt W hns 1 := by
  rw [ZSMulEqSmulEvalAt, smulEval_one, one_zsmul]
  simp only [WeierstrassCurve.Affine.Point.toJacobian,
    WeierstrassCurve.Jacobian.Point.fromAffine_some]

/-- Exact first field for the general bridge: the doubling identity for the
actual `smulEval` triple. -/
def DoublingIdentity {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  ∀ (x y : F) (n : ℤ),
    WeierstrassCurve.Jacobian.dblXYZ W (smulEval W x y n) =
      smulEval W x y (2 * n)

/-- Exact first field for the general bridge: the addition identity for
consecutive multiples. -/
def AdditionIdentity {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  ∀ (x y : F) (n : ℤ),
    WeierstrassCurve.Jacobian.addXYZ W (smulEval W x y n)
        (smulEval W x y (n + 1)) =
      smulEval W x y (2 * n + 1)

end LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual

#print axioms LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual.smulEval_zero
#print axioms LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual.smulEval_one
#print axioms LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual.zsmulEqSmulEvalAt_zero
#print axioms LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual.zsmulEqSmulEvalAt_one

end
