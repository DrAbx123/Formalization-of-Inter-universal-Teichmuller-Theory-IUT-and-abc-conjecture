import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1472ZSMulOmegaPortActual

/-! # S1560: omega identity and the remaining ZSMul affine/doubling gaps

S1521 proves TauCeti's `ω_spec`/`two_mul_ω`.  This file specializes the omega
identity to a concrete affine point, then records the exact remaining
TauCeti `ZSMul.lean` inputs: the doubling and addition identities for the
SMulEval triple, and the affine recursion.  No point-coordinate formula is
assumed; the general bridge is still conditional on these Props. -/

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1560ZSMulPointFormulaFromOmegaActual

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- The omega defining identity from S1521, evaluated at a concrete point.
(recorded as a Prop; its proof is the S1521 `ω_spec` specialization). -/
def S1560OmegaEvalIdentity : Prop :=
  forall (x y : F) (n : Int),
    2 * Polynomial.evalEval x y (W.ω n) +
        W.a₁ * Polynomial.evalEval x y (W.φ n) *
          Polynomial.evalEval x y (W.ψ n) +
        W.a₃ * (Polynomial.evalEval x y (W.ψ n)) ^ 3 =
      Polynomial.evalEval x y (W.ψc n)

/-- Exact remaining doubling identity for the concrete smulEval triple. -/
def S1560DblXYZIdentity : Prop :=
  forall (x y : F) (n : Int),
    WeierstrassCurve.Jacobian.dblXYZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      S1472ZSMulOmegaPortActual.smulEval W x y (2 * n)

/-- Exact remaining addition identity for the concrete smulEval triple. -/
def S1560AddXYZIdentity : Prop :=
  forall (x y : F) (m n : Int),
    WeierstrassCurve.Jacobian.addXYZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y m)
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      Polynomial.evalEval x y (W.ψ (n - m)) •
        S1472ZSMulOmegaPortActual.smulEval W x y (n + m)

/-- Exact remaining affine recursion identities (TauCeti `smulX_add` /
`smulY_add_sub_negY`), stated at the universal smulX/smulY layer of S1535. -/
def S1560AffineRecursion : Prop :=
  (forall n : Int, WeierstrassCurve.Universal.smulX n *
      WeierstrassCurve.Universal.polyToField
        (WeierstrassCurve.Universal.curve.toAffine.ψ n) ^ 2 =
      WeierstrassCurve.Universal.polyToField
        (WeierstrassCurve.Universal.curve.toAffine.φ n)) ∧
  (forall n : Int, WeierstrassCurve.Universal.smulY n *
      WeierstrassCurve.Universal.polyToField
        (WeierstrassCurve.Universal.curve.toAffine.ψ n) ^ 3 =
      WeierstrassCurve.Universal.polyToField
        (WeierstrassCurve.Universal.curve.toAffine.ω n))

/-- Target: TauCeti `zsmul_point_eq_smulEval` on the concrete triple. -/
def S1560ZSMulPointFormula : Prop :=
  forall (x y : F) (h : W.Nonsingular x y) (n : Int),
    (n • (WeierstrassCurve.Affine.Point.some x y h).toJacobian).point =
      ⟦S1472ZSMulOmegaPortActual.smulEval W x y n⟧

#check S1560OmegaEvalIdentity
#check S1560DblXYZIdentity
#check S1560AddXYZIdentity
#check S1560AffineRecursion
#check S1560ZSMulPointFormula

end LeanFormal.IUT.XiFPaper.S1560ZSMulPointFormulaFromOmegaActual
end
