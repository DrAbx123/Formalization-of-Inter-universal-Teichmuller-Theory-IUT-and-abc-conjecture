import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1472ZSMulOmegaPortActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual

/-! # S1557: selected TauCeti ZSMul point-formula layer

TauCeti `DivisionPolynomial/ZSMul.lean` proves `zsmul_point_eq_smulEval` from
the omega defining identity `ω_spec`/`two_mul_ω`, the doubling/addition
identities `dblXYZ_smulEval`/`addXYZ_smulEval`, and the affine recursion.

S1523/S1530/S1533/S1535 supply the universal curve/ring/field/smulX/smulY,
S1472 the concrete smulEval triple, and S1491 the EDS-net theorem.  S1410
explicitly leaves `two_mul_omega` unproved, so the omega defining identity
and the affine recursion are recorded here as exact missing Props.  No point
formula is assumed and no coordinate is fabricated. -/

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S1557ZSMulPointFormulaActual

open WeierstrassCurve
open WeierstrassCurve.Universal

universe u

/-- Exact missing omega defining identity: TauCeti's `ω_spec`/`two_mul_ω`, at a
concrete affine point. -/
def S1557OmegaDefiningIdentity {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  forall (x y : F) (n : Int),
    2 * Polynomial.evalEval x y (W.ω n) +
        W.a₁ * Polynomial.evalEval x y (W.φ n) *
          Polynomial.evalEval x y (W.ψ n) +
        W.a₃ * (Polynomial.evalEval x y (W.ψ n)) ^ 3 =
      Polynomial.evalEval x y (W.ψc n)

/-- Exact missing doubling identity for the concrete smulEval triple. -/
def S1557DblXYZIdentity {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  forall (x y : F) (n : Int),
    WeierstrassCurve.Jacobian.dblXYZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      S1472ZSMulOmegaPortActual.smulEval W x y (2 * n)

/-- Exact missing addition identity for the concrete smulEval triple. -/
def S1557AddXYZIdentity {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  forall (x y : F) (m n : Int),
    WeierstrassCurve.Jacobian.addXYZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y m)
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      Polynomial.evalEval x y (W.ψ (n - m)) •
        S1472ZSMulOmegaPortActual.smulEval W x y (n + m)

/-- Exact missing affine recursion identities used by TauCeti's final induction. -/
def S1557AffineRecursion : Prop :=
  (forall n : Int, smulX n * polyToField (curve.toAffine.ψ n) ^ 2 =
      polyToField (curve.toAffine.φ n)) ∧
  (forall n : Int, smulY n * polyToField (curve.toAffine.ψ n) ^ 3 =
      polyToField (curve.toAffine.ω n))

/-- Target point formula, exactly TauCeti's `zsmul_point_eq_smulEval` read on
the actual concrete `smulEval` triple of S1472. -/
def S1557ZSMulPointFormula {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop :=
  forall (x y : F) (h : W.Nonsingular x y) (n : Int),
    (n • (WeierstrassCurve.Affine.Point.some x y h).toJacobian).point =
      ⟦S1472ZSMulOmegaPortActual.smulEval W x y n⟧

#check S1557OmegaDefiningIdentity
#check S1557DblXYZIdentity
#check S1557AddXYZIdentity
#check S1557AffineRecursion
#check S1557ZSMulPointFormula

end LeanFormal.IUT.XiFPaper.S1557ZSMulPointFormulaActual
end
