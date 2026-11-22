import tmp.sheaf.xif.paper.S1560ZSMulPointFormulaFromOmegaActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual

/-! # S1572: Z-coordinate identities for smulEval — exact first polynomial gap

TauCeti `DivisionPolynomial/ZSMul.lean` proves:

```text
dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2*n)
addZ_smulPoly : addZ (smulPoly m) (smulPoly n) =
  curve.ψ (n+m) * curve.ψ (n-m)
```

then `dblXYZ_smulField`/`addXYZ_smulField` and the concrete
`dblXYZ_smulEval`/`addXYZ_smulEval`.  The current tree has the omega input
(S1521) and the EDS-net input (S1491), but not the S1523 nested-polynomial
`curvePoly` specialization or the XYZ point upgrade.  This file records the
exact missing Z identities on the concrete smulEval triple; no coordinate is
fabricated. -/

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1572ZCoordinateSmulActual

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- Exact missing `dblZ_smulPoly` on the concrete triple. -/
def S1572DblZSmulEval : Prop :=
  forall (x y : F) (n : Int),
    WeierstrassCurve.Jacobian.dblZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      Polynomial.evalEval x y (W.ψ (2 * n))

/-- Exact missing `addZ_smulPoly` on the concrete triple. -/
def S1572AddZSmulEval : Prop :=
  forall (x y : F) (m n : Int),
    WeierstrassCurve.Jacobian.addZ
        (S1472ZSMulOmegaPortActual.smulEval W x y m)
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      Polynomial.evalEval x y (W.ψ (n + m) * W.ψ (n - m))

/-- Exact missing XYZ upgrade: from the Z identities to the full doubling
triple identity. -/
def S1572DblXYZMissing : Prop :=
  forall (x y : F) (n : Int),
    WeierstrassCurve.Jacobian.dblXYZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      S1472ZSMulOmegaPortActual.smulEval W x y (2 * n)

/-- Exact missing XYZ upgrade for addition. -/
def S1572AddXYZMissing : Prop :=
  forall (x y : F) (m n : Int),
    WeierstrassCurve.Jacobian.addXYZ W
        (S1472ZSMulOmegaPortActual.smulEval W x y m)
        (S1472ZSMulOmegaPortActual.smulEval W x y n) =
      Polynomial.evalEval x y (W.ψ (n - m)) •
        S1472ZSMulOmegaPortActual.smulEval W x y (n + m)

#check S1572DblZSmulEval
#check S1572AddZSmulEval
#check S1572DblXYZMissing
#check S1572AddXYZMissing

end LeanFormal.IUT.XiFPaper.S1572ZCoordinateSmulActual
end
