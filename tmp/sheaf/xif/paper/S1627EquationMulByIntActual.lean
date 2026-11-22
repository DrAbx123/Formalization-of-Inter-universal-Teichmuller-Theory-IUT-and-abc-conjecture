import tmp.sheaf.xif.paper.S1626AddXYZSmulEvalPortActual
import tmp.sheaf.xif.paper.S1534GenericPointJacobianActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1627EquationMulByIntActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
open LeanFormal.IUT.XiFPaper.S1534GenericPointJacobianActual
open TauCeti.Isogeny
variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
theorem s1627GenericZSMulEqSmulEval (n : ℤ) :
    (n • (WeierstrassCurve.Affine.genericPoint W).toJacobian).point =
      ⟦s1626SmulEval (W.baseChange W.FunctionField)
        (WeierstrassCurve.Affine.genericX W)
        (WeierstrassCurve.Affine.genericY W) n⟧ := by
  have h := s1626ZSMulPointEqSmulEval
    (W := W.baseChange W.FunctionField)
    (x := WeierstrassCurve.Affine.genericX W)
    (y := WeierstrassCurve.Affine.genericY W)
    (h := WeierstrassCurve.Affine.nonsingular_genericX_genericY W) n
  simpa [WeierstrassCurve.Affine.genericPoint] using h
def S1627SmulEvalGenericX (n : ℤ) : Prop :=
  s1626SmulEval (W.baseChange W.FunctionField)
      (WeierstrassCurve.Affine.genericX W)
      (WeierstrassCurve.Affine.genericY W) n 0 = mulByIntX W n
def S1627SmulEvalGenericY (n : ℤ) : Prop :=
  s1626SmulEval (W.baseChange W.FunctionField)
      (WeierstrassCurve.Affine.genericX W)
      (WeierstrassCurve.Affine.genericY W) n 1 = mulByIntY W n
def S1627SmulEvalGenericZ (n : ℤ) : Prop :=
  s1626SmulEval (W.baseChange W.FunctionField)
      (WeierstrassCurve.Affine.genericX W)
      (WeierstrassCurve.Affine.genericY W) n 2 = psiFunctionField W n
#check s1627GenericZSMulEqSmulEval
#check S1627SmulEvalGenericX
#check S1627SmulEvalGenericY
#check S1627SmulEvalGenericZ
end LeanFormal.IUT.XiFPaper.S1627EquationMulByIntActual
end
