import tmp.sheaf.xif.paper.S1627EquationMulByIntActual
import tmp.sheaf.xif.paper.S1467FunctionFieldPullbackActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1628EquationMulByIntFinalActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
open LeanFormal.IUT.XiFPaper.S1627EquationMulByIntActual
open TauCeti.Isogeny
open LeanFormal.IUT.XiFPaper.S1534GenericPointJacobianActual
variable {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
theorem s1628SmulEvalPhi (n : ℤ) :
    s1626SmulEval (W.baseChange W.FunctionField)
      (genericX W) (genericY W) n 0 = phiFunctionField W n := by
  rw [show s1626SmulEval (W.baseChange W.FunctionField) (genericX W) (genericY W) n 0 =
      Polynomial.evalEval (genericX W) (genericY W)
        ((W.baseChange W.FunctionField).φ n) from rfl]
  rw [show (W.baseChange W.FunctionField).φ n =
      (W.φ n).map (mapRingHom (algebraMap F W.FunctionField)) from
        WeierstrassCurve.map_φ (W := W) (f := algebraMap F W.FunctionField) n]
  rw [evalEval_genericX_genericY, phiFunctionField_def]
theorem s1628SmulEvalOmega (n : ℤ) :
    s1626SmulEval (W.baseChange W.FunctionField)
      (genericX W) (genericY W) n 1 = omegaFunctionField W n := by
  rw [show s1626SmulEval (W.baseChange W.FunctionField) (genericX W) (genericY W) n 1 =
      Polynomial.evalEval (genericX W) (genericY W)
        ((W.baseChange W.FunctionField).ω n) from rfl]
  rw [show (W.baseChange W.FunctionField).ω n =
      (W.ω n).map (mapRingHom (algebraMap F W.FunctionField)) from
        WeierstrassCurve.map_ω (W := W) (f := algebraMap F W.FunctionField) n]
  rw [evalEval_genericX_genericY, omegaFunctionField_def]
theorem s1628SmulEvalPsi (n : ℤ) :
    s1626SmulEval (W.baseChange W.FunctionField)
      (genericX W) (genericY W) n 2 = psiFunctionField W n := by
  rw [show s1626SmulEval (W.baseChange W.FunctionField) (genericX W) (genericY W) n 2 =
      Polynomial.evalEval (genericX W) (genericY W)
        ((W.baseChange W.FunctionField).ψ n) from rfl]
  rw [show (W.baseChange W.FunctionField).ψ n =
      (W.ψ n).map (mapRingHom (algebraMap F W.FunctionField)) from
        WeierstrassCurve.map_ψ (W := W) (f := algebraMap F W.FunctionField) n]
  rw [evalEval_genericX_genericY, psiFunctionField_def]
theorem s1628SmulEval_eq_triple (n : ℤ) :
    s1626SmulEval (W.baseChange W.FunctionField)
      (genericX W) (genericY W) n =
        ![phiFunctionField W n, omegaFunctionField W n, psiFunctionField W n] := by
  funext i
  fin_cases i
  · exact s1628SmulEvalPhi W n
  · exact s1628SmulEvalOmega W n
  · exact s1628SmulEvalPsi W n
end LeanFormal.IUT.XiFPaper.S1628EquationMulByIntFinalActual


end
