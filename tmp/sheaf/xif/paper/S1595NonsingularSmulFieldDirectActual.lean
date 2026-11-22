import tmp.sheaf.xif.paper.S1594NonsingularSmulFieldActual
import tmp.sheaf.xif.paper.S1577CuspPsiEvalActual
/-! # S1595: direct nonsingular smulField — exact equation/derivative stop
Jacobian.Nonsingular = Equation + one partial derivative nonzero.  The
homogeneous equation at smulField and the derivative nonvanishing are not in
the tree; the exact targets are recorded and the implication to Nonsingular is
proved.  No fake coordinates. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1595NonsingularSmulFieldDirectActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
def S1595SmulFieldEquation : Prop :=
  ∀ n : ℤ, (pointedCurve.toJacobian).Equation (smulField n)
def S1595SmulFieldDerivativeZ : Prop :=
  ∀ n : ℤ, MvPolynomial.eval (smulField n)
      (pointedCurve.toJacobian).polynomialZ ≠ 0
theorem s1595Nonsingular_of_equation_of_derivativeZ (n : ℤ)
    (hEq : (pointedCurve.toJacobian).Equation (smulField n))
    (hD : MvPolynomial.eval (smulField n)
      (pointedCurve.toJacobian).polynomialZ ≠ 0) :
    (pointedCurve.toJacobian).Nonsingular (smulField n) := by
  refine (WeierstrassCurve.Jacobian.nonsingular_iff (W' :=
    pointedCurve.toJacobian) (smulField n)).mpr
    ⟨hEq, Or.inr (Or.inr ?_)⟩
  simpa [WeierstrassCurve.Jacobian.eval_polynomialZ] using hD
#check S1595SmulFieldEquation
#check S1595SmulFieldDerivativeZ
#check s1595Nonsingular_of_equation_of_derivativeZ
end LeanFormal.IUT.XiFPaper.S1595NonsingularSmulFieldDirectActual
end
