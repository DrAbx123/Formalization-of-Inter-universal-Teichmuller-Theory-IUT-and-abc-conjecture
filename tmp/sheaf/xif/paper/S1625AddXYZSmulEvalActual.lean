import tmp.sheaf.xif.paper.S1624ZSMulEvalFinalActual
import tmp.sheaf.xif.paper.S1593ZSMulFieldActual
import tmp.sheaf.xif.paper.S1597UniversalAffineFullActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1625AddXYZSmulEvalActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1624ZSMulEvalFinalActual
theorem s1625PolyMap_CC (a : MvPolynomial Coeff ℤ) :
    polyMap a = CC a := rfl
theorem s1625SmulPoly_neg (n : ℤ) :
    Universal.smulPoly (-n) =
      (-1 : Universal.Poly) • Jacobian.neg curvePoly (Universal.smulPoly n) := by
  funext i
  fin_cases i <;> simp [Universal.smulPoly, Jacobian.smul_fin3,
    Jacobian.neg, Jacobian.negY, s1625PolyMap_CC,
    WeierstrassCurve.Universal.S1597UniversalOmegaNeg] <;> ring
def S1625AddXYZSmulField : Prop :=
  ∀ m n : ℤ,
    Jacobian.addXYZ pointedCurve (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m)
#check S1625AddXYZSmulField
theorem s1625SmulField_neg (n : ℤ) :
    smulField (-n) =
      (-1 : Universal.Field) • Jacobian.neg pointedCurve (smulField n) := by
  have hneg1 : polyToField (-1 : Universal.Poly) = (-1 : Universal.Field) := by
    exact (map_neg polyToField (1 : Universal.Poly)).trans (by rw [map_one])
  funext i
  fin_cases i <;> simp [smulField, s1625SmulPoly_neg, Jacobian.smul_fin3,
    Jacobian.neg, Jacobian.negY, map_mul, map_pow,
    pointedCurve, curvePoly, WeierstrassCurve.map]
  all_goals rw [hneg1]
  all_goals simp
end LeanFormal.IUT.XiFPaper.S1625AddXYZSmulEvalActual

end
