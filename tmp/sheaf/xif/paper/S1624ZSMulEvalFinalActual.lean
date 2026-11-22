import tmp.sheaf.xif.paper.S1623ZSMulEvalActual
import tmp.sheaf.xif.paper.S1593ZSMulFieldActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1624ZSMulEvalFinalActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
open LeanFormal.IUT.XiFPaper.S1623ZSMulEvalActual
theorem s1624DblXYZ_smulField (n : ℤ) :
    Jacobian.dblXYZ pointedCurve (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero]
    have h0 : smulField 0 = ![1, 1, 0] := by
      funext i
      fin_cases i <;> simp [smulField, smulPoly, WeierstrassCurve.φ_zero,
        WeierstrassCurve.ω_zero, WeierstrassCurve.ψ_zero]
    have hEq : Jacobian.Equation pointedCurve.toJacobian (smulField 0) := by
      rw [h0]
      exact Jacobian.equation_zero
    rw [Jacobian.dblXYZ_of_Z_eq_zero (W' := pointedCurve.toJacobian) hEq
      (by simp [smulField, smulPoly, WeierstrassCurve.ψ_zero])]
    simpa [h0]
  have h2 : ((2 : ℤ) • (n • s1619Point.toJacobian)).point =
      ⟦Jacobian.dblXYZ pointedCurve (smulField n)⟧ := by
    rw [two_zsmul, Jacobian.Point.add_point, s1623ZSMulPointEqSmulField_all n,
      Jacobian.addMap_eq, Jacobian.add_self]
  have hmul : (2 : ℤ) • (n • s1619Point.toJacobian) =
      (2 * n) • s1619Point.toJacobian := by rw [mul_zsmul]
  have hclass : (⟦Jacobian.dblXYZ pointedCurve (smulField n)⟧ : Jacobian.PointClass Field) =
      ⟦smulField (2 * n)⟧ := by
    rw [← h2, hmul, s1623ZSMulPointEqSmulField_all (2 * n)]
  refine (Jacobian.equiv_iff_eq_of_Z_eq ?_ ?_).mp (Quotient.exact hclass)
  · rw [Jacobian.dblXYZ_Z, dblZ_smulField]
    simp [smulField, smulPoly]
  · simp [smulField, smulPoly]
    exact polyToField_ψ_ne_zero (2 * n) (by omega)
end LeanFormal.IUT.XiFPaper.S1624ZSMulEvalFinalActual
end
