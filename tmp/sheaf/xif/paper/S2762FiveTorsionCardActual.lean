import tmp.sheaf.xif.paper.S1626AddXYZSmulEvalPortActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2762FiveTorsionCardActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
open WeierstrassCurve
open WeierstrassCurve.Jacobian
open Polynomial

/-- Five-torsion criterion for a nonsingular affine point: 5 • P = 0 iff the
5-division polynomial ψ₅ vanishes at (x,y). Actual, from the ported
s1626ZSMulPointEqSmulEval. -/
theorem S2762_five_zsmul_eq_zero_iff_psi
    {F : Type*} [Field F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (5 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 ↔
      (W.ψ (5 : ℤ)).evalEval x y = 0 := by
  constructor
  · intro hzero
    have hpt := s1626ZSMulPointEqSmulEval W h (5 : ℤ)
    have hclass : (⟦s1626SmulEval W x y (5 : ℤ)⟧ : Jacobian.PointClass F) =
        ⟦(![1, 1, 0] : Fin 3 → F)⟧ := by
      rw [← hpt, hzero]
      exact Jacobian.Point.zero_point
    have hz : s1626SmulEval W x y (5 : ℤ) 2 = 0 := by
      have := (Jacobian.Z_eq_zero_of_equiv (Quotient.eq.mp hclass) :
        s1626SmulEval W x y (5 : ℤ) 2 = 0 ↔ (![1, 1, 0] : Fin 3 → F) 2 = 0)
      exact this.mpr rfl
    simpa [s1626SmulEval, s1626EvalEval_ψ] using hz
  · intro hψ
    have hpt := s1626ZSMulPointEqSmulEval W h (5 : ℤ)
    have hns : W.toJacobian.NonsingularLift ⟦s1626SmulEval W x y (5 : ℤ)⟧ := by
      rw [← hpt]
      exact (5 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) |>.nonsingular
    have hz : s1626SmulEval W x y (5 : ℤ) 2 = 0 := by
      simpa [s1626SmulEval, s1626EvalEval_ψ] using hψ
    have heq : s1626SmulEval W x y (5 : ℤ) ≈ (![1, 1, 0] : Fin 3 → F) :=
      Jacobian.equiv_zero_of_Z_eq_zero hns hz
    apply Jacobian.Point.ext_iff.mpr
    rw [hpt, Jacobian.Point.zero_point]
    exact Quotient.sound heq

#check S2762_five_zsmul_eq_zero_iff_psi
#print axioms S2762_five_zsmul_eq_zero_iff_psi

end LeanFormal.IUT.XiFPaper.S2762FiveTorsionCardActual
end
