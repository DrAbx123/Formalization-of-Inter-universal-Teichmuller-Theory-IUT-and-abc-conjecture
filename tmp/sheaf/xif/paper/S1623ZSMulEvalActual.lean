import tmp.sheaf.xif.paper.S1622ZSMulInductionStepActual
import tmp.sheaf.xif.paper.S1593ZSMulFieldActual
import tmp.sheaf.xif.paper.S1605PointedCurveCoeffActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1623ZSMulEvalActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
open LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual
theorem s1623ZSMulPointEqSmulField (n : ℤ) (h0 : n ≠ 0) :
    (n • s1619Point.toJacobian).point = ⟦smulField n⟧ := by
  obtain ⟨hns, hpoint⟩ := s1622ZSMulPointFormula n h0
  have hmap : (n • s1619Point).toJacobian = n • s1619Point.toJacobian := by
    simpa [Affine.Point.toJacobian] using
      (map_zsmul (Jacobian.Point.toAffineAddEquiv (W := pointedCurve)).symm n s1619Point)
  rw [← hmap, hpoint]
  change (Affine.Point.some (smulX n) (smulY n) hns).toJacobian.point = ⟦smulField n⟧
  rw [show (Affine.Point.some (smulX n) (smulY n) hns).toJacobian =
      Jacobian.Point.fromAffine (Affine.Point.some (smulX n) (smulY n) hns) from rfl]
  rw [Jacobian.Point.fromAffine_some]
  change ⟦![smulX n, smulY n, 1]⟧ = ⟦smulField n⟧
  apply Quotient.sound
  symm
  have hz : (smulField n) 2 ≠ 0 := by
    simpa [smulField, smulPoly] using polyToField_ψ_ne_zero n h0
  convert (Jacobian.equiv_some_of_Z_ne_zero (P := smulField n) hz) using 1
  funext i
  fin_cases i <;> simp [smulField, smulPoly, smulX, smulY]
theorem s1623NonsingularSmulField (n : ℤ) (h0 : n ≠ 0) :
    pointedCurve.toJacobian.Nonsingular (smulField n) := by
  have hclass := s1623ZSMulPointEqSmulField n h0
  have hlift : pointedCurve.toJacobian.NonsingularLift
      (n • s1619Point.toJacobian).point :=
    (n • s1619Point.toJacobian).nonsingular
  rw [hclass] at hlift
  exact (Jacobian.nonsingularLift_iff (smulField n)).mp hlift
theorem s1623ZSMulPointEqSmulField_zero :
    (0 • s1619Point.toJacobian).point = ⟦smulField 0⟧ := by
  change (0 : pointedCurve.toJacobian.Point).point = ⟦smulField 0⟧
  rw [Jacobian.Point.zero_point]
  congr 1
  funext i
  fin_cases i <;> simp [smulField, smulPoly,
    WeierstrassCurve.φ_zero, WeierstrassCurve.ω_zero, WeierstrassCurve.ψ_zero]
theorem s1623ZSMulPointEqSmulField_all (n : ℤ) :
    (n • s1619Point.toJacobian).point = ⟦smulField n⟧ := by
  rcases eq_or_ne n 0 with rfl | h0
  · exact s1623ZSMulPointEqSmulField_zero
  · exact s1623ZSMulPointEqSmulField n h0
end LeanFormal.IUT.XiFPaper.S1623ZSMulEvalActual


end
