import tmp.sheaf.xif.paper.S2762FiveTorsionCardActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2764FiveTorsionCriterionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2762FiveTorsionCardActual
open WeierstrassCurve
open WeierstrassCurve.Jacobian
open Polynomial

/-- Five-torsion criterion in affine coordinates, with the univariate odd
division polynomial preΨ₅. -/
theorem S2764_five_smul_eq_zero_iff_prePsi
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (5 : ℕ) • Affine.Point.some x y h = 0 ↔
      (W.preΨ (5 : ℤ)).eval x = 0 := by
  classical
  let P : W.toAffine.Point := Affine.Point.some x y h
  have hmap : Jacobian.Point.fromAffine ((5 : ℕ) • P) =
      (5 : ℕ) • Jacobian.Point.fromAffine P := by
    change (Jacobian.Point.toAffineAddEquiv W).symm ((5 : ℕ) • P) =
      (5 : ℕ) • (Jacobian.Point.toAffineAddEquiv W).symm P
    exact map_nsmul (Jacobian.Point.toAffineAddEquiv W).symm 5 P
  change (5 : ℕ) • P = 0 ↔ (W.preΨ (5 : ℤ)).eval x = 0
  have hiff : (5 : ℕ) • P = 0 ↔
      Jacobian.Point.fromAffine ((5 : ℕ) • P) = 0 := by
    constructor
    · intro hzero
      rw [hzero, Jacobian.Point.fromAffine_zero]
    · intro hzero
      exact (Jacobian.Point.toAffineAddEquiv W).symm.injective (by simpa [Jacobian.Point.fromAffine_zero] using hzero)
  rw [hiff, hmap]
  have hc := S2762_five_zsmul_eq_zero_iff_psi W h
  have hcast : (5 : ℤ) • Jacobian.Point.fromAffine P =
      (5 : ℕ) • Jacobian.Point.fromAffine P := by
    rfl
  rw [hcast] at hc
  rw [hc]
  rw [show (W.ψ (5 : ℤ)).evalEval x y = (W.preΨ (5 : ℤ)).eval x from
    W.evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1 (by decide : ¬ Even (5 : ℤ))]

#check S2764_five_smul_eq_zero_iff_prePsi
#print axioms S2764_five_smul_eq_zero_iff_prePsi

end LeanFormal.IUT.XiFPaper.S2764FiveTorsionCriterionActual
end
