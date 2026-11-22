import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
/-! # S1452: full ZSMul evaluation bridge → weak x-coordinate formula
If the Jacobian coordinates of n • P are (Φ_n(x), Y, ψ_n(x,y)), then the weak
S1372XCoordinateFormula follows from ψ_n ≠ 0 alone, with no psi_1..psi_{n+1}
nonvanishing hypotheses.  The full bridge is the TauCeti zsmul_eq_smulEval
input (elliptic-net theorem absent from Mathlib v4.32.2); it is recorded as an
exact Prop, not assumed globally and not an axiom. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S1452ZSMulEvalBridgeActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
universe u
variable {K : Type u} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K)
/-- Full TauCeti bridge: n • P has Jacobian representative
(Φ_n(x), Y, ψ_n(x,y)). -/
def S1452ZSMulEvalFull {x y : K} (hns : W.Nonsingular x y) (n : ℤ) : Prop :=
  ∃ (Y : K) (h : W.toJacobian.Nonsingular
      ![(W.Φ n).eval x, Y, W.evalDivisionPolynomial x y n]),
    (n • (Point.some x y hns).toJacobian).point =
      ⟦![(W.Φ n).eval x, Y, W.evalDivisionPolynomial x y n]⟧
lemma xCoord_toAffine_jacobian {X Y Z : K} (hZ : Z ≠ 0)
    (hns : W.toJacobian.Nonsingular ![X, Y, Z]) :
    xCoord W (WeierstrassCurve.Jacobian.Point.toAffine W ![X, Y, Z]) =
      some (X / Z ^ 2) := by
  rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hns hZ]
  rfl
lemma toAffineLift_zsmul_toJacobian (P : W.Point) (n : ℤ) :
    ((n • P.toJacobian).toAffineLift) = n • P := by
  have h := map_zsmul (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W) n P.toJacobian
  have h' : (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W) P.toJacobian = P := by
    rw [WeierstrassCurve.Affine.Point.toJacobian]
    exact (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W).right_inv P
  simpa [h'] using h
theorem s1452XCoordinateFormula_of_fullBridge {x y : K}
    (hns : W.Nonsingular x y) (n : ℤ)
    (hbridge : S1452ZSMulEvalFull W hns n)
    (hψ : W.evalDivisionPolynomial x y n ≠ 0) :
    xCoord W (n • Point.some x y hns) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) := by
  obtain ⟨Y, hnsY, heq⟩ := hbridge
  let rep : Fin 3 → K :=
    ![(W.Φ n).eval x, Y, W.evalDivisionPolynomial x y n]
  let Q : W.toJacobian.Point :=
    { point := ⟦rep⟧
      nonsingular := (WeierstrassCurve.Jacobian.nonsingularLift_iff rep).mpr hnsY }
  have hpoint : n • (Point.some x y hns).toJacobian = Q :=
    WeierstrassCurve.Jacobian.Point.ext_iff.mpr heq
  have hLift : ((n • (Point.some x y hns).toJacobian).toAffineLift) = n • Point.some x y hns :=
    toAffineLift_zsmul_toJacobian W (Point.some x y hns) n
  have hx : xCoord W (n • Point.some x y hns) =
      xCoord W (WeierstrassCurve.Jacobian.Point.toAffine W rep) := by
    rw [← hLift, hpoint]
    change xCoord W (Q.toAffineLift) = xCoord W (WeierstrassCurve.Jacobian.Point.toAffine W rep)
    rw [WeierstrassCurve.Jacobian.Point.toAffineLift_eq hnsY]
  rw [hx]
  exact xCoord_toAffine_jacobian W hψ hnsY
theorem s1452XCoordinateFormula_of_allFullBridge
    (hbridge : ∀ (x y : K) (hns : W.Nonsingular x y) (n : ℤ),
      S1452ZSMulEvalFull W hns n) (n : ℤ) :
    S1372XCoordinateFormula W n := by
  intro x y hns hψ
  exact s1452XCoordinateFormula_of_fullBridge W hns n (hbridge x y hns n) hψ
end LeanFormal.IUT.XiFPaper.S1452ZSMulEvalBridgeActual
