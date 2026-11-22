import tmp.sheaf.xif.paper.S1923UniversalFormula
import tmp.sheaf.xif.paper.S1923Intermediate
import tmp.sheaf.xif.paper.S1361DivisionCriterionActual

noncomputable section
set_option maxHeartbeats 1000000
open Polynomial
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual
open WeierstrassCurve

namespace LeanFormal.IUT.XiFPaper.S1923XCoordinateFormulaActual

def S1923UniversalDescent : Prop :=
  ∀ (n : ℤ) (_hn : 1 ≤ n) (K : Type) [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve.Affine K) (x y : K) (h : W.Nonsingular x y),
    W.evalDivisionPolynomial x y n ≠ 0 →
      xCoord W (n • (WeierstrassCurve.Affine.Point.some x y h : W.Point)) =
        some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2)

theorem S1923XCoordinateFormula_of_descent
    (h : S1923UniversalDescent) {K : Type} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve.Affine K) (n : ℤ) (hn : 1 ≤ n) :
    s1361XCoordinateFormula W n := by
  intro x y hns hne
  exact h n hn K W x y hns hne

theorem S1923UniversalXCoordinateFormula :
    ∀ (n : ℤ), 1 ≤ n →
      xCoord Universal.pointedCurve
        (n • (WeierstrassCurve.Affine.Point.some Universal.xU Universal.yU
          Universal.nonsingular_point : Universal.pointedCurve.toAffine.Point)) =
        some (Universal.polyToField (Polynomial.C (Universal.curve.Φ n)) /
          Universal.polyToField (Universal.curve.ψ n) ^ 2) :=
  WeierstrassCurve.Universal.xCoordinateFormula_universal

#print axioms S1923XCoordinateFormula_of_descent
#check S1923XCoordinateFormula_of_intermediate
#print axioms S1923XCoordinateFormula_of_intermediate
#print axioms S1923UniversalXCoordinateFormula

end LeanFormal.IUT.XiFPaper.S1923XCoordinateFormulaActual
