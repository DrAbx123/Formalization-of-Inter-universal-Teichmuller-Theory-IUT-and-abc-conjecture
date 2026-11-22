import tmp.sheaf.xif.paper.S1923UniversalFormula
open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

def S1923UniversalDescent : Prop :=
  ∀ (n : ℤ) (_hn : 1 ≤ n) (K : Type) [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve.Affine K) (x y : K) (h : W.Nonsingular x y),
    W.evalDivisionPolynomial x y n ≠ 0 →
      xCoord W (n • (WeierstrassCurve.Affine.Point.some x y h : W.Point)) =
        some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2)
