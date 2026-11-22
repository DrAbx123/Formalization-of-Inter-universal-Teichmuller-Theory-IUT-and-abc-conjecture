import tmp.sheaf.xif.paper.S1491NormEDSNetActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

open WeierstrassCurve

example {F : Type*} [Field F] (W : WeierstrassCurve F) (x y : F) :
    IsEllipticNet (fun n : ℤ => W.evalDivisionPolynomial x y n) := by
  unfold WeierstrassCurve.evalDivisionPolynomial
  exact isEllipticNet_evalEval_ψ W x y

example {F : Type*} [Field F] (W : WeierstrassCurve F) (x y : F) :
    IsEllipticSequence (fun n : ℤ => W.evalDivisionPolynomial x y n) :=
  IsEllipticNet.isEllipticSequence (by
    unfold WeierstrassCurve.evalDivisionPolynomial
    exact isEllipticNet_evalEval_ψ W x y)
