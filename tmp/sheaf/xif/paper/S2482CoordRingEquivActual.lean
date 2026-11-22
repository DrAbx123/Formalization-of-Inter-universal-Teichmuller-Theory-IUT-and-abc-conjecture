import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482CoordRingEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open Polynomial
open scoped Polynomial.Bivariate

abbrev S2482W : WeierstrassCurve.Affine F := S2482Curve.toAffine

theorem S2482Bivariate_polynomial :
    Polynomial.Bivariate.equivMvPolynomial F S2482W.polynomial =
      S2482AffinePolynomial := by
  have hp : S2482W.polynomial = (Y : F[X][Y]) ^ 2 - C (X ^ 3 - X : F[X]) := by
    simp [S2482W, S2482Curve, WeierstrassCurve.Affine.polynomial]
    ring
  rw [hp]
  simp [S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
    S2482Curve, Polynomial.Bivariate.equivMvPolynomial_X,
    Polynomial.Bivariate.equivMvPolynomial_C_X]
  ring

noncomputable def S2482CoordRingEquiv :
    S2482W.CoordinateRing ≃ₐ[F] S2482CoordinateRing :=
  Ideal.quotientEquivAlg (I := Ideal.span {S2482W.polynomial})
    (J := Ideal.span {S2482AffinePolynomial})
    (Polynomial.Bivariate.equivMvPolynomial F) (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span ({S2482AffinePolynomial} : Set (MvPolynomial (Fin 2) F)) =
        Ideal.span ({(Polynomial.Bivariate.equivMvPolynomial F) S2482W.polynomial} :
          Set (MvPolynomial (Fin 2) F))
      rw [show ((Polynomial.Bivariate.equivMvPolynomial F) S2482W.polynomial) =
        S2482AffinePolynomial from S2482Bivariate_polynomial])


end LeanFormal.IUT.XiFPaper.S2482CoordRingEquivActual

end