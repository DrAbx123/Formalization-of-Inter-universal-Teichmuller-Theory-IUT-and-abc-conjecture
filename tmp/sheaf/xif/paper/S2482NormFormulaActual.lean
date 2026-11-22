import tmp.sheaf.xif.paper.S2482NormTransportActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482NormFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482CoordRingEquivActual
open LeanFormal.IUT.XiFPaper.S2482NormTransportActual
open Polynomial

abbrev S2482cy : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)

theorem S2482CoordRingEquiv_y :
    S2482CoordRingEquiv
      (WeierstrassCurve.Affine.CoordinateRing.mk S2482W
        (Polynomial.X : Polynomial (Polynomial F))) = S2482cy := by
  change Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
      ((Polynomial.Bivariate.equivMvPolynomial F)
        (Polynomial.X : Polynomial (Polynomial F))) = S2482cy
  rw [Polynomial.Bivariate.equivMvPolynomial_X]

noncomputable def S2482AlgEquivPolynomial :
    S2482W.CoordinateRing ≃ₐ[Polynomial F] S2482CoordinateRing :=
  AlgEquiv.ofRingEquiv (f := S2482CoordRingEquiv.toRingEquiv)
    (fun r => S2482CoordRingEquiv_algebraMap r)

theorem S2482_norm_smul_basis (p q : Polynomial F) :
    Algebra.norm (Polynomial F)
      (p • (1 : S2482CoordinateRing) + q • S2482cy) =
      p ^ 2 - q ^ 2 * (X ^ 3 - X) := by
  have h := Algebra.norm_eq_of_algEquiv S2482AlgEquivPolynomial
    (p • (1 : S2482W.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk S2482W
        (Polynomial.X : Polynomial (Polynomial F)))
  rw [map_add, map_smul, map_smul, map_one] at h
  rw [show S2482AlgEquivPolynomial
      (WeierstrassCurve.Affine.CoordinateRing.mk S2482W
        (Polynomial.X : Polynomial (Polynomial F))) = S2482cy
    from S2482CoordRingEquiv_y] at h
  rw [WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis] at h
  simp [S2482W, S2482Curve] at h
  rw [show (X ^ 3 + -X : Polynomial F) = X ^ 3 - X by ring] at h
  exact h


end LeanFormal.IUT.XiFPaper.S2482NormFormulaActual

end