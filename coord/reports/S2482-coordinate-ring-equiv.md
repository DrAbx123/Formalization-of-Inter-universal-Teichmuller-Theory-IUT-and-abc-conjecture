# S2482 coordinate-ring equivalence: actual

## BUILT (EXIT=0)
S2482CoordRingEquivActual.lean:
- S2482W : WeierstrassCurve.Affine F := S2482Curve.toAffine.
- S2482Bivariate_polynomial:
    Bivariate.equivMvPolynomial F S2482W.polynomial = S2482AffinePolynomial.
- S2482CoordRingEquiv :
    S2482W.CoordinateRing ≃ₐ[F] S2482CoordinateRing.
  Constructed by Ideal.quotientEquivAlg along Bivariate.equivMvPolynomial F, with
  the ideal image checked by S2482Bivariate_polynomial.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Use for the norm-degree route
The equivalence identifies the Weierstrass coordinate ring W.CoordinateRing with our R, so the
Mathlib basis/norm_smul_basis/degree_norm_smul_basis API can now be transported to R.
Next exact steps: transport basis and norm, then define the norm/filtration of an F-algebra
automorphism phi of R and prove phi(x)=x via the degree/rank argument.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482CoordRingEquivActual.lean
EXIT=0; SHA256 28170772E456530BFD70E3793F65CB9DE18F660026AA8503F373C7BE47E97C97
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482CoordRingEquivActual.olean
olean SHA256: DF38701B3CD8AFFCBACF35A3C19C6C731349D66820CFE6E5CD716C1FDDF3BAE0
axioms: trio