# S1523: minimal actual Universal curve / smulPoly

Date: 2026-10-31.

## Result

tmp/sheaf/xif/paper/S1523UniversalCurveActual.lean

EXIT=0
source SHA256 077D4AC46A19976B0A9FF7D2F12511268E5AD22BC1BBADC14BD9D8C70009744C
olean .lake/build/lib/lean/tmp/sheaf/xif/paper/S1523UniversalCurveActual.olean
olean SHA256 A224FF9F82D18C83D71020F91E61238CB8B8867202EA367FED224A2510984ED2
size 73144

No sorry/axiom; #print axioms for curve and smulPoly is the standard trio.

## Actual constructed

- Coeff (A1,...,A6);
- curve : WeierstrassCurve (MvPolynomial Coeff Z), with the five universal
  coefficients;
- Poly := (MvPolynomial Coeff Z)[X][Y];
- smulPoly n : Fin 3 -> Poly := ![curve.phi n, curve.omega n, curve.psi n],
  using the actual bivariate omega from S1410;
- projection lemmas smulPoly_apply_zero/one/two.

This is the minimal actual Universal polynomial/curve layer, not a wrapper.

## Exact next construction

Still missing:

1. Universal.Ring := curve.CoordinateRing (quotient by the Weierstrass
   polynomial) and Universal.Field := FractionRing Ring;
2. polyToField : Poly ->+* Universal.Field, with the needed type alignment
   between Poly (two polynomial variables) and the AdjoinRoot coordinate ring
   (one polynomial variable over MvPolynomial Coeff Z);
3. the distinguished universal point equation from polyToField_polynomial;
4. smulX/smulY (phi/psi^2, omega/psi^3) and their affine recursion
   zsmul_point_eq_smulField;
5. only then dblXYZ_smulField/dblXYZ_smulRing and
   addXYZ_smulField/addXYZ_smulRing, then S1472 identities.

The first exact construction is (1)+(2): the universal coordinate ring/field
and the polyToField type alignment.  No fake Universal.Ring/point/recursion is
included.

## Conclusion

- actual: universal coefficient type, universal curve, Poly, smulPoly.
- exact first: Universal.Ring/Field + polyToField type alignment.
- Then point equation, smulX/smulY recursion, dbl/add identities.
- EXIT=0.
