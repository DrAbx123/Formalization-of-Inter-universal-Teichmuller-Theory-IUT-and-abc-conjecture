# S1510: Universal curve / smulRing identities — exact gap

Date: 2026-10-31. No Lean file: minimal Universal layer is a separate large
construction; exact first missing object recorded.

## 1. What S1491/S1410 supply

- IsEllipticNet.normEDS (S1491), removing the EDS net TODO.
- bivariate W.omega, psi, psi_c and their evaluation laws (S1410).
- S1472 smulEval triple and base cases n=0,1.

They do not supply the Universal ring/curve.

## 2. Exact first object

TauCeti's proof needs the universal curve over the universal ring

  Universal.Ring = AdjoinRoot (universal Weierstrass polynomial)
  Universal.Field = FractionRing Universal.Ring
  curve : WeierstrassCurve Universal.Ring
  curveField := curve.baseChange Universal.Field
  point : Affine/Jacobian point of curveField

then the affine coordinate functions smulX, smulY with base values and
recursion, and

  zsmul_point_eq_smulField :
    (n • Jacobian.point).point = ⟦smulField n⟧

where smulPoly n = ![curve.phi n, curve.omega n, curve.psi n] and
smulRing/smulField are its images in Ring/Field.

The exact first missing object is therefore Universal.Ring + universal curve +
the affine smulX/smulY recursion.  S1491 can discharge the EDS identities used
inside that recursion, but the universal objects themselves are absent.

## 3. Exact first missing identity

After the Universal objects, the first identity is

  dblXYZ curveField (smulField n) = smulField (2 * n)

proved from

  zsmul_point_eq_smulField
  Point.two_zsmul_point
  equiv_iff_eq_of_Z_eq
  psi_u_ne_zero.

Then

  addXYZ curveField (smulField m) (smulField n)
    = polyToField (curve.psi (n - m)) • smulField (n + m)

from addZ_smulPoly and Point.add_point_of_ne.

Their images under the universal ring map give dblXYZ_smulRing and
addXYZ_smulRing, and specialization gives S1472's Doubling/Addition identities.

## 4. Why no Lean file

Writing Universal.Ring/curve/smulX/smulY and the affine recursion is a large
port, not a minimal layer.  A file containing only the names/specifications
would be a fake wrapper.  The exact first missing objects and identities are
recorded instead.

## 5. Conclusion

- actual: S1491 EDS net, S1410 omega/eval laws, S1472 base cases.
- exact first object: Universal.Ring + universal curve + smulX/smulY recursion.
- exact first identity: dblXYZ_smulField = smulField (2*n), then
  addXYZ_smulField; then smulRing/smulEval specialization.
- S1472 Doubling/Addition identities remain unproved; no fake file.
- report only, EXIT=0.
