# S1508: ZSMul identities from the EDS net — exact missing identity

Date: 2026-10-31. No Lean file: first missing identity is the omega reduced
invariant identity, then the universal polynomial identities.

## 1. What S1491 now supplies

S1491NormEDSNetActual proves:

  IsEllipticNet (normEDS b c d)
  IsEllipticSequence (normEDS b c d)

and the three-index relation rel3_normEDS.  This removes the EDS net TODO that
blocked S1410 and S1486.

## 2. What S1410 supplies

S1410BivariateOmegaActual gives the actual bivariate omega:

  W.ω n = (reducedInvarNum - complEDS₂Aux ...) / (2 * reducedInvarDenom ...)

with ω_zero, ω_one, map_ω, evalEval_ω, and ψc/ψ_mul_ψc.

S1410 explicitly does not prove the omega defining identity

  2 * W.ω n + a₁ * W.φ n * W.ψ n + a₃ * W.ψ n ^ 3 = W.ψc n.

## 3. Exact first missing identity after S1491

The first missing algebraic identity is the reduced-invariant identity for the
normalised EDS underlying W.ω:

  reducedInvarNum b c d m
    = reducedInvarDenom b c d m * (d + b ^ 4)

with the missing definition reducedInvarNum.  S1410 defines only
reducedInvarDenom (the denominator), not reducedInvarNum.  S1491 supplies the
net property needed to prove the invariant ratio is constant, but the numerator
and its identity are still absent.

Equivalently, the first missing polynomial theorem is the omega defining
identity above for the bivariate W.ω.

## 4. Remaining exact field: universal curve layer

After the omega identity, TauCeti's dblXYZ_smulRing / addXYZ_smulRing still need
the Universal layer, absent from Mathlib v4.32.2:

- Universal.Ring, Universal.Field, universal curve;
- smulPoly / smulRing (universal φ_n, ω_n, ψ_n);
- ringEval and ringEval_comp_smulRing.

Then the identities

  dblXYZ curveRing (smulRing n) = smulRing (2 * n)

  addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1)

would follow by the same polynomial specialization proof as TauCeti.

## 5. Conclusion

- actual: S1491 IsEllipticNet.normEDS; S1410 ω definition/eval laws.
- exact first missing: reducedInvarNum plus
  reducedInvarNum = reducedInvarDenom * (d + b^4),
  equivalently 2ω + a₁φψ + a₃ψ³ = ψc.
- exact second layer: Universal.Ring/curve and dblXYZ_smulRing,
  addXYZ_smulRing.
- S1472 Doubling/Addition identities remain unproved; no fake file.
- report only, EXIT=0.
