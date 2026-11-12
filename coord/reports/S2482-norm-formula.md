# Norm formula on R: actual

## BUILT (EXIT=0)
S2482NormFormulaActual.lean:
- S2482AlgEquivPolynomial : W.CoordinateRing ≃ₐ[F[X]] R.
- S2482CoordRingEquiv_y : e (mk W Y) = S2482cy.
- S2482_norm_smul_basis (p q : Polynomial F):
    Algebra.norm F[X] (p • 1 + q • S2482cy) = p^2 - q^2 * (X^3 - X).
  Proof: Algebra.norm_eq_of_algEquiv along S2482AlgEquivPolynomial, then Mathlib
  CoordinateRing.norm_smul_basis and simplification of the Weierstrass coefficients.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Next (B)
Define W z = (Algebra.norm F[X] z).degree and prove:
- W_smul_basis: W (p • 1 + q • y) = max (2*degree p) (2*degree q + 3);
- weight additivity/no-cancellation: W z < W w -> W (z+w) = W w;
- W_aeval; then phi(x)=x and phi(y)=±y.
This is not done; subagent v2 got infrastructure (REquiv, W_mul, wt_mul_lt) but its first missing lemma
is exactly weight additivity. No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482NormFormulaActual.lean
EXIT=0; SHA256 06546AA18D10033AE5143362EB4ACCF79E707D3F75B73CBF79A0CF16904CFBA9
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482NormFormulaActual.olean
olean SHA256: 99D1868AE76289EEFF3CBFA08CB4BB691E46779E549021553FF6414DD05F3B22
axioms: trio