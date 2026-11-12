# S1543/S1544: corrected K and l-torsion kernel field — exact first missing

Date: 2026-10-31.

## S1544 actual conditional construction

For the actual Gaussian curve X = (S1280Arithmetic l).curve:

- GaussianTorsionBasis l := (Fin 2 -> ZMod l) ~= X.LTorsion l;
- gaussianLTorsionRepresentation b := X.galoisLTorsionMatrixRepresentation l b;
- gaussianKernelField b := X.galoisLTorsionKernelField l b;
- FiniteDimensional and IsGalois instances for gaussianKernelField;
- gaussianKernelField_fixingSubgroup = representation kernel.

These are actual, conditional on one rank-two basis b.

S1544 source is being finalized; the large-image and kernel-field
identification are exact, not proved.

## Why S1544 cannot yet fill S1543CorrectedK

S1543CorrectedK requires a concrete field K with

  Field K, NumberField K, Algebra F K, FiniteDimensional F K,
  IsGalois F K, Module.finrank F K != 1.

The natural K is the l-torsion kernel field L = gaussianKernelField b.
But every construction of L currently needs the rank-two basis b:

  GaussianTorsionBasis l := (Fin 2 -> ZMod l) ~= X.LTorsion l.

That basis is exactly the unresolved D5 first field (S1298/S1329), so L
cannot be instantiated from the current actual Gaussian data.

## Exact first missing object

  b : GaussianTorsionBasis l

equivalently a rank-two ZMod-l basis of E[l] for the actual Gaussian curve.

Once b is supplied, S1544 gives L with finite/Galois instances.  To use L in
S1543CorrectedK one still needs

  Module.finrank F L != 1

Equivalently L != F.  This is not yet proved; it follows from nontriviality of
the l-torsion representation image, which is the large-image/torsion-nontrivial
input, still exact.

## Alternative concrete K

A basis-free candidate is K = F(sqrt(5)) = Q(i, sqrt 5), a quadratic extension
of F = Q(i), hence finite Galois and finrank 2 != 1.  Formalizing it requires:

1. a concrete embedding of Q(i) into a splitting field of X^2 - 5 over Q;
2. irreducibility of X^2 - 5 over Q(i) (5 is not a square in Q(i));
3. the Galois/finite-dimensional instances for the adjoined root.

This is a possible direct construction, but it is not in the tree; no fake K is
asserted.

## Conclusion

- actual: l-torsion representation and kernel field L, conditional on a
  rank-two basis; finite/Galois instances actual.
- exact first missing for S1543CorrectedK: the rank-two l-torsion basis b,
  followed by the nontriviality L != F / finrank != 1 proof.
- alternative K = Q(i, sqrt 5) is mathematically concrete but not formalized.
- No fake K, no S1280 K = F substitution; report EXIT=0.
