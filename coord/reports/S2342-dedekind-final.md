# S2342: remaining S2217Missing transports

Date: 2026-11-03. Layer O; consumer S2217/S2167.

## No new Lean file

S2342 did not produce a closed Lean file.  The available actual input is S2339:
unconditional q-Frobenius transitivity on the roots of every monic irreducible
factor g of fbar in the residue field.

## Exact first missing 1: O_L-roots <-> L-roots

S2167 rootPerm acts on

  (f.map (algebraMap (RingOfIntegers K) K)).rootSet L,

while S2217 redRootEquiv and the transitivity of S2339 live on

  f.rootSet (RingOfIntegers L)

and on residue roots.  Missing: an equivalence

  f.rootSet (RingOfIntegers L) ~= (f.map (algebraMap (RingOfIntegers K) K)).rootSet L

compatible with algebraMap (RingOfIntegers L) L and with the Galois action.

## Exact first missing 2: action compatibility

Given sigma : Gal(L/K) with IsArithFrobAt (RingOfIntegers K) sigma P, need

  redRoot (rootPerm ... sigma x) = permBar (redRoot x)

for all roots x.  This requires reading IsArithFrobAt as the congruence

  sigma(alpha) == alpha ^ #((O_K)/p)  (mod P),

then applying reduction to roots.  No such root-level lemma exists in the
tree.

## Exact first missing 3: factor multiset

Need a bijection between

  fibres of the map root |-> its normalized irreducible factor of fbar

and the normalized factors of fbar, and the multiset identity

  (fibre sizes) = factorDegrees (fbar f p).

Then S2217 cycleType_eq_fiber_sizes gives

  rootCycleType = (factorDegrees fbar).filter (fun n => n != 1),

and orbitSizeMultiset gives the orbit-size version.

## What is actual upstream

- S2339: unconditional transitivity on residue roots of a monic irreducible
  factor g of fbar, with g.Separable and (g.map algebraMap).Splits.
- S2330: orbit/fibre cardinalities and conditional transitivity.
- S2318: orbit/fibre set formulation.
- S2309: finite-field subfield uniqueness.
- S2217: redRootEquiv, permBar, cycleType_eq_fiber_sizes, corrected
  statements.

## Conclusion

- BUILT upstream: residue-root transitivity.
- MISSING: O_L/L root transport, arithFrobAt-action compatibility, factor
  multiset identification.
- no fake; no false S2057 data.
