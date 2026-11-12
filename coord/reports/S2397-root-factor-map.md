# S2397: root-to-normalized-factor map

Date: 2026-11-03. Layer O; consumer S2217/S2395.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2397RootFactorMapActual.lean
  SHA256 19D178B5F9137EF8E88FC71F977BB583E53E5F0B6F2523A420C0D05F74595B57
  EXIT=0
  olean SHA256 EB73BF6237594946CA76D791FC42F4237DF1E232742D862AD98AF059D65F70F4
  size 199992
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2397Fbar_monic / s2397Fbar_ne_zero;
- s2397_minpoly_mem_normalizedFactors:
    for y in the residue rootSet of fbar,
      minpoly F y in normalizedFactors (fbar f p);
  proof: minpoly.irreducible + minpoly.monic + minpoly.dvd,
  then Polynomial.mem_normalizedFactors_iff;
- s2397_exists_root_of_normalizedFactor:
    for g in normalizedFactors (fbar f p),
    there exists a residue root y with minpoly F y = g.
  proof: mem_normalizedFactors_iff gives irreducible/monic/dvd;
  s2339Factor_map_splits gives splitting; Splits.exists_eval_eq_zero gives y;
  map_dvd gives y root of fbar; minpoly.eq_of_irreducible gives minpoly = g.

A local DecidableEq on (O_K / p) is required for normalizedFactors.

## Exact next missing

1. fibre ncard: for g in normalizedFactors, the fibre of the root-to-factor
   map is g.rootSet E intersected with fbar roots, of ncard g.natDegree
   (S2330FiberCard_of_splits_separable + s2339 factor lemmas);
2. multiset identity:
     (fibre sizes) = (normalizedFactors (fbar f p)).map natDegree
       = factorDegrees (fbar f p);
3. apply S2217 cycleType_eq_fiber_sizes / orbitSizeMultiset.

## Conclusion

- BUILT: both directions of the root-to-normalized-factor correspondence.
- MISSING: fibre cardinalities as a partition, multiset identity, S2217
  application.
- no fake; no false S2057 data.
