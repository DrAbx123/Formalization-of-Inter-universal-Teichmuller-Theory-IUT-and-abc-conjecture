# S2408: fibre sizes and factor multiset

Date: 2026-11-03. Layer O; consumer S2217/S2397.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2408FiberSizesActual.lean
  SHA256 B94EFC8F07F67DB605492C0B71AFF980EF1C0A734F907A570D0BE758D55793CB
  EXIT=0
  olean SHA256 8E180268F0538A3DDE8BD9A6917E9E3716A27BE5141B9A0BB9935272B5308966
  size 120920
  axioms propext, Classical.choice, Quot.sound.

Definitions/theorems:

- s2408FiberSet g := {y | minpoly F y = g};
- s2408FiberSet_eq_rootSet:
    for monic irreducible g, the minpoly fibre equals g.rootSet E;
  forward via minpoly.aeval; backward via minpoly.eq_of_irreducible;
- s2408FiberSet_ncard:
    for g in normalizedFactors (fbar f p),
      (s2408FiberSet g).ncard = g.natDegree;
  uses s2339Factor_separable + s2339Factor_map_splits and
  Polynomial.card_rootSet_eq_natDegree;
- s2408FiberSizes_eq_factorDegrees:
    (normalizedFactors (fbar f p)).map
      (fun g => (s2408FiberSet g).ncard)
    = factorDegrees (fbar f p),
  by Multiset.map_congr and the definition of factorDegrees.

## Exact next missing

Apply S2217 cycleType_eq_fiber_sizes / orbitSizeMultiset.

Needed remaining inputs:

1. permBar preserves the root-to-factor map; equivalently
   minpoly F (frobBar p P y) = minpoly F y.
   S2339FrobTransitive gives transitivity on each fibre, but the
   invariance of the fibre map under permBar is not yet extracted.
2. the fibre/cardinality hypotheses for cycleType_eq_fiber_sizes
   (fibre size = natDegree is S2408FiberSet_ncard; transitivity on each
   fibre is S2339FrobTransitive);
3. the filter bridge from fibre sizes >= 2 to factorDegrees.filter (· != 1),
   using natDegree >= 1.

## Conclusion

- BUILT: minpoly fibre = g.rootSet, fibre ncard = natDegree for normalized
  factors, and the multiset identity with factorDegrees.
- MISSING: permBar fibre invariance, cycleType_eq_fiber_sizes application,
  filter bridge, rootPerm alignment.
- no fake; no false S2057 data.
