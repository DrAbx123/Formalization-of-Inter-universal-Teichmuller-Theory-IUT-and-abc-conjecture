# S2339: fbar factor separability/splitting and unconditional Frobenius transitivity

Date: 2026-11-03. Layer O; consumer S2217/S2330.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2339FbarFactorsActual.lean
  SHA256 30CD90B1E368C5F7D6D24B421E286A500A332F7E61ACAF0F3580CF93E95B34B2
  EXIT=0
  olean SHA256 23FDBE3A89B256342E3456F8E62E15BE4CECD2EB29F4C2494515E31F3A40DF71
  size 100024
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2339FbarMap_splits:
    (fbar f p).map (algebraMap F E) splits,
  using S2217 splits_over_ringOfIntegers + map under O_L -> O_L/P and
  Ideal.Quotient.algebraMap_mk_of_liesOver.

- s2339Factor_separable:
    g | fbar -> g.Separable, via Polynomial.Separable.of_dvd.

- s2339Factor_map_splits:
    g.Monic -> g | fbar -> (g.map algebraMap).Splits,
  via Splits.of_dvd on the split image of fbar.

- s2339FrobTransitive:
    g.Monic -> Irreducible g -> g | fbar ->
    roots x y -> exists n, (frobBar p P)^[n] x = y,
  unconditional (uses S2330 conditional transitivity and the two factor lemmas).

## Exact next missing to S2217Missing

1. Transport the residue-root transitivity through S2217 redRootEquiv to
   roots in O_L, and identify it with the action of an arithFrobAt sigma:
   rootPerm K L f hsplit sigma.
2. Identify the fibres of the map root -> irreducible factor with the
   normalized factors of fbar and prove that their sizes multiset equals
   factorDegrees (fbar f p).
3. Apply S2217 cycleType_eq_fiber_sizes (or orbitSizeMultiset)
   to obtain DedekindFrobeniusOrbitSizeTheorem / corrected cycle-type.

No inhabitant of S2217Missing is asserted.

## Conclusion

- BUILT: fbar splits after scalar extension, factor separability, factor
  splitting, and unconditional Frobenius transitivity on residue roots.
- MISSING: transport to rootPerm/arithFrobAt and factor-degree multiset
  identification.
- no fake; no false S2057 data.
