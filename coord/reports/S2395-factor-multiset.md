# S2395: factor multiset status

Date: 2026-11-03. Layer O; consumer S2217/S2167.

## No new closed Lean file

The fibre/factor multiset identification was not completed.  The available
actual steps are:

- S2330FiberCard_of_splits_separable:
    g.Monic -> g.Separable -> (g.map algebraMap).Splits ->
    (s2318Fiber p P g).ncard = g.natDegree;
- S2339Factor_separable / s2339Factor_map_splits:
    every monic factor g of fbar is separable and splits after scalar
    extension;
- S2339FrobTransitive:
    q-Frobenius is transitive on the roots of such g.

## Exact first missing

1. root-to-factor map:

  For a residue root y of fbar, its minpoly over F is a normalized
  irreducible factor of fbar:

    minpoly F y ∈ (normalizedFactors (fbar f p)),

  and conversely every normalized factor has at least one root in E
  (since fbar splits over E).  The converse needs a root-existence lemma
  from `(g.map algebraMap).Splits` and `g.Monic`.

2. fibre identification:

  The fibre of the root-to-factor map over g is exactly `g.rootSet E`
  (intersected with fbar roots), so its ncard is g.natDegree by S2330.

3. multiset identity:

  The resulting multiset of fibre sizes is

    (normalizedFactors (fbar f p)).map Polynomial.natDegree
      = factorDegrees (fbar f p),

  by the definition of factorDegrees.  This part is definitional once the
  factor indexing is aligned.

4. applying S2217:

  `cycleType_eq_fiber_sizes` then gives the corrected cycle-type statement
  (after removing 1s), and `orbitSizeMultiset` gives the orbit-size version.
  For rootPerm on L-roots, S2345/S2368 transport is available, but the
  residue-root cycle type still needs to be compared with rootPerm's cycle
  type.

## Blocking API

Mathlib has `UniqueFactorizationMonoid.normalizedFactors` and
`Polynomial.card_rootSet_eq_natDegree`, but no packaged equivalence

  {roots of fbar in E} ~= {normalized factors of fbar}

with fibre cardinalities.  This must be assembled from minpoly and roots.

## Conclusion

- BUILT upstream: factor separability/splitting, fibre cardinal for each
  factor, and Frobenius transitivity.
- MISSING: root-to-normalized-factor bijection, fibre partition, multiset
  identity, and the final S2217 application.
- no fake; no false S2057 data.
