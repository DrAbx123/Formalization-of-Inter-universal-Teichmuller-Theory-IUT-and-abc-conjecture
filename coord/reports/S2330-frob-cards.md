# S2330: orbit and fibre cardinalities for Frobenius

Date: 2026-11-03. Layer O; consumer S2318/S2217.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2330FrobCardsActual.lean
  SHA256 BC979936D7E61C80449741EEEA7DE0646E92D535DCEE9DCCBADAC334F00AF13E
  EXIT=0
  olean SHA256 BC7DEF90FDE9B8CC5595B2DB9F9AA4ECE2A1FC395877AC4743E594327A5F8FC2
  size 196968
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2330OrbitCard:
    (s2318Orbit p P x).ncard = g.natDegree;
  proof: periodic point frob^d x=x, image of range d = orbit,
  injectivity of n |-> frob^n x on range d by iterate_cancel +
  frobBar_iterate_ne_self.

- s2330FiberCard_of_splits_separable:
    g.Monic -> g.Separable ->
    (map algebraMap g).Splits ->
    (s2318Fiber p P g).ncard = g.natDegree;
  proof: fibre = rootSet g, then card_rootSet_eq_natDegree.

- s2330FrobTransitive_of_splits_separable:
    g.Monic -> Irreducible g -> g.Separable ->
    (map algebraMap g).Splits ->
    roots x y -> exists n, frob^n x = y;
  obtained by applying S2318 to the two cardinality theorems.

## Exact next missing

Derive the two hypotheses for a normalized irreducible factor g of fbar f p:

1. g.Separable from hsep : (fbar f p).Separable and g | fbar;
2. (g.map (algebraMap F E)).Splits from fbar splitting in E and g | fbar.

The second still needs a proof that fbar splits in the residue field
(or that each normalized factor's roots are covered by the reduction
bijection).  These are the remaining inputs for unconditional transitivity.

## Conclusion

- BUILT: both orbit/fibre cardinalities and conditional Frobenius transitivity.
- MISSING: splits/separable transfer for a factor g of fbar.
- no fake; no false S2057 data.
