# S2318: Frobenius transitivity from orbit/fibre cardinality

Date: 2026-11-03. Layer O; consumer S2217/S2307.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2318FrobTransitiveActual.lean
  SHA256 C40ED88BF82A989B4A545C4ADBD1DB0B76367FE95C7C9F65D6C14316AB9DAADE
  EXIT=0
  olean SHA256 2A922838EAA2F426CB2A027363F146EB5C6C6F5057E844F710917A43BFE42FAE
  size 100536
  axioms propext, Classical.choice, Quot.sound.

Definitions:

- s2318Orbit p P x := {y | exists n, (frobBar p P)^[n] x = y};
- s2318Fiber p P g := {y | aeval y g = 0};
- s2318FrobTransitive_of_card:
    if the orbit of x has ncard = g.natDegree and the fibre of g has
    ncard = g.natDegree, then for every root y of g there is n with
    (frobBar p P)^[n] x = y.

Proof: the orbit is contained in the fibre (Frobenius sends roots of a
polynomial over the base residue field to roots); equal ncard and inclusion
give equality of the finite sets; y is then in the orbit.

## Exact first missing

1. s2318OrbitCard:
     (s2318Orbit p P x).ncard = g.natDegree.
   Needed proof: range d -> E, n |-> frob^n x is injective for n<d, using
   frobBar_iterate_ne_self; its image has d elements and equals the orbit.
   The distinctness argument requires applying iterate-cancel to a root and
   was not completed in this file.
2. s2318FiberCard:
     (s2318Fiber p P g).ncard = g.natDegree.
   Needed proof: fibre = rootSet g in the residue field; g splits there and
   is separable (as a factor of fbar), then card_rootSet_eq_natDegree.

## Conclusion

- BUILT: reduction of Frobenius transitivity to exactly two cardinality
  inputs, with actual conditional theorem.
- MISSING: orbit cardinal and fibre cardinal.
- no fake; no false S2057 data; no assumed Frobenius theorem.
