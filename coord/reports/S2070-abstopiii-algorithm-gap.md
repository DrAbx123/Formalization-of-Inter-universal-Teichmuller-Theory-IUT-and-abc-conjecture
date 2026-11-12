# S2070: paper-level first missing for the group algorithm

Date: 2026-11-02. Layer O. No fake/all-units/IndIntegralMonoid.

## File

tmp/sheaf/xif/paper/S2070AbsTopIIIAlgorithmGap.lean
Source SHA256 7dd7d652f8055a24c4f065b83f4a1821729a06b783ac0f8b93fb11d5969e64ad
olean SHA256 fa7bd2b36bda29c299f4905559c62f67c365e2b001b7ddf74b22aedaa4f97189
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Reduction

S2070OtriangleAlgorithm is the missing [AbsTopIII], Proposition 5.8(i),
functorial group-theoretic algorithm

  G |-> O^◃(G)

of IUT II, Example 1.8(ii).  No inhabitant is asserted.

S2070UnitsMuAlgorithm derives from it the O^×μ algorithm of Example 1.8(iv):

  units  G := TimesMuQuotient (Units (O^◃(G)))
  map    := torsion-quotient of Units.mapEquiv of the algorithm's map,

giving S2069GroupAlgorithmReconstruction.  Thus S2069GroupAlgorithmRequired is
reduced to S2070OtriangleAlgorithmRequired, i.e. exactly the AbsTopIII
Proposition 5.8(i) algorithm, not to an arbitrary candidate.

## No candidate installed

A continuous-finite-quotient candidate does not carry O^◃(G), so it cannot be
used.  The exact first missing is the paper's algorithm (∗◃) and its
functoriality; the tree has only KappaOrbitUnitsActionDatum after an
FPrimeStrip/local-field datum, not a group-only construction.
