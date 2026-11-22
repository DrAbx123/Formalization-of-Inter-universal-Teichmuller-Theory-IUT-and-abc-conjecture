# S1959: paper coric vertices and operation-level Kummer/evaluation arrows

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S1959PaperCoricVerticesActual.lean.

## Outcome

**Missing** for the paper-level target; a reduced times-mu construction is
checked and the exact first missing is identified.  No Prop slot, empty type,
arbitrary inhabitant, sorry or axiom is used.  No fake F^⊩ vertex type is
declared.

## Constructed (checked, EXIT=0)

On an actual S1895PaperInput D, with the four actual source strips
envStrip/gauStrip/lgpStrip/lgpLowerStrip of S1951:

* ReducedVertex.env/gau/LGP/lgp: the canonical times-mu lifts
  SourceFTimesMuPrimeStrip.canonical of those strips (the tree's reduced
  F^⊢▶×μ layer, not the paper's F^⊩ primes);
* ReducedVertex.upperEvaluation, lowerHorizontal, leftKummer,
  rightKummer: full poly-isomorphisms of times-mu prime-strips induced by
  the actual source links fLinkAt 0 0 0 1, 1 0 1 1, 1 0 0 0, 1 1 0 1;
* reducedSquare: a SourceFTimesMuPrimeStripPolyIsomorphismSquare with
  commutes and both two-sided horizontal-existence fields;
* provenance theorems: the F-components are exactly the generic fLinkAt
  links, and the times-mu components are
  TimesMuQuotient.congr (Units.mapEquiv phi.isoMon v);
* fourSourceStrips_from_distinct_theaters: the four source strips are the
  prime strips of four pairwise distinct Hodge theaters (the paper's four
  vertices are built from one Theta±ellNF-Hodge theater).

## Exact first missing

1. **Type level.** The tree has no F^⊩-prime-strip carrier
   (C^⊩, Prime(C^⊩) = V, F^⊢, {rho_v}) of IUT I, Remark 5.2.1, (ii), and
   IUT II, Definition 4.9, (vii)--(viii).  FPrimeStrip is only the F^⊢
   part; the only global realified Frobenioid attached to the S1895 input is
   paperGlobalRealifiedFrobenioid D (= C^⊩mod), not the four paper global
   Frobenioids.
2. **Construction level.** The first paper object in IUT II, Corollary
   4.6, (iv), is the local theta monoid assignment
   PsiFenv(daggerHT_Theta) = {Psi_{daggerF_Theta,v}}, built by the
   group-theoretic algorithm of IUT II, Proposition 4.1, (i)--(iv).  There is
   no theta monoid or Gaussian monoid in the active LeanFormal/Iut tree.
   The input Theta-bridge/gluing is also only a reduced Hodge theater; if the
   paper's full Theta-bridge is required as input, that gluing is the first
   missing.  Next: C^⊩env, C^⊩gau (Corollary 4.6, (v)) and the local
   isomorphisms Phi.
3. **Operation level.** The domain O^×μ(G) of the Definition 4.9, (i),
   Kummer isomorphism is reconstructed by the group-theoretic algorithm
   G -> (G acting on O^×(G)) of IUT II, Example 1.8, (iii), (iv); it is
   absent.  The existing KappaOrbitUnitsActionDatum interface records the
   required data, but the unconditional inhabitants in the tree are the
   canonical/self completions with TimesMuKummer.Isomorphism.refl or its
   conjugate.  The evaluation isomorphism of Corollary 4.10, (ii), is
   likewise not constructed; S1951's unit layer is the
   strip-equivalence-induced unit map.

## Evidence

* source SHA256: 52DB9F255045EF92DBC807C8E68C428A7A8A5E9A4A1A5843AB5D086E0C188CF5
* EXIT=0: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1959PaperCoricVerticesActual.olean tmp/sheaf/xif/paper/S1959PaperCoricVerticesActual.lean
* olean: 140912 bytes, SHA256 1B1C006D8E52F61EA25F60CB9F75C8947B7969EC0F7436044E19EEC2520799D5
* axioms: propext, Classical.choice, Quot.sound only; no sorryAx
* consumer: tmp/sheaf/xif/paper/_S1959Consumer.lean, EXIT=0

## Not run

Full Project build, target comparator, independent review.
