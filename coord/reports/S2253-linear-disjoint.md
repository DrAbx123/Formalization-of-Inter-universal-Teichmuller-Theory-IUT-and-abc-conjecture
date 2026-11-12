# S2253: common algebraic closure and linear-disjointness reduction

Date: 2026-11-02. Layer O; consumer S2216/S2228/S2167.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2253LinearDisjointActual.lean
  SHA256 00412EE3C6CCE17E3FF2EB25346B2AD1ECAA415E25989EDD8B0838936DF72056
  EXIT=0
  olean SHA256 AFE513BC87516550E267D8B968F0CCDEB926112F1EC7A72319A8D8E36417E466
  size 46224
  axioms propext, Classical.choice, Quot.sound.

Constructions:

- s2253Omega := AlgebraicClosure Q;
- s2253EmbedF : S1720Field ->+[Q] s2253Omega := IsAlgClosed.lift;
- s2253EmbedL : s2216AbsoluteFiveDivisionField ->+[Q] s2253Omega;
- s2253FImage / s2253LImage := IntermediateField.map ... top;
- s2253Intersection := s2253FImage inf s2253LImage.

Theorems:

- s2253LinearDisjointness_iff:
    s2216LinearDisjointness s2253Omega s2253EmbedF s2253EmbedL
      <-> s2253Intersection = bot;
- s2253LinearDisjointnessRequired_of_intersection:
    s2253Intersection = bot -> s2216LinearDisjointnessRequired.

## Exact first missing

  s2253IntersectionIsBot : s2253Intersection = (bot : IntermediateField Q s2253Omega).

The common algebraic closure and both embeddings are actual; what remains is
the arithmetic intersection computation F' cap Q(E[5]) = Q.  Equivalent
degree criterion:

  [F' : Q] * [Q(E[5]) : Q] = [compositum : Q].

Current tree has neither the degrees [F':Q], [Q(E[5]):Q] nor the compositum
degree, and no coprime-discriminant/ramification computation for this pair.

## Conclusion

- BUILT: actual common Omega, embeddings, intersection, and reduction of
  S2216's existential linear-disjointness target to one intersection equality.
- MISSING: s2253IntersectionIsBot (equivalently the degree product equality).
- no fake; no target change.
