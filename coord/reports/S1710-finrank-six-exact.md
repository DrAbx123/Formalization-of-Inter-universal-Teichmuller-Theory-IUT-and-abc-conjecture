# S1710: finrank_Q S1687Field = 6 — exact missing field-theory lemma

Date: 2026-10-31. Report only; no new Lean.

## Target

S1687Field = SplittingField S1687H, H(t)=P(t^2), P = S1667 residual cubic.
Need Module.finrank Q S1687Field = 6.

## Actual available

- S1687H.natDegree = 6, nonzero;
- S1687Field is a NumberField (finite-dimensional);
- S1687H splits in S1687Field with six distinct roots;
- S1667: P has no rational root; disc(P) square class -3;
- S1687 constructs six roots and 3-torsion points.

These do not compute the field degree.  In particular H splittings and six
distinct roots only give roots, not [S1687Field:Q]=6.

## Exact first missing field-theory lemma

One of:

1. Irreducible S1687H and the Galois-group order computation for its
   splitting field (S3 action on six roots y with y^2 a root of P); or
2. the domain identity

  SplittingField S1687H = SplittingField P

  together with Module.finrank Q (SplittingField P) = 6.

P is an irreducible cubic (no rational root) with non-square discriminant,
so its splitting field has Galois group S3 and degree 6.  But the passage

  splitting field of P  ->  splitting field of H = P(X^2)

is not formalized.  H roots are +/- sqrt(alpha_i); one must show no
additional square-root degree occurs for this H, or prove H irreducible and
identify the splitting-field Galois group/order exactly.

## Conclusion

- actual: H degree/splitting/six roots, NumberField instance, S1667 no-root.
- exact first missing: Irreducible S1687H plus splitting-field degree 6, or
  the identity F = Q(P roots) with [F:Q]=6.
- No Lean file: assuming degree 6 is forbidden; no fake.
- report EXIT=0.
