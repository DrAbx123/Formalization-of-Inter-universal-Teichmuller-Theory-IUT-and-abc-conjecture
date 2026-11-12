# S1699: finrank_Q SplittingField(H) = 6 — exact missing field-theory lemmas

Date: 2026-10-31. Report only; no new Lean.

## Target

S1687Field = SplittingField S1687H, H(t) = P(t^2), P the S1667 residual cubic.
Goal: Module.finrank Q S1687Field = 6.

## What is actual

- S1687H is degree 6 and nonzero;
- S1687Field is a NumberField (finite dimensional);
- S1687H splits in S1687Field and has six distinct roots (S1687 card_rootSet);
- S1667 proves the residual cubic P has no rational root;
- S1687 constructs the six roots and the 3-torsion points.

These give only upper/root information, not [S1687Field : Q] = 6.

## Exact first missing lemma

Need an irreducibility/Galois-group statement in one of two forms:

1. H irreducible over Q and Galois group of its splitting field has order 6
   (e.g. S3 via the square class of disc(P) = -3); or
2. a direct degree computation:

  Module.finrank Q (Polynomial.SplittingField S1687H) = 6.

The first missing algebraic lemma is

  Irreducible S1687H

together with the splitting-field degree bound.  H irreducible alone gives
[F:Q] >= 6, but not <= 6; the latter needs the Galois group order/transitive
action computation (the S3 action on the six roots y with y^2 a root of P).

## S1667 data not yet connected

S1667 proves P has no rational root and records disc(P) square class -3.
A cubic with no rational root is irreducible; its splitting field has S3
Galois group because disc is non-square.  But the passage

  splitting field of P  ->  splitting field of H = P(X^2)

and the comparison of their degrees is not formalized.  In particular H's
roots are +/- sqrt(alpha_i); one must prove the square roots do not force a
larger degree than 6 for this specific H (the S1687 construction of the six
roots is a start, but not a degree computation).

## Conclusion

- actual: H degree/splitting/six roots, NumberField instance, S1667 no-rational-root.
- exact first missing: Irreducible S1687H and the splitting-field degree/
  Galois-group order computation giving finrank = 6.
- No Lean file written: assuming degree 6 is exactly what is forbidden; no fake.
- report EXIT=0.
