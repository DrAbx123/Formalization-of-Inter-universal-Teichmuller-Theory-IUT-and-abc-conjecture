# S2535 AdjoinRoot algebraMap commutation: ACTUAL

## BUILT (EXIT=0)
S2535AdjoinRootAlgebraMapActual.lean:
- S2535_commutes_adjoinRoot: for f:A→ₐ[F]B and x:Q, f(algebraMap F A (AdjoinRoot.of p x)) = algebraMap F B (AdjoinRoot.of p x).
- S2535_commutes_root: same on AdjoinRoot.root p.
Axioms trio; no sorryAx.

## Note
AdjoinRoot.of (X^2+1) is Q →+* F in this Mathlib version, so the precomposition in S2534 is over Q, not Q[X].
These lemmas are the exact AdjoinRoot-element commutations needed for the cover morphism compatibility.

## Artifacts
EXIT=0; SHA256 F3D03783AEF040B9E480D5A51C4D9FA1CB833FC0561E979B79D46D7CF00BEC44
olean SHA256: A9AE97D5A9E20A3C2DBAD50580583A3028D52716C31113BBB4C0C14A4AAF3207
axioms: trio