# S1511: Orbicurve Pi group data

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1511OrbicurvePiActual.lean
EXIT=0; SHA256 9F9738128811917E26F0B6DC626A65A51027E1F2A8489492A0D39C43D0E68511
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1511OrbicurvePiActual.olean

## Actual

S1511Orbicurve l := S1419Orbicurve l : HyperbolicOrbicurve (S1348K l);
actual nonterminal and actual once-punctured elliptic signature:
- S1511Orbicurve_signature;
- S1511Orbicurve_nonterminal.

S1511Galois l := AbsoluteGaloisProfinite (S1348K l).

## Exact first missing structure

S1511OrbicurvePiExactFirstField l : Type 1 :=
  Iut.OrbicurveFundamentalGroupData (S1511Orbicurve l) (S1511Galois l).

Fields needed: arithmeticGroup, arithmetic OrbicurveEtaleFundamentalGroup,
projection to S1511Galois with surjectivity, and geometric OrbicurveEtaleFundamentalGroup.
No inhabitant is asserted.

Conditional actual: S1511FirstFieldOfGroups groups : S1348D6FirstMissingField l
via S1419D6FirstMissingFieldOfGroups.

## Not used

The l-torsion sequence is not used as Pi. The S1348 finite etale double
cover and the graph group do not supply the Galois category/fiber functor/
action data of OrbicurveEtaleFundamentalGroup; hence the exact first field.

No terminal/point fiber, no l-torsion substitution, no arbitrary group.