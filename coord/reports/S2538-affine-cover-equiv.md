# S2538 affine cover equivalence: ACTUAL

## BUILT (EXIT=0)
S2538AffineCoverEquivActual.lean:
- S2538AffineCoverEquiv : FiniteEtaleCover S2482AffineScheme ~= (CommAlgCat.FiniteEtale S2482CoordinateRing)^op.
Imported from actual no-sorry S1799AffineFiniteEtaleEquivActual (coverToAlg equivalence).
Axioms trio; no sorryAx.

## Use
This supplies the base cover <-> finite etale algebra equivalence for S2482's coordinate ring,
the missing comparison at the affine base level.
Still need to pass through S2517InvObj (orbicurve cover) and derive S2534QuotMap injectivity.
No fake.

## Artifacts
EXIT=0; SHA256 6DCC26D10BE497AA69B79890A83EFC8188A48F0B24D90459EEF8FE55EB4D787A
olean SHA256: C3809520BE6E2EBDA2B2466F3CBA48A85CC82999011BAA153D34B5CD5D5CF0AA
axioms: trio