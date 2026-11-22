# S111: formal boundary log with codomain K x Z

Date: 2026-10-29.

## Construction

The formal codomain is K x Z.  For x in O-boundary with DVR decomposition
x = u * pi^n,

  boundaryLogFormal x = (unitLog u, n),
  unitLogFormal u = (unitLog u, 0),
  boundaryLogFormal(pi) = (0,1).

The DVR decomposition is unique for a fixed pi, so this is an actual monoid
homomorphism to the additive formal codomain and extends the unit logarithm.

## Actual results

* boundaryUnitDecomposition_unique: uniqueness of n,u for a fixed uniformizer;
* boundaryLogFormal_one, boundaryLogFormal_mul;
* boundaryLogFormalHom : sourceOBoundaryMonoid ->* Multiplicative (K x Z);
* boundaryLogFormal_ext_unit: on the embedded O-times it equals unitLogFormal;
* boundaryLogFormal_uniformizer: the chosen uniformizer maps to (0,1).

Changing pi changes only the integer coordinate and the unit part; logPi is a
formal canonical symbol, not an element of K.

No fake field logarithm/sorry/axiom/True/PUnit.
