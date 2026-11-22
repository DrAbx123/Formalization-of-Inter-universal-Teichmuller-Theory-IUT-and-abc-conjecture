# S56: actual O-triangle / O-times / O-times-mu carriers

Date: 2026-10-29.

## Paper/source structure

The extracted source uses O-triangle (O with triangle) for the monoid of
integral elements of the local field, O-times for its unit group, and O-times-mu
for the roots of unity inside those units.  These are not:

* the integral ring CompletionIntegers regarded as an additive ring;
* the number-field ring of integers O_k = RingOfIntegers k;
* the unit group of O_k.

## Actual Lean construction

S56 constructs, for a finite place:

* oTriangularMonoid =
  (CompletionIntegers place).toSubring.toSubmonoid,
  the actual multiplicative submonoid of integral elements (O-triangle);
* oTimesUnits = (CompletionIntegers place)^x (O-times);
* oTimesMu = rootsOfUnity (2l) (CompletionIntegers place) (O-times-mu).

ODecoratedCarrierAudit packages the three carriers as distinct Type fields; no
equality between the monoid, the unit group, and the ring is asserted.

The paper O-triangle is the integral monoid; there is no separate boundary type
beyond it in the frozen source.  OBoundaryDecorationGap records that exact
missing source field; OBoundaryDecorationRequired is not asserted.

No fake equality/sorry/axiom/True/PUnit.
