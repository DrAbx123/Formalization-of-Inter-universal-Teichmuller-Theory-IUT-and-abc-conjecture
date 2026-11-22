# S60: O-triangle versus O-boundary

Date: 2026-10-29.

## Source distinction

Hoshi's local p-adic setup (hoshi.txt, around the opening notation) defines:

  O-triangle = { a | |a| <= 1 }          (integral monoid, includes 0)
  O-boundary = { a | 0 < |a| <= 1 }      (nonzero integral elements)
  O-times    = { a | |a| = 1 }           (units)
  O-times-mu = roots of unity in O-times.

Thus O-triangle and O-boundary are different monoids: O-boundary is the
nonvanishing part of O-triangle.  Neither is the integral ring regarded
additively, and neither is the number-field ring of integers O_k.

## Actual Lean carriers

S56 already constructs O-triangle:

  oTriangularMonoid = (CompletionIntegers place).toSubring.toSubmonoid.

S60 constructs O-boundary:

  oBoundaryMonoid = { x : Completion place | x in CompletionIntegers place and x != 0 }

with actual one/mul closure proofs, plus

  oBoundaryToTriangular : oBoundaryMonoid -> oTriangularMonoid

and oBoundary_ne_zero.  OTriangleBoundaryCarriers packages O-triangle,
O-boundary, O-times and O-times-mu as distinct Type fields.

No equality between O-triangle, O-boundary, the integral ring, and O-times is
asserted.

No fake equality/sorry/axiom/True/PUnit.
