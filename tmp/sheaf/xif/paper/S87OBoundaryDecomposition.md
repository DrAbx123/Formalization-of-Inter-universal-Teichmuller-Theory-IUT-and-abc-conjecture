# S87: DVR unit decomposition of O-boundary

Date: 2026-10-29.

## Actual construction

The norm integral ring Integers K is a DVR (isDiscreteValuationRingIntegers).
Choose an actual uniformizer pi by IsDiscreteValuationRing.exists_irreducible.

For x in O-boundary, convert x to a nonzero element of Integers K and apply
eq_unit_mul_pow_irreducible, obtaining

  x = u * pi^n,  u a unit, n : Nat.

This yields OBoundaryUnitDecomp (with actual equality) and
boundaryUnitDecomposition.  Given a chosen logPi, the choice-dependent map is

  boundaryLogWith logPi x = n • logPi + unitLog u.

## Choice / indeterminacy

pi is chosen by Classical.choice from the DVR existence theorem, and logPi is
an additional chosen logarithm of pi.  BoundaryLogIndeterminacy records the
uniformizer, its irreducibility, and logPi.  Changing pi/logPi changes the
decomposition/log by a unit/torsion factor; no canonical choice is asserted.

No fake canonical log/sorry/axiom/True/PUnit.
