# S93: unit compatibility of boundaryLogWith and choice data

Date: 2026-10-29.

## 1. Unit compatibility (proved)

boundaryLogWith_unit proves: for a unit u embedded in O-boundary via
sourceOTimesToBoundary,

  boundaryLogWith logPi (sourceOTimesToBoundary u) = unitLog u.

Proof: the DVR decomposition x = d.u * pi^d.n of the unit x has addVal(x) = 0,
so d.n = 0; then d.u = x = u, and the n • logPi term vanishes.

## 2. Uniformizer change

UniformizerChangeData records a second uniformizer, its irreducibility, the
decomposition exponents/units for the same O-boundary element, and a
change_formula proposition.  The exact transformation formula is not proved in
this file; changing pi changes the decomposition unit by the corresponding unit
factor, so the difference is not asserted to be only an integer multiple of
logPi without that unit-log term.

## 3. Canonical logPi

CanonicalLogPiRequired records the exact missing canonical logarithm of the
chosen uniformizer; no canonical choice (e.g. p-adic log of a specific
uniformizer) is supplied by the source and none is fabricated.

No fake compatibility/independence/sorry/axiom/True/PUnit.
