# S566: QvPhiQOrderFields from S556/S561 input

Date: 2026-10-29. Actual zero fields; pi preimage exact missing.

## Input

P : S561MinimalPackage K; s566Input P := s561Input P;
A : Object (qvPhi R).

## Actual QvPhiQOrderFields

zeroQvPhiQOrderFields:
  divisor := 0
  rationalFunction := 0 (additive identity of rationalFunctions)
  divisor_eq: data.divisor A.base 0 = of 0, by map_zero.

zeroTau is tauOfQOrderFields of these fields (powers of the identity
endomorphism), with zeroTau_eq_powers.

## Exact missing pi preimage

QvPhiPiPreimage qOrder:
* divisor in the effective carrier with divisor = ULift.up qOrder;
* rationalFunction in rationalFunctions.obj A.base;
* data.divisor A.base rationalFunction = of divisor.

QvPhiPiPreimageRequired qOrder := Nonempty.

tauOfPiPreimage: conditional tau = powers of the pi element once the preimage
is supplied.  No pi element, qOrder alignment, or tau=pi^Z is asserted.

No fake pi/tau; no completion/L.
