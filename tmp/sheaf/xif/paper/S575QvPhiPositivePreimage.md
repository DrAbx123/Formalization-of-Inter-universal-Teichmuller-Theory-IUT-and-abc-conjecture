# S575/S585: positive qOrder unit and aligned divisor formula

Date: 2026-10-29. Formula proved; positive preimage constructed.

## positiveUnit

positiveUnit qOrder := Classical.choose ((P.valuation A.base).valuation_surjective qOrder).

positiveUnit_valuation:
  toAdd (valuation (positiveUnit qOrder)) = qOrder.

## S585 formula

positiveUnit_divisor:
  (s566Input P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit qOrder)))
    = of (ULift.up qOrder : ((qvPhi P.ramification).obj A.base).carrier).

Proof: S491 divisor evaluation, divisorMap_apply, positiveUnit_valuation,
intToStageDivisorGrothendieck_ofNat, S583 grothendieckStageDivisorULift'_of,
and stageDivisorULiftEquiv'_ulift_up.

## Actual positive preimage

PositiveQvPhiPreimage qOrder:
  qOrder_pos, rationalFunction := Additive.ofMul (ULift.up (positiveUnit qOrder)),
  divisor := ULift.up qOrder, divisor_eq := positiveUnit_divisor.

positiveQvPhiPreimage qOrder hq constructs it for 0<qOrder.

No fake preimage/divisor; no completion/L.
