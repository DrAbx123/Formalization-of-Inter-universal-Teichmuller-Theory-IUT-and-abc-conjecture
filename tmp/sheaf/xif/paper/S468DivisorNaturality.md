# S468: conditional divisor naturality from unit inclusion pullback

Date: 2026-10-29. Function-field inclusion pullback; no norm.

## Construction

DvSmallValuationFamily := forall X : Example32SmallBase K,
  DvCoverNormalizedValuationData K (coverField X).

DvSmallValuationCompatibility V := forall {X Y} (f : X -> Y) (x : (coverField Y)^x),
  (V X).valuation (unitInclusionPullback f x) = (V Y).valuation x.

unitInclusionPullback f := Units.map (arrowAlgebraMap f).toMonoidHom
(S456), with arrowAlgebraMap f : coverField Y ->+[K] coverField X.

## Conditional theorem

divisorMap_naturality:
given V and hV compatibility, for f : X -> Y and x,
  divisorMap (V X) (Additive.ofMul (unitInclusionPullback f x))
  = divisorMap (V Y) (Additive.ofMul x).

Proof: both sides unfold via S457 divisorMap_apply to
intToStageDivisorGrothendieck of the corresponding valuation exponent; hV
identifies the two exponents.

DvSmallDivisorNaturalityData packages the valuation family, compatibility,
and the naturality theorem.

No norm is used. No fake valuation/compatibility; no completion/L.
