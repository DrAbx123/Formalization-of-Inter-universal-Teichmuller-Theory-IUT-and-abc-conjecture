# S465: lifted S457 divisor map at universe u+1

Date: 2026-10-29. Map/additivity only; no naturality.

## Construction

uliftAdditiveDown : Additive (ULift.{u+1} L^x) ->+ Additive L^x
  x |-> Additive.ofMul x.toMul.down.

liftedDivisorMap V :
  Additive (ULift.{u+1} L^x) ->+ GrothendieckAddGroup StageDivisor.{u}
  := (divisorMap V).comp uliftAdditiveDown.

LiftedDivisorMap_apply: value is divisorMap V of the ULift-down.
LiftedDivisorMap_add: additivity.

liftedDivisorMapFamily packages the per-cover map from a valuation family
Vf : forall L, DvCoverNormalizedValuationData K L.obj.obj.

The codomain is the S457 codomain GrothendieckAddGroup StageDivisor.{u};
only the source is lifted to universe u+1, as specified.

No divisor naturality, no fake valuation, no completion/L, no inequality.
