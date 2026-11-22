# S457: divisor map to Grothendieck of the stage divisor monoid

Date: 2026-10-29. Map/additivity only; no divisor naturality.

## Construction

For V : DvCoverNormalizedValuationData K L:

valuationExponentHom : Additive L^x ->+ Z
  toFun x := Multiplicative.toAdd (V.valuation x.toMul)
  map_zero/map_add from V.valuation being a monoid hom.

divisorMap : Additive L^x ->+ GrothendieckAddGroup StageDivisor
  := intToStageDivisorGrothendieck.comp valuationExponentHom.

divisorMap_apply unfolds this formula; divisorMap_add is map_add.

divisorMapFamily packages the per-cover map from a valuation family
Vf : forall L, DvCoverNormalizedValuationData K L.obj.obj.

StageDivisor is the actual ULift Nat stage divisor monoid; the target is its
Grothendieck additive group.

No divisor naturality is asserted. No fake valuation, no completion/L,
no inequality.
