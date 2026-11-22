# S652: extension image log from actual finite Dirac image measure

Date: 2026-10-29. No fake Haar.

## Actual extension image log

extensionImageLog hq :=
  Real.log ((rootThetaImageMeasure (rootThetaUnitBall)).toReal).

rootThetaImageMeasure is the actual finite sum of Dirac measures on the root
Theta image points (PaperRootThetaProductMeasureActual).

extensionImageLog_eq_log_card:
  extensionImageLog hq = Real.log (Fintype.card (ThetaLabel l)).

This uses rootThetaImageMeasure_unitBall under hq.

## qPilot scalar comparison

qPilotScalar := Real.log G.thetaPacket.q.

ExtensionImageLogQPilotComparison hq :=
  extensionImageLog hq = qPilotScalar.

No inhabitant is provided; the finite Dirac image cardinality has no derived
relation to the q-pilot scalar.

## Exact Haar/measure gap

ExtensionImageHaarGap := RootThetaProductHaarGapRequired.

The Dirac image measure is explicit but is not a product Haar measure; the
algebraic-closure product has no Haar in this API. No compatibility is assumed.

No fake measure/Haar; no completion/L.
