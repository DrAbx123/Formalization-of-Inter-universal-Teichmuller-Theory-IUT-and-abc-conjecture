# S627: paper xi-f thetaSourceComparison exact gap

Date: 2026-10-29. No concrete scalar obstacle used.

## Exact comparison

For actual
O : PaperQPilotObjectActual I and P : PaperSignedHull X label,

thetaSourceComparison O P : Prop
  := P.procession.average <= -O.signedQPilotLogVolume.

The right side is O.qPilotLogMagnitude = -O.signedQPilotLogVolume.

## Reduction

thetaSourceComparison_iff_gap:
  thetaSourceComparison O P
    <-> P.procession.average <= O.qPilotLogMagnitude.

thetaSourceComparison_of_gap:
  the exact comparison follows from the explicit
  average <= qPilotLogMagnitude inequality.

## Exact gap

MissingPaperXiFComparison O P :=
  P.procession.average <= O.qPilotLogMagnitude.

No inhabitant is provided; PaperXiFComparisonExactGap records the same Prop.
No concrete source numerical inequality, no obstacle, no qVFamilyK/Phi/tau
alignment is used.

No fake comparison; no completion/L.
