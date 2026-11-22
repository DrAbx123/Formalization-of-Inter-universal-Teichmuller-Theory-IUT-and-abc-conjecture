# S962: tensor-packet paper inequality

Date: 2026-10-30. Inequality only; S961 supplies the exact S945 carrier
log-volume datum, and S962 defines the normalized log-volume on its
FinalLTensorLogVolumeData. No equality is asserted.

## Tensor log-volume

tensorNormalizedLogVolume D S =
  log (D.measure S).toReal - log (D.measure D.unitRegion).toReal.

tensorNormalizedLogVolume_mono:
  S subset U -> 0 < mu S -> mu U < top -> V(S) <= V(U),
via measure_mono and Real.log_le_log.

## qPilot and paper hull

qPilotTensorLog D := V D (qPilotPaperImageInLValued).
paperTensorHullLog D := V D (paperTensorHull D).

## Conditional per-b inequality

qPilotTensorLog_le_paperTensorHullLog:
  S957ThetaImageDenseInQPilot D ->
  0 < mu (qPilotPaperImageInLValued) ->
  mu (paperTensorHull D) < top ->
  qPilotTensorLog D <= paperTensorHullLog D.

This is exactly S957 density + S956/S961 log data, no equality/scaling.

## Global weighted

tensorPacketPaperWeightedInequality D :=
  weightedPaperV (fun b => qPilotTensorLog (D b)) <=
  weightedPaperV (fun b => paperTensorHullLog (D b)).

tensorPacketPaperWeightedInequality_of_perB:
  per-b density, qPilot positivity, hull finiteness -> global weighted
  inequality, using S919.weightedPaperV_mono with actual nativeBadLocalWeight.

No equality; exact hypothesis list recorded.
