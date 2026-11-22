# S669: S663 actual PaperSignedHull into PaperXiFSourceLink theta side

Date: 2026-10-30. A/hnormal discharged by S663.

## Actual theta hull

s663PaperSignedHull is the actual S663 PaperSignedHull
  (ArithmeticTensorTupleBlock places tuple, SignedLabel l.value)
with A := s663Interface average and hnormal := s663Interface_logVolume_hull.

## Conditional source link

s669PaperXiFSourceLink takes only:
* hident: the four source paper identifications;
* hqpaper: S669QPilotLogVolumeEqPaper O C3, i.e.
  O.qPilotLogVolume = paperQPilotLogVolume C3;
* link_identification : Prop;
* link_implies_inclusion: link_identification ->
  O.qPilotLogVolume in hullLogVolumeRay (s663PaperSignedHull).signedHullLogVolume.

It builds PaperXiFSourceLink O s663PaperSignedHull C3 with those fields.

s669PaperXiFInclusion additionally takes hlink : link_identification and
builds PaperXiFInclusion.

s669_qPilot_mem_ray yields the paper xi-f membership.

No fake q/paper equality; no fake link implication; A/hnormal not parameters.
