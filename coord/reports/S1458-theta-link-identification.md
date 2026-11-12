# S1458: concrete ThetaLink link_identification

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/OrigXiFThetaLinkIdentificationActual.lean
EXIT=0; SHA256 42AEFFD0601AB221DB15E937830077F716BBF621C0090CD06E0DF3A7DDC61AF2
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/OrigXiFThetaLinkIdentificationActual.olean

## Concrete replacement

OrigXiFThetaLinkIdentification O D C3 : Prop :=
  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3 /\
  OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D.

The first conjunct is the actual paper qPilot scalar compatibility (from
OrigXiFPaperQPilotScalarActual); the second is the actual signed-hull
log-volume comparison (from OrigXiFPaperSignedHullActual).  It is not the
ray-membership target: the ray membership is derived.

## link_implies_inclusion

OrigXiFThetaLinkIdentification_implies_inclusion:
  O.qPilotLogVolume in
    hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume.

Proof: rewrite by the scalar equality, then use OrigXiFThetaLinkRay_iff_le
with the actual comparison. No circular target-as-input.

## Exact residuals retained

- OrigXiFThetaLinkScalarExactFirstField O C3 :
    O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3;
- OrigXiFThetaLinkComparisonExactField D C3 :
    OrigXiFPaperQPilotLogVolume C3 <= OrigXiFSignedThetaHullLogVolume D.

No placeholder Prop, no PUnit/True, no circular assumption.
