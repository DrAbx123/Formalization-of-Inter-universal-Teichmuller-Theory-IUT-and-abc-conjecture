# S1463: O-layer OrigXiFThetaLinkActual

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/OrigXiFThetaLinkActual.lean
EXIT=0; SHA256 68F8478F489705B125E384403D331925F4934FB466F0A70A51404F83A50F17AA
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/OrigXiFThetaLinkActual.olean

## Structure

OrigXiFThetaLinkActual O D C3 where
  scalar_eq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3
  signedHull_le : OrigXiFPaperQPilotLogVolume C3 ≤ OrigXiFSignedThetaHullLogVolume D.

The two exact scalar fields are structure inputs; no inhabitant is asserted.

## link_identification

OrigXiFThetaLinkActual.link_identification A : Prop :=
  OrigXiFThetaLinkIdentification O D C3 (the S1458 concrete proposition),
with rfl equality. Not a free Prop field.

## link_implies_inclusion

OrigXiFThetaLinkActual.link_implies_inclusion A h:
  O.qPilotLogVolume in hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume.
Actual, via S1458 OrigXiFThetaLinkIdentification_implies_inclusion.

## Conditional constructor

origXiFThetaLinkActualOf O D C3 hscalar hcomparison :
  OrigXiFThetaLinkActual O D C3.

No fabricated inhabitant.  Linter warnings only: duplicate namespace (structure
and namespace same name) and defProp for the constructor returning a Prop; no
errors.
