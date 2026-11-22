# S1451: layer-O OrigXiFPaperSignedHull repair

Date: 2026-10-31. EXIT=0.

## Fix

The file failed because ActualThetaHull is defined in
LeanFormal.IUT.XiFPaperThetaHull, not in the opened XiFPaper namespace. Added

  open LeanFormal.IUT.XiFPaperThetaHull

at the top. No changes to objects or claims.

## Actual content preserved

* ActualThetaHull: actual 1,circ U compact image union, holomorphic hull,
  normalized Haar log-volume, lambda*O containment;
* SignedHullLogActual: actual determinant/log-volume finite hull packets,
  procession, positive determinant tensor power, signed procession normalization;
* OrigXiFThetaHullAmbient reads the IQHullLogVolumeInterface off ActualThetaHull;
* OrigXiFDeterminantFiniteHull from the actual procession values;
* OrigXiFSignedThetaHullLogVolume = -(actual hull log-volume).toReal, proved
  equal to the actual signed determinant-procession normalization and
  nonpositive;
* OrigXiFPaperSignedHull actual PaperSignedHull with projected ambient/procession;
* OrigXiFThetaHullLogVolumeRay and OrigXiFThetaLinkRay_iff_le compute the
  ThetaLink ray obligation as the actual signed-hull inequality.

## Remaining exact datum

The existing structure field
  thetaHull.haar.logVolume thetaHull.compactHull.hull
    = ENNReal.ofReal determinant.procession.average
is the paper procession-normalization identification (IUT III Step xi-d/e).
Also ActualThetaHull.paper_IQCarrier_realization is the pre-existing exact
paper IQ carrier realization field. Neither is a free Real parameter or a new
Prop placeholder; both are exact obligations on actual objects.

## Verification

lake env lean compile EXIT=0. No sorry/axiom/True/PUnit in the file body
(only module-docstring words). SHA reported.
