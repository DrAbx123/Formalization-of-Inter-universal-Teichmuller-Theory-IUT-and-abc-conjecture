# S1306: original SourceHDDReadout / true HDD hull+det module

Date: 2026-10-30. Exact only. S1287/S1262 rank=1 unit-section surrogate is
NOT used.

## Paper object required

SourceHDDReadout consumes a source dsc run and produces the paper HDD object:

  actual holomorphic hull carrier  IQ(S+-; n, D^vdash_vQ)
  detTensorPower / determinant module  det (x)^M
  log-volume normalization and the signed readout
  plus the dsc -> hull+det integration.

## What exists

Finite/packet level (actual, but not the module):
* Volume.lean: PositivePacket packetDet/packetLogVolume, FiniteHull volume and
  average_le;
* HullDeterminantLogVolumeReduction.lean:
  HullDeterminantLogVolumeFrozenSpec and
  hullDeterminantLogVolumeFrozenSpec_holds; matrixLogDet laws;
  Cor312ComparisonData and cor312CThetaLowerBound are cards at the paper
  object boundary.
* SourceK1K2ActualTuplePacket.actualTuplePacket: actual finite-place tuple
  packet with determinant = actual Haar measure of the scaled canonical hull,
  logVolume = actualTupleHullLogVolume, possibleImage = actual hull-volume
  initial segment.  This is an actual finite tensor/Haar packet, not the paper
  arithmetic-vector-bundle determinant module.

Explicit boundary in HullDeterminantLogVolumeReduction.lean header:
the paper objects (IQ carrier, actual det (x)^M operation, log-volume
normalization) are NOT represented by the frozen spec; d5CarrierModelHullAdjunction
and the scalar log-degree model are calibration witnesses only, not the paper
carrier.

Explicit boundary in Volume.lean: the paper's holomorphic hull and source-facing
log-volume construction remain pending (Obligation
IUT-III.holomorphic-hull-determinant-log-volume).

Not usable: S1262 rank=1 unit-section HDD lattice / S1287 assembly.  They are
simplified HDD local-lattice/readout surrogates, not a hull+det module.

## First exact field

For the true HDD module:

  holomorphicHull : actual carrier of the paper holomorphic hull
    (not a rank-1 span, not a scalar/real-line calibration model)

Then:

  detTensorPower : holomorphicHull -> determinant module (det (x)^M)
  logVolume / normalized readout on that module
  dsc-to-hull+det integration (source dsc:H2FProcession first; see S1165/S1287
  exact fields).

No actual holomorphicHull carrier or detTensorPower operation exists in the
tree.  The finite packet Haar model and the frozen spec do not supply them.

## Consumer

SourceHDDReadout (dsc -> hull + det), Step 3.11.5 / SHE q-vs-hull.  A true
module would remove the HDD hull+det module requirement; the rank=1 surrogate
does not.

## Status

EXIT=0 report; no new wrapper and no S1262 surrogate used.
