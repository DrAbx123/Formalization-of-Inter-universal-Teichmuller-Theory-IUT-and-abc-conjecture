# S1305: HDD local lattice from actual hull+det — exact first field

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1305HDDLatticeFromHullDetExact.lean — EXIT=0.

## Actual hull+det sources present

- HullDeterminantLogVolumeFrozenSpec, with actual proof
  hullDeterminantLogVolumeFrozenSpec_holds: finite positive-packet determinant,
  tensor, rescaling and hull-average identities.
- Actual matrix log-det laws in HullDeterminantLogVolumeReduction.
- DetTensorPowerLogVolumeBookkeeping: named det(x)M log-volume bookkeeping, but
  only the scalar log-degree calibration instance exists; the file itself states
  it is not the paper carrier.
- SourceImageHull/SourceImageHullVolume: actual value-monoid source hull,
  sourceHullVolume, and named SourceCompactBound; hull volume can be top under
  pointwise degree faithfulness.
- Cor312ComparisonData: scalar comparison card, not a lattice module.

## Exact first field

No actual local-field lattice/module is produced by these hull+det sources,
and no localRing-module structure on the value monoid or on bundle.total is
available. Therefore the first field remains exact:

  S1215HDDLocalLattice (I := I)
    rank : Nat
    lattice : Theorem311Output I -> place -> Set (Fin rank -> localField v).

The file records S1305HDDLocalLatticeExactType; no inhabitant is asserted.

## Surrogate status (STOPPED)

S1262/S1286/S1295 rank-one unit-section HDD lattice is a SHE/1-column
surrogate, not the paper HDD hull+det module. It is not used for the first
field here and is not a final original-object construction.

No Fin 1 or arbitrary Set surrogate is introduced.
