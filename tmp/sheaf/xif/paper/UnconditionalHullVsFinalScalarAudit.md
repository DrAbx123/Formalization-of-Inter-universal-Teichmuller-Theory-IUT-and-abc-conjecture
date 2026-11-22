# unconditionalPaperSignedHull vs final global scalars

Date: 2026-10-29

## Objects compared

From `ConcreteSignedHullUnconditionalActual`:

```text
unconditionalPaperSignedHull
  : PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value)
```

It uses the C3 source theater data `actualSignedC3 l V I D` and the normalized
Haar measure `normalizedHaarMeasure ... D nu`.  Its actual procession is

```text
unconditionalPaperSignedHull_procession_eq:
  hull.procession = c3ThetaSignedProcession (actualSignedC3 ... D)
unconditionalPaperSignedHull_hull_logVolume_eq:
  hull log-volume = ENNReal.ofReal (c3ThetaSignedProcession ...).average
```

From `ConcreteSourceComparisonActual`:

```text
concreteQLogVolume I
  = (paperQPilotObjectConcrete l I).qPilotLogVolume
  = sourceQPilotSignedLog I.initial
```

The concrete comparison is

```text
P.procession.average <= -concreteQLogVolume I.
```

From `PaperLevelXiFTargetProofActual`, the final scalars are

```text
globalQPilotLog      = sum_b nativeBadLocalWeight b * perBQPilotLog b
globalThetaHullLog   = sum_b nativeBadLocalWeight b * perBThetaHullLog b
```

where `perBQPilotLog b` is the normalized `c_norm` tensor scalar and
`perBThetaHullLog b` is the actual normalized root-hull log-volume on
`qVFamTensorBlock T b`.

## Equality check

**No current instance / theorem identifies these objects.**

Reasons, each an actual type-level mismatch:

1. **Different source object**
   `unconditionalPaperSignedHull` uses `actualSignedC3 ... D`, whose theta packet
   is the C3 theater theta packet from the donor D.
   `perBQPilotLog` uses `qVFamily T b`, the Clause-B q family.
   `SourceTheaterQVFamilyMismatchActual` already records the exact missing
   identification of the concrete theater q with qVFamily q; no such theorem is
   in the tree.

2. **Different carrier**
   `PaperC6Carrier places tuple` is not `qVFamTensorBlock T b`; the concrete hull
   uses `PaperC6Carrier` and the final proof uses the per-b one-factor
   ArithmeticTensorTupleBlock.

3. **Different measure**
   The concrete hull uses `normalizedHaarMeasure ... D nu`; the final proof uses
   `Measure.addHaar` on each `qVFamTensorBlock T b`.

4. **Different scalar normalization**
   `concreteQLogVolume = sourceQPilotSignedLog I.initial` is the source signed
   q-pilot log.  `perBQPilotLog` is the normalized tensor coefficient
   `c_norm` scalar `-c_norm * log p_b`, with no equality to the source scalar.

## Exact reusable bridge (not inhabited)

A bridge proving the correspondence would have to supply, per bad b, all of:

```text
structure ConcreteFinalScalarBridge where
  c3_scalar_eq_qVFam :
    concreteQLogVolume I = globalQPilotLog
  procession_average_eq_hullLog :
    (unconditionalPaperSignedHull ...).procession.average
      = globalThetaHullLog
  theater_q_eq_qVFamily : ...
  carrier_measure_compatibility : ...
```

No constructor is available.  In particular the first two equalities cannot be
obtained by `rfl` or by the current concrete link: `concreteSourceComparison`
only connects the concrete procession average to `-concreteQLogVolume`, not to
the final normalized qVFamily/root-hull scalars.

## Conditional reuse

The concrete link is reusable only at its own level:

```text
(unconditionalPaperSignedHull ...).procession.average <= -concreteQLogVolume I
  <=> concreteQLogVolume I in hullLogVolumeRay (hull.signedHullLogVolume)
```

and the final proof is reusable only at its own level:

```text
globalQPilotLog <= globalThetaHullLog
```

Neither implication transfers across the missing bridge above.

## Status

- Concrete procession average: actual (`c3ThetaSignedProcession ...`).
- Concrete q-pilot scalar: actual (`sourceQPilotSignedLog I.initial`).
- Final normalized qVFamily/root-hull scalars: actual and compiled.
- Equality/bridge between the two layers: **exact gap**, with the four
  mismatches above.  No fake equality was added.
