# Theta-pilot global signed hull: replacement assessment

Status: **do not replace yet**. The current `unconditionalPaperSignedHull` is a
real finite C3 theta-packet signed hull with the paper-normalized Haar measure,
but it is **not** the global Theta-pilot signed hull of IUT III, Theorem 3.11 /
Corollary 3.12. Replacing it now would silently change the ambient carrier and
the arithmetic object, which is exactly the kind of fake integration that the
current source tree does not support.

This document records the exact actual objects that exist, the objects that are
still missing, and the files that must be changed when the global hull is
actually constructed.

## 1. What the current unconditional hull actually is

File: `tmp/sheaf/xif/paper/ConcreteSignedHullUnconditionalActual.lean`

Constructed objects:

- `unconditionalPaperSignedHull`:
  `PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value)`
- `unconditionalPaperSignedHull_procession_eq`:
  the procession is `c3ThetaSignedProcession (actualSignedC3 D)`
- `unconditionalPaperSignedHull_hull_logVolume_eq`:
  the C6 IQ hull log-volume equals
  `ENNReal.ofReal (c3ThetaSignedProcession (actualSignedC3 D)).average`
- `unconditionalPaperSignedHull_signedHnormal`

The Haar normalization is constructed in
`tmp/sheaf/xif/paper/NormalizedHaarHnormalActual.lean`:

- `normalizedHaarScale`
- `normalizedHaarMeasure = ENNReal.ofReal normalizedHaarScale • nu`
- `normalizedHaarMeasure_concreteHnormalEquality`
- `normalizedHaarMeasure_signedHnormal`

Thus hnormal is not an assumption in the unconditional file. But the ambient
carrier is `C6ActualIQData.actual places tuple mu`, and the procession is the
finite C3 packet procession
`c3ThetaSignedProcession (actualSignedC3 D)`, not the global Theta-pilot
arithmetic hull.

## 2. What the global Theta-pilot signed hull needs

For the global Theta-pilot object of Theorem 3.11 / Corollary 3.12, the
`PaperSignedHull` fields must be instantiated by:

1. `ambient : IQHullLogVolumeInterface X`
   - the global paper carrier `IQ(S±_{j+1}; n,∘D^vdash_{vQ})` with its hull,
     image union, unit region, lambda-scaling, normalized Haar log-volume and
     compactness containment;
   - not the finite arithmetic tensor block currently used by
     `C6ActualIQData.actual`.

2. `procession : WeightedValues label`
   - the global Theta-pilot procession/average, over the actual global
     `S±_{j+1}` labels and the actual global `vQ`/place data;
   - not the one-packet `c3ThetaSignedProcession` of a single source-theater
     C3.

3. `hull : FiniteHull label`
   - the actual finite hull data attached to the global Theta-pilot image/hull,
     with `volume` and `hullVolume` read from the actual global object;
   - not the finite sum of absolute one-packet values.

4. `weighted_matches_hull`, `weights_nonnegative`, `average_nonneg`
   - actual proofs for the global procession/hull, not transferred from the
     finite C3 model.

5. `hull_logVolume_eq_average`
   - the actual global normalized Haar equality for the global hull;
   - `normalizedHaarMeasure_concreteHnormalEquality` is only the finite C6
     tensor-block equality and must not be renamed as the global one.

6. The arithmetic Theta-pilot divisor data
   - the actual arithmetic divisor determined by the zero locus of the theta
     values `q_j^2`;
   - the q-pilot divisor and the Theta-link relation.

## 3. Actual objects that exist today

These are real and reusable, but do not by themselves form the global hull:

- `tmp/sheaf/xif/paper/ThetaPilotObjectActual.lean`
  - `ThetaPilotImageHullAt v R n`
  - `thetaPilotImageHullAt v R n`
  - `thetaPilotImage_subset_hull`
  - `qPilotPoint_mem_thetaPilotHull`
  - actual value-layer image/hull at one place/procession
  - explicitly **not** the global arithmetic-divisor Theta-pilot object
  - exact missing: `ThetaPilotArithmeticDivisorData` /
    `MissingThetaPilotArithmeticDivisor` (theta divisor, q-pilot divisor,
    zero-locus data, Theta-link relation)

- `tmp/sheaf/xif/paper/C3LogShellTensorPacketActual.lean`
  - `C3LogShellFiber`
  - `C3LogShellTensorBlock`
  - `actualC3LogShellTensorRegion`
  - `actualC3LogShellTensorRegion_compact`
  - `actualC3LogShellTensorIQ`
  - `actualC3LogShellTensorHaar`
  - actual finite C3 tensor log-shell packet/regions/Haar data

- `tmp/sheaf/xif/paper/PrimeStripLogShellActual.lean` and
  `PrimeStripC3LogShellCapsuleActual.lean`
  - actual F-/D-prime-strip capsule
  - actual C3-indexed local log-shell data
  - exact missing: `PrimeStripC3PlaceComparison` (actual `V ≃ C3.tensorIndex`
    and place agreement)

- `tmp/sheaf/xif/paper/GlobalQPilotProcessionLogVolumeActual.lean`
  - actual global q-pilot log magnitude from the `V_bad` base q family
  - this is the q-pilot side, not the Theta-pilot hull side

- `tmp/sheaf/xif/paper/GlobalQPilotVsSignedHullComparisonActual.lean`
  - compares the finite signed-hull average with the actual global q-pilot
    magnitude
  - already shows the finite average is not silently the global normalization

- `tmp/sheaf/xif/paper/SourceFiniteMultiradial.lean` and
  `tmp/sheaf/xif/paper/IndeterminaciesActual.lean`
  - actual finite `ProcessionChoice` core/profile, Ind1/Ind2/Ind3 value-layer
    actions
  - these are finite models, not global `IQ`-hull carriers

- `tmp/sheaf/xif/paper/NormalizedHaarHnormalActual.lean`
  - actual normalization for the finite C6 tensor block `ArithmeticTensorTupleBlock`
  - not a Haar measure on the global `IQHullLogVolumeInterface` carrier

## 4. Files/objects that must change on replacement

When the global Theta-pilot hull object actually exists, replace the following
consumers/definitions. Until then, keep the finite objects under their current
names; do not rename them as global.

1. `tmp/sheaf/xif/paper/ConcreteSignedHullUnconditionalActual.lean`
   - current: `unconditionalPaperSignedHull`
   - replacement target: `globalThetaPilotSignedHull`
   - new ambient must be the global `IQHullLogVolumeInterface`; new
     procession/hull must be the global Theta-pilot procession/hull; new
     hnormal must be proved for the global Haar measure.

2. `tmp/sheaf/xif/paper/ConcretePaperSignedHullActual.lean`
   - current: `concretePaperSignedHull`
   - replacement target: map from the global hull object to
     `PaperSignedHull`; the current finite C3 construction should remain only
     as the finite source-theater model.

3. `tmp/sheaf/xif/paper/PaperThetaMagnitudeSignedActual.lean`
   - current: `actualSignedHull`, `SignedHnormal` for `actualSignedC3`
   - keep as the C3 finite source-theater model; do not use it as the global
     Theta-pilot object.

4. `tmp/sheaf/xif/paper/PaperSignedHullSignedActual.lean`
   - current: `paperSignedHullFromSignedTheater`,
     `signedSourceTheaterFiniteHull`, `sourceTheaterC3Signed`
   - keep for C3/Gaussian alignment; the global hull must use the global
     arithmetic divisor/theta zero locus, not this finite theater packet.

5. `tmp/sheaf/xif/paper/ConcretePaperUnconditionalDataActual.lean`
   - current: `concretePaperUnconditionalData` with `ConcreteHnormalEquality`
     input
   - replacement: consume `globalThetaPilotSignedHull`; do not keep a
     conditional hnormal interface for the global object.

6. `tmp/sheaf/xif/paper/ConcreteCor312ConclusionActual.lean`
   - current: `unconditionalConcreteHull`,
     `unconditionalPaperUnconditionalData`, `unconditionalPaperXiFInclusion`
   - replacement: same consumers over `globalThetaPilotSignedHull`; the
     `PaperXiFInclusion` and `PaperUnconditionalData` fields must be
     repopulated with the global signed hull.
   - keep the two exact source-comparison Props
     (`ConcreteQPilotLogNormalizationObstacle`,
     `UnconditionalSourceComparisonObstacle`) until the corresponding actual
     global comparisons are proved.

7. `tmp/sheaf/xif/paper/NormalizedHaarHnormalActual.lean`
   - current: `normalizedHaarMeasure` on `ArithmeticTensorTupleBlock`
   - replacement: a global normalization on the actual global hull carrier,
     using the actual global Haar measure and the actual compactness/unit-region
     data; the finite normalization may remain as a finite model.

8. `tmp/sheaf/xif/paper/GlobalQPilotVsSignedHullComparisonActual.lean`
   - current: finite average vs actual global q-pilot magnitude
   - replacement: compare actual global `ThetaPilotSignedHull.signedHullLogVolume`
     with the actual global q-pilot magnitude; keep the exact comparison Prop,
     do not assert the inequality.

9. `tmp/sheaf/xif/paper/ThetaPilotObjectActual.lean`
   - current: per-place/value-layer actual image/hull
   - extend with the actual global arithmetic divisor object; the current file
     already records `ThetaPilotArithmeticDivisorData` as the exact missing
     object.

10. `tmp/sheaf/xif/paper/PrimeStripLogShellActual.lean`
    - current: exact missing `PrimeStripC3PlaceComparison`
    - this comparison is required before the global hull can use the actual
      C3 log-shell/tensor carriers as the global `IQ` carrier.

## 5. Dependency order for a real replacement

1. Construct `ThetaPilotArithmeticDivisorData`:
   - actual theta divisor from the zero locus of `q_j^2`;
   - actual q-pilot divisor;
   - actual theta/q-pilot zero-locus data;
   - actual Theta-link relation.
   No arbitrary divisor or zero-locus placeholder.

2. Construct the actual global `IQHullLogVolumeInterface` for
   `IQ(S±_{j+1}; n,∘D^vdash_{vQ})`:
   - global carrier, hull, image union, unit region, lambda-scaling,
     normalized Haar log-volume, compactness containment;
   - use the actual global log-shell/tensor data and the actual Haar measure;
   - this is not the finite `ArithmeticTensorTupleBlock` field.

3. Construct the actual global Theta-pilot procession and finite hull:
   - actual global labels/places/processions;
   - actual theta values;
   - actual finite hull volume from the global hull object;
   - actual `weighted_matches_hull` and `average_nonneg`.

4. Prove the global hnormal:
   `globalAmbient.logVolume globalAmbient.hull =
     ENNReal.ofReal globalProcession.average`
   from the actual global Haar normalization, not by assumption.

5. Update the consumer files 1-8 above; keep the finite C3/Gaussian files as
   the finite source-theater model and as alignment witnesses for
   `actualSignedC3` / `actualGaussianC3`.

6. Only after the global hull is actual, connect the Cor312 consumer and the
   source comparison. The exact comparison Props remain explicit until the
   actual global comparison is proved.

## 6. Decision

- **Do not replace now.**
- The current `unconditionalPaperSignedHull` is unconditional only with respect
  to hnormal; it is not the global Theta-pilot signed hull.
- The global object requires new actual arithmetic-divisor, global `IQ`-hull,
  global procession, global Haar normalization, and global comparison objects.
- The C3/Gaussian files remain legitimate finite source-theater objects; they
  should not be renamed or repackaged as global objects.
- No inequality is asserted in this plan, and no fake global object is
  introduced.

## 7. References

- IUT III, Theorem 3.11, (i), (ii), (Ind1)/(Ind2)/(Ind3).
- IUT III, Corollary 3.12, Step (xi), signed `-|log Theta|`.
- IUT III, Definition 3.8, (i) (Theta-pilot divisor).
- IUT III, Remark 3.9.5, (i), (ii) (holomorphic hull).
- IUT III, Proposition 3.2 (tensor packets of log-shells).
