# C9 q-pilot region/log-volume interface - stage 1

- Task: C9-QPILOT-REGION (B route).
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/C9QPilotRegion.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorry: one (`qPilotProcessionNormalizedVolumeTarget_obligation`).

## Actual q source

`nativeQ X := NativeC3.nativeQActual X : FinitePlaceQCandidate
  (NativeC3.nativeFPlaceOverBad X)`.

This is the actual native C3 q built from the source Tate comparison witness;
the completion is the actual `Completion (nativeFPlaceOverBad X)`.

## Region source

`qPilotRegionSource X : Set (Completion (nativeFPlaceOverBad X)) := {(nativeQ X).q}`.

Actual singleton q-pilot region, with `qPilotRegionSource_nonempty` and
`nativeQ_mem_region` proved.  No arbitrary Type is introduced.

## Actual signed log/magnitude

- `qPilotSignedLog X := ArithmeticQPilotLogVolume.localSignedLog (nativeQ X)`;
- `qPilotLogMagnitude X := ArithmeticQPilotLogVolume.localLogMagnitude (nativeQ X)`;
- `qPilotSignedLog_eq_localSignedLog` rfl; `qPilotSignedLog_neg` from production.

`localSignedLog` is the production `Real.log ‖q‖` donor; it is actual and
uses the same `FinitePlaceQCandidate` as C3.

## Kummer-relative volume (actual, zero sorry)

`qPilotKummerRelativeVolume X :=
  `Multiplicative.toAdd (unitNormLogDegree (Completion ...)
    (Units.mk0 (nativeQ X).q (nativeQ X).q_ne_zero))`.

`qPilotKummerRelativeVolume_eq : qPilotKummerRelativeVolume X = qPilotSignedLog X`
is the production theorem `ArithmeticQPilotLogVolume.unitNormLogDegree_q`.
This is the actual Kummer/unit-relative q volume, no sorry.

## Procession-normalized volume: exact target + named sorry

Production arithmetic normalization is conditional on selected places:

- `qPilotSelectedPlaces X := {nativeFPlaceOverBad X}` (actual singleton);
- `qPilotSelectedParameters` sends the selected place to the actual native q;
- `qPilotProcessionNormalizedVolume X :=
  `ArithmeticQPilotGlobalNormalization.selectedLowerSignedLog
    (qPilotSelectedPlaces X) (qPilotSelectedParameters X)`.

Exact target:

`qPilotProcessionNormalizedVolumeTarget X := qPilotProcessionNormalizedVolume X = qPilotSignedLog X`

`qPilotProcessionNormalizedVolumeTarget_obligation : ... := by sorry`.

Gap: production has no actual full procession-normalized q-pilot volume donor;
`selectedLowerSignedLog` is the conditional arithmetic normalization, and the
identification with the actual q scalar is the missing relation.  No free
Real/Type field is introduced.

## Interface record

`QPilotRegionInterface` has actual fields: region (with equality), signedLog,
kummerRelativeVolume, processionNormalizedVolume (with equality fields).
`qPilotRegionInterface` is the actual constructor, zero sorry.

## Status

- statement_compiles: true (EXIT=0).
- actual region source, signed log, Kummer-relative volume, interface constructor.
- procession-normalized identification: named sorry target.
- no Lean target changed outside this new file.