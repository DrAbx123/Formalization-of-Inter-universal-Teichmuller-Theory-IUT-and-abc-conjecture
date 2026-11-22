# C9 output-region stage-1 target (per VALUESPAPER-SEMANTICS-REVIEW)

## Required object

Paper values are not point/singleton log-degrees.  The next executable object is:

`OutputRegionData`: for each actual C4 output configuration `(n,x,w)`, an actual
region `R(n,x,w) ⊆ IQCarrier` (or the paper-local output carrier), together with:

- provenance: the actual C4 witness/output data determining R;
- determinand/tensor-power data for the relative determinant (xi-c/xi-d);
- a valid-region condition (nonempty? measurable? positive/finite Haar mass as
  required by the normalization donor);
- the actual normalized log-volume readout of R after determinant/tensor power;
- comparison with the source q-pilot region and Theta hull.

`R` cannot be a free field, an arbitrary subset, or `{thetaImage n w.1}`; the
singleton degeneracy is killed by Haar translation invariance.

## Existing facts

- `C6ActualIdentification.lean`: exact equalities characterizing
  `C6ActualIQData.actual` (hull/iqInterface/signedHullLog/normalizedLogVolume/
  unitReferenceLog/normalizationWeight). Arbitrary B must carry `.IsActual`.
- `FinitePlaceNormalizedUnitScalingLogVolume`: normalization requires positive
  mass for small sets and finite mass for large sets; singleton Haar mass is not
  the output-region volume.
- C4 `eval`/`U` currently independent of `x`; a faithful output-data model or a
  proved x-invariance statement is required (C4-STAGE1 G4).
- C7Reductions: actual U->IQ map missing; weak constant map is not a source map.
- C9Paper Q/Theta structures still have free fields; not target-valid.

## Next executable steps

1. Define the actual output region map from C4 witness/output data; if absent,
   record exact missing production declaration (no free map).
2. Prove valid-region/normalization conditions using the actual Haar/measure
   donor, not singleton values.
3. Only then define ValuesPaper and prove boundedness/approximation against
   QPaper/ThetaPaper.

## Status

Old C9ValuesPaper singleton definition and current free-field C9Paper are NOT
accepted targets.  No N8 closure.