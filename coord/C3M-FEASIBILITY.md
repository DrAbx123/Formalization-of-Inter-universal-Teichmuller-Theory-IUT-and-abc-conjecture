# C3M-FEASIBILITY — can R = |log Θ| be computed? (A971)

Status: **NOT numerically computable** from current tree; M = A − R remains symbolic.  MODEL/analysis only.

## 1. Where R comes from

- `R = −rhs`, where
  `rhs = (concreteVariantData D).rhsData.rhs = R.vol.processionVol R.thetaHull`
  (`Iut/Cor312/RightHandSide.lean:107`);
- `gap D := rhs + sF(nC)·A − V` (`Iut/WallEquiv/Gap.lean:523`);
- paper margin `M = V + gap − (sF−1)A = A + rhs = A − R`.

## 2. Candidate data sources read

- `S3137QThetaPilotLogVolumeReadingsActual.lean` (olean true):
  - `thetaPilotHullLogVolumeReal := Real.log ((actualC3LogShellTensorHaar C3)
     (thetaPilotHull C3)).toReal` (:128-129);
  - `thetaPilotHull := actualHolomorphicHull C3 (actualUnitRegion C3)` (:97);
  - `qPilotLogVolumeReading` (:77).
  This is an actual Haar volume, but requires a concrete
  `C3 : SourcePilotRegionData` and the actual log-shell tensor region/measure;
  no numeric value or closed form is produced.
- `GlobalThetaHullVsQPilotComparisonActual.lean` (olean true):
  - `thetaHullSignedLogVolume := -globalThetaHullLogVolume` (:59);
  - `qPilotMagnitude := -I.qPilotSignedLogVolume` (:63);
  - comparison is an explicit `Prop` (`qPilotThetaHullComparison`), NOT a value.
- `GlobalThetaPilotHullLogVolumeActual.lean`:
  - `globalThetaHullLogVolume := ∑ v, Real.log (thetaHullVolumeAt ...).toReal`
    (:54-55), with `thetaHullVolumeAt := I.sourceSetVolume v (I.possibleThetaPilotImageSet v (R v) n)`;
  - this is an abstract per-place source-set Haar volume; `I.sourceSetVolume`/
    `sourceHolomorphicHull` have no numeric instantiation here.
- `Ind3OutputHullQPilotActual.lean`: only compactness/measure-positivity; no value.
- `Mzk1PaperNormThetaActual` / `Mzk1ScaledTheta*`: paper-normalized θ-side forms
  (`thetaSumPaper`, `paperDeficit`), but they use `A` and `sF`, not the actual
  Θ-pilot hull Haar volume R.

## 3. Feasibility verdict

R is **not computable** from the current data:
1. `rhs` is an abstract `vol.processionVol thetaHull` field of `RHSData`
   (`vol : LogVolumeData container`), not a formula with numerical inputs;
2. `globalThetaHullLogVolume` needs for each `v : V`:
   - the actual source-space measure `I.sourceSetVolume v`, and
   - the actual source holomorphic hull `I.sourceHolomorphicHull v (R v) n`
   (or the concrete C3 `C3LogShellTensorBlock` Haar measure and region);
3. no concrete `C3 : SourcePilotRegionData` for l=5 with its actual
   theta-pilot hull/measure is instantiated; the C1 model data (bad primes/q)
   do not determine R.

## 4. Symbolic table

`coord/c1_margin_symbolic.csv` columns:
`base,k,A_from_T,M_symbolic,M_ss_symbolic,note`,
where `A = T/(sF−1) = T/1.5` from the C1 sample, and
`M = A − R`, `M_ss = A − R − gap`.  R and gap are NOT numerical; the table only
shows the computable A side and the exact symbolic dependence.

## 5. Needed data to compute R (gap list)

1. Concrete `C3 : SourcePilotRegionData` for the target D (l=5) with actual
   `tensorIndex`, tensor places, tensor unit/landing data;
2. `actualC3LogShellTensorRegion` and `actualC3LogShellTensorHaar` (or
   `I.sourceSetVolume` + `sourceHolomorphicHull`) evaluated for that C3;
3. the `LogVolumeData` / `RHSData.vol` packet formula for `thetaHull`
   (`Iut/Cor312/RightHandSide.lean` definitions), including the `1/nC`
   procession aggregation;
4. a concrete `qPilot`/`I` to get A and the bad-place data;
5. C0's `ind2Term` exact formula for gap (if M_ss sign is needed).

Until these exist, no numeric M=A−R table is possible; do not reuse M0.
