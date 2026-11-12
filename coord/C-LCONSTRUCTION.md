# C-LCONSTRUCTION — L-version and concrete-D path (A978)

Status: **NOT constructible numerically**; L version blocked at the same missing R/tensor data.
Date 2026-11-12; lane hull.

## 1. Read: S3137 / globalTheta fields

`S3137QThetaPilotLogVolumeReadingsActual` (olean true):
- `qPilotLogVolumeReading P := P.signedQPilotLogVolume` (:77);
- `thetaPilotHull C3 := actualHolomorphicHull C3 (actualUnitRegion C3)` (:97);
- `thetaPilotHullLogVolume C3 := haarLogVolume (actualC3LogShellTensorHaar C3)
   (thetaPilotHull C3)` (:112);
- `thetaPilotHullLogVolumeReal C3 := Real.log
   ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal` (:128);
- `qThetaPilotLogVolumeComparison` (:145) is the exact comparison Prop (pending).

`GlobalThetaPilotHullLogVolumeActual` (olean true):
- `thetaImageVolumeAt v := I.sourceSetVolume v (I.possibleThetaPilotImageSet v (R v) n)`;
- `globalThetaHullLogVolume := ∑ v : V, Real.log (thetaHullVolumeAt v).toReal` (:54);
- `globalThetaPilotHullLogVolumeData` packages the same data.

`GlobalThetaHullVsQPilotComparisonActual` (olean true):
- `thetaHullSignedLogVolume := -globalThetaHullLogVolume` (:59);
- `qPilotMagnitude := -I.qPilotSignedLogVolume` (:63);
- `qPilotThetaHullComparison` is a Prop, no numeric value.

## 2. L-version attempt

Target: `thetaPilotHullLogVolumeL (PL : OrigXiFPaperQPilotObject) (C3L : SourcePilotRegionDataL)`.

Blocked, because:
- S3137's `thetaPilotHull`/`thetaPilotHullLogVolume` need `C3 : SourcePilotRegionData`
  and the type `C3LogShellTensorBlock C3` with `actualC3LogShellTensorHaar`;
- `SourcePilotRegionDataL` (S1391:244) has the L roots/Kummer/tensor fields but is
  NOT a `SourcePilotRegionData` (old schema impossible, A940); there is no
  `C3LogShellTensorBlock`/log-shell tensor region/Haar for the L core in tree;
- `OrigXiFPaperQPilotObject` (OrigXiF...Actual) gives a q-pilot/line/strip object,
  but not a `C3` tensor Haar region;
- the global source formula needs `R : ∀v, I.SourceImageRealization v` and
  `n : ThetaPilotCarrier`; the L paper object does not supply the R realization
  (that is exactly the A948 image-realization gap).

So an L-version may be *typed* only by introducing a new L tensor-log-shell block
and Haar measure; no such object exists yet.  Do not fake it.

## 3. sourceSetVolume / sourceHolomorphicHull: concrete definitions

`SourceImageHullVolume.lean`:
- `sourcePointVolume v x := ENNReal.ofReal (sourceLocalLogDegree v x)` (:107);
- `sourceLocalLogDegree v x := ∑ i : SourceVolumeIndex l, logDegreeAt 0 0 v (x i)`;
- `sourceSetVolume v S := ⨆ x ∈ S, sourcePointVolume v x` (:188);
- `sourceHullVolume v R n := sourceSetVolume v (sourceHolomorphicHull v R n)` (:193).

`SourceImageHull.lean`:
- `logDegreeAt n m v x := Multiplicative.toAdd ((I.primeStripAt n m).degree v x)` (:100).

Thus R is formally computable from `I`, `R : ∀v, SourceImageRealization v`, `n`,
and the theta-pilot points/image set:
  `R = -∑ v, Real.log ((sourceHullVolume v R n).toReal)`
(using globalThetaHullLogVolume).  The missing data are the concrete I/R/n,
not the volume definition.

## 4. Concrete-D path: Iut/Concrete/Existence.lean:303

`thetaData : InitialThetaData` takes:
- `C : EllipticCurveData` (F, Fbar, E, badAll, etc.);
- `CA : C.CurveArithmetic`;
- `TI : C.TateInputs`;
- `ℓ` prime with **`7 ≤ ℓ`** (`h7`), so **l=5 is not allowed** by this theorem;
- `R : C.ModEllRepData ℓ`;
- `hsl : ∀ A, A.toGL ∈ R.rep.range` (SL2 image);
- `hP2 : ∀ w ∈ C.badAll, ¬ ℓ ∣ TI.qOrder w`;
- `hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ ≠ ℓ`;
- `hcore : OrbicurveDataSection.HasCoreUniversally C.F C.E`.

Verdict for model l=5: **impossible via this constructor** (h7: ℓ≥7); for ℓ≥7
the inputs C/CA/TI/R/hsl/hP2/hP5/hcore are not available for a concrete model
curve in this repo.  The synthetic `concreteI`/`sourceHaarActualOriginalInput`
are V=Unit, q=1 Haar objects, not a real elliptic-curve Θ-data.

## 5. R computation path / gap list

1. concrete `EllipticCurveData` + CurveArithmetic + TateInputs + ModEllRepData for a
   real curve with ℓ≥7 (not l=5);
2. `SourceImageRealization` for all v (A948 R gap),
3. `n : ThetaPilotCarrier` and the source theta-pilot points/image set;
4. concrete L tensor log-shell block/Haar if the L route is used;
5. then `globalThetaHullLogVolume` and R are numeric via sourceSetVolume.

Until then M=A−R stays symbolic; no C3 numeric table is possible.
