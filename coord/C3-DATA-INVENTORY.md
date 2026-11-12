# C3-DATA-INVENTORY — concrete C3/tensor/Haar data for route-C R computation

Status: READ-ONLY inventory, 2026-11-12. No files outside coord modified.
Question: is there enough concrete data to compute R (or rhs) for l=5/model D?

## 1. C3 log-shell tensor block

Definitions (tmp/sheaf/xif/paper/C3LogShellTensorPacketActual.lean; olean 282104 B):
- C3LogShellTensorBlock C3 (line 58) is an abbrev:
    ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple
  parameterized by C3 : SourcePilotRegionData (l,V,I).
- actualC3LogShellTensorRegion (:74) = tensorIntegralRegion of actualC3LogShell per factor;
- actualC3LogShellTensorRegion_compact (:82);
- actualC3LogShellTensorIQ (:91) = Q-span of the region;
- actualC3LogShellTensorHaar (:96) = Measure.addHaar;
- actualC3LogShellTensorHaar_isAddHaar (:101);
- actualC3LogShellTensorLogVolume (:107) = (haarLogVolume ...).toReal;
- structure ActualC3LogShellTensorPacket (:113) and constructor
  actualC3LogShellTensorPacket (:133).
These are green definitions/constructors, but every one is conditional on a C3 term.
There is no standalone C3LogShellTensorBlock instance and no numeric evaluator for the
Haar log-volume.

Concrete C3 data:
- C3Actual.lean:44 SourcePilotRegionDonors (19 donor fields);
  sourcePilotRegionDataOfDonors (:79); nonempty sourcePilotRegion_nonempty_of_donors (:105);
- C3ActualThetaPacketWitnessConstruction: donorWithActualThetaPacket (:70),
  actualC3OfDonors (:93), actualC3ThetaPacketWitness (:106),
  actualC3ThetaPacketWitness_nonempty_of_donors (:127);
- There is NO actual SourcePilotRegionData instance: old C3 requires completion roots;
  completion-root impossibility (A936/OLD-SCHEMA-MIGRATION) makes old
  SourcePilotRegionData impossible for concrete q. The L replacement is
  SourcePilotRegionDataL (S1391:244/329), which is not accepted by
  C3LogShellTensorPacketActual (it consumes the old SourcePilotRegionData).
- So C3LogShellTensorBlock cannot be instantiated from currently green concrete data;
  it would need an L-typed C3 tensor consumer or a bridge.

## 2. Theta hull and RHS data

Theta hull:
- GlobalThetaPilotHullLogVolumeActual.lean (olean 177744 B):
  thetaHullVolumeAt (v) := I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n) (:46);
  globalThetaHullLogVolume := sum_v log (thetaHullVolumeAt v).toReal (:54);
  globalThetaImageLogVolume (:58);
  data structure GlobalThetaPilotHullLogVolumeData (:90) and constructor
  globalThetaPilotHullLogVolumeData (:105).
- These are actual definitions on I, R : forall v, SourceImageRealization v, n, but no
  concrete values: sourceSetVolume/sourceHolomorphicHull are source functions, not
  numerically evaluated in the tree.
- C3LogShellTensorHolomorphicHullActual (olean 101160 B):
  thetaPilotHull = actualHolomorphicHull C3 (actualUnitRegion C3), with
  thetaPilotHull_eq_region, thetaPilotHull_compact, thetaPilotHullLogVolume (ENNReal).
  Still conditional on C3.

RHSData / LogVolumeData:
- Iut/Cor312/RightHandSide.lean:65 RHSData (container, proc_standard, toRational,
  vol, hull, thetaPilot, thetaPilot_hullAdmissible);
  rhs (:107) := R.vol.processionVol R.thetaHull.
- Iut/Cor312/LogVolume.lean:79 LogVolumeData (weight, componentVol, packetVol, laws);
  Iut/Concrete/Container.lean:280 container (LargeVolumeContainerData) and :378 vol
  (LogVolumeData) — actual source constructions for the concrete local container;
- Iut/Concrete/ThetaRegion.lean:320 rhsDataOn, :335 rhsData / :340 rhsDataLit
  (RHSData from InitialThetaData and thetaPilot sets).
- Oleans for Iut/Concrete/Container.lean, Iut/Concrete/ThetaRegion.lean, and
  Iut/Cor312/RightHandSide.lean are NOT built in the current .lake tree (source exists,
  compile not green). So rhsDataOn/rhsData are source-level constructors, not green
  artifacts in this build.
- No concrete InitialThetaData is available: Iut/Concrete/Existence.lean:303 thetaData
  is conditional on EllipticCurveData + CurveArithmetic + TateInputs + ModEllRepData etc.
  No actual elliptic curve/Theta-data term is constructed.

## 3. S3137QThetaPilotLogVolumeReadingsActual

File tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean (olean 93384 B).
Inputs:
  C3 : SourcePilotRegionData (l,V,I)
  P : PaperQPilotObjectActual (l,I)
Definitions:
  qPilotLogVolumeReading (P) := P.signedQPilotLogVolume;
  qPilotLogVolumeReading_eq_neg_abs_qParameter;
  thetaPilotHull := actualHolomorphicHull C3 (actualUnitRegion C3);
  thetaPilotHull_eq_region; thetaPilotHull_compact;
  thetaPilotHullLogVolume (ENNReal) := haarLogVolume ...;
  comparison qThetaPilotLogVolumeComparison is a named pending Prop (not proved).
No green instance:
- no actual SourcePilotRegionData (old C3; completion roots impossible);
- no actual PaperQPilotObjectActual: the old QPilotLineActual needs C1/C2/C3 old, and
  the canonical object constructor is conditional; the green L paper object
  (OrigXiFPaperQPilotOfBoundary / SPaperQPilotObject) is an OrigXiFPaperQPilotObject,
  not the old PaperQPilotObjectActual required here.
Thus S3137 readings are defined but cannot be instantiated for a concrete l=5/model D.

GlobalThetaPilotHullLogVolumeActual: the data constructor is green, but it is a wrapper
around sourceSetVolume/sourceHolomorphicHull; it is not a numeric evaluator.

## 4. Verdict: is there an R-computable path?

No complete path from currently green concrete data. Exact gaps:
1. No actual SourcePilotRegionData (old C3): the completion-root obstruction is
   unconditional for concrete q (A936). The L record SourcePilotRegionDataL is actual
   but has a different type; C3LogShellTensorPacketActual and S3137 consume the old type.
   Need either (a) an L-typed C3 tensor consumer, or (b) a bridge that does not require
   old completion roots.
2. No actual OriginalInput/InitialThetaData concrete D with numeric
   sourceSetVolume/sourceHolomorphicHull. thetaHullVolumeAt/globalThetaHullLogVolume are
   green functions but not evaluated.
3. RHSData/rhsDataOn constructors in Iut/Concrete are not compiled (no oleans); even if
   compiled they need a concrete InitialThetaData and thetaPilot sets.
4. No actual PaperQPilotObjectActual for S3137; the green L paper object is a different
   type (OrigXiFPaperQPilotObject).
5. C3LogShellTensorLogVolume is a Haar log-volume; no normalization/evaluation lemma
   computes it from finite data. Actual C3 tensor is a formula, not a number.

Minimal work to make R computable:
- Build a concrete InitialThetaData/OriginalInput (curve + arithmetic + Tate inputs +
  prime data) or a model D with all fields;
- Provide a concrete SourcePilotRegionDataL-to-C3 tensor adapter (or retype
  C3LogShellTensorPacketActual to C3L);
- Evaluate sourceSetVolume/sourceHolomorphicHull for that D (or supply numeric hull
  volumes as data with proofs of the definitions);
- For RHSData, compile Iut/Concrete/Container+ThetaRegion and instantiate thetaPilot;
- For S3137, supply actual P (old PaperQPilotObjectActual) or retype to L object.

Conclusion: the tree has green **definitions and conditional constructors** for C3 tensor,
Haar log-volume, theta hull log-volume, RHSData and S3137 readings, but **not** a concrete
C3/D/P instance; no routing computes R numerically for l=5/model D. The precise missing
piece is the old C3 record and concrete D/P, not a missing definition.
