# REUSE-AUDIT-HULL — existing region/hull/det assets (A1048)

Status: read-only inventory; no compile.  Companion: `REUSE-IQHULL-INTEGRATION.md`,
`XID-DETERMINANT-PLAN.md`, `SIGNED-REUSE-CONFIRM.md`.

## 1. Theta/q/C3 region definitions and inclusions

| file | object | status |
|---|---|---|
| `C3LogShellTensorPacketActual.lean` | `C3LogShellTensorBlock`, `actualC3LogShellTensorRegion`, `actualC3LogShellTensorIQ`, `actualC3LogShellTensorHaar`, `actualC3LogShellTensorLogVolume`, `ActualC3LogShellTensorPacket` | green defs; region = tensor integral of local log-shells |
| `C3LogShellTensorHolomorphicHullActual.lean` | `actualUnitRegion`, `actualNonzeroScalings`, `actualScaledRegion`, `actualCandidateHulls`, `actualHolomorphicHull`; `actualRegion_subset_hull`, `actualHolomorphicHull_subset_candidate`, `actualHolomorphicHull_unitRegion_eq`, `actualHolomorphicHull_monotone` | green; least λO hull |
| `S3137QThetaPilotLogVolumeReadingsActual.lean` | `thetaPilotHull`, `thetaPilotHull_eq_region`, `thetaPilotHullLogVolume`, `thetaPilotHullLogVolumeReal` | green; theta hull = C3 region |
| `S2723GlobalIQHullActual.lean` | `globalIQUnitRegion`, `globalIQHull`, `globalIQLogVolume`, `globalIQLogVolume_mono`, `globalIQHullInterface` | green; global IQ hull |
| `RootHullContainmentInequalityActual.lean` | `qPilotClassicalRegion`, `rootThetaRegion`, `rootThetaImageSet`, `rootThetaHull`; `qPilotClassicalRegion_subset_rootHull`, `qPilotClassicalLog_le_rootThetaHullLog` | green; **q⊆rootThetaHull** (this is not A1049 direction; it is a q-side inclusion into a root-theta hull) |
| `GenericQPilotCompletionPowerActual.lean` | `genericQPilotRegion`, `genericQPilotImagePoint`, `qParameterUnitLambdaHull`; `GenericQPilotRegionSubsetGap`, `GenericQPilotRegionUnitCorrectionGap` | region actual; full region inclusion is a GAP structure/Prop, only image point inclusion proved |
| `FinitePlaceIQHullSharpUpperBound.lean` | `arithmeticTupleCanonicalHull_subset_IQHullUnitRegion`, `arithmeticTupleIQHullUnitRegion`, `arithmeticTupleIQHull_hull_logVolume_le_unitRegion` | green; hull⊆scaled unit region |
| `SourceImageHull.lean` / `SourceImageHullVolume.lean` | `sourceHolomorphicHull`, `sourceHullVolume`, `sourceSetVolume`, `sourceLocalLogDegree` | green; source-set model (sign-degenerate under realified action, see `DECOMP-L-MODEL-SIGNS.md`) |

## 2. Monotonicity / containment lemmas

| lemma | statement | status |
|---|---|---|
| `haarLogVolume_mono` (`FinitePlaceIQHullInterface:68`) | `S⊆T ⇒ haarLogVolume μ S ≤ haarLogVolume μ T`; no finiteness | green |
| `haarLogVolume_of_lt_top` (`:55`) | finite measure bridge | green |
| `haarLogVolume_mono_of_subset` (`Mzk1QRegionInclusionActual:44`) | negative-log: `S⊆T` ⇒ `logVol T≤logVol S` | green abstract |
| `arithmeticTupleNormalizedLogVolume_mono` (`FinitePlaceNormalizedUnitScalingLogVolume:107`) | `S⊆T`, `0<μS`, `μT<⊤` ⇒ normalized log mono | green |
| `actualHolomorphicHull_monotone` (`C3LogShellTensorHolomorphicHullActual:135`) | `P⊆Q` ⇒ `hull P⊆hull Q` | green |
| `actualRegion_subset_hull` (`:82`) | `P⊆hull P` | green |
| `qPilotClassicalRegion_subset_rootHull` (`RootHullContainmentInequalityActual:81`) | qPilot classical ⊆ rootThetaHull | green |
| `qPilotClassicalLog_le_rootThetaHullLog` (`:123`) | normalized-log inequality from the inclusion | green |
| `globalIQLogVolume_mono` (`S2723:80`) | `S⊆T` ⇒ `globalIQLogVolume S≤globalIQLogVolume T` | green |
| `sourceSetVolume_mono` (`SourceImageHullVolume`) | ENNReal source-set mono | green (but sign issue) |
| `componentVol_le_of_subset` / `packetVol_mono` (LeanFormal lana-derived) | positive-volume mono | green; importable |

## 3. Rank>1 / exterior / tensor power assets (beyond `DeterminantLogVolumeActual`)

Contrary to the first XID plan, rank>1 infrastructure **exists**:

- `S1476HDDRankActual.lean` (`:82`):
  `S1476RankArithmeticVectorBundle (r)`, `s1476GlobalLocalization`,
  `s1476FreeArithmeticVectorBundle`, `s1476LocalLattice`,
  `s1476LocalLatticeEquiv`, `S1476ArithmeticVectorBundleLocalization`,
  `s1476ActualLocalization`,
  `s1476S1215HDDLocalLattice_rank_gt_one`;
- `S1418HDDConsumerActual.lean`:
  `S1418GlobalLattice`, `s1418GlobalLattice_eq_hull`, `s1418GlobalLattice_mono`,
  `s1418DetTensorPower_globalLattice`, `s1418DetTensorPower_image`,
  `s1418DetTensorPower_two`, `s1418ActualFrozenHullDetSpec`;
- `S1422HDDDetActual.lean`:
  `DetTensorPowerLogVolumeBookkeeping` (det tensor power/log-volume laws),
  `detDataOfHull`, `dependentDetDataOfChar`, `hullPacket_det_eq_prod`,
  `hullPacket_logVolume_eq_log_det`, `frozenSpecZero_holds`;
- `Hull09H5GapsActual.lean` reuses
  `detTensorPowerBookkeeping_scalarLogDegree` (`HullDeterminantLogVolumeReduction:483`);
- `HullPacketActual.lean` / `Mzk1ChainInferredReuseActual.lean` use
  `packetLogVolume_tensorPower`;
- `DeterminantLogVolumeActual.lean` remains the **rank-one** fractional-ideal layer.

Verdict: a rank>1/lattice-det basis is present (S1476/S1418/S1422), but it is
stated on the HDD/dependent-product region, not directly on the C3 theta region;
an identification is still needed.

## 4. `S2807 hpacket`, `S2714`, `S3016` non-interface versions

- `S2807SG3bScalarActual.S2807_upperGap_of_packetLogVolume_le` has
  `hpacket : actualC3LogShellTensorLogVolume = packetLogVolume` as an explicit
  hypothesis.  No green theorem proves it.  `S2807ThetaHullVolumeIdentityActual`
  proves only `S2717ThetaHullLogVolume = -Haar(log-volume of C3 region)`, not the
  packet identity.
- `S2714CThetaUpperInventoryActual` is an upper-bound inventory; its
  `S2714_sourceSignedHull_upper_zero` is the trivial `≤0` estimate, not the
  paper CTheta bound.
- `S3016CThetaUpperActual` is an **interface** (`S3016CThetaUpperInterface`)
  carrying `thetaSigned ≤ cthetaPaper*|stepVLogMagnitude|` as a field; no
  non-interface theorem proving it.
- `S3016StepVQPilotIdentificationActual` states the identification as a
  `Prop`/`GAP`, not a theorem.
- `S3017StepVUpperGapAssembly` is partial (procession average only, CTheta
  pieces missing).

## 5. Usability summary

| need | reusable asset | caveat |
|---|---|---|
| theta hull region | `actualC3LogShellTensorRegion` / `thetaPilotHull` | concrete; hull=region green |
| q region | `qPilotClassicalRegion`, `genericQPilotRegion`, `QRegionCarrierSpec.region` | q region definitions on different carriers; no single identification |
| theta⊆q inclusion | none directly | `RootHullContainment` gives q⊆rootThetaHull (opposite); `XiEContainment` gives q⊆hull |
| log monotonicity | `haarLogVolume_mono`; `haarLogVolume_mono_of_subset` | use negative-log form for A1049 |
| rank>1 det | S1476/S1418/S1422 | HDD/dependent-product, not C3; bridge needed |
| hpacket | assumption only | no green non-interface version |
