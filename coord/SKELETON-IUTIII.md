# SKELETON-IUTIII - IUTIII 190-file node map (hull A429; event-level; 2026-11-11)

Method: source tree D:/lean/LeanFormal/IUT/IUTIII has 190 .lean files; olean coverage checked against D:/lean/.lake/build/lib/lean/LeanFormal/IUT/IUTIII. Tree asset status only (no full rebuild or checker run). No new math.

## 0. Headline
- 190 source files, 187 built oleans; 3 sources have NO olean: Corollary312/StepXI/HolomorphicHull/CardHullRealR9PointMembershipAudit.lean, Theorem311/SourceK1K2CardReduction.lean, Theorem311/SourcePacketDegreeLedger.lean.
- Tree three layers: Theorem311 (77 files + Indeterminacy 14 + Output 9) -> Corollary312 (7 files) -> StepXI (32 files) -> HolomorphicHull (51 files).
- Cor 3.12 paper-layer consumers: S3182Cor312HullDetAssemblyActual (Cor312HullDetConclusion conditional on HullDetAssemblyInputs) and S3180ConditionalAssemblyActual (imports IUTIII Corollary312.StepXI.Contract; ABCConjecture conditional). Hull wrappers: Hull08/Hull10/Hull12/Hull13 (H7 Ob9), Hull09 (H5 Ox), Hull06 (det tensor).
- IUTII linkage: no direct import LeanFormal.IUT.IUTII edge inside IUTIII (grep across all 190 files); the thetas link is carried by paper-layer S31xx/AbsTopIII files that import both interfaces. This is the Lean-level 3.11-IUTII gap.

## 1. Module inventory (src/olean)
- Theorem311: 77/75. Theorem 3.11 source-algorithm and route library: D-theta, K1/K2 packets, finite routes, hull envelope conditions.
- Theorem311/Indeterminacy: 14/14. Ind1, Ind2, Ind3, reductions, orbit/quotient transport, StepX formal quotient docking.
- Theorem311/Output: 9/9. MultiradialAlgorithm(+Reduction/GeneralRouteNormalForm), CarrierConnectorSpecification, Frobenius bridge, presentation wiring.
- Corollary312: 7/7. Comparison, Routes, Obligations, APT, ArithmeticQPilot{LogVolume,BaseChange,GlobalNormalization}, TateQPilotJComparison.
- Corollary312/StepXI: 32/32. Contract, ContractSourceReduction, ParametricStepXI, FiniteCertificateBridge, CertificateHullWiring(Realization/Signed), ThetaPacketBridge, SourceProcessionStepXI family, SourceLogShellMuNQuotientCarrier, SourceSharedBoundary, SourceColumnCarrierIdentification, SHE/IPL transports.
- Corollary312/StepXI/HolomorphicHull: 51/50. SourceHullCompactnessReduction, SourceHullInterfaceDischarge, CardHullReal* (GeometryReduction, Dichotomy, Edge, GapCards, Generator, R9, SignedLogVolume, FinitePhaseGate, HaarDilation), HullDeterminantLogVolumeReduction, OModuleCompactnessLayer, LocalField*Hull volumes, Volume, WeightedNormalization, SourceQSideComparison, certificate comparison/transfer.

## 2. Key files, declarations, status (tree assets)
### 2.1 Corollary312 main
- Corollary312/Comparison.lean:7: cor312Conclusion_of_contract (contract : StepXIContract) : Cor312Conclusion contract (PROVED wrapper).
- Corollary312/Routes.lean:44: Cor312Conclusion certificate.contract (route certificate consumption).
- Corollary312/APT.lean:2-3: imports Theorem311.SourceMultiradialTwoActionEquivalence and Theorem311.SourceArithmeticHolomorphicLanding; defines SourceTheorem311MultiradialAlgorithm and SourceTheorem311TwoActionEquivalence (Theorem 3.11 source-algorithm interface; proved reflexivity/transitivity layer plus Props).
- Corollary312/Obligations.lean, ArithmeticQPilotLogVolume/BaseChange/GlobalNormalization, TateQPilotJComparison: q-pilot log-volume normalization, residue norm base, local log magnitude/order identities, QPilot comparison (real-object proved lemmas).
### 2.2 StepXI
- StepXI/Contract.lean: StepXIContract and Cor312Conclusion core definitions (Cor 3.12 statement layer; conditional contract fields). S3180 imports this file directly.
- ContractSourceReduction, ParametricStepXI: source reduction and parametry. FiniteCertificateBridge. CertificateHullWiring(Realization/Signed): certificate-hull wiring, imports HolomorphicHull.SourceHullInterfaceDischarge, FiniteCertificateBridge, ThetaPacketBridge, SourceSharedBoundary, SourceQSideComparison, IQCarrierConcreteModel.
- ThetaPacketBridge: theta-packet bridge anchors. SourceLogShellMuNQuotientCarrier: muN quotient and weightN log (IUTII log-shell anchor inside IUTIII).
- SourceProcessionStepXI(+MinimalForm/InclusionResidual), SourceColumnCarrierIdentification, SourceAdjacentColumnProcessionIsomorphism, SHE transports: Step (xi) column/procession layer.
### 2.3 HolomorphicHull (H5-side tree assets)
- SourceHullCompactnessReduction.lean: IQHullLogVolumeInterface (:52), imageSet_logVolume_le_hull (:88), hull_logVolume_lt_top (:95), lower_bound_and_finiteness (:104), singletonRealWitness (:112), iqHullLogVolume (:148, Obligation).
- SourceHullInterfaceDischarge.lean: hull_logVolume_realRepresentation (:85), haarContractionInterface (:109) plus hull_logVolume_lt_top (:149), sourceHullVolume_not_lt_top_of_degreeFaithful (:170), ValueHullCompactnessInput (:205), sourceHullVolume_lt_top_of_compactnessInput (:223), iqHullInterfaceDischarge (:252, Obligation).
- CardHullRealGeometryReduction.lean: sourceScalingUnits_subset_sourceHolomorphicHull (:94), sourceHolomorphicHull_eq_closure (:108), sourcePointVolume_mul_le (:129), sourceHullVolume_eq_imageVolume_iff (:152), sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le (:162/181), negative counterexamples (:200/213/230), sourceHullVolume_le_imageVolume_of_candidate (:278), sourceLocalLogDegree_le_zero_of_mem_sourceHolomorphicHull (:297). This is the H5 hull-vs-image-volume engine consumed by Hull09.
- HullDeterminantLogVolumeReduction.lean: HullDeterminantLogVolumeFrozenSpec (:123), hullDeterminantLogVolumeFrozenSpec_holds (:153), packetLogVolume_eq_matrixLogDet (:249), matrixLogDet/packet diagonal tensor lemmas (:173-256). Det-tensor bookkeeping consumed by Hull06/Hull09.
- CardHullReal* edge/generator/gap normalization layer; OModuleCompactnessLayer; LocalField*Hull*; Volume.lean; WeightedNormalization.lean; SourceQSideComparison.lean; certificate comparison/transfer files.
### 2.4 Theorem311 anchors
- Output/MultiradialAlgorithm(+Reduction/GeneralRouteNormalForm), CarrierConnectorSpecification: multiradial output algorithm.
- SourceMultiradialTwoActionEquivalence and SourceArithmeticHolomorphicLanding: the two anchors consumed by Corollary312/APT.lean.
- ConcreteFiniteModel(+Transport), ConcreteRouteNormalForm/Uniqueness: concrete finite route model (StepXI concrete columns consume via ConcreteFiniteRouteColumns).
- SourceK1K2* family (about 20 files): K1/K2 construction, hull presentation, packet, realization, volume translation, multiradial two-action. No olean: SourceK1K2CardReduction; SourcePacketDegreeLedger.
- Hull* files: HullDirectednessCovolumeSignProbe, HullEnvelopeConditionsDischarge, HullImageDirectednessStatementLayer, HullLambdaDilationLayer, HullPresentationAlternativeProbe (hull envelope/directedness statement layer).
- SourceDThetaConstruction, SourceH1H2Construction, SourceDependencyChain, Obligations: D-theta/H1H2/obligation ledger.

## 3. Dependency edges (exact)
- Paper layer to IUTIII: S3180ConditionalAssemblyActual imports IUTIII Corollary312.StepXI.Contract; S3182Cor312HullDetAssemblyActual imports Hull04/Hull05 plus AbsTopIII14 and S3129/S3132 wrappers and produces Cor312HullDetConclusion conditional on HullDetAssemblyInputs.
- IUTIII internal: Corollary312/Comparison <- StepXI/Contract; Routes <- StepXI/Contract; StepXI/CertificateHullWiring <- HolomorphicHull.SourceHullInterfaceDischarge, FiniteCertificateBridge, ThetaPacketBridge, SourceSharedBoundary; CardQCMPComparison <- ContractSourceReduction plus ParametricStepXI plus ArithmeticQPilotGlobalNormalization; ConcreteFiniteRouteColumns <- Theorem311.ConcreteFiniteModelTransport plus HolomorphicHull.Volume/WeightedNormalization plus FiniteCertificateBridge.
- Theorem311 anchors <- Corollary312/APT.lean.

## 4. Cor312 <- 3.11 <- IUTII: exact links and gaps
- Cor 3.12 in tree: Corollary312.StepXI.Contract (StepXIContract, Cor312Conclusion); proved wrappers Comparison.cor312Conclusion_of_contract and Routes.lean:44.
- Theorem 3.11 in tree: source-algorithm/comparison interface in Corollary312/APT.lean (built on Theorem311/SourceMultiradialTwoActionEquivalence and SourceArithmeticHolomorphicLanding). No single theorem311 conclusion theorem exists; Theorem311 is the source-algorithm/route library.
- GAP 1: no direct IUTII import edge in IUTIII; IUTII theta/log-shell/Kummer objects are bridged outside IUTIII by paper-layer S3136* (model source clause/native data with Haar), S3129/S3132 (IQ-hull/log-volume source), AbsTopIII05/14. Missing Lean link: an IUTIII-level hypothesis/instance carrying the IUTII EtaleThetaKummerClass/SourceLogShellDatum data into StepXIContract fields.
- GAP 2: StepXIContract fields are the named/conditional part of Cor 3.12; Cor312Conclusion is derived from the contract and S3182 instantiates it from hull/det inputs conditionally.

## 5. Missing-olean / fragile files
- Corollary312/StepXI/HolomorphicHull/CardHullRealR9PointMembershipAudit.lean (no olean, audit file).
- Theorem311/SourceK1K2CardReduction.lean (no olean, K1/K2 card reduction).
- Theorem311/SourcePacketDegreeLedger.lean (no olean, packet degree ledger).
All other 187 files built.

## 6. Declarations NOT in E/plan docs (candidates to merge into E-EXISTING-CLOSURE-MAP.md)
- Cor312: Cor312Conclusion, StepXIContract, cor312Conclusion_of_contract, Cor312Conclusion certificate.contract.
- StepXI: CertificateHullWiring family, ThetaPacketBridge, SourceLogShellMuNQuotientCarrier, SourceProcessionStepXI*, SourceContour/ColumnCarrierIdentification, FiniteCertificateBridge, SourceSharedBoundary, SHE/IPL transports.
- HolomorphicHull: IQHullLogVolumeInterface (+imageSet_logVolume_le_hull/hull_logVolume_lt_top/lower_bound_and_finiteness/singletonRealWitness/iqHullLogVolume), ValueHullCompactnessInput/sourceHullVolume_lt_top_of_compactnessInput/iqHullInterfaceDischarge, HullDeterminantLogVolumeFrozenSpec/hullDeterminantLogVolumeFrozenSpec_holds, CardHullReal* normalization/gap/generator/R9 files, OModuleCompactnessLayer, LocalField*Hull* volume/transport.
- Theorem311: Hull* envelope/directedness files, SourceK1K2* family, SourceDThetaConstruction/H1H2Construction/SourceDependencyChain, MultiradialAlgorithm*/CarrierConnectorSpecification, ConcreteFiniteModel*/ConcreteRoute*.

## 7. Consumer status summary
- Cor 3.12 hull/det: CONDITIONAL (S3182 HullDetAssemblyInputs -> Cor312HullDetConclusion). H5/H7 wrappers Hull09/10/12/13 and Hull06 det tensor consume the tree anchors above; H5 class-A items proved, named class-B: full O(-)^-1 normalization on arithmetic line bundle and hull <= image-volume inequality; H7 named: deep arbitrary-iterate Ob9 independence.
- ABC: S3180 conditional (q != 1 tree readouts plus hull/det) - no closure.
- EtTh/AbsTopIII (qpilot A426 map): real objects largely built; 6 mechanical build gaps (OddThetaNegativeDecay, OddThetaTermAlgebra, AbsoluteKummer{Continuity,Injection,Quotient}, SourceThetaPilotIQContainment); deep class-B = EtTh02 10 inputs + EtTh11 rows 5-7 + Prop5.8(i)(ii)/Cor5.5 algorithm parts.

## 8. Next steps
1. Merge Section 6 declaration lists into coord/E-EXISTING-CLOSURE-MAP.md (mainline).
2. Build the 3 no-olean files to close tree coverage 187 -> 190.
3. GAP 1 (IUTII -> IUTIII): decide interface carrier (e.g. structure indexed by existing SourceLogShellDatum/EtaleThetaKummerClass objects) to replace the paper-layer conditional link.
4. Hull side: keep H5/H7 named layers as in A398/A402 pins; no new math in this mapping task.

Status: mapping only; tree assets not re-verified by checker; GATE NOT PASSED; binding HOLD; pins 14041/23066/18800; no registry edits.