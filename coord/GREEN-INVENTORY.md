# GREEN-INVENTORY — tmp/sheaf/xif/paper green oleans

Snapshot: current `tmp/sheaf/xif/paper` tree.

| metric | value |
|---|---|
| source `.lean` files (recursive) | 17,226 |
| oleans (recursive) | 8,702 |
| green oleans with matching source | **8,525** |
| orphan oleans (no source) | 177 |

NOTE: the task brief cited 16,597 sources / 8,629 oleans; the live tree now has 17,226 / 8,702 (8,525 green), so the numbers below are the live snapshot.

## 1. Green files by theme

| group | count | representative files |
|---|---|---|
| ABC | 141 | _AG_TAUCETI_BelyiAbcProbe<br>_AutoProbe_AbcStatementAlignmentActual<br>_AutoProbe_GenEllP0AbcStatusActual<br>_MainlineABCEquivProbeActual<br>_Mzk1Cor312ToABCConsumerProbe<br>_S3128Cor312ToABCInputAuditProbe |
| Cor312 | 132 | _AutoProbe_Mzk1Cor312ObligationConsumerActual<br>_AutoProbe_Mzk1Cor312TargetWiringActual<br>_Cor312_DownstreamAxiomsProbe<br>_Mzk1TreeCor312ComparisonProbeActual<br>_Mzk1TreeCor312GreenFactsProbeActual<br>_Mzk1TreeCor312RouteAuditProbeActual |
| Theta | 574 | _AutoProbe_AbsTopIII09ThetaHullScalingActual<br>_AutoProbe_GlobalPositiveThetaHullLogVolumeActual<br>_AutoProbe_GlobalThetaPilotLogVolumeActual<br>_AutoProbe_H4HullThetaCertificateActual<br>_AutoProbe_KummerThetaPacketConsumerActual<br>_AutoProbe_KummerThetaPacketDetInverseActual |
| Pilot | 164 | _AutoProbe_GlobalQPilotNormalizedLogVolumeActual<br>ConcretePaperQPilotWitnessActual<br>ConcreteQPilotLogIdentificationActual<br>EtTh04QPilotDataActual<br>GenericQPilotCompletionPowerActual<br>GlobalQPilotNormalizedLogVolumeActual |
| LogVolume | 86 | BaseQLogVolumeActual<br>DeterminantLogVolumeActual<br>Mzk1HolomorphicHullLogVolumeReconciliationActual<br>Mzk1HullLogVolumeFormulaActual<br>Mzk1LocalLogVolumeScalingActual<br>Mzk1LogVolumeAdmissibleActual |
| Hull | 277 | _AbsTopIIIHullBatch2ProbeActual<br>_AbsTopIIIHullProbeActual<br>_AutoProbe_Hull01DefinitionActual<br>_AutoProbe_Hull02ClosureOperatorActual<br>_AutoProbe_Hull03PhiXiActual<br>_AutoProbe_Hull04CertificateWiringActual |
| S3137 | 136 | Mzk1S3137ReadoutBridgeActual<br>S3137AuditPinsRecordActual<br>S3137BatchCProbe<br>S3137BatchDProbe<br>S3137BatchFProbe<br>S3137BatchGProbe |
| Estimate | 39 | ExpEst02ElementaryEstimatesActual<br>GenEll01cHeightMulEstimatesActual<br>Mzk1EstimateInequalitiesActual<br>Mzk1ExplicitEstimatesStatementActual<br>Mzk1HeightEstimateQpilotActual<br>Mzk1LanaIutIVLocalEstimateAuditActual |
| Gap | 198 | _ProbeV2Mzk1IUTIVSec1Sec2GapActual<br>_ProbeV2Mzk1N8RemainingGapsStatementActual<br>_S3134CanonicalQFormulaGapAxiomsProbe<br>C3IQActualPacketGapActual<br>Mzk1ContainerNormalizedGapActual<br>Mzk1CorrectedGap1UnconditionalActual |
| Acceptance | 21 | Mzk1AcceptanceEvidenceBundleActual<br>Mzk1AcceptanceFinalChecksActual<br>Mzk1AcceptanceFinalRewriteActual<br>Mzk1AcceptanceIntegrationActual<br>Mzk1AcceptanceResolvedActual<br>Mzk1AcceptanceWrapUpActual |
| Hqneg | 16 | Mzk1HqnegCleanGateQpilotActual<br>Mzk1HqnegCleanGateShaActual<br>Mzk1HqnegConditionalReductionQpilotActual<br>Mzk1HqnegConditionalReductionShaActual<br>Mzk1HqnegDischargedGateQpilotActual<br>Mzk1HqnegDischargedTCleanGateShaActual |
| LANA | 12 | Mzk1LanaBridgeAuditActual<br>Mzk1LanaBridgeAuditShaActual<br>Mzk1LanaChainGateStatusActual<br>Mzk1LanaChainGateStatusV4Actual<br>Mzk1LanaDependencyHierarchyActual<br>Mzk1LanaMultiradialSpecRefActual |
| Stage | 155 | _S2932_S2934_StageModel_QFTPCAxiomsProbe<br>_Stage4GreenProbe<br>_StageBParamProbe<br>EtTh00Stage0LedgerActual<br>Mzk1IUTIVStage5NumericalActual<br>Mzk1IUTIVStage5NumericalCoreActual |
| Source | 179 | _S3132ConcreteSourceCanonicalProbeActual<br>_S3132ConcreteSourceNormProbeActual<br>_S3132ConcreteSourceVFormProbeActual<br>_SourceChoiceStripMirror<br>APTComparisonFromSource<br>BadPlaceNormalizationSourceActual |
| IUT | 90 | _AutoProbe_IUTExternal10IndexIdsActual<br>_AutoProbe_IUTExternal11CitationRowsActual<br>_AutoProbe_IUTExternal12AssetsMapActual<br>_AutoProbe_IUTExternal20ProofStatusActual<br>_AutoProbe_IUTExternal21ExtAliasesActual<br>_AutoProbe_IUTExternal30PrerequisiteCompletionActual |
| Other | 6305 | _A3LocalGlobalAgent<br>_AbsTopIII07Probe<br>_AbsTopIIIBatchProbe<br>_AG_FLT_AxiomsProbe<br>_AG_FLT_CanonicalDivisorProbe<br>_AG_FLT_CechPromotionProbe |

## 2. Special lists

### ABCTwoEstimates (38)

- `Mzk1ABCTwoEstimatesAuditCorrectionShaActual`
- `Mzk1ABCTwoEstimatesCanonicalCrossCheckProbeShaActual`
- `Mzk1ABCTwoEstimatesCanonicalCrossCheckShaActual`
- `Mzk1ABCTwoEstimatesCleanGateQpilotActual`
- `Mzk1ABCTwoEstimatesComponentsProbeShaActual`
- `Mzk1ABCTwoEstimatesComponentsShaActual`
- `Mzk1ABCTwoEstimatesConditionalShaActual`
- `Mzk1ABCTwoEstimatesEvidenceActual`
- `Mzk1ABCTwoEstimatesEvidenceProbeActual`
- `Mzk1ABCTwoEstimatesGapDecompositionActual`
- `Mzk1ABCTwoEstimatesGapLimitShaActual`
- `Mzk1ABCTwoEstimatesGapShapeAuditShaActual`
- `Mzk1ABCTwoEstimatesGateVerificationShaActual`
- `Mzk1ABCTwoEstimatesHeightLemmasShaActual`
- `Mzk1ABCTwoEstimatesHeightWeightShaActual`
- `Mzk1ABCTwoEstimatesModelQpilotActual`
- `Mzk1ABCTwoEstimatesNumericEvidenceActual`
- `Mzk1ABCTwoEstimatesNumericEvidenceShaActual`
- `Mzk1ABCTwoEstimatesNumericQpilotActual`
- `Mzk1ABCTwoEstimatesRealModelActual`
- `Mzk1ABCTwoEstimatesRealModelGateShaActual`
- `Mzk1ABCTwoEstimatesRealModelShaActual`
- `Mzk1ABCTwoEstimatesReductionInterfaceActual`
- `Mzk1ABCTwoEstimatesReductionQpilotActual`
- `Mzk1ABCTwoEstimatesReductionShaActual`
- `Mzk1ABCTwoEstimatesShaActual`
- `Mzk1ABCTwoEstimatesThinReexportShaActual`
- `Mzk1ABCTwoEstimatesVolumeLemmasShaActual`
- `Mzk1ABCTwoEstimatesWitnessShaActual`
- `Mzk1Stage4ABCTwoEstimatesEvidenceActual`
- `Mzk1Stage4ABCTwoEstimatesWrapupActual`
- `Mzk1StepXIABCTwoEstimatesConsequenceActual`
- `Mzk1StepXIABCTwoEstimatesGapReductionActual`
- `Mzk1StepXIABCTwoEstimatesIntermediateActual`
- `Mzk1StepXIABCTwoEstimatesModelActual`
- `Mzk1StepXIABCTwoEstimatesNormalizationActual`
- `Mzk1StepXIABCTwoEstimatesNumericActual`
- `Mzk1StepXIABCTwoEstimatesReductionActual`

### Cor312 (138)

- `_AutoProbe_Mzk1Cor312ObligationConsumerActual`
- `_AutoProbe_Mzk1Cor312TargetWiringActual`
- `_Cor312_DownstreamAxiomsProbe`
- `_Mzk1Cor312ToABCConsumerProbe`
- `_Mzk1TreeCor312ComparisonProbeActual`
- `_Mzk1TreeCor312GreenFactsProbeActual`
- `_Mzk1TreeCor312RouteAuditProbeActual`
- `_S3128Cor312ToABCInputAuditProbe`
- `_S3136Cor312SupplyInstantiationProbe`
- `Cor312ComparisonRegionV2Actual`
- `Cor312ComparisonRegionV2AdditiveActual`
- `Cor312RegionV2S2586`
- `Mzk1ChainTreeCor312Actual`
- `Mzk1Cor312AcceptanceA618ProofShaActual`
- `Mzk1Cor312AcceptanceAuditMachineActual`
- `Mzk1Cor312AcceptanceDoneActual`
- `Mzk1Cor312AcceptanceFinalActual`
- `Mzk1Cor312AcceptanceFinalAuditShaActual`
- `Mzk1Cor312AcceptanceFinalAxiomPayloadActual`
- `Mzk1Cor312AcceptanceFinalPackageActual`
- `Mzk1Cor312AcceptanceGreenSummaryActual`
- `Mzk1Cor312AcceptanceHqnegCleanGateShaActual`
- `Mzk1Cor312AcceptanceHqnegConditionalShaActual`
- `Mzk1Cor312AcceptanceHqnegGateActual`
- `Mzk1Cor312AcceptanceInterfaceActual`
- `Mzk1Cor312AcceptancePackageActual`
- `Mzk1Cor312AcceptancePackageProbeActual`
- `Mzk1Cor312AcceptancePackageV2Actual`
- `Mzk1Cor312AcceptanceResolvedActual`
- `Mzk1Cor312AcceptanceResolvedConsumerActual`
- `Mzk1Cor312AcceptanceResolvedV2`
- `Mzk1Cor312AcceptanceShapeChecksActual`
- `Mzk1Cor312AcceptanceStrictChainSummaryActual`
- `Mzk1Cor312AcceptanceV2Actual`
- `Mzk1Cor312AcceptanceV4Actual`
- `Mzk1Cor312AcceptanceWrapUpActual`
- `Mzk1Cor312AcceptedFinalActual`
- `Mzk1Cor312ActualReadingBridgeActual`
- `Mzk1Cor312AssemblyBundleActual`
- `Mzk1Cor312AxiomGateActual`
- `Mzk1Cor312AxiomGateExtActual`
- `Mzk1Cor312AxiomGateExtensionActual`
- `Mzk1Cor312BoundsActual`
- `Mzk1Cor312BoundsV2Actual`
- `Mzk1Cor312ChainCertificateActual`
- `Mzk1Cor312FinalAssemblyActual`
- `Mzk1Cor312FinalChecksIndependentActual`
- `Mzk1Cor312FinalChecksV7Actual`
- `Mzk1Cor312FinalConsumerActual`
- `Mzk1Cor312FinalCThetaActual`
- `Mzk1Cor312FinalSelfChecksActual`
- `Mzk1Cor312FinalStatementActual`
- `Mzk1Cor312FromFourTrianglesActual`
- `Mzk1Cor312FullActual`
- `Mzk1Cor312GreenSummaryShaActual`
- `Mzk1Cor312HqnegDischargedActual`
- `Mzk1Cor312NumericalContentActual`
- `Mzk1Cor312ObligationConsumerActual`
- `Mzk1Cor312PaperConsumerActual`
- `Mzk1Cor312PaperInputsActual`
- `Mzk1Cor312PaperLedgerConsumerActual`
- `Mzk1Cor312PaperNonvacuityActual`
- `Mzk1Cor312PaperReadoutConsumerActual`
- `Mzk1Cor312RequirementResolvedActual`
- `Mzk1Cor312RequirementResolvedAxiomGateActual`
- `Mzk1Cor312RequirementSignedChecksActual`
- `Mzk1Cor312ResolvedAcceptanceSlotsActual`
- `Mzk1Cor312ResolvedStrictAcceptanceV3Actual`
- `Mzk1Cor312S3137AssemblyActual`
- `Mzk1Cor312SelfCheckIndependentActual`
- `Mzk1Cor312ShaPaperEquivalenceActual`
- `Mzk1Cor312SignedMagnitudeChecksActual`
- `Mzk1Cor312StatementAuditActual`
- `Mzk1Cor312StrengthAuditActual`
- `Mzk1Cor312StrengthHullUpgradeActual`
- `Mzk1Cor312TargetWiringActual`
- `Mzk1Cor312TargetWiringProbeActual`
- `Mzk1Cor312ToABCConsumerActual`
- `Mzk1Cor312VariantDictionaryChecklistShaActual`
- `Mzk1Cor312VariantStatementAuditShaActual`
- `Mzk1Cor312WiringCertificateConsumerActual`
- `Mzk1GogopexCor312AuditActual`
- `Mzk1PaperCor312StatementActual`
- `Mzk1PriestAmbroseCor312AuditActual`
- `Mzk1SignedCor312ContractActual`
- `Mzk1SignedLogVolumeCor312Actual`
- `Mzk1StepXICor312FullAssemblyActual`
- `Mzk1TreeCor312ClusterConsumer3Actual`
- `Mzk1TreeCor312ClusterConsumer4Actual`
- `Mzk1TreeCor312ClusterRollupActual`
- `Mzk1TreeCor312ComparisonActual`
- `Mzk1TreeCor312ComparisonGreenAllActual`
- `Mzk1TreeCor312ComparisonGreenConsumerActual`
- `Mzk1TreeCor312GreenBundleConsumerActual`
- `Mzk1TreeCor312GreenCertificateActual`
- `Mzk1TreeCor312GreenConsumer5Actual`
- `Mzk1TreeCor312GreenConsumer6Actual`
- `Mzk1TreeCor312GreenConsumer8Actual`
- `Mzk1TreeCor312GreenConsumer9Actual`
- `Mzk1TreeCor312GreenFactsActual`
- `Mzk1TreeCor312GreenFactsConsumer2Actual`
- `Mzk1TreeCor312GreenFactsConsumer3Actual`
- `Mzk1TreeCor312GreenFactsConsumerActual`
- `Mzk1TreeCor312GreenRouteActual`
- `Mzk1TreeCor312ObligationGreenConsumerActual`
- `Mzk1TreeCor312RouteAuditActual`
- `Mzk1TreeCor312RouteObligationJointActual`
- `RefLANACor312ContainerActual`
- `RefLANACor312ProcessionActual`
- `RefLANACor312RationalPlaceActual`
- `S1000FinalCor312AssemblyActual`
- `S1024FinalCor312Actual`
- `S1030FinalConditionalCor312Actual`
- `S2587Cor312PointMapSkeletonActual`
- `S2717Cor312FullTargetActual`
- `S2800LineBundleCor312BridgeActual`
- `S3055PaperCor312Assembly`
- `S3127Cor312StepXIAssemblyActual`
- `S3127Cor312StepXIStageAssemblyActual`
- `S3128ABCCor312AdditiveBoundConsumerActual`
- `S3128Cor312StepXIAssemblyActual`
- `S3128Cor312StepXICombinedConsumerActual`
- `S3128Cor312ToABCHeightBoundConsumerActual`
- `S3128Cor312ToABCInputConsumerActual`
- `S3136PriorArtCor312SuppliesActual`
- `S3136VendorCor312SchemaAdaptedActual`
- `S3182Cor312HullDetAssemblyActual`
- `S620Cor312ContractActual`
- `S634PaperXiFConditionalCor312Actual`
- `S676FinalConditionalCor312Actual`
- `S733CorrectedPaperFinalCor312Actual`
- `S804FinalCor312NonzeroActual`
- `S858PaperGapConditionalCor312Actual`
- `S860GlobalCor312AuditActual`
- `S941PaperCor312FaithfulContractActual`
- `S968FinalTensorInequalityCor312Actual`
- `S994FiniteCarrierCor312Actual`
- `S995FiniteCarrierCor312ConclusionActual`

### IUTToABC (incl. ToABC variants) (8)

- `_Mzk1Cor312ToABCConsumerProbe`
- `_S3128Cor312ToABCInputAuditProbe`
- `Mzk1Cor312ToABCConsumerActual`
- `Mzk1CorrectedGap2ToABCActual`
- `Mzk1V2ToABCTargetActual`
- `S3128Cor312ToABCHeightBoundConsumerActual`
- `S3128Cor312ToABCInputConsumerActual`
- `S3131IUTIVChainToABCActual`

### NonemptyIff (1)

- `Mzk1ABCBridgeNonemptyIffActual`

### Gap1 (51)

- `Mzk1ABCBridgeGap1ConsumerActual`
- `Mzk1ABCBridgeGap1ReexportActual`
- `Mzk1ABCBridgeGap1ScalingConsumerActual`
- `Mzk1CorrectedGap1UnconditionalActual`
- `Mzk1CorrectedGap1UnconditionalQpilotActual`
- `Mzk1CorrectedGap1UnconditionalShaActual`
- `Mzk1CorrectedGap1UnconditionalV2ShaActual`
- `Mzk1CorrectedRegionGap1Actual`
- `Mzk1CorrectedRegionGap1ShaActual`
- `Mzk1Gap1FullRatioScalingElementAuditShaActual`
- `Mzk1Gap1NumericWitnessQpilotActual`
- `Mzk1Gap1ObjectActual`
- `Mzk1Gap1PaperScalingElementActual`
- `Mzk1Gap1ParamAssemblyQpilotActual`
- `Mzk1Gap1ScalingLawTargetActual`
- `Mzk1Gap1ScalingLawTargetAuditShaActual`
- `Mzk1Gap1ScalingLawWiringShaActual`
- `Mzk1Gap1TheoremizationFinalShaActual`
- `Mzk1Gap1TheoremizationQpilotActual`
- `Mzk1Gap1TheoremizationSummaryShaActual`
- `Mzk1Gap1UnconditionalNonnegQpilotActual`
- `Mzk1Gap1WiringQpilotActual`
- `Mzk1Gap1WiringV2ShaActual`
- `Mzk1SelfContainedGap1QpilotActual`
- `Mzk1Stage4CorrectedRegionGap1ConsumerActual`
- `Mzk1Stage4Gap1ScalingLawConsumerActual`
- `Mzk1Stage4Gap1WiringActual`
- `Mzk1Stage4UnconditionalGap1AuditActual`
- `Mzk1StepXICorrectedGap1ParamActual`
- `Mzk1StepXICorrectedGap1UnconditionalActual`
- `Mzk1StepXICorrectedGap1UnconditionalAuditActual`
- `Mzk1StepXICorrectedGap1UnconditionalAuditV3Actual`
- `Mzk1StepXICorrectedGap1UnconditionalV4Actual`
- `Mzk1StepXICorrectedGap1UnconditionalV5Actual`
- `Mzk1StepXICorrectedRegionGap1Actual`
- `Mzk1StepXICorrectedRegionGap1ConditionalActual`
- `Mzk1StepXIGap1FullRatioV2Actual`
- `Mzk1StepXIGap1Gap2AssemblyV2Actual`
- `Mzk1StepXIGap1Gap2AuditV2Actual`
- `Mzk1StepXIGap1Gap2BridgeHeightActual`
- `Mzk1StepXIGap1Gap2InterfaceSummaryActual`
- `Mzk1StepXIGap1MonotonicityActual`
- `Mzk1StepXIGap1ScalingLawV2Actual`
- `Mzk1StepXIGap1TestActual`
- `Mzk1StepXIGap1TheoremizationActual`
- `Mzk1StepXIGap1TheoremizedRatioActual`
- `Mzk1StepXIGap1WiringActual`
- `Mzk1StepXIGap1WiringAuditActual`
- `Mzk1StepXIGap1WiringV2Actual`
- `S2609SignedGap1InputsActual`
- `S2771Gap1ClosedActual`

### Gap2 (46)

- `ABCGap2AxiomsProbeActual`
- `ABCGap2FiniteC3SupplyActual`
- `Mzk1ABCBridgeGap2ConditionalActual`
- `Mzk1ABCBridgeGap2ConsumerActual`
- `Mzk1ABCBridgeGap2NumericActual`
- `Mzk1ABCBridgeGap2WeightRadicalActual`
- `Mzk1ABCEntryGap2QpilotActual`
- `Mzk1CorrectedGap2ABCQpilotActual`
- `Mzk1CorrectedGap2CalibrationActual`
- `Mzk1CorrectedGap2CalibrationShaActual`
- `Mzk1CorrectedGap2ToABCActual`
- `Mzk1Gap2ArithmeticizationShaActual`
- `Mzk1Gap2ArithmeticQpilotActual`
- `Mzk1Gap2ArithmeticReductionActual`
- `Mzk1Gap2ArithmeticReductionAuditShaActual`
- `Mzk1Gap2ArithmeticReductionShaActual`
- `Mzk1Gap2ArithmeticTightnessActual`
- `Mzk1Gap2BadSumNatRadicalActual`
- `Mzk1Gap2NumericWitnessQpilotActual`
- `Mzk1Gap2OneDirectionalTightnessQpilotActual`
- `Mzk1Gap2ShapeABCStrengthQpilotActual`
- `Mzk1Gap2ShapeAuditActual`
- `Mzk1Gap2ShapeDecompositionShaActual`
- `Mzk1Stage4Gap2ArithmeticConsumerActual`
- `Mzk1Stage4Gap2ConsumerActual`
- `Mzk1Stage4Gap2NumericWitnessActual`
- `Mzk1Stage4Gap2ObjectCalibrationActual`
- `Mzk1Stage4Gap2StrengthRelationActual`
- `Mzk1StepXIABCStage5Gap2ConsumerActual`
- `Mzk1StepXICorrectedGap2SemanticsV2Actual`
- `Mzk1StepXICorrectedGap2TightnessV2Actual`
- `Mzk1StepXIGap1Gap2AssemblyV2Actual`
- `Mzk1StepXIGap1Gap2AuditV2Actual`
- `Mzk1StepXIGap1Gap2BridgeHeightActual`
- `Mzk1StepXIGap1Gap2InterfaceSummaryActual`
- `Mzk1StepXIGap2NumericWitnessActual`
- `Mzk1StepXIGap2RealFormActual`
- `S2610SignedGap2ConditionalActual`
- `S2611SignedGap2SourceActual`
- `S2722Gap2AssemblyActual`
- `S2724BallGap2Actual`
- `S3131Gap2AdditiveWiringActual`
- `S3131Gap2ReductionReuseActual`
- `S3132ThetaSideGap2AnchorRecordActual`
- `S3136Gap2AdditiveThetaFormActual`
- `S3136Gap2AdditiveWiringActual`

## 3. Direct support for the ABC chain (curated)

### Conditional two-estimate → ABC core
- `Mzk1ABCTwoEstimatesCanonicalCrossCheckProbeShaActual`
- `Mzk1ABCTwoEstimatesCanonicalCrossCheckShaActual`
- `Mzk1ABCTwoEstimatesCleanGateQpilotActual`
- `Mzk1ABCTwoEstimatesComponentsProbeShaActual`
- `Mzk1ABCTwoEstimatesComponentsShaActual`
- `Mzk1ABCTwoEstimatesConditionalShaActual`
- `Mzk1ABCTwoEstimatesEvidenceActual`
- `Mzk1ABCTwoEstimatesEvidenceProbeActual`
- `Mzk1ABCTwoEstimatesNumericEvidenceActual`
- `Mzk1ABCTwoEstimatesNumericEvidenceShaActual`
- `Mzk1ABCTwoEstimatesReductionInterfaceActual`
- `Mzk1ABCTwoEstimatesShaActual`
- `Mzk1ABCTwoEstimatesWitnessShaActual`
- `Mzk1Stage4ABCTwoEstimatesEvidenceActual`

### Bridge / region / final-boundary consumers
- `Mzk1ABCBridgeGap1ConsumerActual`
- `Mzk1ABCBridgeGap1ReexportActual`
- `Mzk1ABCBridgeGap1ScalingConsumerActual`
- `Mzk1ABCBridgeGap2ConditionalActual`
- `Mzk1ABCBridgeGap2ConsumerActual`
- `Mzk1ABCBridgeGap2NumericActual`
- `Mzk1ABCBridgeGap2WeightRadicalActual`
- `Mzk1ABCBridgeNonemptyIffActual`
- `Mzk1Cor312S3137AssemblyActual`
- `Mzk1FinalBoundarySzpiroActual`
- `Mzk1N3SharedContainerBridgeShaActual`
- `Mzk1PaperComparisonRegionScalingActual`
- `Mzk1PaperRegionGapComponentsShaActual`
- `Mzk1Stage4PaperComparisonRegionScalingDesignActual`

### RETRACTED / vacuous (do NOT count as direct support)
- `Mzk1FinalConditionalABCActual` (RETRACTED)
- `Mzk1FinalConditionalVacuityActual` (RETRACTED)
- `Mzk1StepXIFinalConditionalABCStatusActual` (RETRACTED)

## 4. Reading

- The directly usable ABC-chain greens are the **conditional two-estimate reductions** (HeightEstimate+VolumeEstimate ⇒ ABC) and the **bridge/region consumers** (paperGap/region ⇒ ABC), all conditional on their named estimates.
- `qThetaPilotLogVolumeComparison` / `thetaPilotHullLogVolumeReal` remain the named comparison gap; `Mzk1Cor312S3137AssemblyActual` consumes it as a hypothesis.
- `Mzk1FinalConditionalABC*` and `natRadicalWeightBound*` are RETRACTED/vacuous (hfull unsatisfiable) and are not support.
- No file proves unconditional ABC; the green inventory contains conditional reductions only.


## 5. ABCBridge/Geometry green inventory (live: 122)

Path: `LeanFormal/IUT/ABCBridge/Geometry`; source `.lean` 123, green oleans **122** (task brief said 120; live count is 122).

| theme | count | representative files |
|---|---|---|
| FinitePlace | 75 | FinitePlaceAdicCompletionRingEquiv<br>FinitePlaceArithmeticIQHull<br>FinitePlaceArithmeticIQHullTransport<br>FinitePlaceArithmeticIQHullVolume<br>FinitePlaceArithmeticIQTensor |
| Frey | 26 | FreyConductorOdd<br>FreyConductorTwoAdic<br>FreyDiscriminantRadical<br>FreyLegendreComparison<br>FreyMinimalBaselineCards |
| Legendre | 9 | LegendreJFunctionDivisor<br>LegendreJTwoAdicValuation<br>LegendreLevelTwoStructure<br>LegendreParameterGalois<br>LegendreParameterIsomorphisms |
| TateOggSaito | 1 | TateOggSaitoTwoAdicCards |
| ABC | 2 | ABCModelHeightComparison<br>ABCResidueDiscriminant |
| P1/Quadratic/Rational/Relative | 4 | P1CarrierDesignActual<br>QuadraticTwistArithmetic<br>RationalCommonPrimeFinrank<br>RelativeCompletionFinrankReduction |
| Other | 5 | AdicCompletionChineseRemainder<br>AdicCompletionChineseRemainderAxiomProbe<br>AdicCompletionRingEquivAxiomProbe<br>AdicCompletionValuationUniqueness<br>BoundedDegreeLegendreIsomorphisms |

### 5.1 Theme -> ABC-chain role

- **Frey** (`FreyWeierstrassCurve`, `FreyDiscriminantRadical`, `FreyConductorOdd/TwoAdic`, `FreyOddReduction`, `FreySplitMultiplicativeReduction`, `FreyTwoAdic*`, `FreyTwoTorsion`, `FreySplittingFields`, `FreyTateAnalyticInput`, `FreyTateParameterComparison`): arithmetic/Frey-curve side of the ABC bridge; discriminant=radical, conductor exponents, reduction and Tate-parameter dictionary. **Directly relevant to the ABC arithmetic side** (conditional on the comparison/hull side).
- **Legendre** (`LegendreWeierstrassCurve`, `LegendreJFunctionDivisor`, `LegendreParameter*`, `LegendreLevelTwoStructure`): Legendre parameter/j-invariant model and height comparison inputs.
- **FinitePlace** (local IQ hull/log-shell/tensor/Step-V assembly): *hull/local volume side*; `FinitePlaceIQHullInterface`, `FinitePlaceIQHull*`, `FinitePlaceStepVAssembly`, `FinitePlaceSelectedPrimeWeightedHullVolume`, `FinitePlaceArithmeticIQHullVolume` supply local hull/log-volume and weighted-hull data. **Directly relevant to the hull/3.12 volume side**, not to q/Theta comparison.
- **ABC** (`ABCModelHeightComparison`, `ABCResidueDiscriminant`): height/j-invariant comparison and residue discriminant dictionary; **arithmetic height-side bridge**.
- **TateOggSaito** (`TateOggSaitoTwoAdicCards`): 2-adic Ogg–Saito conductor case data (cards/records; not a standalone theorem).
- **Other** (`P1CarrierDesignActual`, `QuadraticTwistArithmetic`, `RationalCommonPrimeFinrank`, `RelativeCompletionFinrankReduction`): carrier/degree/twist auxiliaries.

### 5.2 Direct ABC-chain support from Geometry

- `ABCModelHeightComparison`
- `ABCResidueDiscriminant`
- `FinitePlaceArithmeticIQHullVolume`
- `FinitePlaceIQHullInterface`
- `FinitePlaceIQHullInterfaceScaledUnit`
- `FinitePlaceIQHullSignedLogVolume`
- `FinitePlaceLogShellDiscrepancy`
- `FinitePlaceSelectedPrimeWeightedHullVolume`
- `FinitePlaceStepVAssembly`
- `FinitePlaceStepVAssemblyAxiomProbe`
- `FreyConductorOdd`
- `FreyConductorTwoAdic`
- `FreyDiscriminantRadical`
- `FreyOddReduction`
- `FreySplitMultiplicativeReduction`
- `FreySplittingFields`
- `FreyTateAnalyticInput`
- `FreyTateParameterComparison`
- `FreyTwoAdicMinimalityCriterion`
- `FreyTwoAdicMinimalReduction`
- `FreyTwoTorsion`
- `FreyWeierstrassCurve`
- `LegendreJFunctionDivisor`
- `LegendreLevelTwoStructure`
- `LegendreParameterGalois`
- `LegendreParameterIsomorphisms`
- `LegendreParameterSymmetry`
- `LegendreWeierstrassCurve`

### 5.3 Not evidence

- `*AxiomProbe*` / `*Cards*` / `*Batch*` files are probes/records; they compile but are not mathematical support.
- Geometry greens supply the arithmetic/hull **inputs**; they do not prove `qThetaPilotLogVolumeComparison`, the paper carrier realization, or unconditional ABC.
- The overall ABC-chain status is unchanged: conditional reductions only; the q/Theta comparison and exact hull upper bound remain the named gaps.
