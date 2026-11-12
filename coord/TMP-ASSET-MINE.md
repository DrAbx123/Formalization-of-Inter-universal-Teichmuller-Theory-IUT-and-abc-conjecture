# A480-B: tmp / uncovered 资产挖掘（file:decl → 可对应前置对象 → 消费者建议）

来源: coord/repo-route-index-data.json（897 行, uncovered=671）。规则: 只列已存在文件（citable=OLEAN_FRESH/NO_RESULTS_LINE/EXIT1/STALE_NO_SOURCE/OLEAN_MISSING），不复制、不 adapted；消费者建议均为“组合已编译 tree 资产”类，禁止簿记/占位。

## 1. 统计（一行）

- uncovered 671 个: source={"LeanFormal":37,"tmp":634}
- category={"route":155,"candidate":25,"obligation":8,"gap":72,"paper-layer":325,"attempt":84,"alternative":2}
- citable={"OLEAN_FRESH":29,"OLEAN_MISSING":8,"EXIT0 (citable evidence)":140,"NO_RESULTS_LINE":483,"EXIT1":11}（OLEAN_FRESH 即可直接复用为前置资产的候选）
- tags 非 unmapped 的 uncovered: 265 个（语义相关，优先挖）。

## 2. 高价值 uncovered（按 citable/语义排序，前 150）

| file | decls | citable | 可对应前置对象 | 消费者建议 |
|---|---|---|---|---|
| LeanFormal/IUT/Foundations/Geometry/ConvexHullVertexSupReduction.lean | iSup_ofReal_le_iSup_vertices_of_subset_convexHull, convexHull_iSup_ofReal_eq_iSup_vertices | OLEAN_FRESH | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceRouteDeterminantNormalization.lean | Label, Choice, Step | OLEAN_FRESH | IUT III Cor 3.12 / StepXI 前置对象 | 组合 tree Contract/Routes/Comparison（或 HullDet/Volume）写 route/hull consumer |
| LeanFormal/IUT/IUTIII/Theorem311/ConcreteRouteUniqueness.lean | Label, Choice, Step | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean | generatedQuotientMap_eq_of_ind1Step, Ind1Setoid, ind1QuotientMap | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean | Ind2AlienLink, linkMap_ind1Step, linkMap_ind2Step | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmGeneralRouteNormalForm.lean | and, horizontalSteps_idempotent, horizontalSteps_isHorizontal | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean | applyRoute_ind1_commute, applyRoute_ind2_commute, applyRoute_ind1_commute_logVolume | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/ParametricRouteAlgebra.lean | horizontal_generated, horizontal_quotient_eq, horizontal_profile_eq | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteRouteNaturality.lean | Label, Choice, Step | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Theorem311/SourceTheorem311ReferenceContract.lean | SourceTheorem311ReferenceOutput, assemble, output_recovered | OLEAN_FRESH | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportObligations.lean | that, toLink, SourceEvaluationLegUpgrade | OLEAN_FRESH | IUT III Cor 3.12 / StepXI 前置对象 | 组合 tree Contract/Routes/Comparison（或 HullDet/Volume）写 route/hull consumer |
| LeanFormal/IUT/ABCBridge/Geometry/FreyOddReduction.lean | freyPadicIntegralModel, freyPadicCurve, freyPadicIntegralModel_eq_int_map | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/ABCBridge/Geometry/FreySplitMultiplicativeReduction.lean | FreyResidueField, freyResidue_prime_eq_zero, freyResidue_charP | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/ABCBridge/Geometry/FreyTwoAdicMinimalReduction.lean | freyTwoAdicHalvingChange, freyTwoAdicHalvingModel, freyTwoAdicHalvingModel_a | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/Audit/Diagnostics/LegacyContracts.lean | Side, Copy, PrimeStrip | OLEAN_FRESH | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| LeanFormal/IUT/Foundations/Analysis/SourceContractionRadius.lean | sourceContractionRadius_nonneg, norm_le_sourceContractionRadius, sourceContractionRadius_lt_one | OLEAN_FRESH | GenEll/EtTh source realization 前置 | 组合 GenEll/EtTh consumer 链写 realization consumer |
| LeanFormal/IUT/Foundations/Geometry/GenericNodalReduction.lean | NodalReductionEquation, residueCurve, nodalCurve | OLEAN_FRESH | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| LeanFormal/IUT/Foundations/Geometry/LocalReduction.lean | HasGoodReductionOnMinimalModel, HasMultiplicativeReductionOnMinimalModel, HasSplitMultiplicativeReductionOnMinimalModel | OLEAN_FRESH | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| LeanFormal/IUT/Foundations/Geometry/ReductionBaseChange.lean | isIntegral_map_of_commutes, splitReductionPolynomial_map, integralModel_map_eq_of_commutes | OLEAN_FRESH | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| LeanFormal/IUT/Foundations/Geometry/TateCurveLocalReduction.lean | ResidueField, integralCurve_c4_cast, integralCurve_c6_cast | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/Foundations/Geometry/TateStableReductionBoundary.lean | StableResidueField, CanonicalStableReductionBoundary, canonicalStableReductionBoundary | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/Foundations/Geometry/TateUniformizationContract.lean | tateParameterUnit_ne_one, tateParameterUnit_algEquiv_map, tateParameterDeckSubgroup_algEquiv_map | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/Foundations/Geometry/TateUniformizationPointMapReduction.lean | tatePairCoordinatesSeparateOrbits, tateCoordinatesCoverNonzeroPoints, tateQuotientPoint_injective_iff_pairCoordinatesSeparateOrbits | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/Foundations/PAdicAnalytic/TateContraction.lean | tateBall, exists_tateHRemainder_fixed, exists_tateH_eq_t | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/Foundations/PAdicAnalytic/TateContractionGeneral.lean | tateMapGeneral_mapsTo_closedBall, tateMapGeneral_contracting_on_ball, tateMapGeneralOnBall_lipschitz | OLEAN_FRESH | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| LeanFormal/IUT/IUTI/InitialTheta/ReductionPlacePartition.lean | goodReductionPlaces, multiplicativeReductionPlaces, stableReductionPlaces | OLEAN_FRESH | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| LeanFormal/IUT/IUTI/InitialTheta/SplitReductionInput.lean | InitialThetaSplitReductionInput, splitReduction_spec, stableReduction | OLEAN_FRESH | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| LeanFormal/IUT/IUTII/Frobenioid/Example36LocalContraction.lean | deltaAdd_inv_contraction, deltaAdd_div, localContractionRel | OLEAN_FRESH | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiStableReductionFinalConsumer.lean | SourcePsiActualReductionTypeConsumerData, sourcePsiActualReductionTypeConsumerData, SourcePsiActualReductionTypeConsumer_trichotomy | OLEAN_MISSING | GenEll/EtTh source realization 前置 | 组合 GenEll/EtTh consumer 链写 realization consumer |
| LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31D2Candidate.lean | arithmetic, output, arithmetic_recovery | OLEAN_FRESH | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/_Mzk1GeomCoreFiniteMapRouteProbeActual.lean |  | EXIT0 (citable evidence) | [Mzk1] Thm 2.5 / GeometricCore / RR 前置 | 组合 Mzk1* paper consumer 或 RR tree 资产写 GeomCore/RR consumer |
| tmp/_S3134NativeContractShrinkAxiomsProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/_S3136Cor312SupplyInstantiationProbe.lean |  | EXIT0 (citable evidence) | IUT III Cor 3.12 / StepXI 前置对象 | 组合 tree Contract/Routes/Comparison（或 HullDet/Volume）写 route/hull consumer |
| tmp/_S3136PaperInputBatchProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/_S3139ModelRouteProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/_S3139RouteBatch2Probe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/_S3139RouteBatchProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/ConcretePaperSignedHullActual.lean | concretePaperSignedHull_procession_eq, concretePaperSignedHull_eq_actualSignedHull, concretePaperSignedHull_hull_logVolume_eq | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/GlobalHullPaperXiFActual.lean | paperQParameter, paperQParameter_pos, log_paperQParameter | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/GlobalPositiveHullPaperXiFActual.lean | log_positiveGlobalPaperQParameter, paperSignedLog_positiveGlobalPaperQParameter, paperXiF_globalPositiveHull_iff | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/Mzk1GeomCoreFiniteMapRouteActual.lean | finiteMapData_of_construction, preciseWitness_of_route, recast_of_route | EXIT0 (citable evidence) | [Mzk1] Thm 2.5 / GeometricCore / RR 前置 | 组合 Mzk1* paper consumer 或 RR tree 资产写 GeomCore/RR consumer |
| tmp/PaperC3RootThetaHullActual.lean | primitiveMu2lRoot_zeta_ne_zero, paperRootThetaHull_mem, RootThetaHullLogComparison | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperC3SourceQHullRelationActual.lean | qParameterUnitLambdaHull_subset_sourceQHullInPaperBlock, genericQPilotImagePoint_mem_sourceQHullInPaperBlock, SourceQHullTransportGap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperC3TensorHaarHullActual.lean | paperC3TensorPlaces, paperC3TensorTuple, paperC3TensorBlock | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperFinalLValuedThetaIndHullActual.lean | Carrier, rootThetaImage_subset_indUnion, ind1Image_subset_indUnion | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullActual.lean | paperLambdaOScaledRegion_eq, paperLambdaOCandidates, paperQParameterImageSet_subset_lambdaOHull | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullEqualityActual.lean | paperQParameterImagePoint_zero, candidate_contains_unitReference, paperLambdaOHull_eq_unitReference | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullHaarActual.lean | lambdaOPlaces, lambdaOTuple, paperLambdaOScaledRegion_eq_smul | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullNonzeroLabelsActual.lean | paperLambdaOScaledRegion_eq_smul, paperQParameterNonzeroImageSet, paperQParameterNonzeroImageSet_subset_possibleImage | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullQVFamilyActual.lean | qParameterUnitLambda_mem_nonzeroCandidates, paperNonzeroLambdaOHull_subset_qUnitLambdaHull, qParameterUnitScaledImagePoint_one_eq | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullReverseReductionActual.lean | unitReference_subset_lambdaOHull_iff_forall_candidate | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperLambdaOHullWitnessActual.lean | paperUnitReference_mem_lambdaOCandidates, paperLambdaOHull_subset_unitReference, PaperLambdaOHullEqualsUnitReference | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperQZeroLimitConsumerActual.lean | PaperQZeroLimitData, paperQZeroLimitData_support_mem_iff, paperQZeroLimitData_support_eq_thetaCoeffAt | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/PaperRootExtensionThetaHullActual.lean | rootExtensionProductThetaHull, rootExtensionProductThetaHullLog_eq_zero, rootExtensionProductThetaHull_measure_pos_lt_top | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperRootExtensionThetaHullAuditActual.lean | rootExtensionProductImageHull, rootImageRadius_ge, rootExtensionProductThetaImageSet_subset_imageHull | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperRootExtensionThetaHullScalingActual.lean | IsCoordinatewiseScaledHull, rootExtensionProductImageHull_is_scaledHull, rootExtensionProductImageHull_subset_scaledHull | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperSignedHullNormalizationActual.lean | PaperSignedHullNormalizationObstruction, signedRealHaarIdentity_of_unitFactor_noUnit, signedHnormal_of_unitFactor_noUnit | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperSignedHullSignedActual.lean | PaperC6Carrier, c3ThetaSignedProcession_weights_nonnegative, c3ThetaSignedProcession_average_eq_neg | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperTheta311DataActual.lean | PaperTheta311ThetaData, paperTheta311ThetaData_q0_value, paperTheta311ThetaData_coeffAt_support | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| tmp/PaperThetaCoeffConsumerActual.lean | PaperThetaCoeffData | EXIT0 (citable evidence) | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/PaperThetaHullThenAverageActual.lean | PaperHullThenAverageData, paperHullThenAverage_eq, PaperHullBeforeAverageRequired | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperThetaHullUnitInflationActual.lean | one_mem_paperLabelHull, PaperProductHullContainsIdentity, paperProductHullContainsIdentity_holds | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperThetaInitialThetaConsumerActual.lean | InitialThetaCoeffData, InitialThetaQZeroData | EXIT0 (citable evidence) | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/PaperThetaLinkConsumerActual.lean | actualPaperThetaLinkData_ipl_projection, actualPaperThetaLinkData_kummerEvaluation_projection, actualPaperThetaLinkData_ipl_factorization_consumer | EXIT1 | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/PaperThetaLinkDataConsumerActual.lean | selfPaperThetaLinkData_ipl_projection, selfPaperThetaLinkData_kummerEvaluation_projection, selfPaperThetaLinkData_inputLink_projection | NO_RESULTS_LINE | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/PaperThetaPilotHullOnGlobalIQActual.lean | hullC3, GlobalIQImageCarrier, GlobalIQHullBlock | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/PaperThetaPilotHullOnGlobalIQNormalizedActual.lean | QSidePossibleImageCarrier, qSidePossibleImageSet, QSideToGlobalIQTransport | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S1076RootStackPaperThetaHullMeasureActual.lean | s1076Hull_eq_image, S1076HullCompact, s1076Hull_measure_lt_top_of_compact | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S1311PaperInd1PermutationLiftActual.lean | sourcePermutationIndex, sourcePermutationIndex_injective, sourcePermutationCapsuleLift_nonempty_iff | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2） | 组合 Ind*/K1K2 tree 资产写 quotient/boundary/closure consumer |
| tmp/S2692Paper312SignedHullAuditActual.lean | S2692QPilotScalar_eq, S2692QPilotScalar_eq_sourceBadQAbsLog, S2692SignedHullDataMissing | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3055PaperCor312Assembly.lean | S3055_paperCor312Full_of_q_bridge | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象 | 组合 tree Contract/Routes/Comparison（或 HullDet/Volume）写 route/hull consumer |
| tmp/S3127FreeQuotientPaperInputConsumerActual.lean | S3127FreeQuotientPaperInputData, S3127FreeQuotientPaperInputData_universal, S3127FreeQuotientExists_of_paperInputData | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3127FreeQuotientPaperStatementActual.lean | S3127G2PaperStatement, S3127G2PaperStatement_holds, S3127FreeQuotientExists_of_paperInput_via_data | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3128Stage1PaperRootHullConsumerActual.lean | S3128Stage1PaperRootHullLog_eq_formula, S3128Stage1PaperRootHullScalar_eq_formula | EXIT1 | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullAugmentedConsumerActual.lean | S3128Stage1PaperSHull_augmentedHull_empty_subset, S3128Stage1PaperSHull_augmentedHull_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullClosedConsumerActual.lean | S3128Stage1PaperSHull_isClosed, S3128Stage1PaperSHull_closure_minimal, S3128Stage1PaperSHull_closure_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullClosureThetaConsumerActual.lean | S3128Stage1PaperSHull_closureTheta_subset | EXIT1 | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullConsumerActual.lean | S3128Stage1PaperSHull_modelHull_subset, S3128Stage1PaperSHull_theta_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullDownstreamConsumerActual.lean | S3128Stage1PaperSHullDownstream_modelHull_subset, S3128Stage1PaperSHullDownstream_theta_subset, S3128Stage1PaperSHullDownstream_union_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullEmptyIndConsumerActual.lean | S3128Stage1PaperSHull_empty_ind, S3128Stage1PaperSHull_empty_ind_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullIndImageConsumerActual.lean | S3128Stage1PaperSHullIndImage_indImage_subset, S3128Stage1PaperSHullIndImage_union_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullLeastLambdaOConsumerActual.lean | S3128Stage1PaperSHullLeastLambdaO_subset | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullMonoConsumerActual.lean | S3128Stage1PaperSHull_eq_closure, S3128Stage1PaperSHull_mono | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3128Stage1PaperSHullQPilotConsumerActual.lean | S3128Stage1PaperSHullQPilot_qPilot_subset, S3128Stage1PaperSHullQPilot_qPilot_subset_modelHull | EXIT1 | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3130PaperSignedHullFiniteActual.lean | BatchAQualifiedInput, H_C_set, H_C | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3131ModelRoutePriorArtReuseActual.lean | S3131ModelRoutePriorArtReuse, S3131ModelRoutePriorArtReuse_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131ModelRouteReopenNotePreparedActual.lean | S3131ModelRouteReopenNotePrepared, S3131ModelRouteReopenScope, S3131ModelRouteReopenScope_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperNormalizedComparisonActual.lean | S3131PaperHullReadout_eq_LocalHullReadout, S3131PaperQ_le_PaperHull, S3131PaperRegionalHull_eq_RegionalHC | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperQFormulaE1Actual.lean | S3131PaperRootCoefficient_eq_rootHalf_of_e_one, S3131PaperQFormula_iff_scalingData | EXIT1 | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteAssemblyActual.lean | paperRouteResidualData_of_families | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteBatchProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteComparisonDataActual.lean | S3131PaperRouteComparisonData, qSigned_neg, qSigned_le_theta | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteDependencyDataActual.lean | S3131PaperRouteDependencyMap, S3131PaperRouteDependencyMap_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteInterfaceMapActual.lean | S3131PaperRouteInterfaceMap, S3131PaperRouteInterfaceMap_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteProvableSeparationActual.lean | S3131PaperRouteProvableNow, S3131PaperRouteRemainingStrength, S3131PaperRouteProvableNow_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteResidualLedgerActual.lean | S3131PaperRouteResiduals, S3131PaperRouteResiduals_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteStatusDataActual.lean | S3131PaperRouteFieldStatus, S3131PaperRouteFieldStatus_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteThetaStatusActual.lean | S3131PaperRouteThetaStatus, S3131PaperRouteThetaStatus_length | EXIT0 (citable evidence) | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/S3131PaperRouteV2RegionReuseActual.lean | S3131V2ComparisonRegion, S3131V2RegionMembershipCondition | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteVendorBridgeLinkActual.lean | abc_of_families_and_vendorPayload | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131PaperRouteVendorWiringActual.lean | comparisonDataOf, comparisonDataOf_magnitude | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131R2ReductionActual.lean | S3131Nu_qVFamNormalizedGenerator_eq_exponent, S3131QVFamTensorP_eq_natGenerator, S3131RationalPlaceAbsNormMissing | EXIT1 | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131R2ReductionV2Actual.lean | S3131Nu_qVFamNormalizedGenerator_eq_exponent, S3131QVFamTensorP_eq_natGenerator, S3131RationalPlaceAbsNormMissing | EXIT1 | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RootSupplyToolProbeActual.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RouteBatch4Probe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RouteDependencyMapV2Actual.lean | S3131RouteDependencyMapV2, S3131RouteDependencyMapV2_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RouteFirstTriangleWiringActual.lean | S3131RouteFirstTriangleWiring, S3131RouteFirstTriangleWiring_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RouteInvarianceImplementedActual.lean | S3131RouteInvarianceImplemented, S3131RouteInvarianceImplemented_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RoutePayloadLGPWiringActual.lean | abc_of_families_and_LGPPayload | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3131RouteRegionConsumptionMapActual.lean | S3131RouteRegionConsumptionMap, S3131RouteRegionConsumptionMap_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3132PaperHullSetPropertiesActual.lean | actualHolomorphicHull_eq_self_of_candidate, actualHolomorphicHull_least, actualHolomorphicHull_paper_properties | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置 | 组合 HullDet/Volume/CardHull tree 资产写 hull-average/det consumer |
| tmp/S3132PaperIQCarrierIdentificationActual.lean | actualC3TensorRegion_subset_IQCarrier, literalIQUnitRegion_subset_arithmeticIQCarrier | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3132SharperThetaTargetReductionActual.lean | MissingVFormCanonicalIdentification, MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm, canonicalTarget_iff_factor_zero_of_VForm | EXIT0 (citable evidence) | initial theta / theta 前缀对象 | 组合 Theta tree 资产（oddTheta/Gaussian/SignedLabel）写 theta value/chain consumer |
| tmp/S3133M2BaseQReductionActual.lean | S3133GaussianArithmetic_F_eq_Fmod, S3133GaussianQParameterMatchAtBase_defining, S3133GaussianQParameterMatchAtBase_of_baseQIdentification | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3133ModelRouteEvidenceRecordActual.lean | S3133ModelRouteEvidenceIds, S3133ModelRouteEvidenceStatus, S3133ModelRouteEvidenceStatus_holds | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3133ModelRouteF4StatusActual.lean | S3133ModelRouteF4a, S3133ModelRouteF4bStatus | NO_RESULTS_LINE | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3133QPilotPaperMissingActual.lean | MissingRealifiedGlobalFrobenioidPresentation, MissingRealifiedGlobalFrobenioidPresentationData, qPilotTimesMuCandidate_toFPrimeStrip | EXIT0 (citable evidence) | ABC bridge: frontier/Frey/Tate/q-pilot 前置 | 组合 ABCBridge tree 资产写 frontier/height/q 形式 consumer |
| tmp/S3134NativeContractShrinkActual.lean | S3134NativeBadPlaces_eq_bad, S3134NativeStableReduction, S3134NativeStableReduction_proved | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135F5ActualReductionActual.lean | S3135ActualUnitHullCard, S3135ActualPointWeightCard, s3135_actualFrontierRegionClause_of_cards | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135ModelRouteDocsActual.lean | s3135ModelRouteOptionBEvidence | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135RouteBatch10ProbeActual.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135RouteBatch8ProbeActual.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135RouteBatch9ProbeActual.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135RouteFunctionLayerDocsActual.lean | s3135RouteFunctionLayerMap | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135Task56RouteRecordActual.lean | s3135Task56RouteRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3135Task72SkeletonProbeActual.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3136CardAMPLSupplyReuseActual.lean | lgpCardAMPL_realVolume_le, lgpCardAMPL_of_realVolume_le, lgpCardAMPL_nonempty_iff | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3136GenEllPaperStatementsActual.lean | LGPGenEllStatementRow, lgpGenEllStatements, lgpGenEllStatements_length | EXIT0 (citable evidence) | GenEll/EtTh source realization 前置 | 组合 GenEll/EtTh consumer 链写 realization consumer |
| tmp/S3136GenEllReductionShapeActual.lean | LGPGenEllEquivalence, lgpGenEll_reduction, lgpGenEll_immediate | EXIT0 (citable evidence) | GenEll/EtTh source realization 前置 | 组合 GenEll/EtTh consumer 链写 realization consumer |
| tmp/S3136ModelReductionClauseProviderActual.lean | lgpModelReductionClauseProvider_partition | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3136PaperInputIndexActual.lean | LGPInputArtifactRow, lgpPaperInputIndex, lgpPaperInputIndex_length | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3136PaperInputStatementHooksActual.lean | LGPTheoremAShape, LGPGenEllGeneralShape, LGPGenEllCompactlyBoundedShape | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137FromScratchModelSupplyActual.lean | fromScratchIndexEquiv, BadSelfTensorIndexDonor, badSelfTensorIndexDonor | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137FromScratchModelSupplyProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137ModelOriginalInputSkeletonActual.lean | modelULiftEquiv, modelOriginalInput_theaterAt, S3137ModelOriginalInputRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137ModelRouteCompositionIndexActual.lean | S3137ModelRouteCompositionDecls, S3137ModelRouteCompositionDecls_length, S3137ModelRouteCompositionRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137ModelRouteIdsNoteActual.lean | S3137ModelRouteIds, S3137ModelRouteIds_length, S3137ModelRouteIdsRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137ModelSkeletonSupplyActual.lean | ModelIndex, modelIndexEquiv, modelPermutation | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137ModelSkeletonSupplyProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137ModelTheaterSkeletonActual.lean | ModelIndex, ModelTheaterData, ModelTheaterData.toFamily | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137PaperLevelFocusMapActual.lean | S3137PaperLevelFocusMap, S3137PaperLevelFocusMap_length, S3137PaperLevelFocusMapRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137PaperRouteComparisonDataActual.lean | S3137Corollary312ComparisonData, S3137Corollary312ComparisonData.ofQTheta, S3137Corollary312ComparisonData.ofQTheta_signed | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137PaperRouteFieldCActual.lean | paperRouteComparisonRegion, paperRouteThetaBound, paperRouteRegionVolumeWeightShape | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137PaperRouteMapProbe.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137RouteBridgeStatusActual.lean | S3137RouteBridgeStatus, S3137RouteBridgeStatus_length, S3137RouteBridgeStatusRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3137StepxiRouteIdsNoteActual.lean | S3137StepxiRouteIds, S3137StepxiRouteBatchRecord | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3139C3RouteIntegrationSummaryActual.lean |  | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3139FirstTriangleRouteCompositionActual.lean | FirstTriangleRouteResidual, firstTriangleRouteComposition | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3139FirstTriangleRouteConclusionActual.lean | firstTriangleRouteConclusion | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |
| tmp/S3139RouteCapsuleLabelResidualActual.lean | SourceCapsuleLabelLinkResidual, firstTriangleRouteComposition_with_capsuleLabel | EXIT0 (citable evidence) | unmapped（需人工归档） | 人工判定：无对应前置对象则归档，不造 adapted 副本 |

## 3. 其余 uncovered（全量压缩清单: file | category | citable | 前置对象）

- tmp/S3139RouteComparisonInvarianceActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteComparisonInvarianceConsumerActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteEndgameChecklistV2Actual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteEndgameIdsActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteFinalCompositionHardenedActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteFinalResidualActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteIdsUpdate4Actual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteIntegrationChecklistUpdatedActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteRegistryIdsActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteResidualMainlineM0NamedActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteResidualNamedActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteResidualQpilotNamedActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteResidualUpdateV3Actual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3139RouteResidualUpdateV4Actual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3146PaperRouteFieldCAuditActual.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3146RouteGreenAuditActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3146RouteResidualNamingAuditActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3150ModelRouteAuditCriteriaActual.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3161PaperLevelAuditSupportPlanActual.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3198PaperConditionedWiringAuditActual.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S523EtThReductionSelectorActual.lean | route | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S616FinalCor312ContractActual.lean | route | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S620Cor312ContractActual.lean | route | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S634PaperXiFConditionalCor312Actual.lean | paper-layer | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S645RootNormalizedPaperSignedHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S646PaperRootHullComparisonActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S650ActualSignedCor312Contract.lean | route | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S658RootNormalizedPaperSignedHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S660RootPaperSignedHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S665PaperSignedHullXiFInterfaceActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S716PaperThetaHullLogSourceAuditActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S721ActualHullToPaperSignedHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S725PaperHullCorrectedSourceLinkActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S729PaperSignedHullActualHullLogActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S733CorrectedPaperFinalCor312Actual.lean | paper-layer | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S739PaperOrderThetaHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S743PaperSignedHullPaperOrderActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S745PaperRootHullNonzeroCorrectionActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S785PaperOrderThetaHullBypassActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S792RootStackPaperHullRebaseActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S793PaperLeastLambdaOHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S797PaperHullFirstAuditActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S801PaperHullLogActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S809PaperLeastHullRootStackBridgeActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S810LeastHullPaperCarrierActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S814PaperHullLogInterfaceActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S814SkeletonQuantizedLeastHullActual.lean | route | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S904PaperCor312ScalingActual.lean | paper-layer | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S909PaperSVsLeastHullActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S911PaperQPilotHullCorollaryActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S922ModelHullPaperSHullInequalityActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S929RQpilotPaperSHullFinalActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S941PaperCor312FaithfulContractActual.lean | paper-layer | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S944PaperSHullFiniteActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S998FinitePaperHullFinitenessActual.lean | paper-layer | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/_S3136CObligationWiringProbe.lean | obligation | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/_S3136OldAttemptMiningProbe.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/EtaleThetaHalfIntEmbeddingApplyConsumerActual.lean | gap | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperIQHullLogVolumeInterfaceCandidateActual.lean | candidate | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置
- tmp/PaperRootThetaHullCarrierGapActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S1174StageToLocalGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1205StageToLocalConcreteGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1209ConcreteStagePlaceGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2719HullCoverGapActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S3070HullNativeMagnitudeBoundAttempt.lean | attempt | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S3101C3NativeIndexMeasureAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3106DonorWithNativeIndexAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3107MultiPrimeDonorAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3108AdjoinRootSetAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3108PerPrimeDonor5Attempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3108PMapEqAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3109BaseQDescentAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3110BaseQNormDescentAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3113ConcreteDonorAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3114DonorFromTAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3114TprimeAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3116BKBTInhabitantAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3117AlgC3Attempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3117GlobalThetaHullAlgAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3118ActualTCandidateAudit.lean | candidate | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3119GeometricCorePrefixAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3119NegInvolutionAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3119UniqueInvolutionAttempt.lean | attempt | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/S3121DiagramAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3123CoreCFQuotientAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128AverageAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128AwayActionAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128AwayActionHomAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128AwayEquivAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128AwayRingEquivAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128BasicOpenLocalizationAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128BasicOpenLocalizationSurjAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128SpecAutNaturalAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3128Stage1ModelHullGapConsumerActual.lean | gap | EXIT1 | IUT III holomorphic hull / H5-H7 前置
- tmp/S3128Stage1PaperSGapLeastActual.lean | gap | EXIT1 | unmapped（需人工归档）
- tmp/S3128Stage1PaperSVsGapConsumerActual.lean | gap | EXIT1 | unmapped（需人工归档）
- tmp/S3128Stage1PaperSVsGapPointConsumerActual.lean | gap | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3128SurjHa0Attempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3129CoverSchemeFiniteEtaleAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3129FiniteEtaleCompositionAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3129RepresentableFiniteEtaleAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3131CardAMPLInstantiationAttemptActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3131CoefficientGapActual.lean | gap | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3131HunitInstantiationAttemptActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3131OldAttemptsMiningActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3131PaperRouteFieldObligationsActual.lean | obligation | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3131RegionRelativeInstantiationAttemptActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3131SourceImageHullVolumeAttemptActual.lean | attempt | EXIT0 (citable evidence) | IUT III holomorphic hull / H5-H7 前置
- tmp/S3131SourceQSideInstantiationAttemptActual.lean | attempt | EXIT0 (citable evidence) | GenEll/EtTh source realization 前置
- tmp/S3132ThetaSideGap2AnchorRecordActual.lean | gap | EXIT0 (citable evidence) | initial theta / theta 前缀对象
- tmp/S3133QPilotFTimesMuCandidateActual.lean | candidate | EXIT0 (citable evidence) | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S3135FinalAssemblyGateV4CandidateActual.lean | candidate | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136AbcJointCObligationStatusActual.lean | obligation | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136CarrierBridgeAttemptActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136FiberHostGapActual.lean | gap | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136Gap2AdditiveThetaFormActual.lean | gap | EXIT1 | initial theta / theta 前缀对象
- tmp/S3136LGPLocalFractionalIdealCandidate.lean | candidate | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136OldAttemptHonestyAuditActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136RegionCObligationStatusActual.lean | obligation | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136SourceUnitRegionInstantiationAttemptActual.lean | attempt | EXIT0 (citable evidence) | GenEll/EtTh source realization 前置
- tmp/S3136ThetaConstantIdentificationAttemptActual.lean | attempt | EXIT0 (citable evidence) | initial theta / theta 前缀对象
- tmp/S3136UnitRegionInterfaceCandidateActual.lean | candidate | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3136VendorScaffoldObligationAdaptedActual.lean | obligation | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3152GapsListActual.lean | gap | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S3162PaperLevelGapMapActual.lean | gap | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S517EtThSpecialTwoTorsionGapActual.lean | gap | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S640RootHullGapComparisonActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S653RootThetaTensorHullCarrierGapActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S719PaperRootHullGapDecompositionActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S726PaperHullVsS663GapActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S806PaperRootHullNonzeroGapsActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- tmp/S858PaperGapConditionalCor312Actual.lean | gap | NO_RESULTS_LINE | IUT III Cor 3.12 / StepXI 前置对象
- tmp/S875PaperGapHullLogActual.lean | gap | NO_RESULTS_LINE | IUT III holomorphic hull / H5-H7 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiActualMinimalModelReduction.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiCorrectedReductionSpecialFiber.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiIntegralModelReduction.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiReductionActualConstruct.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiReductionTypeActual.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiStableReductionFinal.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiStableReductionFromSource.lean | route | OLEAN_MISSING | GenEll/EtTh source realization 前置
- tmp/_FinalPaperXiFProbe.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_paper312_axioms.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_PaperTargetProbe.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_S1779RouteProbe.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_S2038PaperOActualWIP.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_S2038PaperOActualWIP2.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_S2038PaperOActualWIP3.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/_S2814_PaperQZeroAxiomsProbe.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/_S3271ReductionProbe.lean | route | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/_SHEFourthJoint_PaperQZeroAxiomsProbe.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/ActualPaperThetaLinkActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/AssemblyKummerIndThetaPaperBridgeActual.lean | paper-layer | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/BadPlaceHalfRootSupplyActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/BadPlacePaperConstantsActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/BadPlacePaperNormalizedActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/BadPlacePaperNormalizedComparisonActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/BadPlacePaperRootComparisonActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/BadPlacePaperTargetStrictActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/BaseQContractionUnconditional.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/ConcretePaperQPilotWitnessActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/ConcretePaperUnconditionalDataActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/ConcretePaperUnconditionalDataUnconditionalActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/ConcretePaperXiFInclusionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/NativeGlobalQPilotVsPaperThetaPilotActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/NativeSplitReductionProof.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/OrigXiFPaperQPilotComponentsActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperAC3IndexTransportActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperACompletionThetaCarrierActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperAPureCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperBadPlaceProductCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperBadPlaceTensorGeometryActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperC3KummerExtensionActual.lean | paper-layer | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/PaperC3PrimitiveMu2lRootActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperC3QPilotLogComparisonActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperC3SourceDataActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperC3SourceDataQConsistencyActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperC3SourceDataQTensorActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperC3TensorBlockActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperC3TensorGeometryActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperC3ThetaRootTensorPacketActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperC3ThetaUnitSourceActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperC3ThetaValuesActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperCompletionTensorActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperCompletionThetaValueActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperFinalLInd1Actual.lean | paper-layer | NO_RESULTS_LINE | IUT III Thm 3.11 前置（Ind1/2/3、K1K2）
- tmp/PaperFinalLMu2lExtensionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperFinalLValuedTensorCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperGlobalIQCarrierEquivActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperIndFinalPacketObstructionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperIQCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperKummerLocalTensorActual.lean | paper-layer | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/PaperKummerLocalTensorNormedActual.lean | paper-layer | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/PaperKummerNumberFieldModelActual.lean | paper-layer | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/PaperLineBundleCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperLineBundleCarrierBase.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperLogKummerTargetActual.lean | paper-layer | EXIT0 (citable evidence) | IUT II Kummer/log-shell 前置对象
- tmp/PaperLZetaNormedActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperMonoAnalyticUnitRegionSourceActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperMuLogIQCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperMuLogUnitRegionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperMuTwoLTensorActionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperOneColumnLabelActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperPlaceFamilyInjectivityActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperProcessionEqSigned.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperQPilotIdentificationsActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperQPilotLineBundleConcreteActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperQPilotObjectConcreteActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperQPilotObjectSourceActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperQPilotStripTargetActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/PaperQZeroLimitAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootBaseLZetaActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootCompletionTensorActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionDiscreteValuationActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionEquivActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionFieldScalingHaarActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionHaarActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionHaarDirectionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionHaarFactorActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionNormBoundActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionPrimeDecompositionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionPrimeScalingActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionProductHaarActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionUnitDecompositionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootExtensionValuedActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootLQSideHaarActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootLThetaMigratedActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperRootLValuedTensorCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootLZetaActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootTensorHaarActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootTensorHaarFinitePadicActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootTensorHaarLiftActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootTensorThetaCarrierActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperRootThetaNormBoundActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperRootThetaPacketActionsActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperRootThetaProductCarrierActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperRootThetaProductMeasureActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperScopeLemma24Actual.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/PaperScopeLemma24ProbeActual.lean | paper-layer | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/PaperSixTorsionCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperSourceGeometryActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperSourceGeometryKummerActual.lean | paper-layer | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/PaperSourceGeometryQActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperSourceThetaConsistencyActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperSymbolTypesActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperThetaLinkNontrivial.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaMagnitudeActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaMagnitudeComparisonProof.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaMagnitudeSignedActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaNamingActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaPilotComponentImageActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaPilotMonoAnalyticNormalizationActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaPilotNormalizedVolumeActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaPilotOnGlobalIQActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaPilotPossibleImageCoordinateActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaPilotUnitRegionActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaProcessionNormalizedLogActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaRootObstructionActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperThetaSideObjectActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperUnifiedLZetaCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperWeightedThetaSignedActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/PaperXiFGlobalDirectActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperXiFSourceLinkActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/PaperXiFSpec.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperXiFTheorem.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/ProbeBisectLocalReduction.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/ProbeBisectReductionBaseChange.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/QPilotPaperLineBundleActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/QVFamNormalizedSupplyCoefficientActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/RelativeNormContraction.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/RelativeNormContractionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1039PaperQFieldAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1051PaperGlobalFinalActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1052PaperQParameterCardActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1054PaperFinalLinksActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1055PaperGlobalFinalAssemblyActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1057PaperGlobalQPilotLogActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S1059PaperGlobalSignActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1063PerBQPilotPaperNonzeroActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S1066PaperSourceLinkActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S1068CorrectedPaperTargetActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1074SupplyCNormOrderActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1093PaperAssemblyActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1110GlobalPaperQPilotActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S1111PaperThetaQVFamilyAuditActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S1112SourceComparisonProductReductionActual.lean | route | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S1134PaperScalarAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1260UniformizerFactorReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1313IntegralLogShellContractActual.lean | route | NO_RESULTS_LINE | IUT II Kummer/log-shell 前置对象
- tmp/S134ActualPaperTargetCorrectionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S137PaperTargetCorrectionStatusActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1406PaperPolyIsoBase.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1406PaperPolyIsoBase2.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S151PaperNormalizationChoiceActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1532PaperNativeRootActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S154PaperNormalizedQUnitActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1647RouteARootActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1649RouteCReadoutActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1650RouteFQMarkActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1713SplitReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1724PaperArithmeticActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1959PaperCoricVerticesActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2050PaperOActualComponents.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2066PaperOUnitsMuUnconditional.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2364D5GroupRouteActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2453PadicDemushkinReduction.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2455PadicThreeGeneratorsReduction.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2456PaperFamilyActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2558ReverseReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2576TateBadReductionActual.lean | route | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S2577TateBadReductionActual.lean | route | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S2588PaperSourceBadQBoundActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S2589S2404IdentityReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2590LocalizedPrimeContractionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2594P4AllPlacesSkeletonActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2596pReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2598PaperDCorrectionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2599PaperP4WiringActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2611CurveSkeletonActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2617CuspClauseReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2619ActionGroupoidFiberSkeleton.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2662D9StackGoalReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2663D9IsStackReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2668D9ReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2678PaperUnconditionalHcompActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2679PaperHcompNormalizationActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2679PaperUnconditionalAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2684BadPlaceContractConditionalActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2684PaperNormalizationAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2686PaperConcreteHqHcompActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2687PaperQAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2688BadReductionSelectionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2690D4ContractAuditActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2692D4ConditionalContractActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2692WeierstrassPointDataReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2693PaperQNeTateQActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S2694PaperQPilotSignedLogAuditActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S2702PaperConditionalActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2707PaperUnconditionalActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2726ReductionFiveActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2764GoodReductionOfUnitDeltaActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2814BadPlaceContractActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2838HeightComparisonReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2859A6CoreFieldReductionAudit.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2956CThetaPaperUpperActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S2968PaperHeightRoute.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3045CThetaPaperNonnegCounterexample.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S3049PaperAlignmentConstantsActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S424QVFamilyPaperQAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S554QHalfPaperActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S607ModelPaperPhiAlignmentActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S616ModelPaperAlignmentActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S620FinalContractActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S622PaperXiFFieldAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S628PaperXiFSourceLinkConstructionActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S637ActualPaperXiFBridgeActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S638ActualToPaperXiFSourceLinkActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S638PaperThetaNormalizationActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S640PaperRootThetaProcessionActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S641CorrectedPaperThetaComparisonActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S642PaperRootThetaProcessionActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S644PaperRootThetaProcessionActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S669S663PaperXiFSourceLinkActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S697QPilotRegionCoefficientReductionActual.lean | route | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S703GlobalPaperThetaComparisonActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S704PaperThetaLogVolumeFormulaActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S720OneFactorTensorNormReductionActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S734PaperCoefficientBridgeActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S737PaperCoefficientBridgeCorrectionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S744PaperOrderReplacementActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S750PaperRootStackOtriCarrierActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S773RootCorrectedPaperTargetActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S775PaperOrderQPilotCorrectionActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S777PaperTargetRootStackAlignmentActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S778PaperQPilotHalfRegionActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S788PaperQpilotRegionActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S790StackToPaperQPilotThetaActual.lean | paper-layer | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S797PaperOrderRegionContainmentActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S799LeastLambdaOPaperTargetActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S813PaperInterfaceHub.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S815PaperScalingDataFiniteLActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S819PaperRootCompletionGeneratorActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S827PaperValueGroupNormCardActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S828PaperRootValueGroupActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S829PaperNormValuationSpectralActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S833PaperNormalizedStackHaarActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S835PaperRootValueGroupIffActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S837PaperRootMinimalCompactActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S853PaperOrderNoEActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S854ProductCompactRouteActual.lean | route | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S859PaperIntrinsicLogVolumeActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S862OtriLogVolumeInterfacePaperActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S864PaperLambdaOLogVolumeActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S867OtriPaperIntegrationActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S868GlobalPaperTargetInterfaceActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S901ProbeS819PaperRootCompletionGeneratorActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S913PaperMonodromyActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S914PaperLVExInstantiationActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S921RQpilotPaperRegionPositivityActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S930GlobalWeightedPaperInequalityActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S939PaperSCarrierAuditActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S942ActualPaperSInterfaceActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S945TensorPacketPaperSActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S946TensorPaperSContainmentActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S949PaperQPilotCarrierBridgeActual.lean | paper-layer | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S950PaperFaithfulFinalInequalityActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S956PaperTensorClosureActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S962TensorPacketPaperInequalityActual.lean | paper-layer | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S983PaperXiFSourceLinkConstructionActual.lean | paper-layer | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/ThetaPacketContractionProof.lean | route | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/ThetaPacketContractionProof2.lean | route | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/_s2857gaprobe.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/ABCGap2AxiomsProbeActual.lean | gap | EXIT0 (citable evidence) | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/ABCGap2FiniteC3SupplyActual.lean | gap | EXIT0 (citable evidence) | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/BasePlaceQCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/C3IQActualPacketGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/EtaleThetaQExponentGap.lean | gap | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/FinitePlaceQCandidateValuationActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/InverseJQCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/IQCarrierObligationsActual.lean | obligation | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/NativeTorsionGapsSourceFieldsActual.lean | gap | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/OrbicurveEtaleFundamentalGroupAssemblyAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperFinalLValuedHaarMuLogGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperIndRootPacketObjectGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/PaperRootThetaProductHaarGapActual.lean | gap | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/ProbeObligations.lean | obligation | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/QPilotCompletionPowerRegionGapActual.lean | gap | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/RepresentableEtaleCoverCategoryAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/RootExtensionTensorGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/RootTensorBlockLGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/RootThetaIndActionsGapActual.lean | gap | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S100QVFamNormInstanceGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1165SourceHDDReadoutGapActual.lean | gap | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S1218ConcreteInputBridgeGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1790SmallnessAlternativesActual.lean | alternative | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S1899CoherentStrongApexActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2002D5RangeFieldGapsActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2461DiagramInvolutionAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2592ValueMapCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2593P4CandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2602S1322GapDependencyActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2607SignedGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2608SignedGapDataActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2609SignedGapPartsActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2611SignedGap2SourceActual.lean | gap | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S2617CuspParameterCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2638D7SectionGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2684GaussianFiveQCandidateActual.lean | candidate | EXIT0 (citable evidence) | initial theta / theta 前缀对象
- tmp/S2685TateInverseJGapActual.lean | gap | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S2685TateUniformizationGapAuditActual.lean | gap | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S2721PadicBallVolumeAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2724BallGap2Actual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2726ComparisonRhoPerCoordinateAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2727ActualInputCandidates.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2730CoordinateProductRegionAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2732ScaleShiftScalingAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2771Gap1ClosedActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2777MixedSpaceHeightGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2911CorrectedCompletionAttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2918ThetaUpperConstructionAttemptActual.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/S2936HeightBridgeAttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2946ElementaryTargetAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S2965MinimalAttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3017StepVUpperGapAssembly.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3047bActualParameterHscalarAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3053UpperGapClosed.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3076CSqEqOneAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3076cWeightedProductAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3076dNormProductBridgeAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3076eSourceFamilyQValueAttempt.lean | attempt | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S3079GlobalSumIdentificationAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3082S3083AttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3084S3085AttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3086CorrectedPlaceIndexAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3092NonBadZeroAttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3094ActualQFamilyAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3095ActualQOriginalInputAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3096IndexBridgeAttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3096NativeTConstructionAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3096S3097S3098AttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3099BadFamilyProjectionAttempt.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S3262AuditConfirmationsAttemptActual.lean | attempt | EXIT0 (citable evidence) | unmapped（需人工归档）
- tmp/S348C3CarrierIdentificationGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S355OrbifoldRootStackCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S372APacketC3TransportGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S476GenericGroupLikeGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S479TwoTorsionParityGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S507PhiCvCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S508PaperPhiCvCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S511PhiCvCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S513DvPhiCvCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S540QvPhiTauExactGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S546QHalfCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S555QvPhiTauConstructionGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S564QvPiOtriangleCandidateActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S613QvPhiDivisibilityAttemptActual.lean | attempt | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S621ConcreteComparisonMinimalGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S624FinalConcreteSourceComparisonGapActual.lean | gap | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/S677OtriFromTauGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S702QPilotRegionNormCandidateActual.lean | candidate | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/S754CandidateRootsTorsorActual.lean | candidate | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S781TwoLTargetGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S869OtriGapsFilledActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S873PaperGapIntrinsicVolumeActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S881PaperGapIntrinsicVolumeS869Actual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S884PaperGapIntrinsicVolumeRebuildActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S898PaperGapFromScalingActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S928ActualIndImageGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/S934PaperIndImageExactGapActual.lean | gap | NO_RESULTS_LINE | unmapped（需人工归档）
- tmp/SourceQvCandidateActual.lean | candidate | NO_RESULTS_LINE | GenEll/EtTh source realization 前置
- tmp/TateJacobiHahnAttempt.lean | attempt | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/TateJacobiStandardAttempt.lean | attempt | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/TateJacobiTripleProductAttempt.lean | attempt | NO_RESULTS_LINE | ABC bridge: frontier/Frey/Tate/q-pilot 前置
- tmp/TateThetaAdditionAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaDuplicationAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaLayerAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaLogDerivAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaNormalizationAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaOddCoefficientAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaOddEquationAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TateThetaProductAttempt.lean | attempt | NO_RESULTS_LINE | initial theta / theta 前缀对象
- tmp/TauCetiPort/TauCeti/LinearAlgebra/Matrix/Alternating.lean | alternative | NO_RESULTS_LINE | unmapped（需人工归档）

## 4. 使用建议

1. 对 citable=OLEAN_FRESH 且 tags 非 unmapped 的行，优先核对 decls 与 tree 资产是否重复：重复则只登记为“已有资产消费者”，不新写 Lean。
2. 对 tmp/paper 层 EXIT0/OLEAN_FRESH 行，若其 decls 已被其他 consumer 消费，直接标注消费者；若无消费者，写“真实组合 consumer”（引用现有定理，无 sorry/空声明）。
3. 对 citable=EXIT1/STALE_NO_SOURCE 行：先复跑/修复原文件（queue 修错），不新建 adapted 副本。
4. 对 unmapped 且无前置对象的行：归档登记（DAG-BLOCKED/说明），不批量造文件。

## A480-C lattice 补充：tmp 资产可执行清单（与 shehdd 上表去重/合并）

generated: 2026-11-10T19:59:31.906Z（lattice A480；只读扫描，未复制/未 adapted）

### 统计（一行）

- repo-route-index tmp rows=804，其中 citable=OLEAN_FRESH/EXIT0 且非 tmp/sheaf/n8/closure：**666**；有 olean：**666**；可映射到 IUT 前置对象：**142**；其余 other=524。
- 按目录: tmp/sheaf/xif=666
- tmp/a428_gap_pins.txt exists=true size=1071
- tmp/external exists=true，tmp/ported exists=false

### 可执行清单（前 60，按 olean 优先 + 前置对象映射）

| file | decls | citable | 前置对象 | olean | 消费者建议 |
|---|---|---|---|---|---|
| tmp/sheaf/xif/paper/ActualPaperThetaLinkActual.lean | actualPaperThetaLinkData_inputLink_eq_composite, actualPaperThetaLinkData_kummerEvaluation_commutes | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/AssemblyKummerIndThetaPaperBridgeActual.lean | AssemblyKummerIndThetaPaperData, assemblyKummerIndThetaPaperData_carrierFields | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/BadPlacePaperRootThetaHullActual.lean | PaperRootHullFormulaGap, paperRootThetaHullLog_eq_formula_of_gap | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/ConcretePaperQPilotWitnessActual.lean | ConcreteObjectType, ConcretePaperQPilotWitness | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/EtaleThetaHalfIntEmbeddingApplyConsumerActual.lean | halfInt_le_iff, halfIntOrderEmbedding_apply | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/Hull09H5GapsActual.lean | hull09_scalingUnits_subset_hull, hull09_hull_eq_closure | OLEAN_FRESH | H5 | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（H5），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/OrigXiFPaperLogKummerActual.lean | OrigXiFActionFactorization, OrigXiFactionConj_eq_unitsAction | OLEAN_FRESH | Kummer | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Kummer），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/OrigXiFPaperQPilotComponentsActual.lean | OrigXiFPaperQPilotComponents, origXiFPaperQPilotComponents_boundary | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/OrigXiFPaperQPilotFromSourceLActual.lean | OrigXiFQPilotFirstFieldType, OrigXiFQPilotFirstField | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/OrigXiFPaperQPilotObjectActual.lean | OrigXiFPaperBadQAbsLog_eq_source, OrigXiFPaperQPilotScalarIdentified | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/OrigXiFPaperQPilotObjectPreorderActual.lean | OrigXiFPaperBadQAbsLog_eq_source, OrigXiFPaperQPilotScalarIdentified | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/OrigXiFPaperQPilotScalarActual.lean | OrigXiFPaperQPilotLogVolume_eq_neg_abs_log_q, OrigXiFPaperQPilotLogVolume_eq_log_norm | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3KummerExtensionActual.lean | KummerBase, KummerRootValue | OLEAN_FRESH | Kummer | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Kummer），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3QPilotLogComparisonActual.lean | paperQUnitBlockMeasurableSpace, sourceQTensorMeasurableSpace | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3RootThetaHullActual.lean | primitiveMu2lRoot_zeta_ne_zero, paperRootThetaHull_mem | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3ThetaRootActual.lean | RootExtension, RootThetaCarrier | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3ThetaRootTensorPacketActual.lean | RootThetaTensorCarrier, RootThetaTensorPacketActual | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3ThetaUnitSourceActual.lean | ThetaUnitSourceData, qParameterUnit_norm | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperC3ThetaValuesActual.lean | ThetaExtension, paperQParameterThetaValue_eq_q_pow | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperFinalLInd1Actual.lean | finalTensorIndex_isSingleton, finalTensorIndex_card | OLEAN_FRESH | Ind1 | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Ind1），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperFinalLValuedThetaIndHullActual.lean | Carrier, rootThetaImage_subset_indUnion | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperIQHullLogVolumeInterfaceCandidateActual.lean | paperIQHullLogVolumeInterfaceCandidate_unitRegion_logVolume_lt_top | OLEAN_FRESH | HeightVolume | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（HeightVolume），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperKummerLocalTensorActual.lean | KummerLocalField, KummerLocalProductCarrier | OLEAN_FRESH | Kummer | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Kummer），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperKummerNumberFieldModelActual.lean | GlobalQLift, KummerAdjoinRoot | OLEAN_FRESH | Kummer | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Kummer），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperLogKummerTargetActual.lean | PaperLogKummerTarget, paperLogKummerTarget_objectLogKummer | OLEAN_FRESH | Kummer | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Kummer），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperQPilotIdentificationsActual.lean | paper_strip_identification_actual, paper_lineBundle_identification_actual | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperQPilotLineBundleConcreteActual.lean | ConcretePlaces, concreteQPilotLineBundle_eq_inv_ideal | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperQPilotObject.lean | - | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperQPilotObjectConcreteActual.lean | concreteProcessionChoicePreorder, concreteBoundary | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperQPilotObjectSourceActual.lean | MissingPaperQPilotStripTarget, MissingPaperLineBundleTarget | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootExtensionThetaHullActual.lean | rootExtensionProductThetaHull, rootExtensionProductThetaHullLog_eq_zero | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootExtensionThetaHullAuditActual.lean | rootExtensionProductImageHull, rootImageRadius_ge | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootExtensionThetaHullScalingActual.lean | IsCoordinatewiseScaledHull, rootExtensionProductImageHull_is_scaledHull | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootLThetaMigratedActual.lean | Carrier, RootLThetaImage_subset_IndUnion | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootTensorThetaCarrierActual.lean | rootTensorUnitBallMeasure_eq_one, rootTensorThetaImage_subset_IndUnion | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootThetaHullCarrierGapActual.lean | paperNonzeroRootThetaImageSet_subset, paperRootThetaUnit_pow_twoL_eq | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootThetaNormBoundActual.lean | rootExtensionUnitNorm_nonneg, rootExtensionUnitNorm_pow | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootThetaPacketActionsActual.lean | RootPacket, rootThetaToCarrier | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootThetaProductCarrierActual.lean | RootThetaProductCarrier, rootThetaUnitBall | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootThetaProductHaarGapActual.lean | RootThetaLocalHaarData, RootThetaProductHaarData | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperRootThetaProductMeasureActual.lean | rootThetaImageMeasure_unitBall, rootThetaImageMeasure_unitBall_pos_lt_top | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperSourceGeometryKummerActual.lean | completionValueQ_eq_thetaPacket, valueToCompletion_completionValueQ | OLEAN_FRESH | Kummer | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Kummer），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperSourceThetaConsistencyActual.lean | sourceThetaPlace, sourceThetaQ_pos | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperTheta311DataActual.lean | PaperTheta311ThetaData, paperTheta311ThetaData_q0_value | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaCoeffConsumerActual.lean | PaperThetaCoeffData | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaInitialThetaConsumerActual.lean | InitialThetaCoeffData, InitialThetaQZeroData | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaLinkDataActual.lean | selfPaperThetaLinkData_inputLink, selfPaperThetaLinkData_ipl_factorization | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaLinkDataConsumerActual.lean | selfPaperThetaLinkData_ipl_projection, selfPaperThetaLinkData_kummerEvaluation_projection | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaLinkNontrivial.lean | intermediateStrip, gauStrip | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaMagnitudeActual.lean | actualC3_thetaPacket_contraction, actualC3_procession_average_nonpos | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaMagnitudeComparisonProof.lean | thetaCard, thetaCard_pos | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaMagnitudeSignedActual.lean | actualSignedC3, actualSignedC3_hlog | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaNamingActual.lean | paperTheta | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaProcessionNormalizedLogActual.lean | thetaSideGlobalProcessionNormalizedLog_formula, thetaSideGlobalProcessionRootCoefficient_formula | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaRootObstructionActual.lean | sourceRootField, paperQParameterThetaValue_eq | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/PaperThetaSideObjectActual.lean | ThetaSideObject, thetaSideObject_hull_eq_thetaHolomorphicHull | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/QPilotCompletionPowerRegionGapActual.lean | QPilotCompletionPowerRegionGap, QPilotCompletionPowerRegionGapRequired | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/QPilotPaperLineBundleActual.lean | QPilotBaseField, qPilotLineBundle_eq_inv_zeroLocus | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/RootThetaIndActionsGapActual.lean | RootThetaIndCarrier, rootThetaIndImageUnion_contains_image | OLEAN_FRESH | Thetas | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（Thetas），禁止 adapted 副本/簿记 |
| tmp/sheaf/xif/paper/S1057PaperGlobalQPilotLogActual.lean | paperGlobalQPilotLog_eq_weighted, paperGlobalQPilotLog_eq_s1050 | OLEAN_FRESH | QPilot | yes | 组合该文件 decls 与已编译 tree 资产写真实 consumer（QPilot），禁止 adapted 副本/簿记 |

### 去重说明

- 上表 shehdd 已覆盖 LeanFormal 与部分 tmp；本表只列 tmp 且排除 n8/closure，按 file 去重（若同一 file 已在上文出现，仅作为可执行消费者候选，不重复资产计数）。
- 建议按前置对象分组执行：每对象取 1-3 个 OLEAN_FRESH 资产写真实 consumer/链式定理（不复制理论、不改原文件）。

- 已消费: LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean -> tmp/sheaf/xif/paper/ShehddInd2LinkChainActual.lean (shehdd: ind2-link-chain, 3 个真实链定理; A480)

### A480-D S2748 修复确认（lattice）

- file: `tmp/sheaf/xif/paper/S2748AbsNormGeRationalPrimeActual.lean`
- 修复内容: `theorem S2748_absNorm_ge_rationalPrime (P : FinitePlaceAtPrime K p) : p <= Ideal.absNorm P.val.maximalIdeal.asIdeal` 由真实证明给出（imports `FinitePlaceCompletionNormTransport` / `S2690TwoPlaceBadQActual`；用 Mathlib `Ideal.absNorm = p ^ inertiaDeg` 与实际 comap/maximal-ideal LiesOver bridge），当前源码 `sorry` 计数=0。
- 时间: 源文件 mtime 2026-11-11 03:58（并发 worker 修复；lattice 复核源码无 sorry）。
- olean: 修复前旧产物 stale；已加入 `dag/watchdog/extra-targets.txt` 等重建，重建后自动进正式 olean DAG 并由 CONDITIONAL/GAP 转 PROVED。
- 审计: `dag/SORRY-AUDIT.md`（生成 2026-11-10T19:54:53Z）对 S2748 的条目为 stale，重建后自动清；**不是 DAG-BLOCKED**。


- 已消费: LeanFormal/IUT/Foundations/Geometry/ConvexHullVertexSupReduction.lean -> tmp/sheaf/xif/paper/Mzk1HullVertexBoundConsumerActual.lean (lattice: hull_volume_le_of_vertex_bound / hull_volume_le_of_eq_vertex_bound; 真实 consumer，组合 iSup_ofReal_le_iSup_vertices_of_subset_convexHull + ENNReal.ofReal monotonicity; A480)

- 已消费: LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean -> tmp/sheaf/xif/paper/ShehddIndRouteCommuteChainActual.lean (3 个真实链定理; A480)

- 已消费: tmp/sheaf/xif/paper/S1057PaperGlobalQPilotLogActual.lean -> tmp/sheaf/xif/paper/Mzk1QPilotLogChainConsumerActual.lean (lattice: s1050PaperGlobal_eq_weighted / paperGlobalQPilotLog_eq_badWeighted / paperGlobal_eq_s1050_badWeighted; 真实 transitivity consumer，组合 S1057 eq_s1050 + eq_weighted; A480)

- 已消费: tmp/sheaf/xif/paper/PaperThetaSideObjectActual.lean -> tmp/sheaf/xif/paper/Mzk1ThetaHullTransportConsumerActual.lean (lattice: thetaHolomorphicHullObject_carrier_eq_singleScaledRegion / thetaSideObject_image_subset_singleScaledRegion / hullLog & hullMeasure compatibility; 真实 equality transport consumer; A480)
