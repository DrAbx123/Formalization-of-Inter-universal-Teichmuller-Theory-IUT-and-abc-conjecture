# A477 只读核对：shehdd 区域已有资产清单 + 真缺失短清单

日期: 2026-11-11. 口径: 只读扫描 dag/generated/declarations-index.json (1,572,263 条声明)、LeanFormal/tmp/papers 文件系统; 未新建 Lean 文件、未改 fragment、未加 DAG 节点/extra-targets。

## 1. 区域统计（声明索引 file 前缀聚合）

| 区域 | 文件数 | 声明数 | 主要 kind |
|---|---|---|---|
| IUT III Cor 3.12 tree | 88 | 1718 | theorem 1168, def 451, structure 69 |
| IUT III Thm 3.11 tree | 100 | 6443 | theorem 5361, def 760, structure 247 |
| IUT II Kummer/log-shell | 44 | 766 | theorem 509, def 218, structure 23 |
| IUT II other | 149 | 4884 | theorem 3177, def 1152 |
| IUT I (theta/hodge theater) | 69 | 5086 | theorem 4045, def 813 |
| IUT IV | 12 | 284 | theorem 212, def 56 |
| ABC bridge/Frey/Tate | 158 | 2592 | theorem 1938, def 438 |
| Foundations | 533 | 9242 | theorem 6288, def 1797 |
| paper layer (tmp/sheaf/xif/paper) | 9041 | 80862 | theorem 39568, def 24153, lemma 7417 |
| external ported | 2159 | 33287 | theorem 23773, def 4739 |

关键源文件存在性: 54/54 存在，54/54 对应 olean 新鲜（.lake/build/lib/lean 同路径），0 missing source、0 stale。

## 2. 关键资产（file:decl，仓库已有）

Cor 3.12 / StepXI:
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean: StepXIContract, Cor312Conclusion, cor312_of_constructed_stepXI, q_positive_of_constructed_stepXI
- LeanFormal/IUT/IUTIII/Corollary312/Routes.lean: Cor312Route, Cor312RouteCertificate, conclusion
- LeanFormal/IUT/IUTIII/Corollary312/Comparison.lean: cor312Conclusion_of_contract
- LeanFormal/IUT/IUTIII/Corollary312/TateQPilotJComparison.lean: qPilotLogVolume, tateJInvariantLogVolume, qPilotLogVolume_eq_log_prime, tateJInvariantLogVolume_eq_log_prime, qPilotLogVolume_pos, tateJInvariant_norm_mul_q_norm_one
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/Volume.lean: PositivePacket, FiniteHull, WeightedValues, StepXIFiniteCertificate, q_le_theta, q_positive
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean: HullDeterminantLogVolumeFrozenSpec, hullDeterminantLogVolumeFrozenSpec_holds, matrixLogDet_*_posDef, packetLogVolume_tensorPower
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction.lean: sourceHullVolume_eq_imageVolume_iff, sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le, sourceHullVolume_le_imageVolume_of_candidate

Thm 3.11 / Ind / K1K2:
- Theorem311/Indeterminacy/Ind1Reduction.lean: ind1QuotientLift, ind1QuotientMap_ind1, ind1QuotientLift_unique
- Theorem311/Indeterminacy/Ind3Reduction.lean: PossibleImage, lowerClosure, le_iff_carrier_subset_of_isLowerClosed
- Theorem311/SourceK1K2CardReduction.lean: logShellRayPresentation_univ_iff, negLogVolume_hind3, k1BoundaryOf_negLogVolumeRayPresentation, sourceVerticalRealizationOf_negLogVolumeRayPresentation
- Theorem311/SourceLabelWeightedDiagonal.lean: labelWeight, zeroLabel, oneLabel, labelWeight_zeroLabel, toFiniteLabel_zeroLabel
- Theorem311/SourceSharedBoundary.lean: NonzeroFiniteLabel, signedLabel_cardinality, nonzeroFiniteLabel_cardinality, cuspLabel_cardinality

Kummer / log-shell:
- IUTII/Kummer/SourceLogShellCarrier.lean: SourceLogShellDatum, preLogShell, logShell, unitLayer, logShell_eq_invScaledPreLogShell, IQSpan
- IUTII/Kummer/SourceLogShellAbsTopIIIBridge.lean: SourceLogShellInvariantImageIdentification, codomainKummerContained_of_invariantImageIdentification, kummerImages_mem_logShell
- IUTII/Kummer/SourceLocalLogShellDatum.lean: sourceLocalLogShellDatum, _pStar, _logShell_eq_integralLogShell, _zero_mem_logShell
- IUTII/Kummer/AbsoluteKummerInjection.lean: RootsOfUnityFixed, chosenRoot_spec, absoluteKummerMap_eq_one_iff; AbsoluteKummerQuotient: nthPowerSubgroup, absoluteKummerMapQuotient_injective; AbsoluteKummerContinuity: isLocallyConstant_absoluteKummerMap, continuous_absoluteKummerMap
- IUTII/Kummer/KummerGaloisClass.lean: kummerRatio, kummerRatioHom, kummerMap, kummerMap_eq_one_iff, kummer_pow_mem_of_trivial
- IUTII/Kummer/AlgebraicClosureKummerRoots.lean: exists_root_algebraicClosure, fixed_by_absoluteGalois_mem_base
- IUTII/Kummer/SourceThetaPilotIQContainment.lean: possibleImage_subset_of_generator_mem, sourceThetaPilotIQPacket, possibleImage_subset_sourceThetaPilotIQPacket

Hodge theater / theta:
- IUTI/HodgeTheater/SourceThetaLinkGraphAutomorphismReduction.lean: FrobeniusPictureGraphAut, chainTranslation, graphAut_eq_translation, graphAut_one
- IUTI/HodgeTheater/SourceThetaLinkDisplacementReduction.lean: ThetaQDisplacement, ThetaScaleDisplacement, hodgeTheaterLink_displacement
- IUTI/HodgeTheater/SourceHodgeTheaterFamilyLawsReduction.lean: thetaPacket_eq, theater_ne_of_ne, not_constant_theater_of_ne
- IUTI/InitialTheta/SourceDefinition31Boundary.lean: SourcePlacePartition(labels_agree/transports), SourceSectionClause(sectionMap_injective/surjective)
- Foundations/Theta/OddTheta.lean: oddThetaExponent, oddThetaSign, oddThetaTerm, oddTheta, oddThetaSign_add, oddThetaExponent_coe
- Foundations/Theta/OddThetaShift.lean: oddTheta_shift; OddThetaNormalization: oddThetaFraction_eval_unconditional; OddThetaNonvanishing: oddTheta_ne_zero_at_i
- Foundations/Theta/GaussianKernel.lean: gaussExponent, thetaValue, realThetaValue, log_realThetaValue; GaussianSquareSum: gaussianSquareSum_formula, normalizedGaussianDegree_eq_factor
- Foundations/Theta/SignedLabelEquiv.lean: toFiniteLabel, representative, representative_toFl, toFiniteLabel_injective

ABC bridge / Frey / Tate:
- ABCBridge/Bridge/ABCFrontier.lean: ABCFrontier, bridgeInterface_of_frontier, abcConjecture_of_frontier, abcFrontier_iff_abcConjecture
- ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean: Cor312ToABCBridgeInterface, cor312ToABCBridge_abcConjecture, cor312ToABCBridge_heightBound
- ABCBridge/Bridge/ABCEllipticHeightCriterion.lean: ABCFreyJProductHeightCriterion 等四判据 + 四等价
- ABCBridge/Bridge/ABCFrontierSingletonReduction.lean: not_ABCFrontierPointwiseReduced; ABCHFrontierHeightWeightRefutation: not_FrontierHeightWeightClause, not_ABCFrontierGapReduced(V2)
- ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean: ABCHeightWeightAdditiveBoundV2, abcConjecture_iff_ABCHeightWeightAdditiveBoundV2
- ABCBridge/Arithmetic/LogarithmicBoundEquivalence.lean: ABCLogConjecture, abcLogBound_exists_iff_rpow_exists, radical_eq_natRadical, radical_log_eq_arithmeticWeight
- ABCBridge/Arithmetic/ABCInvariantCoprimality.lean: abcInvariantPolynomial_coprime_*, abcInvariantDenominator_pos, abcInvariantCancellation_le_256
- ABCBridge/Arithmetic/ABCInvariantRadicalBridge.lean: abcJInvariant_den_radical_bounds, abcJInvariant_den_logRadical_double
- ABCBridge/Arithmetic/ABCNonemptyOddBadSupport.lean: abcOddBadPrimeSupport, mem_abcOddBadPrimeSupport_iff, abcOddBadPrimeSupport_nonempty_iff, odd_bad_prime_mem_j_valuation_neg
- ABCBridge/Geometry/FreyTateAnalyticInput.lean: freyAbcTateCandidateQ_norm_lt_one, _norm_le_invNine, _arithmeticCertificate; FreyTateParameterComparison: freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP
- ABCBridge/Geometry/FreyWeierstrassCurve.lean: freyWeierstrassCurve_discriminant, _c4/_c6, _isElliptic_of_isUnit
- ABCBridge/Geometry/ABCModelHeightComparison.lean: rationalFreyWeierstrassCurve_j_eq_abcJInvariant, _j_height_bounds, exists_odd_bad_prime_freyAbcTateAnalyticInput
- Foundations/Geometry/TateCurveArithmetic.lean: canonical_equation_coefficients, canonical_b/c/delta laws; TateCurveDiscriminantEstimates: deltaValue_expanded; TateJInvariantNorm: tateJInvariant_norm, _norm_eq_prime, _norm_mul_q_norm
- Foundations/Geometry/TateUniformizationContract.lean: tateParameterUnit, _ne_one, _pow, _algEquiv_map, CurveIndexedTateUniformization
- Foundations/Geometry/EllipticTorsion.lean: AllNTorsionRational, Torsion23Rational, LTorsion, galoisActionOnPoint(_one/_mul), galoisActionOnLTorsionLinearEquivHom
- Foundations/LocalFields/IntegralUnits.lean: Integers, unitOfNormOne, principalUnits; IntegralUnitLogarithm: unitLog, unitLog_mul/pow; LogarithmLocalInverse: exists_log1p_preimage, exists_unitLog_eq_scale_mul, integers_subset_integralLogShell
- Foundations/NumberField/LocalQParameter.lean: FinitePlaceQCandidate; Foundations/Arithmetic/Radical.lean: natRadical_* (pos/dvd/mul/pow); NormLog: unitNormLogDegree_*

paper 层与本区域相关已编译资产（抽查）: tmp/sheaf/xif/paper/AbcStatementAlignmentActual.lean: abcConjecture_iff_tauCeti, tauCeti_nat_form; Mzk1GeomCorePreciseToOldActual.lean: toOldWitness, toOldRecast, genEll15GeometricCoreStatement_of_precise; Mzk1GeometricCorePreciseActual.lean: MapsTToZero, UnramifiedOverZero, PullbackIsoDegree; S1995* 系列文件 32 处存在。

## 3. 真缺失短清单（逐条附搜索证据）

1) **IUT III Cor 3.12 顶层陈述的逐字命名**缺失: 声明索引正则 IUT312|iut312 命中 0；语义等价实现已有（StepXIContract/Cor312Conclusion/路线 3 条 + paper 层 IUT312TopStatement 类文件）。
2) **IUT II Cor 4.10 逐字命名**缺失: 索引文件路径正则 cor4[._]?10|corollary4[._]?10 命中 0；语义资产已有（SignedLabel/Fl 字典、SourceLogShellInvariantImageIdentification、NonzeroFiniteLabel 基数）。
3) **IUT III Def 3.8(i) Theta-pilot 对象层逐字命名**缺失: 正则 ThetaPilotDef38|thetaPilotObjectLayer 命中 0；语义实现已有 one-place 版本（SourceThetaPilotIQContainment）与 FinnitePlaceThetaPilotScaledRegion。
4) **IUT I Def 3.1(b) 独立 q-parameter 对象逐字命名**缺失: 正则 qParameterDef31|def31b 命中 0；语义实现已有 FinitePlaceQCandidate + ArithmeticQPilot{LogVolume,BaseChange,GlobalNormalization}。

非缺失（曾疑似缺口，核对后确认仓库已有）: H6 geometric core precise (10 文件命中: Mzk1GeometricCorePreciseActual 等)；Sources 1995-2015 named 资产 (32 文件命中: S1995* 系列)；Cor 4.10 label 语义资产；scheme-side sectionMap (SourceDependentSectionMap/valuationSectionMap, sectionMap_injective/surjective 已证)。

## 4. DAG/watchdog 状态（只读，未改）

- dag_validate_decl2: problems 0, nodes 1311, 0 条 shehdd 相关 problem；我的 fragment 72 节点/142 边保持原样（未改、未新增）。
- watchdog 队列未干预；本轮未新增 extra-targets 条目。
- 结论: 本区域“可用已有资产”充足；真缺失仅为 4 条逐字命名层(语义等价实现均存在)，不建议再批量造 bridge/consumer 文件。
