# INVENTORY-hull-A477 — 我区域（hull / IUT III pre-objects / H5-H7-HDD-K1K2-Ind / StepXI / Cor312）已有资产清单

A477 只读核对（不写 Lean、不改 fragment、不碰 watchdog、不编译）。时间 2026-11-11T03:4x。搜索范围: LeanFormal/ 全树、tmp/sheaf（含 xif paper-layer 与 xif 早期资产）、tmp/n8、tmp/external、coord/、papers/、.lake 关键 olean；declarations-index 未定位到 rail 文件（仅 Mathlib 构建产物同名），证据改用 olean 存在性 + 源文件声明。
格式: 对象 → 仓库已有资产（file:decl，olean=已构建）。

## A. LeanFormal 树（源码 + 多数 olean=yes）

| 对象 | 已有资产（file:decl） | 状态 |
|---|---|---|
| H5 hull/interface | LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean: `IQHullLogVolumeInterface`(52), `imageSet_logVolume_le_hull`(88), `hull_logVolume_lt_top`(95), `lower_bound_and_finiteness`(104); `SourceHullInterfaceDischarge.lean`: `hull_logVolume_realRepresentation`(85), `haarContractionInterface`(109), `haarContractionInterface_hull_logVolume_lt_top`(149) | 已有（olean yes） |
| H5 hull 几何副产物 | HolomorphicHull/CardHullRealGeometryReduction.lean: `sourceScalingUnits_subset_sourceHolomorphicHull`(94), `sourceHolomorphicHull_eq_closure`(108), `sourcePointVolume_scaling_le_of_hullVolume_le_imageVolume`(260), `sourceHullVolume_le_imageVolume_of_candidate`(278), `sourceLocalLogDegree_le_zero_of_mem_sourceHolomorphicHull`(297) | 已有（olean yes；hull≤image 仅条件形） |
| H5 AMPL 界/phase | CardAMPLThetaBoundSupply.lean: `CardAMPLThetaBoundSupply`(78), `realVolume_le`(94), `ofReal_le_theta_of_imageSet_lower`(101), `exists_hull_eq_ofReal`(109), `of_realVolume_le`(116), `nonempty_iff`(125); CardHullReal{EdgeNormalizationDichotomy,EdgeNormalizationReduction,FinitePhaseGate,GeneratorNonpositivity,GeometryGapCards,HaarDilationDocking,SignedLogVolume}.lean | 已有（olean yes） |
| HDD / 行列式张量 | HolomorphicHull/HullDeterminantLogVolumeReduction.lean: `HullDeterminantLogVolumeFrozenSpec`(123), `hullDeterminantLogVolumeFrozenSpec_holds`(153), `matrixLogDet`(173), `matrixLogDet_mul_posDef`(179), `_smul_posDef`(187), `_kronecker_posDef`(197), `_pow_posDef`(213), `packetDet_pos`(241), `packetLogVolume_eq_matrixLogDet`(249), `packetLogVolume_tensorPower`(302) | 已有（olean yes） |
| HDD 组装（paper-layer） | tmp/sheaf/xif/paper/S3182Cor312HullDetAssemblyActual.lean: `HullDetAssemblyInputs`(75), `Cor312HullDetConclusion`(91), `cor312_hullDet_conditional`(98), `cor312_fieldScaling_component`(110), `cor312DeepStepRows`(123) | 已有（olean yes, GREEN/CITABLE） |
| H7 / Ob9 层 | xif: `Indet06H7Ob9WiringActual`（H7Ob9IndetWiring/h7Ob9IndetWiring/h7Ob9_comparison_ind1_invariant/_ind2_invariant/_ind3_one_sided/h7Ob9ConsumerInterface, EXIT0 CITABLE）; `Hull08Ob9LogLinkActual`: `HullOb9Inputs`(58), `hull_ob9_interface`(66), `hull_ob9_repClass_congr`(86); `Hull10H7Ob9ConsumerActual`: `HullH7Ob9ConsumerInputs`(56), `hull10_h7ob9_consumer`(66), `hull10_logLinkIterate_eq`(86); `Hull12Ob9BoundTransferActual`: `hull12_upperBound_transfer`(52), `hull12_upperBound_transfer_base`(64); `Hull13TwoSidedBoundActual`, `Hull13H7Ob9ComparisonConsumerActual` | 已有（paper-layer；Hull08/10/12 olean yes；Hull13BothSidedBase 文件名不存在，改由 Hull13TwoSidedBound/H7Ob9Comparison 覆盖） |
| K1/K2 包约简 | Theorem311/: `SourceK1K2CardReduction.lean`: `labelledKummerIdentity`(55), `labelledKummerIdentity_map`(63), `_inverse`(66), `k1BoundaryOf_univRayPresentation`(134); `SourceK1K2KummerPrimeLift.lean`: `localKummerPolynomial_irreducible_of_prime_exponent`(94), `localKummerLift_injective_of_prime_exponent`(105), `labelledKummerIso_nonempty_of_prime`(131); `SourceK1K2HullPresentationModel.lean`, `SourceK1K2ActualTuplePacket.lean`(80/91/95/99), `SourceK1K2VolumeTranslationLaw.lean`(65/71/76/79/90), `SourceK1K2ArchUpperSemiBridge.lean` | 已有（olean yes） |
| Ind 1/2/3 | Theorem311/Indeterminacy/: `Ind1.lean`, `Ind1QuotientTransport.lean`, `Ind1Reduction.lean`, `Ind2.lean`, `Ind3UpperSemiConstruction.lean`: `outputImageFamily`(47), `_carrier`(51), `_mem_iff`(56), `_value`(66), `normalizedLogVolume_ind3_le_of_le`(74), `_upper`(85), `_le_iff`(96) | 已有（olean yes） |
| Multiradial / Thm 3.11 | Theorem311/: `SourceTheorem311Assembly.lean`: `SourceTheorem311Layers`(47), `assemble`(60), `t1/t2/t3_recovered`(81/85/89), `output_recovered`(93); `SourceArithmeticHolomorphicLanding.lean`, `SourceMultiradialTwoActionEquivalence.lean`, `SourceVerticalDThetaProjection`(`DThetaHodgeTheater`43) | 已有（olean yes） |
| StepXI 合同/义务 | Corollary312/StepXI/: `Contract.lean`(`StepXIContract/Cor312Conclusion/cor312Conclusion_of_contract`), `SourceSHETransportObligations.lean`: `SourceSHESquareSupply`(165), `sheStatement_evidence`(191), `sheSlot_evidence`(197), `sheSupply`(229), `oneColumnTheater_arithmetic`(257); `SourceProcessionStepXI.lean`(`routeWall`45/wall_dStage/source/target/output), `SourceSharedBoundary.lean`(`oneColumnTopStage_source_injective`88), `SourceLogShellMuNQuotientCarrier.lean`(`muNQuotient`66, `muNQuotientMap`70, ker 75/surj 80, `weightNLog_pow`106), `CertificateHullWiring.lean`(73/80/93/99/106), `FiniteCertificateBridge.lean`(17/29/45/52) | 已有（olean yes） |
| Cor312 → ABC | ABCBridge/Bridge/: `Cor312ToABCBridgeInterface.lean`(113/126/135/156/184 + abcConjecture 446), `ABCFrontier.lean`(reduce_realLine 268), `ABCFrontierReductions.lean`(clauses 77-243, reduce 256/273, bridge 294/307, abc 301); `IUTToABC.lean`(36/64); `Arithmetic/ABCHeightArithmeticWeightComparison.lean`(167) | 已有（olean yes） |
| Theta/Kummer 载体 | IUTII/Kummer/: `SourceThetaPilotIQContainment.lean`(possibleImage_subset 126, productMap 141); `SourceLogShellXMuPacket.lean`(87/93/99/105/125); `SourceLogShellIQTensorPacket.lean`(106/113/118/128/135/148); `AbsoluteKummerInjection.lean`(70/119); `AbsoluteKummerContinuity.lean`(33/74); `SourceThetaPilotIQContainment`; `SourceLogShellTensorLegCompletion.lean` | 已有（olean yes） |
| IUT I/II 基对象 | IUTI/HodgeTheater/HodgeTheaterCore.lean(`HodgeTheater`31, `HodgeTheaterLink`36, refl/symm/trans 49/54/59); IUTI/InitialTheta/SourceInitialThetaData.lean; IUTII/Frobenioid/PrimeStripsConstruction.lean(`FPrimeStripLink`46, refl 65/trans 75); IUTII/Theta/ThetaLinkAssembly.lean(`thetaLink`51, unitPower 57/embeddedUnit 66/generator 74); IUTII/Kummer/AbsoluteKummerContinuity | 已有（olean yes） |
| Stage4/mainline Frey | ABCBridge/Geometry/FreyOddReduction.lean(22/26/30/37/45), FreyConductor{TwoAdic,Odd}.lean, FreyTwoAdicMinimal*.lean, FreyDiscriminantRadical.lean, FreyLegendreComparison.lean; ABCBridge/Arithmetic/{ABCInvariant*,RationalLocalHeightDecomposition}.lean; f4b 相关 clauses 在 ABCBridge/Bridge/{Cor312PointwiseMembershipWeakening,ABCFrontier*}.lean | 已有（olean yes；f4b 为 clause/reduction 层，非 numMaxP 本体） |

## B. xif paper-layer 已有资产（文件簿记/paper 对象；非本轮新建）

| 对象 | 已有资产（file:decl） | olean |
|---|---|---|
| HullDetAssembly | S3182Cor312HullDetAssemblyActual: HullDetAssemblyInputs, Cor312HullDetConclusion, cor312_hullDet_conditional, cor312_fieldScaling_component | yes |
| H7/Ob9 | Indet06H7Ob9WiringActual, Hull08Ob9LogLinkActual, Hull10H7Ob9ConsumerActual, Hull12Ob9BoundTransferActual, Hull13TwoSidedBoundActual, Hull13H7Ob9ComparisonConsumerActual | Hull08/10/12 yes |
| H5 | Mzk1H5GapStatementActual（statement，含 OminusInverseNormalization 字段） | 需核（本清单以外） |
| 仓库搜索证据 | Mzk1RepoSearchEvidenceActual（A475 行表：Ominus=0 LF/ hmm）、Mzk1IUTIVReuseIndexActual、Mzk1PaperInputIndexActual、Mzk1Stage4GapRegistrationsActual | no（源存在） |
| f4b numMaxP | Mzk1NestedInductionActual: numMaxP(:612), numMaxP_image_ofFinite(:661), maxDeg/numMax(85/88); Mzk1F4bFiniteReuseActual: FiniteNumMaxStrictStatement(32) 等 | Mzk1NestedInduction yes；F4bFiniteReuse no |
| fixedBetaChoice | Mzk1StepProviderGapStatementsActual（StepProviderFixedBetaChoiceInput）；Mzk1StepProviderFromFixedBetaActual: stepProvider_of_fixedBeta(44) | no |
| ProblemDApplicability | Mzk1ProblemDApplicabilityActual: ProblemDApplicabilityData(11), card_ge_of_data(19), divisor_eq_of_data(21), ProblemDApplicabilityInput(22) | yes（DONE EXIT=0） |
| schemeSideMaps | Mzk1SchemeSideMapsActual(SchemeSideMapsData 36/schemeSideMapsDataOfBridge 45/sectionMap 55/placePoint 62); Mzk1SchemeSideBridgeActual(SchemeSideBridgeMaps 30/sectionMap_apply 47/placePoint_mem 52) | no（源仅存） |
| HTLink | Mzk1HodgeTheaterLinkLawsActual: structure HTLink(8), htRelRefl/Symm/Trans(16/18/20) | no |
| EtaleThetaKummerClass | EtTh01StatementActual（EtaleThetaKummerClass 等 statement 对象）、IUTExternal21ExtAliasesActual、EtFrd05IdsActual(30) | EtFrd05Ids/EtTh09Status yes |

## C. 真缺失短清单（仓库当前无实现；附证据）
1. **H5 O(-)^{-1} normalization on arithmetic line bundle**: LeanFormal/tmp/xif 全树无 Lean 定理/定义（`Ominus` 仅 xif statement 字段 + coord 文档；TauCeti Spin 文件为无关同名）。→ 缺。
2. **H5 hull log-volume ≤ image log-volume（无条件形）**: 仅条件判定 `sourceHullVolume_le_imageVolume_of_candidate`(CardHullRealGeometryReduction:278) 与必要方向 `sourcePointVolume_scaling_le_of_hullVolume_le_imageVolume`(260)；无无条件定理。→ 缺（条件形已有）。
3. （部分，不算完全缺失）**qPilotPreciseConstruction 单一命名对象**: LeanFormal/xif 无该名对象；内容分散于 `SourceLogShellXMuPacket` + `SourceThetaPilotIQContainment`（内容已有，命名/單一构造未建）。
4. （部分）**f4bNumMaxStrict 的严格 numMax 部分**: 有限部分 `numMaxP`(Mzk1NestedInduction:612) 与 `FiniteNumMaxStrictStatement`(Mzk1F4bFiniteReuseActual:32) 已有；严格（无限/一般）形式无。
5. （部分）**Hull13BothSidedBaseActual 文件名不存在**: 由 `Hull13TwoSidedBoundActual` + `Hull13H7Ob9ComparisonConsumerActual` 覆盖（two-sided 内容已有，命名文件缺）。

## D. 统计（各一行）
- 仓库已有（LeanFormal，olean yes）: 覆盖 12 组、约 80+ 声明（H5/H5-geom/AMPL/HDD-det/K1K2/Ind/Multiradial-Thm311/StepXI/Cor312-ABC/Theta-Kummer/IUTI-II-base/Frey-mainline）。
- 仓库已有（xif paper-layer，olean yes）: 9 个（S3182 HullDet、Indet06、Hull08/10/12、Hull13TwoSided/H7Ob9Comparison、Mzk1ProblemDApplicability、EtFrd05Ids、EtTh09Status、Mzk1NestedInduction）。
- 仓库已有（xif paper-layer，源仅存/未构建）: 10+ 个（SchemeSideMaps/SchemeSideBridge/HTLink laws/F4bFiniteReuse/Stage4GapRegistrations/RepoSearchEvidence/PaperInputIndex/IUTIVReuseIndex/StepProviderFromFixedBeta 等）。
- **真缺失（完全无实现）: 2 项**（H5 Ominus normalization；H5 hull≤image 无条件形）。
- 部分/仅接口/命名缺: 3 项（qPilotPrecise 单一对象、f4bNumMaxStrict 严格形、Hull13BothSidedBase 文件名）。
- 本轮：未写 Lean、未改 fragment、未加 DAG 节点/extra-targets、未碰 watchdog、未编译。
