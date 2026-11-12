# PRIOR-ART INDEX (仓库先例索引, durable memory)

> 规则(7.10, 强制): 任何 agent 写新 Lean 前必须: (1) 跑 tools/xif_deep_search.ps1 -Query '<精确类型/定理名>'; (2) 读本文件对应小节; (3) 批次报告第一行写 STEP 0 prior-art: queries -> hits -> reuse/adapt/none; (4) 新发现立即追加本文件(日期+file:line+一句话). 禁止重证已存在结果.

格式: - <gap> -> <file>:<line> <decl> (reuse|adapt|none|trap)

## A. 模型/构造/具体载体
- theater family (index=IntxInt, injective, links+laws) -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:122 sourceHaarActualPrimeStrip, :143 Theater, :151 PrimeStripEquiv, :213 TheaterLink, :224-284 laws, :288 Theater_injective, :322 Family (reuse)
- 模型 OriginalInput/ImageRealization/HaarData -> 同上 :346 sourceHaarActualOriginalInput, :374 sourceHaarActualImageRealization, :407 UnitRegion, :416 Data, :458 MinusOne, :462 StrictPoint (reuse)
- 具体 IQ 载体 interface + 5 unconditional inputs -> HolomorphicHull/IQCarrierConcreteModel.lean:193 interface, :230 logShellPoint, :303/:315 hunit, :346 hweightvol, :358 hsplit, :373 hptfin, :386 hpoint, :413 epsilonComparison, :431 epsilonComparisonAdditive (reuse)
- carrier bridge (旧尝试, 曾误标 MISSING) -> tmp/sheaf/xif/paper/S2586IQHullLogVolumeInstantiationActual.lean:32 S2586IQHullLogVolumeInterface (logVolume:=Measure.addHaar, unitRegion:=arithmeticTupleCanonicalUnitReference, hull:=rootNormHull, scaleShift:=id) (reuse/adapt)
- Haar 单位质量/平移载体 -> HolomorphicHull/HaarTranslateRealLineConsumerWiring.lean:127/132/140/165 (reuse)
- Haar 膨胀-收缩 log-volume 分解 -> HolomorphicHull/CardHullRealHaarDilationDocking.lean:178 (reuse)
- IQ HULL 接口 -> HolomorphicHull/SourceHullCompactnessReduction.lean:52 (reuse)
- ThetaPilotPoint/SourceImageRealization 定义 -> HolomorphicHull/SourceImageHull.lean:139, :161 (reuse)

## B. R1/M1/M2b/F4
- M1 contract/obstruction -> tmp/sheaf/xif/paper/S3133M1InjectionReductionActual.lean:55/79, S3133M1ContractObstructionActual.lean:56/67 (reuse)
- M1 concrete donor (tensorIndex:=Bad, prime match=5, closes TensorIndexPlaceCompatibility) -> S3133M1ConcretePrimeMatchActual (citable; remaining index identification class C)
- M2a CLOSED -> S3133M2aClosedActual + S3133M2aNormReductionActual
- M2b q-parameter convention -> IUT III corpus:10350; IUT I Def 3.1(b)/Ex 3.2(iv); IUT II Def 4.9(viii); in-model qVFamily:=model q => descent=rfl
- in-model Option-B adaptation -> S3133ExistingModelAdaptationActual (9 decls: TreeModelInput/Realization/HaarData, theta q=1, M1 datum, M2b rfl, BaseUnitScaling interface)
- in-model R1 composition (M1+M2b+baseUnit) -> S3133ModelRouteM1StatusActual, S3133ModelRouteM2bStatusActual, S3133ModelRouteR1StatusActual (probe trio)
- F4.a realified identification -> S3135RealifiedIdentificationActual; F4.b procession unit datum -> S3135ProcessionUnitDatumActual; F4(a)+(b)=>clause -> S3135F4BothByConstructionActual
- -1 非平凡 scaling 见证 mu((-1)O)=mu(O) -> S3135ModelSkeletonInterfaceActual (6 decls) + S3135TreeModelBaseUnitScalingActual; 单独 BaseUnit 文件已撤回 (trap)
- Fact prime 实例 -> LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:28-29; RationalCommonPrimeFinrank.lean:22 fact_prime_five

## C. Theta 侧 (V-form/rooted scaling)
- V-form canonical readout 初等化 -> S3132VFormScalingReductionActual (RootedScalingDecomposition; canonicalReadout_eq_weighted_scaling; ReducedVFormResidual; vformCanonical_of_reducedResidual) [IUT III Prop 3.9(i) 6838-6860, Rem 3.9.4, Rem 3.9.5(i)]
- R1 free (scalar:=exp(rooted log)), sharp residual = R2 exactly -> S3132RootedScalingDataTrivialActual + S3132ThetaSideSharpResidualReducedActual
- paper formula scalar p^(-sum c), hc DATA (not unconditional) -> S3132RootedScalingDataFormulaActual; prior art QVFamNormalizedGeneratorSupplyActual, BadPlaceRootHullScalingFormulaActual:87/113
- paper rooted hull formula -> BadPlacePaperRootThetaHullActual.lean:45/51/56/68/82/86/90; half-coefficient -> BadPlaceRootHullScalingFormulaActual.lean:64-117
- hull<=theta / certificate slot -> CertificateHullWiring.lean:99/106/155/173/199/204/272/347; CardAMPLThetaBoundSupply.lean:78/94/101/116/125/135/149/172/193 (adapt)
- q-side -> SourceQSideComparison.lean:88/96/108/125/140/170/184 (reuse)
- signed hull/image log-vol -> CardHullRealSignedLogVolume.lean:114/129/143/155/176/204/259
- matrix log-det scaling 律 -> HullDeterminantLogVolumeReduction.lean:123/153/173/179/187/197

## D. (b)/(c) (IUT IV §1/§2)
- (c) Gap-2 归约 -> LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:306 cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound (reuse; :55/:127/:359/:391)
- Gap-2 供给/形状 -> Cor312ComparisonGapSupplyLayer.lean:271; Cor312GapDictionaryLayer.lean:34/39/176-372/368; Cor312ToABCBridgeInterface.lean:70/248/332/426
- hunit 实际 D0 -> tmp/sheaf/xif/paper/S2722HunitDActual.lean:34/44/68; hsplit -> S2720BridgeHaarActual.lean:70; hptfin singleton-null (诚实: hval refuted, hpoint singleton-null 退化)
- unit-region bound 形状 -> HunitEpsilonTransferReduction.lean:62/70/90/103/118/141/166/188 (:90 恰是界形状; :166 frozen refutation)
- weighted average/(R4) -> IUTIV/Estimates/StepVProcessionAverage.lean:35/39/54/68/100/125; StepVDivisorAverage; StepVDistinguishedSlotAverage
- Thm 1.10 初等估计 e1-e6 -> IUTIV/Estimates/ElementaryEstimates.lean:76-146
- height/weight 函数层 -> IUTIV/Estimates/ArithmeticDivisorDegree.lean:1214/1221/1225/1310/1613; ThetaBoundToHeightWeight.lean:67
- (b) 归约 undilated=>field b -> S3131PaperRouteHeightReductionActual; (c) -> S3131PaperRouteRegionReductionActual
- (b) 精确剩余 -> S3131HeightVolumeDictionaryAttemptActual + S3135HeightWeightAtPaperActual
- (c) 精确剩余 (hull half 免费, remaining weight<=theta) -> S3135RegionRelativeIQActual + S3135RegionRelativeObligationActual

## E. 引用/论文
- [GenEll] Mochizuki Arithmetic Elliptic Curves in General Position, Okayama 52 (2010) 1-28; corpus papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt; Thm 2.1 (615-687) = proved equivalence/reduction (compactly bounded <=> general ABC), NOT ABC proof (class B)
- [Mzk1] Noncritical Belyi Maps (corpus text present; class B); [AbsTopIII] Topics in Absolute Anabelian Geometry III (Prop 5.8(ii) proved; class B)
- IUT III Prop 3.9 (proved, corpus 6838/6993); Rem 3.9.4 (~7151); Rem 3.9.5(i) hull:=lambda*O (7652-7680)
- IUT IV Thm 1.10 (p.1255/1363-1385), Thm A, Cor 2.2 (p.2426-2505), Cor 2.3 (§2 ~2330+) — all proved (class B formalization targets)
- vendor (source reference only, separate lake, cannot import) vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/: IUTStage1IUTIVAlgebra.lean:8056 height_le_weighted_logDiff_logCond_minus_lowerBound (+:8085), :9900 genEll_transfer (+:9919 compact_subset_theoremA); IUTStage1HodgeSHE.lean:3996/4017/5936/5970 logVolume_le; IUTStage1SourceCore.lean:1109/1121 container log-volume estimates; CorollarySchema.lean:28/41/55/63/66/77/85
- GenEll shadow (本仓库) -> S3132IVGenEllShadowAdapterActual.genEll_transfer

## F. 旧尝试/工具/陷阱
- 旧 paper-route -> tmp/sheaf/xif/paper/S2607HeightUpperTargetActual, S2720BridgeSkeletonActual, S2721BridgeSkeletonActual, S2721BridgeDataActual, S2722Gap2AssemblyActual, S2722HunitDActual, S2586IQHullLogVolumeInstantiationActual, S2595Dictionary*
- 归档 -> tmp/archive_sorry_20261028/, tmp/sheaf/gap-exploration-20261030/snapshots/
- 可 import 库 -> tmp/local-cft-port/ (PadicField/Brauer/Reciprocity/...)
- 搜索工具 -> tools/xif_deep_search.ps1 -Query '<regex>' [-MaxHits N]
- 陷阱: S3135ModelBaseUnitActual 已撤回; S3133ModelTheaterFamilyActual doc-only 不算证据; S3133Model* Sum-V 路由 superseded 不算; 旧引用 pins 13129 过期 (当前 registry **14041** frozen; gate 23066; record 18800; FINAL-ARTIFACTS 17816 sha EE328D9D; 第三次 re-pin 已完成; 用户指示不再中间 reopen, 只在论文级定理证出时更新一次)
- registry 状态: frozen at 14041 (第 3 次 Option-B closure 后; 用户指示暂停 reopen; 下一次仅在论文级定理证出时更新)


### 2026-11-11 (mainline, batch14/15 + paper-focus STEP 0)
- (b)/(c) reuse anchors -> tmp/sheaf/xif/paper/S3131Gap2AdditiveWiringActual.lean (data: gap-2 reduction :306 + hsplit :409 + hptfin :432 + pointBound :455 + approved additive input GapDictionaryLayer:372) (reuse; 未证 #checks 已移除)
- (c) aggregated status (proven/proved-degenerate/partial/added) -> S3131RegionStatusTableActual.lean (8 rows; NET (c) NOT DISCHARGED) (record)
- 旧 carrier/hunit wiring 复用 -> S3131OldCarrierBridgeReuseActual (S2586:32 lgpNativeIQInterface), S3131OldHunitDReuseActual (hunit actual D0; honesty: hval refuted/hweightvol open/hpoint degenerate) (reuse/adapt)
- certificate theta-slot -> S3131CertificateThetaSlotReuseActual (CertificateHullWiring:173/:199/:301 + CardAMPL) (reuse)
- (b) bridge-verified prior art -> S3131ThetaBoundToHeightWeightReuseActual (V2 data = heightWeightBound_of_normalizedVolumeComparison hypotheses; already used by cor312ToABCBridge_heightBoundV2) (reuse)
- concrete IQ interface reuse -> S3131IQCarrierModelInterfaceReuseActual (IQCarrierConcreteModel:193 interface) (reuse)
- STEP 0 deep search done 2026-11-11 (queries: UndilatedHeightBound|RegionRelativeToHullAndWeight|heightWeightBound_of_normalizedVolumeComparison|genEll_transfer|height_le_weighted_logDiff_logCond|GenEll -> LeanFormal 11 / paper 264 / gap-exploration 3 / vendor 10 / corpus 27) -> mostly already indexed; new file rows appended above.

## G. 2026-11-10 §7.10 deep-search additions (paper-level focus)

- (c) hull theta bound (citable, hull half free) -> LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:306 cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound (reuse; remaining = weight<=theta + hpoint/dictionary)
- hpoint/hweightvol concrete witnesses -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierConcreteModel.lean:346 hweightvol, :386 hpoint (reuse)
- (b) height<=volume shape -> tmp/sheaf/xif/paper/S3135HeightVolumeReuseActual.lean:16/21, S3135HeightWeightAtPaperActual.lean:28; vendor/IUTStage1/IUTStage1IUTIVAlgebra.lean:8056 height_le_weighted_logDiff_logCond_minus_lowerBound + :8085 (adapt; vendor cannot import - separate lake)
- (b) volume<=weight+thetaBound+D shape -> same S3135HeightVolumeReuse:16/21; thetaBound = hull logVolume (Cor312ToABCBridgeInterface.lean:362/436) (adapt)
- GenEll Theorem 2.1 -> corpus papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt:615-687; LeanFormal references 0 (only shadow field S3132IVGenEllShadowAdapterActual.lean:43 genEll_transfer) -> FORMALIZE statement (class B; genuine paper-level target)
- route bridges sameC/capsule-label/stage4-unit-map/invariance -> tmp/sheaf/xif/paper/S3137PaperRouteMapActual.lean, S3137PaperRouteFieldCRegionActual.lean, S3136ModelAssemblyPipelineActual.lean (adapt)
- post-freeze in-model R1 evidence (doc-only; no reopen) -> S3133ModelRouteM1StatusActual, S3133ModelRouteM2bStatusActual, S3133ModelRouteR1StatusActual, S3135TreeModelBaseUnitScalingActual (citable; probes trio)
- TRAP updates: S3135ModelBaseUnitActual WITHDRAWN (do not count); S3133ModelTheaterFamilyActual doc-only; S3133Model* Sum-V superseded; FINAL-ARTIFACTS current sha 48A24175B7C84FD3... (NOT EE328D9D); pins = registry FROZEN 14041 / gate 23066 / record 18800.


## G. abc batch-11 consume records (2026-11-10 05:45)
- (b) 归约复用 -> S3131PaperRouteHeightReductionActual:21/27; 消费记录 S3135PaperRouteHeightConsumeActual (Obligation) + S3135HeightWeightAtPaperActual:1 (paper 高度/权重特化)
- (c) 归约复用 -> S3131PaperRouteRegionReductionActual:20/27/43; 消费记录 S3135PaperRouteRegionConsumeActual; 具体实例 S3135RegionRelativeIQActual (hull<=theta+finiteness from CardAMPLThetaBoundSupply; 剩余 weight<=theta)
- [GenEll] 陈述形式 -> S3132IVGenEllShadowAdapterActual:23/39/43 (genEll_transfer 字段; corpus Thm 2.1 lines 615-687 class B); 消费记录 S3135GenEllConsumeActual
- hull_le_theta 接口等价 -> CertificateHullWiring.lean:45/90/99/106; 消费记录 S3135CertificateHullConsumeActual
- qpilot interface fill -> S3135TreeModelBaseUnitScalingActual (baseUnit=-1, norm one; INDEX.MODEL.stage4-unit-map-baseunit, Option-B complete per lattice)
- pins: registry frozen 14041; FINAL-ARTIFACTS sha 48A24175 (not EE328D9D); withdrawn/doc-only not counted: S3135ModelBaseUnitActual, S3133ModelTheaterFamilyActual, S3133Model* Sum-V

## 2026-11-10 05:30 — qpilot STEP 0 prior-art (paper-level focus: (c) weight<=theta, (b) two families, GenEll 2.1, route bridges)

Query: normalizedComparisonRegion|RegionRelativeToHullAndWeight|weight_le_theta|height_le_comparisonRegionVolume|GenEll|CardAMPLThetaBoundSupply|logShellPoint
Hits: LeanFormal 42, tmp/sheaf/xif/paper 453, gap-exploration 3, vendor 8, corpus 27.
PRIOR-ART lines (reuse/adapt):
- LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:53-57 -> REUSE: logShellPoint datum + normalizedComparisonRegion := scaleShift '' (unitRegion ∪ {logShellPoint}).
- LeanFormal/IUT/ABCBridge/Bridge/Cor312PointwiseResidualSupply.lean:12-14,172 -> REUSE: pointwise residual supplies (logVolume {scaleShift point} < top and toReal bound).
- LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean:133,195,203 and Cor312ComparisonGapReduction.lean:11-39 -> REUSE/ADAPT: gap supply layer + normalized region decomposition; direct prior art for (c) weight<=theta.
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply.lean:78-86 -> REUSE: CardAMPLThetaBoundSupply structure (theta bound slot, hull<=theta); FiniteCertificateLinkEvidenceWiring.lean:113 aligns hull_le_theta.
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierConcreteModel.lean:22,330,350 -> REUSE: concrete IQHullLogVolumeInterface + logShellPoint unit-region membership + normalizedComparisonRegion inequalities; the model carrier for (b)/(c).
- LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean:25,132-133 -> REUSE: F3a logShellPoint data record + cor312Gap1 declare the weight/region comparison frontier (including not_forall negative direction).
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullNormalizationConditionalClosure.lean:307-316 -> REUSE: source-hull normalization conditional closure using normalizedComparisonRegion.
- LeanFormal/IUT/IUTIV/Estimates/Section2.lean:5,36-38 -> REUSE as GenEll/Theorem 2.1 statement target (no LeanFormal references yet per directive).
- tmp/sheaf/gap-exploration-20261030 (3 hits) and vendor (8 hits) inspected: no additional applicable formalization beyond the above.
NET: for (c) weight<=theta use Cor312ComparisonGapSupplyLayer/Reduction + CardAMPL hull<=theta; for (b) height<=volume use Cor312PointwiseResidualSupply + Cor312ToABCBridgeInterface; GenEll Theorem 2.1 has corpus statement only (Section2.lean records lines L2329-3663), formalization not yet present -> next new work.

## 2026-11-10 05:45 hull update (STEP 0 batch6/7)
- (C) signed certificate shape -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiringSigned.lean:132 StepXIFiniteCertificateSigned (adapt: S3132ThetaSideCertificateSignedShapeActual)
- (C) hull_le_theta genuine measure-inclusion prior art -> LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullSignedCertificateNonvacuous.lean:20/86/103, FinitePlaceIQHullSignedCertificate.lean:15/89, FinitePlaceIQHullSharpUpperBound.lean:119/176/221, Volume.lean:160/167, ContractSourceReduction.lean:73/88, SourceFiniteRouteArithmetic.lean:320 (adapt; hθ slot nonvacuous)
- (C) iqHullCertificate consumers -> CardHullRealEdgeNormalizationDichotomy.lean:418/434, CardHullRealGeometryGapCards.lean:69, CardHullRealSignedLogVolume.lean:397/410, CertificateCThetaTransfer.lean:63/113, IQCarrierHaarData.lean:368, IQHullValueCarrierWiring.lean:119, SourceValueHullRealizationBridge.lean:47/80 (reuse for H4 adapter)
- (C) frozen obstacles -> CardQCMPComparison.lean:50-68 (q family arithmetic-only; target no object-level definition; real+finiteness empty premise space; hull_le_theta = registered certificate-hull/AMPL boundary) (trap/record)
- (C) stage4 gap2 wiring -> tmp/sheaf/xif/paper/S3136Gap2AdditiveWiringActual.lean:45 lgpSourceInterface (IQHullLogVolumeInterface on sourceHaarActualOriginalInput), :51 lgpSourceInterface_hunit (D0=0), :62 lgpGap2_of_additive (named inputs hmem, hadd, hline) (reuse/adapt for H4/H5 feeding)
- (C) hc generator supply -> QVFamNormalizedGeneratorSupplyActual.lean:66 qVFamNormalizedCoefficient, :72 generator_norm, :89 NormalizedGeneratorSupplyAt, :111 pos, :130 qVFamNormalizedGeneratorSupplyAt (adapt for H3: hc data = normalized generator supply)
- (D) (c) gap2 objects -> ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:306 cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound (reuse; hull half free)

## 2026-11-10 05:38 — GenEll P0 陈述层资产 + lattice ledger (lattice)
- GenEll00NamingActual (naming/coordination map), GenEll01BasicActual (PaperHeight/BDClassOn/CompactlyBoundedSubset; IsBDLe reuse), GenEll05Theorem21Actual (CaseI/CaseII; theorem21_i_implies_ii PROVED; Theorem21_ii_implies_i_required paper-input; Theorem21ReductionInputs 4 inputs), GenEll08MainReductionActual (GenEllMainReductionStatement/genEll_mainReduction_shape/GenEllIUTIVSection2Consumer) -> P0 陈述层 (reuse; owner mainline/abc/stage4)
- lattice GenEll ledger (CITABLE): GenEll10StatementLedgerActual (14-row statement ledger P0-P3, corpus 99-1425), GenEll11IndexIdsActual (19 INDEX.GENELL ids), GenEll12CitationRowsActual (21 citation rows: [GenEll]/[Mzk1]/[AbsTopIII]/IUT III Prop3.9+Rem3.9.4/3.9.5(i)/IUT IV Thm1.10+ThmA+Cor2.2/2.3/vendor), GenEll13DependencyMapActual (13-row dependency map + deep inputs [Mzk1]/Thm3.8/GRH) (reuse/adapt)
- GenEll05 theorem21_i_implies_ii = PROVED trivial direction (reuse; do not reprove); Thm 2.1 = reduction not ABC proof; deep inputs named not faked

## 2026-11-10 05:40 — [AbsTopIII] statement ledger + INDEX.ABSIII ids (lattice)
- [AbsTopIII] corpus papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt: sec0 graph 1269; sec1 Galois reconstruction 1442; sec2 arch 2523; sec3 Log-Frobenius 3280 (Def 3.1(iv) 3424-3520); sec4 arch 5284; sec5 global 6044; Cor5.2 6538; Cor5.5 7347; Def5.6 log-shells; Prop5.7 Local Volumes 7915; Prop5.8 Mono-analytic Reconstruction 8059; Cor5.10 Fundamental Properties 8494 -> AbsTopIII10StatementLedgerActual + AbsTopIII11IndexIdsActual (CITABLE; class C concrete-p-adic-formalizable vs D anabelian-deep-input)
- tree citations mapped: SourceEWeightedLogVolumeData:54/244, HaarTranslateRealLineLogCompatibility:6/10, CardHullRealGeometryGapCards:63/79, MonoAnalyticLogShellArchPsiCnsCalibration:19/36/50, SourceLogShellActionCompatibility:42/52, SourceLogShellTensorLegCompletion:35, SourceLogShellAbsTopIIIBridge:6/10/15, SourceThetaLinkGraphAutomorphismReduction:11, CardHullReal{GeneratorNonpositivity:47/59,EdgeNormalizationReduction:53/61/342,EdgeNormalizationDichotomy:14/70/481}, HaarTranslateRealLineConsumerWiring:23/31/124, HaarTranslateRealLineLogFrobeniusCompatibility:6, HaarTranslateRealLineInstance:57/182 (reuse/adapt)
- classification: Prop 5.7/Def 5.6/Cor 5.10/section 3 = C concrete-p-adic-formalizable (tree normalizations cite them); sections 1/5, Cor 5.2/5.5 = D anabelian-deep-input; Prop 5.8 = D with C p-adic shadow; sections 2/4 = B formalizable-partial (archimedean). No registry edits (frozen 14041).

## H. 2026-11-10 §7.10 AbsTopIII/Mzk1/GenEll audit precedents

- [AbsTopIII] Prop 5.7 (corpus 7915-7941) -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealEdgeNormalizationReduction.lean:53/61, CardHullRealEdgeNormalizationDichotomy.lean:14/70, CardHullRealGeneratorNonpositivity.lean:47/59, HaarTranslateRealLineConsumerWiring.lean:23/31 (reuse concrete normalization parts; deep anabelian = named input)
- [AbsTopIII] Prop 5.8 (corpus 8059) -> IUTII/Kummer/MonoAnalyticLogShellArchPsiCnsCalibration.lean:19/36 (explicitly NOT constructing Prop 5.8(v)); IUTIII/Theorem311/SourceEWeightedLogVolumeData.lean:54 (adapt; deep part named input)
- [AbsTopIII] Cor 5.10 (corpus 8494) -> HaarTranslateRealLineLogCompatibility.lean:6/10, HaarTranslateRealLineLogFrobeniusCompatibility.lean:6, HaarTranslateRealLineShellHomotopyRadialAngular.lean:5/12 (reuse/adapt)
- [AbsTopIII] Def 3.1(iv) (corpus 3424-3520) -> IUTII/Kummer/SourceLogShellAbsTopIIIBridge.lean:6/10/67/330 (reduction card; remaining equality registered)
- [AbsTopIII] Def 5.6 / section-0 graph (corpus 1269) -> IUTI/HodgeTheater/SourceThetaLinkGraphAutomorphismReduction.lean:11 (reuse/adapt; deep automorphism reconstruction named input)
- AbsTopIII statement rows -> tmp/sheaf/xif/paper/AbsTopIII02LocalVolumesActual.lean (5205B, 3 decls, CITABLE; sha BA87BF7F...), AbsTopIII06WeightedVolumeBridgeActual.lean (4647B, 6 decls, pending)
- GenEll P0 -> GenEll00NamingActual (CITABLE), GenEll01BasicActual (CITABLE), GenEll05Theorem21Actual (CITABLE 3037B version; extension in progress), GenEll06Section3StatementsActual (CITABLE 4481B sha 34921AD1...), GenEll07Section4StatementsActual (CITABLE 3741B sha 62C02C0B...), GenEll08MainReductionActual (CITABLE 2423B sha 073E147F...)
- [Mzk1] P2 -> Mzk1Section2StatementsActual (3617B, 3 decls, CITABLE), Mzk1ProvabilityClassificationActual (3102B, 4 decls, CITABLE); corpus Noncritical Belyi Maps.txt
- TRAP: GenEll01/05 abstract shape layer (X : Type; ht/logDiff/logCond) — paper-specific Def 1.2/1.5/Ex 1.3 not instantiated yet; track. GenEll05 regression during extension (EXIT=1 3759B; old CITABLE 3037B superseded). Pins registry frozen 14041 / gate 23066 / record 18800.


## G2. 2026-11-10 stage4 GenEll/Mzk1/AbsTopIII volume batch (STEP 0 records)

- STEP 0 deep search 1: 'Noncritical Belyi|Mzk1|GenEll06|GenEll07|IUTStage1IUTIVAlgebra|Theorem 3.8|Proposition 3.4|Corollary 4.3|GRH|Igusa' -> LeanFormal 9 / xif-paper 79 / vendor 15 / corpus 177; read index D/E/F/G. reuse anchors: S3131Mzk1StatementActual (statement wrapper), S3131GenEll* shape files, S1907SerreLargeImageActual (GenEll Thm 3.8 source form), corpus GenEll §§1-4, Mzk1 full text (398 lines).
- STEP 0 deep search 2: 'Local Volumes|localVolume|log-volume|arithmetic log-volume|p-adic volume|additive Haar|log-shell|Prop 5.7|Cor 5.10' -> LeanFormal 632 / xif-paper 1718 / archive 11 / gap-exploration 18 / vendor 171 / corpus 107. reuse anchors: LeanFormal/IUT/Foundations/Volumes/HaarLogVolume.lean:11-45 logClosedBallVolume/addHaar scaling; Foundations/Volumes/WeightedVolume.lean:20 WeightedValues; ABCBridge/Bridge/ThetaBoundToHeightWeight.lean; our S3136NativeHaarFamilyActual; tmp/local-cft-port PadicField; lattice AbsTopIII10StatementLedgerActual (C/D/B).
- NEW (stage4, 2026-11-10): GenEll06Section3StatementsActual (9 rows Lemma 3.1/3.2/Def 3.3/Rem 3.3.1/Prop 3.4/Lemma 3.5-3.7/Thm 3.8 + classification), GenEll07Section4StatementsActual (5 rows Lemma 4.1 GRH-condition named/Lemma 4.2/Cor 4.3/4.4 + classification), Mzk1Section1/2/3StatementsActual (Def 1.1/Cor 1.2/Lemma 2.1-2.4/Thm 2.5/Cor 3.1-3.2 with corpus line refs), Mzk1ProvabilityClassificationActual (classification; only GeometricCore expected deep residual), AbsTopIII02LocalVolumesActual (Prop 5.7 (i)(a)(b)(c)/(ii) + Cor 5.10 (i)(ii)(iv) C/D/B labels aligned with lattice ledger), AbsTopIII06WeightedVolumeBridgeActual (weighted log-volume def/monotonicity + CardAMPL bridge + correspondence rows) -> all queued; checker status recorded in ledger.
- OLD-ATTEMPT MINING (reuse; §7.9): S2586IQHullLogVolumeInstantiationActual:32 lgpNativeIQInterface (carrier bridge EXISTS); S2722HunitDActual:34/44/68 (hunit with actual D0; honesty flags); S2720BridgeHaarActual:70 hsplit; S2590SingletonNull; Cor312PointwiseResidualSupply.lean:198/:211 hptfin, :246 point-height dictionary, :308/:328 hpoint, :350 Cor312PointwiseResidualData, :409/:445 epsilonComparison composites (found via deep search; reuse; NOT discharge); Cor312ComparisonGapReduction:306/409/432/455/525/599; Cor312GapDictionaryLayer:34/39/368; CardAMPLThetaBoundSupply:78/94/116; CertificateHullWiring:173/199/301; StepVProcessionAverage:35/54/68/100; ElementaryEstimates:76-146 (e1-e6).
- TRAPS (current): registry FROZEN 14041; gates/record per index F; S3135ModelBaseUnitActual WITHDRAWN; S3133ModelTheaterFamilyActual doc-only; Sum-V superseded; no intermediate reopen/pin.


### 2026-11-11 (mainline, GenEll P0 batch)
- STEP 0 prior-art: queries GenEll|Theorem 2.1|noncritical Belyi|BDClass -> corpus lines 615-760 / 688-730 (ii)=> (i) chain) -> assets already indexed (S3131GenEll*/S3136BDClassChainTool/ArithmeticDivisorDegree/RationalPointDictionary/S3132IVGenEllShadowAdapterActual) -> reuse; new P0 files: GenEll00NamingActual, GenEll01BasicActual, GenEll05Theorem21Actual, GenEll06Section3StatementsActual (stage4), GenEll07Section4StatementsActual (stage4), GenEll08MainReductionActual (+ probe GenEllP0Probe) -> statement layer use
- GenEll05: theorem21_i_implies_ii PROVED; paper_epsilon_absorption PROVED; (ii)=> (i) = Theorem21_ii_implies_i_required + Theorem21ReductionInputs (a)-(d); single named Mzk1 input (stage4 Thm 2.5/Cor 3.2) to import when green; Thm 2.1 = reduction (NOT ABC proof).
- lattice GenEll ledger: GenEll10StatementLedgerActual, GenEll11IndexIdsActual (INDEX.GENELL), GenEll12CitationRowsActual, GenEll13DependencyMapActual (CITABLE).
## G. AG 基础设施 (Mathlib capability -> curve -> function field/divisors -> line bundles -> cohomology -> RR -> Serre -> pencil -> Mzk1 GeometricCore)
- Mathlib capability audit (lattice AG90) -> Mathlib/AlgebraicGeometry/{Scheme,Over,Properties,Fiber,Limits,Normalization,ValuativeCriterion}.lean (reuse AG01); FunctionField.lean:37 Scheme.functionField/:41 germ/:55/:65 injectivity/:148 fraction ring (reuse AG02); OrderOfVanishing.lean:35 ordHom/:52 ord (reuse AG02); RationalMap.lean (reuse AG03); Modules/Presheaf/Sheaf/Tilde.lean (partial AG03/AG04); Sites/ElladicCohomology.lean:75 (reference only; no coherent cohomology)
- AG03 divisors / AG04 line bundles+sections / AG05 cohomology / AG06 Riemann-Roch / AG07 Serre duality / AG08 basepoint-free pencil = TO BUILD (audited: Mathlib has NO divisor/RR/Serre/basepoint-free asset); AG09 Mzk1 GeometricCore = paper-input (corpus Noncritical Belyi Maps)
- lattice files (CITABLE): AG90MathlibAuditActual (12-row matrix), AG91AgIndexIdsActual (12 INDEX.AG ids AG00-AG10), AG92AgDependencyGraphActual (13-row chain -> GenEll05/IUT IV s2), AG93AgCitationRowsActual (10 Mathlib path/decl rows); ids INDEX.AG.ag00..ag10 (reuse/adapt/build)

- 2026-11-11: GenEll02bProofActual fixed (IsBDLe 3-arg witness C not -C; qualify S3136BDClassChainToolActual.IsBDLe; test-literal lists avoid `rfl` on huge literals - split chunks / length via decide on small lists) (reuse/adapt; EXIT=0 2114).

## H. GenEll P0 §1 statement+proof layer (abc, 2026-11-10 05:55)
- GenEll01BasicActual EXIT=0 (Def 1.2/1.5, Example 1.3; PaperHeight/LogDiff/LogCond, BDClassOn, CompactlyBoundedSubset; reuse S3131BDClassCompositionActual.IsBDLe)
- GenEll02Prop14Actual EXIT=0 (Prop 1.4 statement shape + elementary extractions; corpus 294-423)
- GenEll02bProofActual EXIT=0 (isBDLe_of_le_add_const; Prop 1.4(ii) extraction IsBDLe htL 0 zeroLocus^c; Prop 1.4(iv) extraction)
- GenEll03Prop16Actual EXIT=0 (Prop 1.6 statement IsBDLe htD logCondD UQ, corrected orientation; corpus 505-523)
- GenEll03bProofActual (pending) (Prop 1.6 from pointwise bound via isBDLe_of_le_add_const)
- GenEll04Prop17Actual EXIT=0 (Prop 1.7 statement shape corrected orientation; corpus 524-604)
- GenEll04bProp17ChainActual (pending) (assembly from two BD inputs + chain; anchors DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge / DifferentDegreeUpperBound)
- GenEll05Theorem21Actual EXIT=0 (mainline CaseI/CaseII shapes, theorem21_i_implies_ii)
- height/weight layer anchors: ArithmeticDivisorDegree.lean:1171 hTerm, :1214 heightWeight, :1221/:1225 sums; RationalPointDictionary Height.logHeight1; ThetaBoundToHeightWeight:67
- BD tool orientation note: S3136BDClassChainToolActual.IsBDLe f g F := exists C, forall x in F, g x - f x <= C (i.e. g bounded above by f); GenEll Prop 1.6/1.7 statements use this orientation (log-cond <=~ ht encoded as IsBDLe ht logCond).

- 2026-11-11: official 4-triangle/black-box alignment -> papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt §4 lines 443-572 (diagram 472-501), §2 lines 116-118; RIMS skeletal code not public, Stage 1 = 4th triangle only, Stage 4 external/machine. Used as paper-faithfulness reference (doc-only; no Lean import).

## H. 2026-11-10 stepxi AG infrastructure batch (Mathlib-based; §7.10)
- function field K(X) -> .lake/packages/mathlib/Mathlib/AlgebraicGeometry/FunctionField.lean:37 Scheme.functionField, :42 germToFunctionField, :51 Field instance, :65 germ injective, :148 IsFractionRing of affine open (reuse)
- order of vanishing -> Mathlib/AlgebraicGeometry/OrderOfVanishing.lean:35 ordHom, :52 ord, :64 ord_zero, :81 ord_mul, :88 ord_of_isUnit, :107 ord_add, :119 ord_le_smul (reuse)
- Weil divisor / O(D) / sections -> Mathlib ABSENT (AG00MathlibAuditActual.lean:44-49 lineBundle/coherentCohomology/riemannRoch/serdeDuality/genus all false; only Analysis/Meromorphic/Divisor unrelated) -> NEW first layer: AG02bPrincipalDivisorActual (WeilDivisor := codim-1 points -> Z, principalDivisor z := X.ord f z), AG03DivisorsSectionsActual (divisorSections Submodule of K(X) over Γ(X,U), CodimOneDVR hypothesis explicit), AG03bSectionsBasicActual (restrict/mono/unit)
- production AG affine-etale files (LeanFormal/IUT/Foundations/AlgebraicGeometry/*) -> none for curve divisors (reuse decision: none)
- completion/residue-field layer -> LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionLocalInputs.lean:204 (adapt, not needed first layer)
- postponed honestly: finite support of principal divisors, sum(principal divisor)=0 degree, Riemann-Roch (absent in Mathlib)

## I. 2026-11-10 stepxi first-triangle (Ind1,2,3) indeterminacy batch (§7.10; A35)
- (Ind1) -> LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1.lean:5 Audit.ind1 (pending); MultiradialOutputKernel.lean:15 Core.ind1, :38 Ind1Step; Ind1QuotientTransport.lean:52 generatedQuotientMap_ind1 (proved; quotient absorbs Ind1), :68 quotientClass_eq_iff_level_eq, :80 normalizedLogVolumeOnQuotient; SourceFiniteMultiradial.lean:20 core (ind1 := ind1Act), :25 ProcessionChoice.ind1Act; reuse, not re-proved
- (Ind2) -> Ind2.lean:5 Audit.ind2 (pending); Core.ind2; Ind2AlienCopySeparation.lean:56 ind2ShiftedCopy, :99 linkMap_injective, :122/:133/:145 secondLinkDescent, :191 preserves_volume, :207 zero shift = id, :217 zero link = diagonal; Ind1QuotientTransport.lean:57 generatedQuotientMap_ind2; reuse
- (Ind3) -> Ind3.lean:5 Audit.ind3 (pending); Core.ind3; Ind3UpperSemiConstruction.lean:47 outputImageFamily, :85 outputImageFamily_upper, :96 le_iff, :121 not_le_of_lt, :138 constructedOutputUpperSemi, :198 eq possibleImageUpperSemi iff level zero; UpperSemi.lean:18 UpperSemiCorrespondence; Ind3Reduction.lean:278 IsUpperSemi; reuse
- quotient/up-to -> ConcreteFiniteModelTransport.lean:377 GeneratedEqualityRelation, :386 generatedRelation_level_eq, :397 _of_level_eq, :416 generatedSetoid, :426 generatedQuotientMap; MultiradialOutputKernel.lean:139 GeneratedQuotient; new statement layer Indet01FirstTriangleIndActual + Indet02BPSMultiradialUpToActual (bpsToMultiradial/_ind1/_ind2/_eq_iff_level)
- BPS/0-column full poly-isomorphism (MHYY §4 472-501; IUT III 653-679 Fig I.6) -> formal counterpart = certified C3 closure S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds (reuse; pure-tensor level; no volume invariance claimed)

## 2026-11-10 05:50 — AG90/AG92 更正: SheafCohomology + 外部资产 (FLT/LANA/PRs/MHYY)
- Mathlib 更正（pinned 实际存在）: Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean（Basic: H, cohomologyPresheafFunctor, H.equiv0, H.map; Cech/MV）=> AG04/AG05 = PARTIAL-REUSE（不再写 'only ell-adic'）; Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:75 仅 ell-adic 参考
- 外部资产 FLT: tmp/external/flt-lean = local clone of github.com/anthropics/fermats-last-theorem (Apache-2.0; 1450 lean files under Definitions); key files confirmed: Def_AlgebraicCurve_{DivisorClassGroup,AdelicIndex,CechSectionsOfDivisor,SerrePairing,RiemannRochRows}.lean + Def_AlgebraicGeometry_{SmoothProperCurveBase,SmoothProperCurveFiniteMapData}.lean => AG03/AG04/AG05/AG06/AG07/AG08 ADAPT (source import? external lake project: adapt/copy definitions with license)
- Mathlib 上游 PR: #36218 merged (sheaf cohomology exact sequences) -> AG05; #43392 open (sheaves of modules cohomology API) -> AG04/AG05; #41621 open draft (conditional RR chi(O_X(D))=deg+chi(O_X)) -> AG06
- 论文/报告: MHYY Formalization of IUT (2026-04) papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt (roadmap Stage 1-5, four triangles BPS/etHT/dsc/HDD/SHE/IPL/APT/Ind1,2,3, Thm 3.11/3.11.5/Cor 3.12; kurims URL); LANA report papers/LANA_report_202607.pdf + text tmp/external/lana_report_202607.txt (50pp; §8 Thm3.11->Cor3.12 logic, §9 points to clarify, §10 Scholze-Stix) + github.com/katobungen/LANA_report_202607; Stoll Formalizing Heights talk; Cambridge Brauer/group cohomology Lean4 seminar; Zulip Belyi/Dessins (no Belyi formalization); chip-firing RR for graphs Lean4 arXiv 2606.16679 (RR combinatorial reference)
- lattice files updated (CITABLE): AG90MathlibAuditActual (13-row matrix; AG04/05 PARTIAL-REUSE, AG06/07 ADAPT, FLT local clone, PRs, context), AG91AgIndexIdsActual (16 ids incl. INDEX.AG.external-flt-repo / mathlib-sheaf-cohomology / upstream-prs / roadmap-context), AG92AgDependencyGraphActual (15-row graph with Mathlib-abstract-cohomology/FLT/PR nodes), AG93AgCitationRowsActual (14 citation rows). 无 registry edits (frozen 14041).
## 2026-11-10 05:55 hull AbsTopIII batch (STEP 0)
- [AbsTopIII] log-shell defs/±1 → LeanFormal/IUT/IUTII/Kummer/SourceLocalLogShellDatum.lean:32 sourceLogShellStar_eq_logShellScale; SourceLogShellCarrier.lean:176/182/186/190 (namespace LeanFormal.IUT.SourceLogShellDatum) → REUSE (AbsTopIII01LogShellActual/AbsTopIII04LogFrobeniusActual)
- [AbsTopIII] logShellScale def → LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean:191 def logShellScale (namespace LeanFormal.IUT.LocalFieldLogarithm) → REUSE
- [AbsTopIII] Prop 5.7 (i)(a)(b)(c) corpus 7915-7960; Cor 5.10 corpus 8494/8587-8610; Def 3.1(iv) corpus 3424-3470; Prop 5.8(i) 8059-8075; (ii) 8076-8096; Cor 5.5 7347-7390; §0 1269
- [AbsTopIII] concrete volume side → stage4 AbsTopIII02LocalVolumesActual (CITABLE 161805) + AbsTopIII06WeightedVolumeBridgeActual; lattice AbsTopIII10StatementLedgerActual (12 rows) → REUSE (coordination: hull = log-shell/Prop5.8(v)/Def3.1(iv); stage4 = volume side)
- [AbsTopIII] concrete finite log-volume → S3129IQHullLogVolumeSourceActual:151 sourceHullHaar_integralLogShell_eq_one + S3132ConcreteSourceNormalizationClosureActual sourceHullHaar_integralLogShell_toReal_eq_one → REUSE (AbsTopIII03Cor510Actual)

### 2026-11-10 stage4 Mzk1 proof batch + AbsTopIII01 fix
- Mzk1Lemma21Actual: belyi21_derivative PROVED (X^m(X-1)^n derivative identity), belyi21_derivative_root PROVED (root dichotomy over C) -> GenEll [Mzk1] Lemma 2.1 (b) core now formal, not paper-input; residual (c),(d) real inequalities.
- Mzk1Theorem25StatementActual: Thm 2.5 exact statement rows + Mzk1GeometricCoreStatement named (Riemann-Roch/Serre duality absent in Mathlib) + reduction architecture rows; do not fake GeometricCore.
- AbsTopIII01LogShellActual FIX (shehdd request): lowercase absTopIIILogShellAnchor refs -> AbsTopIIILogShellAnchors; EXIT=0.

## H2. GenEll P0 §1 abc completion (2026-11-10 06:00)
- GenEll01bHeightLayerActual EXIT=0: tree height layer hTerm/hNon/hArc/hBox nonneg (Prop 1.4(ii) lower bound at ArithmeticDivisorDegree:1171/1177/1214/1220-1236); citations list.
- GenEll09BDToolsActual EXIT=0 + probe: isBDLe_add, isBDLe_of_le, isBDLe_add_const_left, isBDLe_neg_swap — BD chain tools for mainline Thm 2.1 (ii)=>(i).
- GenEll04cDifferentInputsActual EXIT=0: Prop17DifferentTheoryInput (exact paper input registration) + assembly from two BD inputs; anchors DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge / DifferentDegreeUpperBound.
- GenEllP0AbcStatusActual (pending): P0 §1 abc status Obligation for mainline.
- Orientation note (again): S3136BDClassChainToolActual.IsBDLe f g F := exists C, forall x in F, g x - f x <= C; GenEll Prop 1.6 = IsBDLe htD logCondD UQ; Prop 1.7 first = IsBDLe (logDiffY-logDiffZ) (logCondE-logCondD) UYQ.

## H3. GenEll P0 §1 abc completion 2 (2026-11-10 06:10)
- GenEll01cHeightMulEstimatesActual EXIT=0: reuse ArithmeticDivisorDegree Lemma 1.3(iv) hNon_mul_le/hArc_mul_le/hBox_mul_le as s3135_hBox_mul_le_reuse / s3135_paperHeight_mul_le / s3135_hNon_mul_le_reuse / s3135_hArc_mul_le_reuse; height product subadditivity wiring for Prop 1.4(i)/(iii) use.
- GenEll02cFinitenessInputActual EXIT=0: Prop14FinitenessPaperInput exact class-B paper-input registration (corpus 323-427 Silv1 Thm 2.1 style) + extraction to HeightBoundedPointsFinite.
- Remaining GenEll §1 named inputs now exactly: Prop 1.4(i) tensor-additivity at the height layer (tree gives only subadditivity 1.3(iv), which is the used direction) + Prop 1.4(iv) finiteness (registered class B).

## 2026-11-10 05:59 — hull execution assets bound into lattice INDEX rows
- AbsTopIII hull (CITABLE, hull 05:45/05:55): AbsTopIII01LogShellActual 163075 (Def5.6/Prop5.8(v) elementary log-shell reuse), AbsTopIII03Cor510Actual 162050 (Cor5.10(i) concrete finite log-volume PROVED), AbsTopIII04LogFrobeniusActual 162648 (Def3.1(iv) dictionary), AbsTopIII05ReconstructionInputsActual 161981 (DEEP inputs named, none proved) -> INDEX.ABSIII.hull.01-logshell/.03-cor510/.04-logfrobenius/.05-deep-inputs (lattice AbsTopIII10/11 rows 16)
- Theta H3-H6 slots (CITABLE): S3132RootedCoefficientCorrectionActual 162986 (H3 e=1 correction), S3132ThetaSideHullSlotWiringActual 161243 (H4 hull<=theta slot), S3132ThetaSideQSideSlotWiringActual 161517 (H5 q-side slot), S3132ThetaSideCertificateSignedShapeActual 161511, S3132ThetaSideComparisonRegionBundleV2Actual 163220, S3132ThetaSideRemainingHypothesesRecordActual 161139 (H1-H6 record; pin 14041) -> INDEX.ThetaSide.h3-correction/h4-slot/h5-slot/cert-signed/bundle-v2/remaining-hypotheses (lattice S3137ThetaSideRootedScalingNotesActual rows 14)
- hull audit cross-checks: S3167AbsTopIIIBatchAuditActual / S3168AbsTopIIICompleteAuditActual (CITABLE decl/sha lists) cited as provenance. No registry edits (frozen 14041).
## 2026-11-10 06:10 hull AbsTopIII batch2 (STEP 0)
- p_v-adic scaling (Prop 5.7(i)(b)/Cor 5.10) -> S3137LogShellHaarLogVolumeScalingActual:46 localLogVolume, :51 log_measure_integralLogShell_eq, :61 log_measure_prime_smul_integralLogShell, :85 localLogVolume_prime_smul_integralLogShell, :96 packetNormalization..., :109 finrank_one -> REUSE (AbsTopIII08PvAdicScalingActual)
- Theta-side p_v scaling -> S3137ThetaHullVolumeScalingActual:51 thetaPilotHull_measure_lt_top, :59 thetaPilotHull_log_measure_prime_smul, :70 thetaPilotHullLogVolumeReal_eq_actualRegion -> REUSE (AbsTopIII09ThetaHullScalingActual)
- volume<->log-shell bridge rows -> stage4 AbsTopIII02LocalVolumesActual (statement ledger) + AbsTopIII06WeightedVolumeBridgeActual (LGPWeightedVolumeBridge) + hull AbsTopIII01/03 -> REUSE (AbsTopIII07VolumeLogShellBridgeActual)
- endgame H1-H6 rows (corrected H3 wording pasted by mainline into ENDGAME-DEPENDENCY-LEDGER) -> S3132ThetaSideEndgameRowsActual (pin 14041)

### 2026-11-10 stage4 Mzk1 proof batch-2 + AbsTopIII volume side + Height/ported asset records
- Mzk1Lemma23Actual: explicit lambda construction PROVED finite complex case (minDist/eps/lam; dist_alpha_lam_ge); reuse as class-A fragment.
- Mzk1Cor31Cor32Actual: Cor 3.1/3.2 statements + reduction plan rows (from Thm 2.5).
- Mzk1Lemma21Actual: derivative identity + root dichotomy PROVED (earlier).
- AbsTopIII07NormalizedLocalVolumeActual: concrete mu_k(O_k)=1 PROVED (normalizedHaar_unitBall; completionNormalizedHaar_unitBall on CommonPrimeCompletion). Hull re-anchor request answered (decl names sent).
- AbsTopIII08PvAdicScalingActual / AbsTopIII09ThetaHullScalingActual: p-adic and theta-hull scaling re-exports from S3137 (PROVED tree).
- New asset records: Mathlib.NumberTheory.Height.{Basic,EllipticCurve,Northcott,Projectivization} (importable, not yet used); ported FLT (FiniteMapData:19, RiemannRochRows:19-47, SerrePairing, CechSectionsOfDivisor, DivisorClassGroup, AdelicIndex) status PENDING adaptation; TauCeti closure in progress per Lead (tmp/external/ported/tauceti2). Use for GeometricCore/Thm 3.8 when green.
- GenEllThm38HeightBoundsActual: physical-layer record for Thm 3.8 effective bounds (23040 identity PROVED as Nat arithmetic after import fix; height assets/paper-input split).

## I. [ExpEst] object layer (abc, 2026-11-10 06:20)
- STEP 0: query ExpEst|explicit estimate|PNT|prime number theorem|Chebyshev|arithmetic divisor|log-diff|3332|23040 -> hits (LeanFormal 25, tmp paper 105, vendor 22, corpus 50) -> REUSE: IUTIV/Estimates/ElementaryEstimates.lean:51/63/76/88/101/121/128/146 (iutIVThm110_e1..e6 PROVED, class A), Section1.lean:23-26 + Section2.lean:16-19 (explicit PNT/Chebyshev forms = class B paper inputs; Mathlib has PNT asymptotics only, no explicit constants).
- ExpEst00NamingActual: naming record Obligation.
- ExpEst01StatementLedgerActual: class A vs class B statement ledger (B1 explicit PNT upper form; B2 prime reciprocal-sum bound; B3 Chebyshev theta explicit bounds).
- ExpEst02ElementaryEstimatesActual: class A re-exports s3135_expEst_e1..e6_reuse + sum lemmas; class B registrations ExpEstPNTUpperPaperInput / ExpEstPrimeReciprocalSumPaperInput.
- No re-proof; no registry edit; frozen 14041.

## J. 2026-11-10 stepxi EtTh / Frobenioid statement layer (§7.10; external-object targets)
- EtTh theta quotient (A, proved) -> LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean:1 thetaDerivedSubgroup, :4 thetaCommutatorKernel, ThetaQuotient, EllipticAbelianization, thetaToElliptic(+_surjective), ModLThetaQuotient/modLThetaProjection(+_surjective), modLThetaToElliptic(+_surjective) (reuse)
- concrete etale-theta bridge -> LeanFormal/IUT/IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean:44 sourceModel := concreteStageModel; packet_rationalPrime_eq_five (reuse)
- concrete Frobenioid boundary (A) -> LeanFormal/IUT/IUTII/Frobenioid/ConcreteSourceFrobenioidBridge.lean ConcreteSourceFrobenioidBoundary + concreteSourceFrobenioidBoundary(l) + boundary_cStage/place/model/model_input/kernel, concrete_place_*, source_stage_base_connected, concreteStageModel : Iut.FrobenioidPresentation (reuse)
- model Frobenioid (A) -> Iut.Foundations.SourceModelFrobenioidPresentation.frobenioidPresentation [IsConnected D] (+ RationalNaturality/ZeroEvaluation) (reuse)
- Frobenius action assets -> IUTII/Frobenioid/Example36FrobeniusValueAction.lean, Example36LogShellFrobeniusAction.lean, Example36PrimeStripDivisorFrobenius.lean, Example36FrobenioidTransport.lean, DivisorialMonoidMinimalReplacement.lean (reuse/adapt)
- corpus anchors: [EtTh] Prop 1.1 l.784 / Lemma 1.2 l.1147 / Prop 1.3 l.1169 / Prop 1.4 l.1338 / Prop 1.5 l.1401 / Thm 1.6 l.1514 / Thm 1.10 l.1979 / Prop 3.2 l.5422 / Prop 3.4 l.5657; [FrdI] Props 1.4-1.11 l.1109-1599; [FrdII] Thm 1.2 l.376 / Prop 1.5 l.584 / Thm 2.4 l.818 / Prop 3.4 l.1446
- new statement layers (citable): EtTh01StatementActual, EtTh02DeepInputsActual (deep inputs proved:=false), EtTh03TreeReuseActual, EtTh04RouteWiringActual, Frd01StatementActual, Frd02ReuseAuditActual, EtFrd00Step0Actual, EtFrd05IdsActual; probes _EtThFrdProbe EXIT0 165942, _S3171BatchProbe EXIT0 164512
- LEAD NOTE (Mathlib/external coverage, to include in next STEP 0): Mathlib.AlgebraicGeometry.EllipticCurve.* (Weierstrass/Affine Point/Formula/DivisionPolynomial/Jacobian/Reduction/NormalForms), Mathlib.NumberTheory.Height.*, Mathlib.CategoryTheory.Sites.SheafCohomology.{Basic,Cech,MayerVietoris}, Mathlib.RingTheory.Valuation/DedekindDomain/AdicValuation, Mathlib.NumberTheory.Chebyshev.primeNumberTheorem; tmp/local-cft-port LocalClassFieldTheory 105 files; ported FLT/TauCeti (AG_TAUCETI_*/AG_FLT_*) -> prefer import before writing new defs

## 2026-11-10 06:45 — qpilot asset audit (Lead-provided external Lean inventory)

Reuse-first asset list verified by Lead; recorded for AG/GenEll streams:
- Pinned Mathlib directly usable: Mathlib.AlgebraicGeometry.EllipticCurve.* (Weierstrass/Affine Point/
  Formula/DivisionPolynomial/Jacobian/Reduction/NormalForms); Mathlib.NumberTheory.Height.{Basic,
  EllipticCurve,NumberField,Northcott,Projectivization}; Mathlib.CategoryTheory.Sites.SheafCohomology.
  {Basic,Cech,MayerVietoris}; Mathlib.RingTheory.Valuation/DedekindDomain/AdicValuation;
  Mathlib.NumberTheory.Chebyshev.primeNumberTheorem. -> REUSE (do not rebuild EC/height/PNT/SheafCohomology).
- tmp/local-cft-port: LocalClassFieldTheory 105 files + eight lake libs (PadicField/Reciprocity/
  ClassFieldAxiom/Galois/Herbrand/Brauer/ContinuousKummerTheory); CFT/local-field/Brauer layer mostly
  complete -> CHECK BEFORE WRITING.
- kbuzzard/ClassFieldTheory (lean 4.36.0-rc2, 105 files): overlaps our LocalClassFieldTheory port;
  port ONLY missing pieces after diff (skip if Tate cohomology/IsNonarchimedeanLocalField already present).
- daira/CompElliptic (lean 4.30, 41 files): SKIP (Mathlib EC stack covers; computable wrapper unnecessary).
- FLT/TauCeti lines unchanged: qpilot flat AG_FLT_* adaptations (DivisorClassGroup/AdelicIndex/
  Repartitions/CoherentBaseChange) + port trees tmp/external/ported/{flt,flt_th,flt_test,tauceti2}.
## 2026-11-10 06:20 hull [EtTh] batch (STEP 0)
- [EtTh] odd theta series -> LeanFormal/IUT/Foundations/Theta/OddTheta.lean:75/80/84/88/94/98/103/126/211 (reuse; AbsTopIII... EtTh01OddThetaSeriesActual)
- [EtTh] Prop 1.4(ii) shift law -> OddThetaShift.lean:14 oddTheta_shift (PROVED in tree; IMPORT BLOCKED: OddThetaTermAlgebra olean absent) -> EtTh02ShiftLawActual records anchors only
- [EtTh] nonvanishing/quotient eval -> OddThetaNormalization.lean:14/29/45 + OddThetaNonvanishing (PROVED; same import blocker)
- [EtTh] theta graphs/quotients -> IUTII/Theta/EtaleThetaQuotient.lean:29-58 (algebraic layer only; geometric/etale realization later obligation) -> EtTh03EtaleThetaGroupActual (reuse: kernel containment/normal, Tate surjectivity/kernel)
- [EtTh] Tate direction -> EtaleTateDirection.lean:17/20/24/28/32/35/39/51/54 (reuse)
- [EtTh] q-pilot identification -> IUTIII/Corollary312/ArithmeticQPilotGlobalNormalization.lean (fibers/degrees only; identification NOT established = frozen) -> EtTh04 interface + EtTh05 class-B rows

## J. IUT 外部对象 (Lead 用户总目标; INDEX.IUTEXTERNAL.*; 无 registry edits, frozen 14041)
- Ref list (MHYY Formalization of IUT (2026-04) Stage 4 corpus 121-124 + bibliography 627-690): [pGC]/[GeoAn]/[AbsAnb]/[NCBel]/[AbSc]/[SemiAn]/[QuCnf]/[CbGC]/[Config]/[FrdI-II]/[EtTh]/[GenEll]/[NodNon]/[AbsTopI-III]/[ExpEst]; ids INDEX.IUTEXTERNAL.* + alias INDEX.EXT.<ref>.<nn> (IUTExternal10IndexIdsActual; owners per coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md)
- citation rows (IUTExternal11CitationRowsActual): MHYY Stage4 corpus 121-124 + bibliography 627-690; per-ref paper/year; classes A/B/C/D, deep inputs named
- asset map (IUTExternal12AssetsMapActual): repo bases + TauCeti/FLT/Mathlib + owners; **TauCeti 本地克隆 tmp/TauCeti 已确认 (Apache-2.0 LICENSE; 20990 lean files)**，含 FieldTheory/FunctionField/** (Belyi/{Basic,BranchPoints,Bundled,Conjugation,GaloisAction,Polynomial,Radical}, Divisor/**, RiemannRoch/** 含 Pencil.lean, Repartition/**, Place/**) 与 AlgebraicGeometry/WeilDivisor/** (Scheme/{LineBundle,Picard,RiemannRoch/** ,SerreDuality,PrincipalParts/Cohomology,EulerCharacteristic,GlobalGeneration,LinearSystem}) + AlgebraicGeometry/LineBundle/SerdeDuality => AG03-AG08 + [NCBel] Belyi 基础设施 REUSE/ADAPT（独立 lake，不可直接 import，照 Apache-2.0 attribution 适配；勿盲目整仓 port）
- FLT: tmp/external/flt-lean (Apache-2.0) + 已 port tmp/external/ported/flt{,2} (源码级) + 可引用 flat AG_FLT_* (DivisorClassGroup/Repartitions/AdelicIndex/CoherentBaseChange/TwoChartCech/CechSectionsOfDivisor); 优先用 flat 可引用集，避免重复 port
- proof-status 维度 (Lead PRIORITY): IUTExternal20ProofStatusActual 自底向上 13 行（曲线/函数域 -> 除子 -> Čech H0/H1 -> RR -> Serde -> Belyi/FiniteMapData -> GenEll -> AbsTopIII -> EtTh/Frd -> IV §1 -> AG 适配层 -> layer-2），每行带 STATEMENT-ONLY / CLASS-A PROVED / COMPLETE-PROOF CITABLE / CLASS-B NAMED(+DEEP) + 源码路径/AG_* 层/checker 状态
- stepxi 新 ids: S3171IdsActual (INDEX.IUTIV.Thm110.*; SHA 6A53C7E6), EtFrd05IdsActual.etFrdIds (INDEX.ETTH/FRD; SHA F36D3C4A), GenEll14P3Wiring/AG04FiniteDivisor/AG04bResidueField/Indet05RouteMultiradialClass
## 2026-11-10 06:35 hull AbsTopIII14 + checkpoint (STEP 0)
- field-scaling mu_k formula -> LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean:25 measure_prime_smul_finiteDimensional (any set), :54 log_measure_prime_smul_finiteDimensional -> REUSE (AbsTopIII14FieldScalingActual: proves log mu(p^n*O_K) = -n*finrank*log p under mu(O_K)=1; residue form -n*f*log p; m_k^n = p^n*O_K unramified identification NAMED REMAINDER, not claimed)
- EtTh anchor batch -> OddTheta.lean:75/80/84/88/94/98/103; OddThetaShift.lean:14 (IMPORT BLOCKED: OddThetaTermAlgebra olean absent); OddThetaNormalization:14/29/45; EtaleThetaQuotient:29-58; EtaleTateDirection:17-54 -> EtTh00-EtTh05 (records/reuse; no re-proof)

## K. 2026-11-10 stepxi AG bottom-up / GeometricCore / canonical ports (§7.10)
- Mathlib coverage (verified in checkout): AlgebraicGeometry/EllipticCurve/{Weierstrass,Reduction,NormalForms,ModelsWithJ,IsomOfJ,VariableChange,LFunction}; NumberTheory/Height/{Basic,NumberField,EllipticCurve,MvPolynomial,Northcott,Projectivization}; CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}; RingTheory/Valuation/Basic(+...); NumberTheory/Chebyshev (single module) (reuse; DivisionPolynomial/Jacobian/AffinePoint NOT separate modules)
- canonical FLT/TauCeti ports (qpilot registry coord/EXTERNAL-PORT-REGISTRY.md): tmp/external/ported/flt_core (SerrePairing/weilDualityAdelic/cechRiemannRoch/SmoothProperCurveFiniteMapData), flt_test (canonical divisor/Kaehler/RR-space), tauceti_rr (RiemannRoch/Pencil/Genus, Differential/CanonicalDivisor, WeilDivisor/SerdeDuality, Belyi/Basic) -> reuse when promotions green; adapted Cech canonical: tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor
- promoted CITABLE (qpilot): AG_FLT_PromotionActual 8 decls (degree_add/zero/mem_degZero_iff/isPrincipal_iff_mem/ell_nonneg/lSpace_mono/adeleBdd_mono/place_deg_nonneg); DivisorClassGroup (72), AdelicIndex (68), Repartitions, CoherentBaseChange
- A-class completion (stepxi): EtTh05FrobenioidBoundaryActual (concreteSourceFrobenioidBoundary), EtTh06ThetaQuotientActual (EtaleThetaQuotient; pre-realization honest scope), Frd03ConcreteModelActual (concreteStageModel : Iut.FrobenioidPresentation)
- AG05/06 (Cech/H0/H1 = L(D) on covers; divisor/degree/Pic/ell/adeleBdd consumers), AG08ProofStatusTableActual, GeomCore01StatementActual ([Mzk1] Thm 2.5: basepoint-free pencil + finite map to P1 + ramification data) -> statement/A-reuse layers queued
- TRAP update: stepxiAGRRFinishActual = duplicate FLT port; STOPPED per Lead/qpilot de-dup (not counted)

## 2026-11-10 06:36 — EtTh05/06 + Frd03 (stepxi class-A assets, citable)
- EtTh05FrobenioidBoundaryActual (SHA 90E8F2EC), EtTh06ThetaQuotientActual (5AD15457), Frd03ConcreteModelActual (30D03FDA), EtFrd06Ids2Actual.etFrdIds2 (A6FDE1C9) -> INDEX.EXT.EtTh.05/06, INDEX.EXT.FrdI-II.03 (alias rows pending compile); AG08ProofStatusTableActual (pending) records canonical-port ownership qpilot + deprecated stepxiAGRRFinishActual; dispatcher backlog 463 (queue saturated, no failures).
## 2026-11-10 07:45 hull H4/H2 gate closure (STEP 0)
- H4 certificate wiring -> CertificateHullWiring.lean:106/155/272; CardAMPLThetaBoundSupply.lean:78/94/116/125; ContractSourceReduction.lean:73/88; CardQCMPComparison.lean:50-68 (frozen boundary) -> ADAPT (Hull04CertificateWiringActual, value-layer wiring PROVED; numerical boundary class-B)
- H2 concrete weighted identity -> S3132VFormScalingReductionActual (ReducedVFormResidual/vformCanonical), S3132RootedScalingDataFormulaActual (formula scalars/paper gap), S3132ThetaSideSharpResidualReducedActual (sharp residual = R2), BadPlacePaperRootThetaHullActual:56/68 -> REUSE (Hull05WeightedIdentityActual: hull05_concreteRow complete-proof row from hc + PaperRootHullFormulaGap + scalar-match)
## 2026-11-10 08:12 hull S3182 Cor 3.12 hull+det assembly (STEP 0)
- Cor 3.12 assembly -> Hull04CertificateWiringActual (H4), Hull05WeightedIdentityActual (H2), AbsTopIII14FieldScalingActual (field scaling), S3132ConcreteSourceNormalizationClosureActual (source volume/log readout) -> REUSE (S3182Cor312HullDetAssemblyActual: real assembly, every input consumed; deep steps IPL/SHE/APT as named interface rows)
## 2026-11-10 08:35 hull Hull06 det tensor H5 row (STEP 0)
- H5 det/lambda-O bookkeeping -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean:123 frozen spec, :153 holds, :173 matrixLogDet, :179 matrixLogDet_mul_posDef, :187 matrixLogDet_smul_posDef, :197 matrixLogDet_kronecker_posDef -> REUSE (Hull06DetTensorActual: re-exported det scaling/mul laws; O^x-stabilization and O(-)^{-1} normalization recorded as named class-B gaps)
## 2026-11-10 08:42 hull S3182 consumed by stepxi S3180 final (consumer event)
- S3182Cor312HullDetAssemblyActual.cor312_hullDet_conditional consumed in S3180 final theorem conditionalAssembly_with_hullDet (M := M) (I : HullDetAssemblyInputs M) : Cor312HullDetConclusion M I.theta ∧ Cor312Conclusion (toContract H hqneg) ∧ ABCConjecture; all HullDetAssemblyInputs fields consumed inside S3182; no consumer-side adapter needed. S3180 final EXIT0 176409, checker CITABLE 11 decls; probe 176455; ids S3180Mzk1IdsActual EXIT0 176502 CITABLE.
## 2026-11-10 12:24 hull EtTh08 + Hull07 (resume batch) (STEP 0)
- theta transformation/quotients -> EtaleThetaQuotient:29-150 (proved), EtaleTateDirection:17-54, OddTheta:75-220 -> REUSE (EtTh08ThetaTransformationActual; OddThetaShift:14 + OddThetaNormalization:29/45 stay class-B because OddThetaTermAlgebra.olean absent)
- H6 x Mzk1 interface -> GenEll10bH6Mzk1WiringActual:35/43/54/63 + S3182Cor312HullDetAssemblyActual -> REUSE (Hull07H6InterfaceActual; GeometricCore single named hypothesis, no closure)
## 2026-11-10 12:41 hull H7/Ob9 + H5 gaps (STEP 0)
- H7/Ob9 log-link compatibility -> Indet05RouteMultiradialClassActual:40-113; Indet06H7Ob9WiringActual:47-106 (authoritative H7Ob9IndetWiring/h7Ob9IndetWiring/projections) -> REUSE (Hull08Ob9LogLinkActual class-level Indet05 consumer; Hull10H7Ob9ConsumerActual consuming Indet06 wrapper)
- H5 class-B gaps -> CardHullRealGeometryReduction:94 sourceScalingUnits_subset_sourceHolomorphicHull, :108 sourceHolomorphicHull_eq_closure; HullDeterminantLogVolumeReduction:483 detTensorPowerBookkeeping_scalarLogDegree, :501 hullLogVolumeRay, :505 mem_hullLogVolumeRay_iff -> REUSE (Hull09H5GapsActual: O^x-stabilization REUSED-PROVED; det bookkeeping/ray reused; full paper normalization + hull<=image named class-B)
## 2026-11-10 12:49 hull Hull10 (H7/Ob9 consumer of Indet06) (STEP 0)
- H7/Ob9 consumer -> Indet06H7Ob9WiringActual:47-106 (authoritative wrapper fields ind1_invariant/ind2_invariant/ind3_one_sided/logLinkIterate) + S3182 -> REUSE (Hull10H7Ob9ConsumerActual: every Indet06 field consumed in hull10_h7ob9_consumer; deep arbitrary-iterate Ob9 class-B named)
## 2026-11-10 13:09 hull EtTh09 (STEP 0)
- theta shift-law corollaries -> EtTh08ThetaTransformationActual (ThetaShiftData); OddThetaShift:14 / OddThetaNormalization:29/45 (class-B import-blocked) -> REUSE (EtTh09ThetaShiftCorollariesActual: shift laws a=0,1,-1,2 + normalized quotient a=1, class A; analytic law class-B named)
## 2026-11-10 13:34 hull EtTh10 (STEP 0)
- mod-l quotient laws -> EtaleThetaQuotient:62-140 (thetaPowerKernel/thetaCommutatorKernel/ModLThetaQuotient/modLThetaProjection/modLEllipticProjection/modLThetaToElliptic_mk) -> REUSE (EtTh10ThetaQuotientLawsActual: definitional composite forms + power-kernel containment + class law)
## 2026-11-10 18:25 hull Hull11 H6 upgrade + EtTh11 realization rows (STEP 0)
- H6 upgrade -> Mzk1Thm25WiringActual:104-161 (Thm25WiringRecord/thm25_wiring/thm25_of_22_24_and_geometricCore), Mzk1GChoiceScaleActual:233 scale_realHypotheses_exists (discharged A160), GenEll10bH6Mzk1WiringActual:35-71, S3182 -> REUSE (Hull11H6Mzk1UpgradeActual: 2.2/2.4/GeometricCore named; no closure)
- EtTh realization rows -> EtaleThetaQuotient:29-160 + EtTh10 -> REUSE (EtTh11ThetaRealizationRowsActual: power-kernel level anti-monotonicity PROVED; projection surjectivity re-exports; realization class-B named)
## 2026-11-10 18:50 hull GenEll15/15b/16 GeometricCore assembly (STEP 0)
- GeometricCore statement/recast -> Mzk1GeometricCoreRealStructureActual (Mzk1FiniteMapData/Witness/Recast over ported flt_th FiniteMapData) + GeomCore01/03 + Mzk1Theorem25StatementActual placeholder -> REUSE/ADAPT (GenEll15GeometricCoreAssemblyActual: precise statement schema + explicit-data recast; placeholder replacement pending owner approval)
- RR/Serde/Cech -> AG_FLT_ProvedTheoremsPromotionActual (CITABLE 3: promotion_serrePairing_bijective_and_flip_bijective / promotion_weilDualityAdelic_of_isAlgClosed / promotion_cechRiemannRoch_of_genusReached, COMPLETE ported proofs) -> CONSUMED (GenEll15bRRConsumptionActual; separate file due flt_core vs flt_test namespace clash)
- Belyi existence -> tmp/external/ported/tauceti_belyi_core/TauCeti/Algebra/Polynomial/Belyi.lean:285/:317 + CriticalValues.lean (FRESH EXIT=0) -> CONSUMED (GenEll16BelyiExistenceActual: BelyiPolynomialCertificate PROVED from ported Belyification theorems)
## 2026-11-10 19:20 hull EtTh13 (STEP 0)
- mod-l projection factorization -> EtaleThetaQuotient:62-140 + EtTh11 (power-kernel anti-monotonicity) -> REUSE (EtTh13ModLFactorizationActual: l1 | l2 => modL theta/elliptic quotient factorization + composition identities, class A)
## 2026-11-10 19:32 hull Hull12 (STEP 0)
- Ob9 one-sided upper-bound transfer -> Indet05 routeMultiradial_ind3_possibleImage_upper + Indet06 H7Ob9IndetWiring + S3182 -> REUSE (Hull12Ob9BoundTransferActual: class A one-sided transfer of upper bounds from (Ind3) iterate back to base; deep arbitrary-iterate Ob9 class-B named)
## 2026-11-10 19:44 hull GenEll17 + Hull13 (STEP 0)
- GeometricCore(iii) polynomial->scheme bridge -> GenEll16BelyiExistenceActual (algebraic Belyi PROVED, ported FRESH) + Mzk1GeometricCoreRealStructureActual (ported flt_test FiniteMapData) + AG_FLT_FiniteMapDataPromotionActual (flt_th alias, cited only) -> REUSE/ADAPT (GenEll17BelyiPairConversionActual: bridge finiteMap+degree_eq consumed; three conditions named; BelyiPair deferred per A197)
- Ob9 one-sided comparison consumer -> Hull10 (H7Ob9 wiring consumer) + Hull12 (bound transfer) + S3182 -> REUSE (Hull13H7Ob9ComparisonConsumerActual: Cor312 conclusion AND base upper-bound transfer; all fields consumed)
## 2026-11-10 20:30 hull canonical H-preservation + BaseProvider (STEP 0)
- H-preservation canonical -> Mzk1Lemma22HypPreservationActual (rows1-5 PROVED), Mzk1Lemma22HypPreservationSeparationActual:76 hyp_separation (PROVED separation; canonical route), Mzk1BelyiCanonicalActual, Mzk1GChoiceScaleActual -> REUSE (Mzk1Lemma22HypPreservationCanonicalActual: FULL preservation assembled)
- Base provider -> Mzk1Lemma24BaseCaseActual.s3135_base_case_shape (PROVED rational) -> REUSE (Mzk1Lemma24BaseProviderActual: same explicit q over C, rational base lift)
