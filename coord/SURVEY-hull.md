# SURVEY-hull — IUT III Cor 3.12 前置对象：现有资产调研 (A470)

日期: 2026-11-11 02:4x (+08:00) 作者: hull（单写者文件；只读调研，不写 Lean、不建节点）
目标第一句: 从基础三公理（propext, Classical.choice, Quot.sound）无条件构建 IUT 3.12 的全部前置对象并证明 abc 猜想。

## 0. 调研来源（全部只读）
- coord/REPO-ROUTE-INDEX.md + coord/repo-route-index-data.json（IUTIII 31 rows；citable 字段）
- coord/SKELETON-IUTIII.md（190 文件/187 olean；树资产与声明/证据）
- coord/MASTER-SKELETON.md（L3/N1-N10/E-rows 映射）
- dag/THEOREM-DAG.md（节点证据行）与 dag/declaration-dag.json（844 nodes / 1145 edges，merged 16）
- dag/nodes/*.json（已冻结的对象级 milestone/leaf 节点，共 90 个文件）
- coord/target-chain.iut-skeleton.json（32 nodes / 50 edges）、target-chain.iut-pre-abc.json（42 nodes / 44 edges）、target-chain.iutiii.json（125 nodes / 74 edges）
- coord/uncovered-leanformal-triage.hull.tsv（20 行）、coord/SKELETON-GAPS.md
- LeanFormal/IUT/IUTIII 实际文件与声明 grep；.lake olean 存在性
- papers/motizuki_corpus（IUT III §0-§3, Thm 3.11, Cor 3.12, §4）

## 1. 表：论文对象 → 现有 Lean 资产 → 证据 → 现有 DAG 节点 id → 状态

状态缩写: PROVED=有证明/EXIT0；TREE_ASSET=olean 已建、接口级；COND=条件式；NAMED=具名缺口；DEF=定义层；GAP=仅有占位/缺口。

### 1.1 Cor 3.12 / Theorem 3.11 层
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|1|Cor 3.12 statement (hull+det/log-volume bound)|Corollary312/Comparison.lean::cor312Conclusion_of_contract；Routes.lean::Cor312RouteCertificate/.conclusion|OLEAN_FRESH（route index row；对比 wrapper 已证）|iut-skeleton:Cor312; iutiii:IUTIII.COR312.TARGET; IUTIII.COR312.WIRING|COND（statement 层已建；无条件链未闭合）|
|2|StepXI contract（q/θ/target signed + ipl/she/apt evidence）|StepXI/Contract.lean::StepXIContract, Cor312Conclusion, cor312_of_constructed_stepXI, q_positive_of_constructed_stepXI|OLEAN_FRESH|iut-skeleton:StepXI; iutiii:IUTIII.STEPXI.CONTRACT; iutiii:IUTIII.STEPXI.CONTRACT.CONSTRUCTION|DEF（构造 Obligation 为 NAMED）|
|3|Step (xi-a)(xi-b)(xi-c) paper obligations IPL/SHE/APT|Corollary312/Obligations.lean::ipl, she, apt（记录 pending）；StepXI/APT.lean, IPL.lean, SHE.lean|OLEAN_FRESH（obligation 记录）；paper 内容未证|iut-skeleton:IPL; iut-skeleton:SHE; iut-skeleton:APT; iutiii:IUTIII.STEPXI.OBLIGATIONS; n8-group5-ipl-she-apt (topo: open)|NAMED（记录层 PROVED，数学内容 NAMED）|
|4|StepXI parametric / source reduction / certificate-hull wiring / theta packet / log-shell muN|StepXI/ParametricStepXI.lean; ContractSourceReduction.lean; CertificateHullWiring.lean; ThetaPacketBridge.lean; SourceLogShellMuNQuotientCarrier.lean|OLEAN_FRESH（tree assets，已建）|iutiii:IUTIII.STEPXI.PARAMETRIC; ...CONTRACT_SOURCE_REDUCTION; ...CERTIFICATE_HULL_WIRING; ...THETA_PACKET_BRIDGE; ...LOGSHELL_MUN|TREE_ASSET|
|5|Theorem 3.11 source assembly（H1/H2,LGP,P1P2,hull/det normalization）|Theorem311/SourceTheorem311Assembly.lean；SourceTheorem311ReferenceContract.lean|OLEAN_FRESH（conditional assembly PROVED，MASTER N9）|iut-skeleton:Thm311; iutiii:IUTIII.THM311.SOURCE_ALGORITHM_INTERFACE; n8-group4-theorem311-multiradial (target proof_checked partial)|COND|
|6|multiradial algorithm output object（Output）|Theorem311/Output/MultiradialAlgorithm.lean::multiradialAlgorithm；MultiradialAlgorithmReduction/GeneralRouteNormalForm.lean|OLEAN_FRESH（route index: MultiradialAlgorithmReduction decls applyRoute_ind1_commute 等）|iutiii:IUTIII.THM311.OUTPUT_ALGORITHM; n8-group4-theorem311-multiradial|TREE_ASSET|
|7|two-action equivalence / arithmetic-holomorphic landing（Thm 3.11 anchors）|SourceMultiradialTwoActionEquivalence.lean；SourceArithmeticHolomorphicLanding.lean；Corollary312/APT.lean 消费|OLEAN_FRESH|iutiii:IUTIII.THM311.TWO_ACTION; iutiii:IUTIII.THM311.ARITH_HOLO_LANDING|TREE_ASSET|
|8|Cor312 → ABC bridge interface（3.12 的消费者）|ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean::Cor312ToABCBridgeInterface, cor312ToABCBridge_abcConjecture, cor312ToABCBridge_heightBound|OLEAN_FRESH（route index；THEOREM-DAG T1）|iut-skeleton:TargetABC; T1-cor312-abc-bridge; cor312-conditional-abc; n8-group6-hull-degree (target, open)|COND（F4/F5 字段 NAMED）|
|9|Cor312 ⇔ upper gap（S2717）|tmp/sheaf/xif/paper/S2717Cor312FullTargetActual.lean::S2717UpperGap:81, PaperCor312Full:103, S2717_full_iff_hupper:185|paper-layer（EXIT0 历史；THEOREM-DAG e-deep:E5.s2717 CONDITIONAL）|e-deep:E5.s2717; iut-skeleton:hCor312; iut-skeleton:hSlack|COND|
|10|Cor312 comparison gap reduction/supply|ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:128/141/152/167/198/232/272/306/367; Cor312ComparisonGapSupplyLayer.lean|OLEAN_FRESH（tree）|e-deep:E5.comparisonGaps (NAMED); iut-skeleton:ClassB|COND/NAMED|

### 1.2 H5（O^× hull）层
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|11|H5 O^×-hull/log-volume 接口（imageSet/hull/logVolume/scaleShift/unitRegion）|HolomorphicHull/SourceHullCompactnessReduction.lean::IQHullLogVolumeInterface, imageSet_logVolume_le_hull:88, hull_logVolume_lt_top:95, lower_bound_and_finiteness:104, singletonRealWitness:112, iqHullLogVolume:148|OLEAN_FRESH（route index row; SKELETON §2.3）|iutiii:IUTIII.HULL.SOURCE_COMPACTNESS; iut-skeleton:H5; e-deep:E2.hullClosureLaws; e-deep:E2.hullRayLaws; n8-c7-holomorphic-hull|TREE_ASSET|
|12|H5 class-A: scaling units ⊆ hull；hull = closure|CardHullRealGeometryReduction.lean:94 sourceScalingUnits_subset_sourceHolomorphicHull, :108 sourceHolomorphicHull_eq_closure|OLEAN_FRESH（route row）|iutiii:IUTIII.HULL.CARD_GEOMETRY; e-deep:E2.H5framing (PROVED)|PROVED（在 OriginalInput 载体上）|
|13|H5 hull 体积有限性 / 实表示|SourceHullInterfaceDischarge.lean::hull_logVolume_realRepresentation:85, haarContractionInterface:109, hull_logVolume_lt_top:149, ValueHullCompactnessInput:205, sourceHullVolume_lt_top_of_compactnessInput:223, iqHullInterfaceDischarge:252|OLEAN_FRESH|iutiii:IUTIII.HULL.SOURCE_INTERFACE_DISCHARGE; n8-c9-hull-carrier-compatibility（obstruction: degree-faithful 时 hull=top）|COND（compactness input NAMED；C9 反例）|
|14|H5 hull ≤ image-volume（class-B）|tmp/sheaf/xif/paper/Hull09H5GapsActual.lean（行记录）；Mzk1H5GapStatementActual.lean::OminusInverseNormalization|paper-layer（EXIT0）；THEOREM-DAG e-deep:E2.h5Gap NAMED|e-deep:E2.h5Gap (NAMED); HULL.H5.WRAPPER|NAMED|
|15|H5 O(-)^-1 normalization on arithmetic line bundle（class-B）|tmp/sheaf/xif/paper/Mzk1H5GapStatementActual.lean::OminusInverseNormalization（行记录）|paper-layer（EXIT0）|e-deep:E2.h5Gap; HULL.H5.WRAPPER|NAMED（无 arithmetic line-bundle API）|
|16|H5 normalization/region（scaleShift 归一化比较区域）|ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:128 cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union, :152, :306|OLEAN_FRESH|e-deep:E5.comparisonGaps; n8-group6-hull-degree|COND/NAMED|
|17|H5 R9 点成员/射线（downRay, valueForm, hull-ray）|CardHullRealR9PointMembershipAudit.lean（olean YES）；tmp/…/Mzk1R9PointMembershipConsumerActual.lean; Mzk1R9HullConsumerActual; Mzk1R9HullRayBundleActual; Mzk1R9HullRayLatticeActual; Mzk1TreeR9HullRayActual|olean YES + probe/EXIT0（我们的 R9 consumers PROVED）|iutiii:IUTIII.HULL.R9_AUDIT_GAP (PROVED); iutiii:IUTIII.HULL.R9.AUDIT_CONSUMER; iutiii:IUTIII.HULL.R9.RAY.BUNDLE (PROVED); IUTIII.HULL.R9.RAY.LATTICE (PROVED); e-deep:hull.Mzk1R9* (PROVED)|PROVED（属性层）/TREE_ASSET|
|18|Hull/AMPL theta bound supply（hull≤theta）|HolomorphicHull/CardAMPLThetaBoundSupply.lean::CardAMPLThetaBoundSupply, realVolume_le, ofReal_le_theta_of_imageSet_lower|OLEAN_FRESH（route index；covered E-EXISTING-CLOSURE-MAP）|无专属节点（可挂 iutiii:IUTIII.HULL.CARD_GEOMETRY 或 HULL.H5.WRAPPER）|TREE_ASSET|
|19|Source hull 体积 = image 体积 的判定/反例|CardHullRealGeometryReduction.lean:152 sourceHullVolume_eq_imageVolume_iff, :162/:181/:278, :200/:213/:230 反例|OLEAN_FRESH|e-deep:E2.h5Gap; n8-c9-hull-carrier-compatibility|TREE_ASSET（含反例，不改题目）|

### 1.3 HDD / determinant tensor 层
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|20|HDD hull/det 分解 ((hull+det) o dsc)|paper 对象；tmp/sheaf/xif/paper/S3182Cor312HullDetAssemblyActual.lean::HullDetAssemblyInputs, Cor312HullDetConclusion；Hull06DetTensorActual.lean|paper-layer EXIT0|iut-skeleton:HDD (DEF); PAPER.S3182.COR312_HULLDET (CONDITIONAL); HULL.E.ASSEMBLY|DEF（分解定理未证）|
|21|determinant line/tensor + matrixLogDet 记账|HullDeterminantLogVolumeReduction.lean::HullDeterminantLogVolumeFrozenSpec:123, hullDeterminantLogVolumeFrozenSpec_holds:153, matrixLogDet/packetLogVolume_eq_matrixLogDet:249, :173-256|OLEAN_FRESH（route row; SKELETON）|iutiii:IUTIII.HULL.DET_LOG_VOLUME (TREE_ASSET); iut-skeleton:HullDet (COND); e-deep:E2.detScalingLaws; e-deep:E2.detInvLaws（均 CONDITIONAL）|PROVED（frozen spec）/COND（additivity）|
|22|det tensor multiplicativity/additivity per packet|同上 matrixLogDet laws；Hull06DetTensorActual（class-A）|OLEAN_FRESH + paper-layer EXIT0|PAPER.S3182.COR312_HULLDET; HULL.E.ASSEMBLY|PROVED（bookkeeping）/COND（tensor 分解）|

### 1.4 H7/Ob9 两层
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|23|H7/Ob9 interface + one-sided bound|tmp/…/Hull08Ob9LogLinkActual.lean::hull_ob9_interface; Hull12Ob9BoundTransferActual.lean::hull12_upperBound_transfer|paper-layer EXIT0；THEOREM-DAG|e-deep:E3.ob9Interface (PROVED); e-deep:E3.oneSided (PROVED); HULL.H7.OB9.WRAPPER; iut-skeleton:H7Ob9|PROVED（接口/单向）|
|24|two-sided bound（ob9 both-sided）|Hull13TwoSidedBoundActual.lean::hull13_twoSided_bound；Hull13H7Ob9ComparisonConsumerActual.lean::hull13_h7ob9_comparison|paper-layer EXIT0；THEOREM-DAG|e-deep:E3.twoSided (PROVED); HULL.H7.OB9.WRAPPER|COND（依赖 named deep inputs）|
|25|deep Ob9 both-sidedness / arbitrary-iterate independence (named)|Hull13TwoSidedBoundActual.lean::HullH7Ob9TwoSidedInputs；Mzk1Hull13BothSidedBaseActual.lean::HullH7Ob9BaseTwoSidedInputs, base_lower_bound, hull13_baseTwoSided（DONE0）|paper-layer EXIT0/probe；THEOREM-DAG e-deep:E3.deepOb9 NAMED|e-deep:E3.deepOb9 (NAMED); e-deep:E3.baseTwoSided (PROVED); HULL.H7.OB9.BUNDLE; IUTIII.HULL.H7.OB9.BUNDLE (GAP)|NAMED（显式 base_lower_bound 假设）|
|26|H7/Ob9 sandwich laws / iterate bound|tmp/…/Mzk1H7Ob9SandwichLawsActual.lean::hull13_twoSided_lower_projection, hull13_twoSided_sandwich；Mzk1Hull13GreenConsumerActual；Mzk1Hull7Ob9BundleActual|paper-layer EXIT0（THEOREM-DAG E3.sandwichLaws PROVED）|e-deep:E3.sandwichLaws (PROVED); iutiii:HULL.H7.OB9.BUNDLE|PROVED（条件投影）|

### 1.5 Indeterminacy 1/2/3
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|27|Ind1 obligation（quotient compatibility）|Theorem311/Indeterminacy/Ind1.lean::ind1（Audit 记录 pending）；Ind1Reduction.lean::generatedQuotientMap_eq_of_ind1Step, Ind1Setoid, ind1QuotientMap；Ind1QuotientTransport.lean|OLEAN_FRESH（route rows；route-index 标注 NONE covered → 覆盖缺口）|iut-skeleton:Ind1; iutiii:IUTIII.IND1; iutiii:IUTIII.THM311.IND_OBLIGATIONS|TREE_ASSET（kernel）；paper NAMED|
|28|Ind2 obligation（second link, alien copies）|Ind2.lean::ind2；Ind2Reduction.lean::Ind2AlienLink, linkMap_ind1Step/ind2Step, secondLinkDescent；Ind2AlienCopySeparation.lean|OLEAN_FRESH（route rows）|iut-skeleton:Ind2; iutiii:IUTIII.IND2; IUTIII.THM311.IND_OBLIGATIONS|TREE_ASSET；paper NAMED|
|29|Ind3 obligation（upper-semi）|Ind3.lean::ind3；Ind3Reduction.lean::PossibleImage, instMembership, instPreorder；Ind3UpperSemiConstruction.lean|OLEAN_FRESH（route rows）|iut-skeleton:Ind3; iutiii:IUTIII.IND3; IUTIII.THM311.IND_OBLIGATIONS|TREE_ASSET；paper NAMED|
|30|Ind1/2/3 paper obligations pending records|Ind1.lean/Ind2.lean/Ind3.lean（Audit.Obligation records）|OLEAN_FRESH|iutiii:IUTIII.THM311.IND_OBLIGATIONS (PROVED records)|NAMED（内容）|

### 1.6 K1/K2 packet 层
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|31|K1/K2 packet construction/realization/descent|Theorem311/SourceK1K2Construction.lean, SourceK1K2Realization.lean, SourceK1K2ActualTuplePacket.lean, SourceK1K2ValueMapEntry.lean, SourceK1K2VerticalRealization.lean|OLEAN_FRESH|iut-skeleton:K1K2; n8-group2-log-k1k2 (target); n8-s3-c2-k1k2 (leaf, no_go)|TREE_ASSET（milestone open）|
|32|K1/K2 packet degree ledger|SourcePacketDegreeLedger.lean（olean YES）|olean YES（tree asset；此前无 olean 已补建）|iutiii:IUTIII.THM311.PACKET_DEGREE_LEDGER_GAP (PROVED); n8-s3-t11-packet (no_go)|TREE_ASSET/PROVED|
|33|K1/K2 card reduction（labelled Kummer identity）|SourceK1K2CardReduction.lean::labelledKummerIdentity, labelledKummerIdentity_map, labelledKummerIdentity_inverse|OLEAN_FRESH（route index row；olean YES）|iutiii:IUTIII.THM311.K1K2_CARD_GAP (PROVED); iut-skeleton:K1K2|TREE_ASSET/PROVED|
|34|K1/K2 hull presentation adoption|SourceK1K2HullPresentationModel.lean, SourceK1K2HullPresentationAdoption.lean, SourceK1K2HullPresentationPacketInstance.lean|OLEAN_FRESH|无专属节点（可挂 iut-skeleton:K1K2 / HULL.E.ASSEMBLY）|TREE_ASSET|
|35|K1/K2 volume translation law / Kummer prime lift|SourceK1K2VolumeTranslationLaw.lean; SourceK1K2KummerPrimeLift.lean; SourceK1K2KummerSlotSeparation.lean|OLEAN_FRESH|无专属节点|TREE_ASSET|
|36|Ind3 scaling audit of K1/K2|SourceK1K2Ind3ScalingAudit.lean|OLEAN_FRESH|无专属节点（挂 IUTIII.IND3 / K1K2）|TREE_ASSET|

### 1.7 multiradial algorithm / Steps (i)-(xi) 输入输出对象
| # | paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|37|Step (i)-(ii): D-Θ / H1/H2 construction|SourceDThetaConstruction.lean; SourceH1H2Construction.lean; SourceH1H2OriginalArrows.lean|OLEAN_FRESH|n8-group4-theorem311-multiradial（消费侧）|TREE_ASSET|
|38|Step (iii)-(iv): θ-link compatibility / IUTII link|SourceLogShellMuNQuotientCarrier.lean；tmp/…/Mzk1IUTIIILinkActual.lean::IUTIIToStepXILink（real SourceLogShellDatum + explicit ipl/she/apt evidence）；tree 无 IUTII→IUTIII import 边|OLEAN_FRESH + EXIT0（typed link PROVED 条件式）；SKELETON GAP1|iutiii:IUTIII.IUTII_LINK_GAP (COND); iutiii:IUTIII.IUTII_LINK.SOURCEDATA.ROUTE (COND); n8-t11-theta-to-iq (statement_compiles, named); n8-group2-log-k1k2|COND/NAMED|
|39|Step (v)-(vi): log-shell / volume transfer|SourceLogShellFamilyDependent.lean; SourceLogShellMuNQuotientCarrier.lean；iuti-ii 的 LogShell 资产|OLEAN_FRESH|iutiii:IUTIII.STEPXI.LOGSHELL_MUN; iut-pre-abc:LogShell.I/pStar/invariants/logFrobenius|TREE_ASSET|
|40|Step (vii)-(viii): procession / column carrier identification|SourceProcessionStepXI.lean; SourceProcessionStepXIMinimalForm.lean; SourceColumnCarrierIdentification.lean; SourceAdjacentColumnProcessionIsomorphism.lean|OLEAN_FRESH|iutiii:IUTIII.STEPXI.PARAMETRIC（部分）; iuti-ii:ThetaLink.procession（iut-pre-abc）|TREE_ASSET|
|41|Step (ix)-(x): finite certificate bridge + hull wiring|FiniteCertificateBridge.lean; CertificateHullWiring.lean; CertificateHullWiringRealization/Signed.lean; HolomorphicHull.SourceHullInterfaceDischarge|OLEAN_FRESH|iutiii:IUTIII.STEPXI.CERTIFICATE_HULL_WIRING; ...PARAMETRIC; IUTIII.STEPXI.CONTRACT_SOURCE_REDUCTION|TREE_ASSET|
|42|Theorem 3.11 Indeterminacy 1/2/3（paper 层）|见 §1.5；n8-group4 记录 Ind3 方向核对|paper-layer|n8-group4-theorem311-multiradial|NAMED（paper 量化/对象未冻结）|

### 1.8 基础对象（IUT I/II；均为可复用现有节点）
| # | paper 对象 | 现有 Lean 资产 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
|43|Hodge theater / link category / concrete examples|IUTI/HodgeTheater/*|OLEAN_FRESH|iut-pre-abc:HodgeTheater.core (DEF); .family (TREE_ASSET); .links (DEF); .concrete|TREE_ASSET/DEF|
|44|Frobenius/étale picture + graph automorphisms|IUTI/HodgeTheater/SourceThetaLinkGraphAutomorphismReduction.lean; Mzk1FrobeniusPictureArrowFactsActual; Mzk1ChainTranslationLawActual|OLEAN_FRESH + EXIT0|iut-pre-abc:FrobeniusPicture.graph/arrowFacts/graphAut/translationClass/translationLaw; .pictureObjects|TREE_ASSET/PROVED|
|45|Initial Θ data / Definition 3.1|IUTI/InitialTheta/SourceInitialThetaData.lean; SourceDefinition31RootLemmas.lean|OLEAN_FRESH|iut-pre-abc:InitialTheta.data; .definition31; .cStage|TREE_ASSET|
|46|prime-strips (F/D) / Frobenioid|IUTII/Frobenioid/PrimeStripsConstruction.lean; PrimeStripFrobenioidCategorySkeleton.lean; Example36*|OLEAN_FRESH|iut-pre-abc:PrimeStrips.FD; .frobenioidCategory; .FxDAction; Frobenioid.Example36; .transport|TREE_ASSET|
|47|θ-link procession/assembly + quotient|IUTII/Theta/ThetaLinkAssembly.lean; EtaleThetaQuotient.lean|OLEAN_FRESH|iut-pre-abc:ThetaLink.procession; .quotient; .unitLaws; iuti-ii:IUTII.Theta.ConcreteBridge|TREE_ASSET|
|48|log-shell I = (p*)^-1 log(O^×) + invariants + log-Frobenius|IUTII/Kummer/SourceLogShellCarrier.lean; SourceLogShellAbsTopIIIBridge.lean; Example36LogShellFrobeniusAction.lean; Mzk1LogShellCarrierArithmeticActual|OLEAN_FRESH + EXIT0|iut-pre-abc:LogShell.I; .pStar (PROVED); .invariants; .logFrobenius|TREE_ASSET/PROVED|
|49|absolute Kummer map / continuity / μN torsion / root systems|IUTII/Kummer/AbsoluteKummerInjection.lean; AbsoluteKummerContinuity.lean; CompatibleRoots.lean; NatRootSystem.lean; Mzk1AbsoluteKummerTrioSummaryActual|OLEAN_FRESH + EXIT0|iut-pre-abc:Kummer.absolute; .continuity; .summary (PROVED); MuN.torsion; .rootSystems|TREE_ASSET/PROVED|
|50|Section 0 oriented graph / paths / saturated sets|tmp/…/AbsTopIII05Section0ObjectsActual.lean; Mzk1Section0PathCompositionActual|EXIT0（paper-layer）|iut-pre-abc:Section0.countablyOrdered/orientedGraph/paths/saturated/orderCat/saturatedClosure|COND/DEF|
|51|q-pilot object + arithmetic divisor/degree machinery|Corollary312/ArithmeticQPilotLogVolume/BaseChange/GlobalNormalization; TateQPilotJComparison; IUTIV/Estimates/ArithmeticDivisorDegree|OLEAN_FRESH|iut-pre-abc:QPilot (def/GAP); QPilot.arithmeticDivisor (TREE_ASSET); iut-skeleton:QPilot (COND)|GAP/TREE_ASSET|
|52|Θ-pilot carrier / X-μ packet / IQ containment|IUTII/Kummer/SourceLogShellXMuPacket.lean（carrier 接口）；Corollary312/StepXI/ThetaPacketBridge.lean|OLEAN_FRESH；carrier 为 NAMED|iut-pre-abc:ThetaPilot.carrier (NAMED); iutiii:IUTIII.STEPXI.THETA_PACKET_BRIDGE|NAMED|
|53|Theorem 3.11 source layers（SourceTheorem311Assembly 输入）|Theorem311/SourceTheorem311Assembly.lean; SourceDependencyChain.lean; SourceTheorem311ReferenceContract.lean|OLEAN_FRESH（conditional assembly PROVED）|n8-group4-theorem311-multiradial; iut-skeleton:Thm311|COND|

## 2. 已存在但未被 route 文档覆盖（uncovered triage，A440/A470）
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsi*（6 files: SourcePsiActualMinimalModelReduction, SourcePsiCorrectedReductionSpecialFiber, SourcePsiIntegralModelReduction, SourcePsiReductionActualConstruct, SourcePsiReductionTypeActual, SourcePsiStableReductionFinal + consumers）— route-index citable=OLEAN_MISSING；triage.hull.tsv 标 P1；**不是 IUT III 3.12 直接前置，暂不挂边，仅登记为 source-Ψ 候选基础（需 olean 后再议）**。
- Theorem311/ConcreteRouteUniqueness.lean、Corollary312/StepXI/SourceRouteDeterminantNormalization.lean、Theorem311/Indeterminacy/Ind1Reduction.lean — route-index covered=NONE（未在任何 coord route 文档）；但 olean 新鲜、可复用（Ind1Reduction 已挂 Ind1 链；ConcreteRouteUniqueness/SourceRouteDeterminantNormalization 可挂 Thm311/StepXI 复用）。
- Theorem311/HullPresentationAlternativeProbe.lean（Hull 类，SKELETON 已提）— 用于 H5 hull 表达替代性（no-go probe），可挂 H5 侧。

## 3. 真缺口（无专属 Lean 对象/声明；A470 后只对真正缺失者建节点）
| # | 缺口对象 | 现状 | 计划 |
|---|---|---|---|
|G1|H5 class-B: O(-)^-1 normalization on arithmetic line bundle|无 arithmetic line-bundle API；仅行文本记录（Mzk1H5GapStatementActual）|保留 NAMED 节点（复用 e-deep:E2.h5Gap）|
|G2|H5 class-B: hull log-volume ≤ image log-volume|无定理；存在判定/反例资产|保留 NAMED，复用 e-deep:E2.h5Gap + Hull09 rows|
|G3|H7/Ob9 deep two-sidedness（arbitrary-iterate both-sided transfer）|只有显式假设 base_lower_bound / HullH7Ob9TwoSidedInputs|保留 NAMED，复用 e-deep:E3.deepOb9|
|G4|HDD 分解定理（hull+det = normalized log-volume）|无证明；仅有 S3182 条件组装与 Hull06 det bookkeeping|保留 DEF/COND，复用 iut-skeleton:HDD + PAPER.S3182|
|G5|det tensor 分解 additivity（跨 packet）|matrixLogDet bookkeeping 已证；分解定理未证|复用 e-deep:E2.detScalingLaws/detInvLaws|
|G6|StepXI.ipl/she/apt 数学内容|仅 Audit 记录 pending|复用 iut-skeleton:IPL/SHE/APT + iutiii:IUTIII.STEPXI.OBLIGATIONS|
|G7|StepXIContract 构造（从 IUT 源数据）|tree Obligation stepXIContractConstruction 未完成|复用 iutiii:IUTIII.STEPXI.CONTRACT.CONSTRUCTION（已有条件构造 consumer）|
|G8|IUTII → IUTIII typed link（无 import 边）|paper-layer IUTIIToStepXILink（条件式、显式 ipl/she/apt evidence）|复用 iutiii:IUTIII.IUTII_LINK_GAP + IUTII_LINK.SOURCEDATA.ROUTE|
|G9|Θ-pilot 构造对象|仅 ThetaPilot.carrier 接口（NAMED）；无构造|复用 iut-pre-abc:ThetaPilot.carrier + iutiii:STEPXI.THETA_PACKET_BRIDGE|
|G10|Cor 3.12 无条件 target（从三公理）|statement 层已建；无条件链未闭合|复用 iut-skeleton:Cor312 | iutiii:IUTIII.COR312.TARGET |

## 4. 复用统计（供后续 fragment 挂边；不新建这些节点）
- 覆盖论文对象（表 1.1–1.8 合计行数）：**53**
- 其中可复用现有 DAG 节点 id（去重）：**67**（见上表第 5 列；涵盖 iut-skeleton 18、iutiii 30、iut-pre-abc 16、e-deep 8、n8-* 9、iut-pre-mainline/T1 2 等；重复 id 跨表已合并）
- 现有 Lean 资产有声明/oleans 的对象：**50/53**（3 个仅 paper/行文本：G1/G2/G3 类）
- 真缺口（无专属 Lean 对象/声明，需新节点或保留 NAMED）：**10**（§3 G1–G10；其中 8 个已有 NAMED/skeleton 占位节点可复用，不需新造；仅“构造/定理内容”本身缺失）
- 结论：后续 fragment 只需（a）用 edges 把 §1 的 53 个对象挂到上述 67 个现有节点；（b）对真正缺失的 10 个缺口**新建/复用**节点（建议复用现有 NAMED/skeleton id，不另造新 id，除非需要 theorem 级细分）。

## 5. 未运行项/诚实声明
- 未编译、未跑 checker/probe、未改 declaration-dag/未建节点（A470 暂停）；本文件仅只读调研 + 表。
- route-index 的 OLEAN_FRESH 来自 repo 现有索引与本机 .lake olean 存在性抽查（表内 8 个关键 olean 均 YES：R9 audit/K1K2CardReduction/PacketDegreeLedger/HullDetLogVolume/SourceHullCompactness/Ind1QuotientTransport/Contract/Comparison）。
- GATE NOT PASSED; binding HOLD; pins 14041/23066/18800; 无 closure 声称。
