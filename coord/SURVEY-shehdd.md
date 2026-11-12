# SURVEY-shehdd — IUT 3.12 前置对象现有资产调研（A470）

日期: 2026-11-11 02:32-02:42 (Asia/Shanghai)；作者: shehdd；性质: 只读调研，不改 Lean、不建节点、不碰 watchdog、不编译。
范围: IUT III Cor 3.12 陈述所需前置对象/定理，以及现有 iut-skeleton + iut-pre-* fragment 的定理级节点/边/evidence 分布。

## 0. 方法与已读来源

- 论文原文: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt:10324-10353 (Cor 3.12 陈述)。
- 骨架/清单: coord/MASTER-SKELETON.md (第1节最终链, 第2节分层, 第3节节点表, 第4节 last-mile), MASTER-SKELETON-OUTLINE.md, SKELETON-IUTIII.md, SKELETON-IUTI-II.md, IUT-PREREQUISITES-REMAINING.md, IUT-PAPER-ROUTE.md。
- 索引: coord/REPO-ROUTE-INDEX.md, coord/repo-route-index-data.json, coord/uncovered-leanformal-triage.tsv (+per-owner tsv), dag/THEOREM-DAG.md (252 nodes/358 edges, 224/252 带 Lean 声明), dag/declaration-dag.json, dag/DAG-CLEAN-REPORT.json。
- fragment: coord/target-chain.iut-skeleton.json, target-chain.iut-pre-abc.json, target-chain.iut-pre-mainline.json, target-chain.iut-pre-stage4.json, target-chain.iut-pre-stepxi.json (快照)。
- 真实 Lean 树: LeanFormal/IUT/{IUTI,IUTII,IUTIII,IUTIV,Foundations,ABCBridge} 文件名/声明检索; tmp/sheaf/xif/paper 的 paper-layer 文件与 probe; olean mtime 与 tmp/xif_guarded_results.log 最新 EXIT 记录。

## 1. 现有 iut-* 前置 fragment 统计（只读快照）

| fragment | nodes | edges | kinds | status | edge kinds | evidence | isolated | no-files | no-decls |
|---|---|---|---|---|---|---|---|---|---|
| iut-pre-abc | 48 | 51 | target=2, def=28, theorem=14, bridge=2, named_input=2 | GAP=5, DEF=3, TREE_ASSET=25, PROVED=6, CONDITIONAL=5, NAMED=4 | statement=39, proof=8, interface=4 | planned=18, observed_source=33 | 0 | 2 | 48 |
| iut-pre-mainline | 0 | 0 |  |  |  |  | 0 | 0 | 0 |
| iut-pre-stage4 | 4 | 2 | named_input=4 | NAMED=4 | gap=2 | planned=2 | 0 | 1 | 1 |
| iut-pre-stepxi | 12 | 41 | target=1, named_input=11 | GAP=10, NAMED=2 | statement=35, proof=3, gap=1, interface=2 | planned=37, observed_source=4 | 0 | 12 | 12 |
| iut-skeleton | 32 | 50 | target=1, theorem=18, def=9, named_input=4 | NAMED=5, CONDITIONAL=18, DEF=9 | statement=25, proof=25 | planned=50 | 0 | 26 | 32 |
| 合计 | 96 | 144 | | | | planned=107, observed_source=37 | | | |

要点: (a) iut-skeleton 全部边 evidence=planned（无 observed_source），证据缺口最大; (b) iut-pre-abc/pre-stepxi 节点 declarations 基本为空; (c) iut-pre-mainline 快照为空（正被 owner 迁移/重写，属并发写窗口）; (d) 语义重叠见第 4 节。统计为读取瞬间快照，fragment 正被各单写者并发追加。

## 2. 论文前置对象 -> 现有资产对照表

图例: 证据列 tree:olean_fresh = LeanFormal 树 olean 存在且不旧; index_fresh = route index 标 OLEAN_FRESH; paper:EXIT0 = tmp/xif_guarded_results.log 最新 EXIT=0; +probe = 存在 probe 文件; no-EXIT0 = 最新非 EXIT0。状态列: 已证/条件/命名/树资产/定义/缺口。

| # | 论文对象（原文位置） | 现有 Lean 文件::声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
| 1 | Theta-pilot 对象 (IUT III Def 3.8(i)) | SourceArithmeticThetaPilotBridge.lean (tree); paper FlUnitsThetaPilotActionActual / Mzk1ThetaPilotPacketInterfaceActual | tree:olean_fresh; paper:EXIT0 | 无专用 Def 3.8(i) 节点（相邻 iut-pre-abc:QPilot=GAP） | 缺口(对象层) |
| 2 | q-pilot 对象 (Def 3.8(i)) + q-参数 | Corollary312/ArithmeticQPilot{LogVolume,BaseChange,GlobalNormalization}.lean; TateQPilotJComparison.lean | tree:olean_fresh; index_fresh(部分) | iut-pre-abc:QPilot (GAP); iut-skeleton:QPilot (CONDITIONAL) | 条件/树资产 |
| 3 | Multiradial representation (Thm 3.11(i)) | Theorem311/Output/MultiradialAlgorithm.lean::multiradialAlgorithm (+Reduction, GeneralRouteNormalForm) | tree:olean_fresh; index_fresh | iutiii:IUTIII.THM311.OUTPUT_ALGORITHM (TREE_ASSET); iut-skeleton:Thm311 (CONDITIONAL) | 树资产 |
| 4 | Indeterminacy Ind1 | Theorem311/Indeterminacy/Ind1.lean::ind1 (+Ind1Reduction, Ind1QuotientTransport) | tree:olean_fresh; index_fresh | iutiii:IUTIII.IND1 (TREE_ASSET) | 树资产 |
| 5 | Indeterminacy Ind2 | Ind2.lean::ind2 | tree:olean_fresh; index_fresh | iutiii:IUTIII.IND2 (TREE_ASSET) | 树资产 |
| 6 | Indeterminacy Ind3 | Ind3.lean::ind3 | tree:olean_fresh; index_fresh | iutiii:IUTIII.IND3 (TREE_ASSET) | 树资产 |
| 7 | possible images 的 holomorphic hull (Rmk 3.9.5(i)) | HolomorphicHull/SourceHullCompactnessReduction.lean::IQHullLogVolumeInterface; CardHullRealGeometryReduction.lean::sourceScalingUnits_subset_sourceHolomorphicHull / sourceHolomorphicHull_eq_closure | tree:olean_fresh; index_fresh | iutiii:IUTIII.HULL.CARD_GEOMETRY (TREE_ASSET) | 树资产 |
| 8 | procession-normalized mono-analytic log-volume (Rmk 3.1.1/Prop 3.9) | HolomorphicHull/HullDeterminantLogVolumeReduction.lean::HullDeterminantLogVolumeFrozenSpec / hullDeterminantLogVolumeFrozenSpec_holds / packetLogVolume_eq_matrixLogDet | tree:olean_fresh; index_fresh | iutiii:IUTIII.HULL.DET_LOG_VOLUME (TREE_ASSET) | 树资产 |
| 9 | Kummer isomorphisms (Thm 3.11(ii)) | StepXI/SourceLogShellMuNQuotientCarrier.lean::muNQuotient / muNQuotientMap / muNQuotientMap_ker; SourceLogShellAbsTopIIIBridge.lean::SourceLogShellInvariantImageIdentification | tree:olean_fresh | iutiii:IUTIII.STEPXI.LOGSHELL_MUN (TREE_ASSET); e-deep:E1.logShellBridge (TREE_ASSET) | 树资产 |
| 10 | 标签 0 / <F_l^#> 的识别 (IUT II Cor 4.10(i)) | 未找到直接声明（库内关键字无命中）；最接近 SourceLogShellAbsTopIIIBridge.lean::SourceLogShellInvariantImageIdentification | tree:olean_fresh | 无 | 缺口 |
| 11 | q-参数 at v in V_bad (IUT I Def 3.1(b)) | SourceDefinition31* 树 (SourceDefinition31RootLemmas / DualContractAlignment 等); ArithmeticQPilotBaseChange.lean | tree:olean_fresh | iut-pre-abc:QPilot 子定义 (arithmeticDivisor); e-deep:iuti-source-def31-dual-alignment | 部分/缺口 |
| 12 | Hodge theater (IUT I) | HodgeTheater/HodgeTheaterCore.lean; SourceHodgeTheaterFamily.lean::theater_injective/link_* | tree:olean_fresh | iut-pre-abc:HodgeTheater.core (DEF) / family (TREE_ASSET); e-deep:iuti-source-def31-dual-alignment (TREE_ASSET) | 树资产 |
| 13 | Frobenioid Example 3.6 模型 (IUT II) | Frobenioid/Example36* (141 files), 例 Example36TateUniformization.lean::concreteFiveTateParameter | tree:olean_fresh | e-deep:E4.example36 (TREE_ASSET); iut-pre-abc:Frobenioid.Example36 (TREE_ASSET) | 树资产 |
| 14 | F/D prime-strips | PrimeStripsConstruction.lean; PrimeStripFrobenioidCategorySkeleton.lean | tree:olean_fresh; index_fresh | iut-pre-abc:PrimeStrips.FD (TREE_ASSET) | 树资产 |
| 15 | Initial Theta data / Definition 3.1 clusters | InitialTheta/SourceInitialThetaData.lean; SourceDefinition31RootLemmas.lean; SourceDefinition31DualContractAlignment.lean::sourceDefinition31Arithmetic_spec | tree:olean_fresh; index_fresh | iut-pre-abc:InitialTheta.data (TREE_ASSET); e-deep:iuti-source-def31-dual-alignment | 树资产 |
| 16 | Etale theta (EtTh) 套件 | IUTII/EtaleThetaQuotient 树; paper EtTh00-EtTh13Actual（statement layer EXIT0） | tree:olean_fresh; paper:EXIT0 | e-deep:E4.etthConsumer (PROVED); e-deep:E4.etthGap (NAMED) | 条件/命名 |
| 17 | Kummer K1/K2 packets | Theorem311/SourceK1K2* (约20 files); SourceK1K2CardReduction.lean | tree:olean_fresh; index_fresh | iut-skeleton:K1K2 (CONDITIONAL) | 条件 |
| 18 | AbsTopIII 输入 (Hodge-Arakelov/theta hull, Prop 5.8) | paper AbsTopIII01-AbsTopIII14Actual（01/03/07/08/09 gate 表 CITABLE）; AbsTopIII05RefinedActual::Prop58iLocalFieldReconstruction / Prop58iiLogShellReconstruction | paper:EXIT0; 部分 CITABLE | e-deep:E1.absTopIII05Refined (PROVED); e-deep:E1.absTopIII05Inputs (NAMED) | 部分/命名 |

| 19 | H5 O^x stabilization / hull<=image-volume | Hull09H5GapsActual::hull09_scalingUnits_subset_hull / hull09_hull_eq_closure / hull09DetTensorBookkeeping_exponent; CardHullRealGeometryReduction | paper:EXIT0 | e-deep:E2.H5framing (PROVED); e-deep:E2.h5Gap (NAMED) | 条件/命名 |
| 20 | H6 geometric core precise | 未找到 Mzk1GeometricCorePrecise* 文件；相邻 Hull11H6Mzk1UpgradeActual / Hull11PreciseConsumerActual（EXIT0） | paper:EXIT0 (相邻) | e-deep:E1.absTopIII05Inputs (NAMED); foundation:HOLD.binding (NAMED) | 缺口/命名 |
| 21 | H7/Ob9 two-sided arbitrary-iterate | Hull12Ob9BoundTransferActual::hull12_upperBound_transfer（one-sided）; Hull13TwoSidedBoundActual::hull13_twoSided_bound / HullH7Ob9TwoSidedInputs | paper:EXIT0 | e-deep:E3.oneSided (PROVED); E3.twoSided (PROVED); E3.deepOb9 (NAMED) | 条件/命名 |
| 22 | GenEll（一般椭圆）结果 | paper GenEll00-GenEll17Actual（statement layer citable）；GenEll10b H6 wiring | paper:EXIT0 | E-hull-h5-h7 相关节点（TREE_ASSET/CONDITIONAL） | 部分 |
| 23 | Belyi / Lemma 2.x 输入 | Mzk1 bottom B1-B5（CITABLE）; LayerAAlgebraicInductionActual::AlgebraicNestedInductionInput (NAMED) | paper:EXIT0+probe | B1-fold / B5-lemma23-moebius (PROVED); N2-alg-nested (NAMED) | 已证(有理层)/命名(Qbar) |
| 24 | IUT IV Theorem 1.10 display | S3171IUTIVSection1DisplayActual::thm110_final_display | paper:EXIT0 | e-deep:E5.display (PROVED) | 条件 |
| 25 | IUT IV Section 2 估计 | IUTIV/Section2.lean; ArithmeticDivisorDegree.lean::deg_pullback; StepV*/Different*/Archimedean* | tree:olean_fresh | T4-iut4-arithmetic-degree (TREE_ASSET) | 树资产 |
| 26 | Cor 3.12 target <=> S2717 upper gap | S2717Cor312FullTargetActual::S2717UpperGap / PaperCor312Full / S2717_full_iff_hupper | paper:no-EXIT0 (待重编) | e-deep:E5.s2717 (CONDITIONAL) | 条件 |
| 27 | (b)/(c) 比较输入（undilated height/region） | Cor312ToABCBridgeInterface.lean::height_le_normalizedRegionVolume（named 字段）、regionVolume_le_normalizedWeight | tree:olean_fresh | e-deep:E5.comparisonGaps (NAMED); T1-cor312-abc-bridge (CONDITIONAL) | 命名 |
| 28 | Theorem 3.11 source assembly | Theorem311/SourceTheorem311Assembly.lean::SourceTheorem311Layers / assemble / t1_recovered / t2 / t3 / output_recovered; paper Mzk1PaperTheorem311AssemblyStatementActual::SourceP1P2Bundle/H1H2Hypotheses/LGPCompatibility | tree:olean_fresh; paper:no-EXIT0 (statement 待重编) | iut-skeleton:Thm311 (CONDITIONAL); routes:theorem311_assembly (CONDITIONAL) | 条件 |
| 29 | Cor 3.12 结论/合同陈述 (CTheta >= -1) | Corollary312/Comparison.lean::cor312Conclusion_of_contract; StepXI/Contract.lean::StepXIContract / q_positive_of_constructed_stepXI | tree:olean_fresh; index_fresh | iutiii:IUTIII.COR312.TARGET (CONDITIONAL); iut-skeleton:Cor312 (CONDITIONAL) | 条件 |
| 30 | Cor 3.12 -> ABC bridge / height bound | Cor312ToABCBridgeInterface.lean::cor312ToABCBridge_abcConjecture / cor312ToABCBridge_heightBound / heightWeightBound_of_normalizedVolumeComparison | tree:olean_fresh | T1-cor312-abc-bridge (CONDITIONAL, 条件定理已证) | 条件 |
| 31 | ABCFrontier / ABC 等价形式 | ABCBridge/Bridge/ABCFrontier.lean::abcConjecture_of_frontier / abcFrontier_iff_abcConjecture; ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean | tree:olean_fresh | T3-abc-frontier (CONDITIONAL; 部分 frontier 路线被 refute 记录) | 条件/部分refuted |
| 32 | ABCConjecture 最终目标 | ABCBridge/Statement.lean::ABCConjecture | tree:olean_fresh | T0-abc-target (DEF) | 定义 |
| 33 | Section 0 对象 (countably ordered/oriented graph/path pairs) | paper Mzk1Section0*Actual（约20 files, mixed EXIT0） | paper:EXIT0 | iut-pre-abc:Section0.* / e-deep Section0 节点 (TREE_ASSET/PROVED/CONDITIONAL) | 部分 |
| 34 | Sources 1995-2015（外部定理输入） | 无 Lean 声明（外部定理） | — | iut-skeleton:Sources1995_2015 (NAMED) | 命名(外部) |
| 35 | Formalization Stage 1-5 / 四三角形 | 文档级（paper Formalization of IUT lines 116-125/443-621）；Lean 无直接对象 | — | routes fragment 相关节点 (CONDITIONAL) | 文档级 |

## 3. 覆盖统计与结论

- 审计对象: 35 个（IUT 3.12 陈述 + Theorem 3.11 装置 + 外部/深输入 + IUT IV/ABC 链）。
- 有现有 Lean 资产可复用: 31 个（树 olean_fresh 或 paper EXIT0/CITABLE；其中 26 个有明确 Lean 声明名，5 个仅文件级）。
- 有现有 DAG 节点可直接复用/挂边: 30 个（iut-skeleton / iut-pre-* / iutiii / e-deep / T0-T4 / B1-B5 等）；5 个无专用节点（#1 Theta-pilot 对象层、#10 标签识别、#11 q-参数、#20 H6 precise、#34 Sources1995 仅命名）。
- 真缺口（对象级/无 Lean 声明）: 5 个 —— #10 标签识别 (IUT II Cor 4.10(i))、#1 Theta-pilot Def 3.8(i) 对象层、#11 q-参数 Def 3.1(b)、#20 H6 geometric core precise、#34 Sources1995-2015（外部命名，按设计不形式化）。
- 深输入命名（已有节点但证明为 named）: AbsTopIII05 deep (#18)、H5 O^x (#19)、H7/Ob9 both-sided (#21)、EtTh02/EtTh11 deep (#16)、GenEll Thm2.1(ii)=>(i) consumer (#22)、(b)/(c) 比较 (#27)、AlgebraicNestedInductionInput (#23) —— 合计 7 条。

## 4. fragment 语义重叠 / 去重建议

- Cor 3.12 陈述: iut-skeleton:Cor312 / iut-pre-mainline:T3 / iut-pre-abc:IUT312.statement → 建议以 iutiii:IUTIII.COR312.TARGET（已有 tree 声明）为 canonical，其余改为引用边。
- Theorem 3.11: iut-skeleton:Thm311 / iut-pre-mainline:T4 + D11 + L11 / routes:theorem311_assembly → canonical iut-skeleton:Thm311 或 tree SourceTheorem311Assembly 节点。
- q-pilot: iut-skeleton:QPilot / iut-pre-abc:QPilot → 保留一个，另一个改为引用边。
- H5: e-deep:E2.H5framing + e-deep:E2.h5Gap + mainline N8 部分重叠 → 保留 E2.* 为 canonical。
- H7/Ob9: e-deep:E3.oneSided/twoSided/deepOb9 + mainline N8 → 保留 E3.*。
- Hodge/Frobenioid/PrimeStrips/InitialTheta/LogShell/Kummer/ThetaLink/Section0: iut-skeleton 的 def 节点 vs iut-pre-abc 细粒度节点 → 建议 iut-skeleton 节点改为 statement 引用（挂边到 pre-abc 细节点），不重复定义。
- T0-T6/D1-D21/L1-L12/N1-N10（iut-pre-mainline）与 iut-skeleton:TargetABC/Cor312/Thm311/Ind1-3/H5/H7Ob9/QPilot/IUT4Estimates 重叠 → skeleton 保留语义层、mainline 为分解层，用 edge 连接不重复声明。

## 5. 证据质量与下一步（不建节点，仅建议）

- iut-skeleton 全部边 evidence=planned → 复用/挂边前先填 observed_source（可用 dag/THEOREM-DAG.md 的 Lean 声明映射 + route index 的 file/decl 证据）。
- iut-pre-abc / pre-stepxi 节点 declarations 基本为空 → 需从现有树/paper 声明填充（本 survey 第 2 节已给出候选文件::声明）。
- iut-pre-mainline 快照为空（并发写窗口）→ 迁移完成后需重跑本审计统计。
- 真缺口对象先复用现有 tree/paper 资产挂边；仅在缺对象层时新建节点（A470/A471），且新边标 evidence。

## 6. 一句话结论

覆盖 35 个 IUT 3.12 前置对象；31 个已有 Lean 资产可复用、30 个已有 DAG 节点可挂边复用；5 个真缺口（标签识别、Theta-pilot Def3.8(i) 对象层、q-参数 Def3.1(b)、H6 precise、Sources1995 外部命名），另有 7 条深输入 named 依赖；证据缺口集中在 iut-skeleton 全 planned 边与 pre-abc/pre-stepxi 空 declarations。

## 7. A475 穷尽搜索证据（纠正早前“缺口”表述）

搜索范围: LeanFormal/ 全树、tmp/（含 tmp/sheaf, tmp/n8-*）、.lake/packages（Mathlib 等依赖）、papers/motizuki_corpus/、coord/ 历史文档、AUDIT_LEDGER、dag/generated/declarations-index.json（1,572,263 条声明）、repo 文件名 glob。
方法: 声明索引正则扫描 + 文件名 glob + 源码 grep（大小写/命名变体/前缀后缀多轮）。

| 早前标注的“缺口” | 搜索词 | 命中 | 结论 |
|---|---|---|---|
| Cor 4.10(i) label identification | cor4_10 / corollary 4.10 / labelzero / toFiniteLabel / invariantImageIdentification | cor4_10=0；label 相关 1379；invariantImageIdentification=26 | 非“缺数学”：仓库有 SignedLabelEquiv、SourceLabelWeightedDiagonal、SourceSharedBoundary、SourceLogShellAbsTopIIIBridge（label/image identification 资产）。仅“Cor 4.10(i) 逐字陈述”未找到（0 命中），可由现有资产适配，已写 consumer 节点。 |
| Theta-pilot Def 3.8(i) 对象层 | thetaPilot / SourceThetaPilot / possibleImage | 2657 命中，含 SourceThetaPilotIQContainment、FinitePlaceThetaPilotScaledRegion | 非缺口：资产存在；full all-place paper tensor 属 tree 当前限制（SourceThetaPilotIQContainment docstring 明确 one-place reduction），已写 consumer 节点。 |
| q-参数 Def 3.1(b) | qParam / qParam / qNorm / qPilot / normalizedNorm | 5200 命中，含 ArithmeticQPilot{LogVolume,BaseChange,GlobalNormalization}、FreyTateAnalyticInput q-norm、normalizedNorm_eq_norm_of_uniformizer | 非缺口：q-参数/归一化资产存在；无单列 Def 3.1(b) 对象，可由现有 tree 资产适配。 |
| H6 geometric core precise | geometricCorePrecise / HullH6Precise / precise 文件 glob | 25 命中：Mzk1GeomCorePreciseToOldActual、Hull11PreciseConsumerActual | **早前判断错误，撤回**：H6 precise 资产已在仓库（precise witness/recast + Hull11 H6 precise consumer）。 |
| Sources 1995-2015 | 1995 / Faltings / sources1995 | 32 命中（tmp S1995* 系列文件） | 非缺口：部分资产存在；其余为外部定理按设计命名。 |
| scheme-side maps (sectionMap/placePoint) | schemeSide / sectionMap / placePoint / FibreBridge | 113 命中，含 SourceDependentSectionMap、sectionMap_injective/surjective、valuationSectionMap | 非缺口：映射资产/接口存在；具体 scheme 构造连接受 tree 限制（D.bridge.maps named 输入仍为 bottleneck，但不是“数学突破”）。 |
| fixed-beta choice | fixedBeta / fixed_beta | 1 命中：StepProviderFixedBetaChoiceInput (named) | 现为显式 named 输入，非未声称缺口。 |
| Problem D applicability | ProblemDApplicability | 1 命中：ProblemDApplicabilityInput (GenEll21GeometricCoreConsumerActual) | 资产存在（named input），非缺口。 |

**结论**: 之前 survey 中 5 个“真缺口”经穷尽搜索后**全部可由仓库现有资产适配/消费者化**；没有需要“数学突破”的缺口。仅两类边界需记录：(a) 逐字论文陈述（如 Cor 4.10(i) 原文 identification）未在声明索引中出现（0 命中证据如上）；(b) tree 明确的范围限制（Theta-pilot one-place reduction、scheme 侧具体构造）——均按“仓库当前不提供逐字形式/超出当前 tree 范围”记录，不表述为数学困难。

