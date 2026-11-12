# SURVEY-stepxi — IUT IV 前置对象现有资产调研（Lead A470）

日期：2026-11-11（Asia/Shanghai）  
单写者：stepxi  
范围：目标第一句『从基础三公理无条件构建 IUT 3.12 的全部前置对象并证明 abc 猜想』中，IUT IV 前置对象（Thm 1.10 display、§1 (b) uniform height/(c) region volume、§2 comparison/height dictionary、arithmetic degree、theta two-sided、final inequality/abc 桥接）。  
Pins：registry 14041；GATE NOT PASSED；binding HOLD；canonical V150@18248/CFC6CE08。

## 0. 方法与证据口径

- 只读调研：`coord/REPO-ROUTE-INDEX.md`/`repo-route-index-data.json`、`dag/declaration-dag.json`、`dag/THEOREM-DAG.md`、`coord/target-chain.*.json`、`papers/motizuki_corpus/text`、`LeanFormal/IUT/` 与 `tmp/sheaf/xif/paper/` 实际文件。
- 证据等级：`EXIT0 <results-line>` = watchdog 编译通过；`olean fresh; NO_RESULTS_LINE` = 源与 olean 新鲜但没有 results 行（按项目约定不冒充 CITABLE）；`OLEAN_FRESH` = REPO-ROUTE-INDEX 记录；`TREE_ASSET` = 真实 Lean 树资产但未走 watchdog 的 statement/proof 分级；`NAMED`/`GAP` = 论文对象只以显式输入/缺口存在。
- 本文不新建节点、不写 Lean、不编译。

## 1. 资产表（paper 对象 → 现有 Lean 声明 → 证据 → 现有 DAG 节点 → 状态）

| # | paper 对象（paper ref） | 现有 Lean 文件:声明（行） | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|---|
| 1 | IUT IV 算术除子/算术次数：weight/localDegree/degLinearMap/deg_apply/ndegLinearMap/ndeg_apply/pullback/deg_pullback/ndeg_pullback/absValAt（IUT IV §0–§1；Lemma 1.3） | `LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean:79,97,116,135,304,325,1054`（`weight`,`localDegree`,`deg_apply`,`ndeg_apply`,`deg_pullback`,`ndeg_pullback`,`absValAt`） | olean fresh；NO_RESULTS_LINE；104 条定理 | `T4-iut4-arithmetic-degree`；`e-deep:E5.iutivAdd` | TREE_ASSET（可复用） |
| 2 | 算术高度字典：uniform valuation bound ⇒ logHeight ≤ B·arithmeticWeight（H1；[GenEll] height dictionary） | `LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:64`（`abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound`） | olean fresh；NO_RESULTS_LINE；条件定理（输入 uniform valuation bound） | 无精确节点；邻近 `iutiv-abc:HW.add`/`mainline:abc-height-weight-additive` | TREE_ASSET / CONDITIONAL（可复用） |
| 3 | §1 (b) UNDILATED height bound：height ≤ comparison-region logVolume | `tmp/sheaf/xif/paper/S3131PaperRouteHeightReductionActual.lean`（`UndilatedHeightBound`,`heightComparisonFamily_of_undilated`） | watchdog EXIT0（SIZE=1684）；`OLEAN_FRESH` | `iutiv-abc:S3131.heightReduction`；`iutiv-abc:E5.uniformHeightConsumer` | PROVED（条件） |
| 4 | §1 (b) uniform height consumer：unit/一般 valuation bound + volume dominance ⇒ undilated height family | `tmp/sheaf/xif/paper/S3171UniformHeightConsumerActual.lean`（`uniformHeightComparison_of_valuation_bound`,`undilatedHeightBound_of_valuation_bound`）；`tmp/sheaf/xif/paper/Mzk1E5UniformHeightActual.lean`（unit-B；EXIT0） | SIZE=4449 EXIT0；Mzk1E5UniformHeightActual EXIT0 211162 | `iutiv-abc:E5.uniformHeightConsumer`；`e-deep:E5.uniformHeightConsumer` | PROVED（条件） |
| 5 | §1 (b) additive variant：ABCHeightWeightAdditiveBoundV2 + region-volume dominance ⇒ undilated height | `tmp/sheaf/xif/paper/Mzk1E5AdditiveHeightActualV2.lean`（`undilatedHeightBound_of_additiveBound_volume`,`exists_additive_constant`） | EXIT0 211753 | `iutiv-abc:E5.additiveHeight` | PROVED（条件） |
| 6 | §1 (c) UNDILATED region-volume bound：(c) `logVolume ≤ weight + logVolume hull + D` | `tmp/sheaf/xif/paper/S3131PaperRouteRegionReductionActual.lean`（`UndilatedRegionBound`,`regionVolumeFamily_of_raw`,`regionVolumeFamily_of_undilated`） | watchdog EXIT0（SIZE=2223）；`OLEAN_FRESH` | `iutiv-abc:S3131.regionReduction` | PROVED（条件） |
| 7 | §1 (b)+(c) ⇒ paper-route residual data ⇒ ABC | `tmp/sheaf/xif/paper/S3171IUTIVSection1DisplayActual.lean`（`paperRouteResidualData_of_undilated`,`abcConjecture_of_undilated`）；`Mzk1E5RegionConsumerActual.lean`（EXIT0 211419） | SIZE=6921 EXIT0；Mzk1E5RegionConsumerActual EXIT0 211419 | `iutiv-abc:E5.regionConsumer` | PROVED（条件） |
| 8 | IUT IV Prop 1.7：加权平均恒等式（IUT IV L927–942） | `LeanFormal/IUT/IUTIV/Estimates/Section1.lean:115,119,125,157,172,186,199`（`iutIVProp17_betaAvg`,`iutIVProp17_lambdaE_pow`,`iutIVProp17_weightedTupleSum`,`iutIVProp17_betaTupleSum`,`iutIVProp17_middle`,`iutIVProp17_value`,`iutIVProp17`） | olean fresh；NO_RESULTS_LINE；真实证明 | `T5-iut4-prop17`；`e-deep:E5.iutivSection1`；`iutiv-abc:IUTIV.S1` | TREE_ASSET（可复用） |
| 9 | IUT IV Prop 2.1(i)：log x ≤ x（L2356；entirely elementary） | `LeanFormal/IUT/IUTIV/Estimates/Section2.lean:111`（`iutIVProp21i_log_le_self`） | olean fresh；NO_RESULTS_LINE | `iutiv-abc:IUTIV.S2`；`e-deep:E5.iutivSection2` | TREE_ASSET（可复用） |
| 10 | IUT IV Prop 2.1(ii)：θ 双侧估计（∃ξ≥5，∀x≥ξ，(2/3)x≤θ(x)≤(4/3)x） | `LeanFormal/IUT/IUTIV/Estimates/Section2.lean:393`（`iutIVProp21ii_theta_two_sided_eventually`） | olean fresh；NO_RESULTS_LINE | `iutiv-abc:IUTIV.S2`；`T6-iut4-theta-two-sided` | TREE_ASSET（可复用） |
| 11 | IUT IV Prop 1.6 / Prop 2.2 PNT 常数：π(η)≤4η/(3logη) 与 nth-prime 版本 | `LeanFormal/IUT/IUTIV/Estimates/Section2.lean:409,436`（`iutIVProp16_primeCounting_le_four_thirds_eventually`,`iutIVProp16_index_le_four_thirds_nthPrime`） | olean fresh；NO_RESULTS_LINE；explicit constants 仍 named | `iutiv-abc:IUTIV.S2` | TREE_ASSET（部分）/ explicit PNT constants GAP |
| 12 | IUT IV StepV：collection bound、sum、procession-average 精确式与不等式（L1736–L1783） | `LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean`（`collectionBound`,`sum_collectionBound`,`processionAverage_eq`,`processionAverage_le`）；`tmp/sheaf/xif/paper/Mzk1StepVPaperActual.lean`（paper-form） | olean fresh；NO_RESULTS_LINE；Mzk1StepVPaperActual EXIT0 211152 | `iutiv-abc:IUTIV.StepV`；`e-deep:E5.stepV`；`iutiv-abc:StepV.paperForm` | TREE_ASSET + PROVED consumer |
| 13 | IUT IV Thm 1.10 display terms（l,dmod,logDFpd,logFFpd,eStar,etaPrm,logQ；lhs/mid/rhs/cor312Gap） | `tmp/sheaf/xif/paper/S3171IUTIVSection1DisplayActual.lean`（`Thm110DisplayTerms`,`thm110Lhs`,`thm110Mid`,`thm110Rhs`,`thm110Cor312Gap`） | SIZE=6921 EXIT0 | `iutiv-abc:IUTIV.S1.display`；`e-deep:E5.display` | PROVED/DEF |
| 14 | IUT IV Thm 1.10 final display（Step (v)，corpus l.1362–1385） | `tmp/sheaf/xif/paper/S3171IUTIVSection1DisplayActual.lean`（`Thm110DisplayInputs`,`thm110_final_display`）；`Mzk1E5DisplaySlackActualV2.lean`（EXIT0 211752）；`Mzk1S1DisplayFActual.lean`（F 修正版 EXIT0 211403） | SIZE=6921 EXIT0；V2/F EXIT0 | `iutiv-abc:IUTIV.S1.display`；`iutiv-abc:E5.displaySlack`；`iutiv-abc:S1.displayF` | PROVED（条件：hCor312+hSlack 或显式 logQ bound） |
| 15 | IUT IV Thm 1.10 hSlack 的显式计算化：显式 logQ bound ⇒ hSlack | `tmp/sheaf/xif/paper/Mzk1Thm110SlackActual.lean`（`thm110Slack_of_logQ_bound`,`thm110DisplayInputs_of_logQ_bound`） | EXIT0 211163 | `iutiv-abc:IUTIV.S1.slack` | PROVED（条件） |
| 16 | CThetaPaper 常数、factor 正性与 bracket 等价（IUT III Cor 3.12） | `tmp/sheaf/xif/paper/S2715CThetaPaperScaleActual.lean:11,44,78`（`CThetaPaper`,`CThetaPaper_ge_neg_one_iff`,`CThetaPaper_lowerBound_of_thetaHull_upper`） | olean fresh；NO_RESULTS_LINE；src 内 `#print axioms` 仅三公理记录 | 无节点（source）→ 挂到 `iutiv-abc:S1.displayCTheta` | TREE_ASSET（条件：lowerBound 需 theta hull upper+q 归一化） |
| 17 | CThetaPaper ≥ -1 ⇒ hCor312 ⇒ 精确 display | `tmp/sheaf/xif/paper/Mzk1S1DisplayCThetaActualV2.lean`（`hCor312_of_CThetaPaper_ge_neg_one`,`thm110_final_display_of_CThetaPaper_logQ`） | EXIT0 211754 | `iutiv-abc:S1.displayCTheta` | PROVED（条件） |
| 18 | S2717UpperGap / PaperCor312Full：Cor 3.12 单一解析端点与 full target 等价 | `tmp/sheaf/xif/paper/S2717Cor312FullTargetActual.lean:81,103,185`（`S2717UpperGap`,`PaperCor312Full`,`S2717_full_iff_hupper`）；`Mzk1E5S2717ConsumerActualV2.lean`（EXIT0 211755） | olean fresh；NO_RESULTS_LINE；V2 EXIT0 211755 | `e-deep:E5.s2717`；`iutiv-abc:E5.s2717` | TREE_ASSET/CONDITIONAL + PROVED aliases |
| 19 | IUT IV §2 per-epsilon comparison 数据 N1/N2 | `LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:224,236,248`（`Cor312EpsilonArithmeticComparison`,`height_le_normalizedRegionVolume`,`regionVolume_le_normalizedWeight`） | EXIT0（results 行存在） | `T1-cor312-abc-bridge`；`T2-bridge-interface`；`e-deep:E5.comparisonGaps` | CONDITIONAL/NAMED（字段仍是 named） |
| 20 | §2 reduced inputs 组装 N1/N2（gap1+gap2 assembly） | `LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:198,306,367`（`cor312Gap1_...`,`cor312Gap2_...`,`cor312GapAssembly_epsilonComparisonOfReducedInputs`） | olean fresh；NO_RESULTS_LINE；`OLEAN_FRESH`（REPO-ROUTE-INDEX） | `iutiv-abc:GapReduction` | CONDITIONAL（从 reduced named inputs 组装） |
| 21 | 显式 EpsilonGapInputs 结构与 comparison 等价 | `tmp/sheaf/xif/paper/Mzk1G2EGapInputsActual.lean`（`EpsilonGapInputs`,`epsilonComparison_of_gapInputs`,`bridgeInterface_of_gapInputs`）；`Mzk1G2EGapInputsIffActual.lean`（`nonempty_gapInputs_iff_nonempty_comparison`） | EXIT0 211390 / 211658 | `iutiv-abc:G2E.gapInputs`；`iutiv-abc:G2E.gapInputsIff` | PROVED（条件） |
| 22 | IUT IV §1→§2 缺失转移：Thm 1.10 display ⇒ N1/N2 | 无 Lean 定理（paper text only） | — | `GAP.sec1_to_sec2`（fragment/`DAG-BLOCKED` 记录） | GAP（真缺口） |
| 23 | IQHullLogVolumeInterface：hull/unitRegion/scaleShift/logVolume；finiteness 从字段证明 | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean:52,95`（`IQHullLogVolumeInterface`,`hull_logVolume_lt_top`） | olean fresh；NO_RESULTS_LINE；`OLEAN_FRESH` | `iutiii:IUTIII.HULL.SOURCE_COMPACTNESS`；`iutiv-abc:IQHull` | TREE_ASSET/CONDITIONAL（literal IQ carrier 未形式化） |
| 24 | product local-field hull：unitRegion/region/hull/normalizedLogVolume/scaling law | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldProductHull.lean`（`unitRegion`,`region`,`hull`,`normalizedLogVolume`,`normalizedLogVolume_smul`,`measure_hull_lt_top`） | olean fresh；NO_RESULTS_LINE | `iutiv-abc:LFP` | TREE_ASSET（可复用） |
| 25 | value-hull 负结果：degree-faithful value hull 不可满足 | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/`（`sourceHullVolume_not_lt_top_of_degreeFaithful`,`not_nonempty_valueHullCompactnessInput_of_degreeFaithful`） | 记录于 `FOUNDATIONS-IUTIV.md` §6；tree source | 无独立 DAG 节点（负结果） | NEGATIVE（复用记录，不再尝试） |
| 26 | Archimedean tensor metric identities | `LeanFormal/IUT/IUTIV/Estimates/ArchimedeanTensorMetric.lean`（`complexTensorToProd_inner`,`complexTensorToProd_norm_sq`,`complexTensorToProd_bijective`,`complexTensor_continuousRingEquiv_inner`） | olean fresh；NO_RESULTS_LINE | `iutiv-abc:IUTIV.Arch` | TREE_ASSET（可复用） |
| 27 | different tower estimate / tame equality | `LeanFormal/IUT/IUTIV/Estimates/DifferentTowerEstimate.lean`；`DifferentTameEquality.lean` | olean fresh；NO_RESULTS_LINE | 无独立 DAG 节点（由 `iutiv-abc:IUTIV.S1` 邻近覆盖） | TREE_ASSET（可复用，节点待挂） |
| 28 | 高度-权重比较：normalized volume comparison ⇒ heightWeightBound | `LeanFormal/IUT/ABCBridge/Bridge/ThetaBoundToHeightWeight.lean`（`heightWeightBound_of_normalizedVolumeComparison`,`exists_oneAdd_sq_le_oneAdd`） | EXIT0 | `iutiv-abc:G2.c`；`mainline:theta-bound-to-heightweight` | PROVED（可复用） |
| 29 | ABC bridge interface + height bound + ABC consumer | `LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:404,426,446`（`Cor312ToABCBridgeInterface`,`cor312ToABCBridge_heightBound`,`cor312ToABCBridge_abcConjecture`）；`tmp/sheaf/xif/paper/Mzk1G2CDConsumerActual.lean`（EXIT0 211157） | EXIT0；consumer EXIT0 211157 | `T1-cor312-abc-bridge`；`iutiv-abc:G2.b`；`iutiv-abc:G2CD.consumer` | CONDITIONAL/proved consumer |
| 30 | bridge 强度校准：Nonempty interface ↔ ABCConjecture | `Cor312ToABCBridgeInterface.lean`（`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`）；`Mzk1G2CDConsumerActual.lean` | EXIT0 211157 | `T1-cor312-abc-bridge`；`iutiv-abc:G2.d`；`iutiv-abc:G2CD.consumer` | PROVED（iff；无 inhabitant） |
| 31 | ABC ↔ 加法 height-weight 界 ↔ log 形式 | `LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:158,167`；`LogarithmicBoundEquivalence.lean`；`Mzk1HWConsumerActual.lean`/`Mzk1ABCLogConsumerActual.lean`（EXIT0） | EXIT0 consumer 211231/211402 | `iutiv-abc:HW.add`；`iutiv-abc:G0.log`；`mainline:abc-log-equivalence`；`iutiv-abc:hull.Mzk1HWConsumerActual`；`iutiv-abc:abcLog.consumer` | DEF/CONDITIONAL + PROVED equivalence consumers |
| 32 | frontier 路线：gapReduced/V2/pointwiseWeakened 全部 refuted（(1,8,9)） | `LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierHeightWeightRefutation.lean`（`not_ABCFrontierGapReduced`,`not_ABCFrontierGapReducedV2`,`not_ABCFrontierPointwiseWeakened`）；`Mzk1G3RefutationConsumerActual.lean`（EXIT0 211477） | REPO-ROUTE-INDEX OLEAN_FRESH；consumer EXIT0 211477 | `mainline:abc-frontier-heightweight-refutation`；`iutiv-abc:G3.refutation` | REFUTED（记录；不重开路线） |
| 33 | IUT IV Prop 1.1：tensor packet ring | 无（grep 无 `iutIVProp11`） | — | 无 | GAP（真缺口） |
| 34 | IUT IV Prop 1.2；Prop 1.4；Prop 1.5；Prop 1.8（general archimedean / elliptic-Serre） | 无（仅有部分 ArchimedeanTensorMetric / different 局部资产） | — | 无（邻近 `iutiv-abc:IUTIV.Arch`） | GAP（真缺口） |
| 35 | IUT IV Thm 1.10 的 actual log-volume estimate（不只是 display 形状） | 无（只有 display shape 与 hCor312/hSlack 条件版本） | — | 无 | GAP（真缺口） |
| 36 | arithmetic transition / theta-link comparison objects（IUT III→IV linkage） | 无独立 formalization（仅在 named input/route 记录中出现） | — | 无 | GAP（真缺口） |
| 37 | explicit Prop 2.2 PNT 常数（非 eventuality 形式） | 部分：`iutIVProp16_*` eventuality 版本；无显式常数 | olean fresh；NO_RESULTS_LINE | `iutiv-abc:IUTIV.S2` | PARTIAL/NAMED |

## 2. 复用/缺口统计

- 表格覆盖 paper 对象：**37** 项。
- 可直接复用现有对象：**约 23** 项（算术次数、Prop 1.7、Prop 2.1 i/ii、StepV、IQHull/LFP、§1 (b)/(c)、§2 assembly、CTheta、S2717、bridge、ABC 等价、consumer 文件）。
- 复用现有 DAG 节点：**约 20** 个 id（见表中 `现有 DAG 节点 id` 列，含 `iutiv-abc:*`、`e-deep:*`、`mainline:*`、`T1–T6-*`）。
- 真缺口/命名输入：**约 9–10** 项：§1→§2 转移、Prop 1.1/1.2/1.4/1.5/1.8、Thm 1.10 actual estimate、explicit PNT 常数、arithmetic transition/theta-link、IQ 字面 carrier、§2 N1/N2 本身的证明。
- 已 refuted/负结果：frontier 三条路线（not_ABCFrontierGapReduced/V2/PointwiseWeakened）；degree-faithful value hull 不可满足；IQHull product realization 为 PRAGMATIC-DEAD-END。

## 3. 对 A469 拆分的直接结论

1. **不要新造已有对象**：算术次数、Prop 1.7、Prop 2.1、StepV、LFP/IQHull、CTheta、S2717、bridge、ABC 等价都已有 Lean 文件/声明，拆分节点时用 `reuse` 指向现有 DAG id（`T4`, `T5`, `T6`, `iutiv-abc:IUTIV.*`, `iutiv-abc:LFP`, `iutiv-abc:GapReduction`, `iutiv-abc:G2.c`, `T1-cor312-abc-bridge`, `iutiv-abc:HW.add`, etc.）。
2. **只新建真缺口节点**：`GAP.sec1_to_sec2`、`S1.prop11`、`S1.prop12`、`S1.prop14`、`S1.prop15`、`S1.prop18`、`S1.thm110actual`、`S2.pnt`、`S2.arithmeticTransition`，以及 `S1.hCor312`/`S1.hSlack`/`S2.N1`/`S2.N2`/`S1b.heightInput`/`S1c.undilatedInput` 这类 named-input 节点。
3. **新边只连到现有节点**：例如 `iutiv-abc:IUTIV.S1.display`（display）、`iutiv-abc:GapReduction`（§2 assembly）、`iutiv-abc:G2.c`（heightWeightBound）、`iutiv-abc:HW.add`（additive）、`iutiv-abc:S3131.heightReduction`/`regionReduction`（(b)/(c)），并用 `evidence: planned/observed_source` 标注。
4. 已有节点状态以 `dag/declaration-dag.json` 为准（本次调研读到：S1.display PROVED、E5.uniformHeightConsumer PROVED、GapReduction CONDITIONAL、T1 CONDITIONAL、T2 NAMED、IQHull CONDITIONAL、LFP TREE_ASSET、G3.refutation PROVED）。

## 4. 证据限制

- LeanFormal 核心树许多文件有新鲜 olean 但 **无 `tmp/xif_guarded_results.log` EXIT 行**；按项目规则不称 CITABLE，只称 `olean fresh; NO_RESULTS_LINE`。
- 本次调研为只读，未运行 lake/lean/checker/probe；未重新验证任何 axiom 集。
- `SURVEY-stepxi.md` 为单写者文件；下一步 fragment `coord/target-chain.iut-pre-stepxi.json` 只追加/复用，不改他人 fragment。


## 5. 拆分落地（A469/A470；调研后按“复用优先”执行）

- 新 fragment：`coord/target-chain.iut-pre-stepxi.json`（owner stepxi，12 个本地节点 / 41 条边；本地 id 为 `IUT312.statement`、`GAP.sec1_to_sec2`、`S1.prop11/12/14/15/18`、`S1.thm110actual`、`S2.pnt`、`S2.arithmeticTransition`、`S1b.heightInput`、`S1c.undilatedInput`）。
- 复用而不是新建：显示/§1(b)/(c)/§2 comparison/arithmetic degree/theta/StepV/S2717 等已有对象全部挂到现有 DAG 节点 id（如 `e-deep:E5.display`、`e-deep:E5.uniformHeightConsumer`、`e-deep:E5.comparisonGaps`、`e-deep:E5.undilatedABCBridge`、`T4-iut4-arithmetic-degree`、`T5-iut4-prop17`、`T6-iut4-theta-two-sided`、`T1-cor312-abc-bridge`、`T2-bridge-interface`、`T0-abc-target`）。
- 合并验证：`node tools/dag_merge3.mjs` → **nodes 789 / edges 1031 / conflicts 0**（复用边追加后；validate problems 0）；`node tools/dag_validate_decl2.mjs` → **ok true / problems 0**（proof 子图 cyclic false；statement/citation 子图 cycle 为 informational）。
- 未手动编译、未碰 watchdog；本次仅只读调研 + fragment/merge/validate。
- 追加复用边：IUT IV prerequisite classes → `e-deep:E5.*`、`T1/T2/T4/T5/T6-*`；以及 `T2→T1`、`T1→T0`、`comparisonGaps→T2`、`displayInputsStatement→comparisonGaps`(gap)、`comparisonGaps→display`(gap) 等语义边。


## 6. A475 穷尽仓库搜索证据（缺口/复用）

搜索范围：`LeanFormal/` 全树、`tmp/`（含 `tmp/sheaf`、`tmp/external/ported`）、`.lake/packages/mathlib`、`coord/` 文档与 `dag/` 索引；关键对象名/变体多轮 grep。结果：

| 对象 | 搜索词 | 命中 | 结论/复用 |
|---|---|---|---|
| IUT IV Prop 1.1/1.2/1.4/1.5/1.8 | `iutIVProp11`\|`iutIVProp12`\|`iutIVProp14`\|`iutIVProp15`\|`iutIVProp18` | LeanFormal=0；tmp/sheaf/xif/paper=0；Mathlib=0；ported=0 | 仓库当前无声明；现有 statement layer 仅以 `NAMED` 结构表达，复用 `Mzk1DeepStatementLayerV2Actual` 的 `IUTIVProp1xStatement` |
| §1→§2 转移（display→N1/N2） | `Sec1ToSec2`\|`sec1_to_sec2`\|`Sec1Sec2` | LeanFormal=0；tmp=33；Mathlib/ported=0 | **已有**：`tmp/sheaf/xif/paper/Mzk1IUTIVSec1Sec2GapActual.lean`（`IUTIVSec1Sec2Gap`）与 `Mzk1DeepStatementLayerV2Actual` 的 `Sec1ToSec2GapStatement`；仅 statement/named gap，无 bridge theorem |
| Thm 1.10 actual estimate | `thm110_actual`\|`Thm110Actual`\|`actualLogVolume`\|`actual_log_volume` | tmp/sheaf/xif/paper=8；Mathlib/ported=0 | **已有** statement layer `IUTIVThm110ActualStatement`（`logVolume_estimate`,`constants_explicit`）；无 actual estimate 证明体，状态 NAMED |
| §2 arithmetic transition/theta-link | `arithmeticTransition`\|`arithmetic_transition` | LeanFormal=0；tmp=7–9；Mathlib/ported=0 | **已有** `IUTIVSec2ArithmeticTransitionStatement`（deep statement layer）；无构造/证明，状态 NAMED |
| explicit Prop 2.2 PNT constants | `iutIVProp16_primeCounting`/`index_le_four_thirds` | Section2 命中；Mathlib/ported=0 | 仅有 eventuality 形式；显式常数以 `IUTIVProp22PNTStatement` NAMED 记录 |
| q-pilot precise / thetaPilot IQ | `qPilotPrecise`\|`qPilot precise` | LeanFormal=0；tmp 命中 deep statement layer 结构 | 复用 `QPilotPreciseConstructionStatement` / `ThetaPilotIQContainmentStatement`（NAMED statement layer） |

**复用决定**：本轮把 `iut-pre-stepxi` 的 11 个 gap/named 节点全部改挂到既有 `hull:PRE.IUTIV.*.STATEMENT` 节点与 `Mzk1DeepStatementLayerV2Actual` 声明；新增 `Mzk1IUTIVStatementLayerConsumerActual.lean` 仅做 bundle/投影/装配，不复制理论。


**A475 不合格资产（禁止复用）**：
- `tmp/sheaf/xif/paper/Mzk1StepXIGapInputsActual.lean` 用 `statement := True` 作为输入占位，违反无 `True`/toy 规则；不导入、不复用，已用 `Mzk1StepXIStatementInputsActual.lean` 的 Type-level 结构替代。
- `tmp/sheaf/xif/paper/Mzk1AbsoluteKummerTrioSummaryActual.lean` 的 `absoluteKummer_trio_summary : (∀ K [Field K], True)` 是 `True`/`trivial` 占位；不导入、不复用。

## 7. A476 质量清理（簿记节点剔除）

- 从 `coord/target-chain.zz-stepxi.json` 删除 **32 个文件簿记/纯投影/import 汇总节点**（含 `Rows` List/String 节点、bundle/projection 节点、纯 re-export 节点），只保留有真实数学内容的 chain/consumer：StepXI source contract、StepXI finite certificate、GapReduction source data、GapInputs assembly、ABCLog↔additive、H5 det inverse、G0 log 单调性、HW 非负常数、bookkeeping V2、Section0 order/graph/opposite/path/orderCat/saturated closure、F0 composition、RR negative degree、G0 log↔rpow、Cor312 assembly chain、Chain.abcBridge、Chain.stepXI、StepProvider fixed-beta 等。
- 保留节点的 declarations 映射同时剔除 `*Rows` 簿记声明；DAG 只登记定理级语义对象。
- 说明：全局 `dag_validate_decl2` 当前 problems 来自并发 `zz-qpilot`/`hull` fragment 的 missing file/decl（非本 fragment）；本 fragment 无自身问题。
