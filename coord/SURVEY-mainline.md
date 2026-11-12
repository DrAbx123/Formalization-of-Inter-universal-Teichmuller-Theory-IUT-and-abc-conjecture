# SURVEY-mainline — IUT 3.12 前置对象现有资产调研（A470）

调研范围：目标链前置（ABC target ↔ Cor 3.12 ↔ Thm 3.11 的精确陈述与必要条件，含 hCor312/hSlack 与 class-B named inputs 的精确定义/地位）、Frey/conductor 桥、additive/comparison 两条等价路线、T0–T6 目标节点。
只读调研；未写 Lean、未新建节点；未碰 watchdog、未编译。

## 索引/文档（读/查过的）
coord/REPO-ROUTE-INDEX.md, coord/repo-route-index-data.json, coord/uncovered-leanformal-*.tsv, coord/SKELETON-IUTI-II.md, coord/SKELETON-IUTIII.md, coord/SKELETON-IUTIV-ABCBRIDGE.md, coord/SKELETON-THETA-ETTH.md, coord/MASTER-SKELETON.md, coord/FOUNDATIONS-IUTIV.md, coord/IUTIV-SECTION1-PLAN.md, coord/IUT_SUBTARGETS.md, THEOREM311_*（root）, coord/OPEN-HARD-PROBLEMS.md, coord/E-EXISTING-CLOSURE-MAP.md, dag/declaration-dag.json, dag/THEOREM-DAG.md（若存在）, papers/motizuki_corpus/text/（IUT I-IV、Explicit estimates、Formalization of IUT 2026-04、AbsTopIII、EtTh、GenEll、NCBel、Frobenioid I-II、Combinatorial Anabelian）, LeanFormal/IUT/ 树（IUTIV/Estimates、IUTIII/Corollary312+Theorem311、ABCBridge、Foundations）。

## 对象表（paper 对象 → 现有 Lean 文件:声明 → 证据 → 现有 DAG node → 状态）
| # | paper 对象 | 现有 Lean（文件:声明） | 证据 | 现有 DAG node | 状态 |
|---|---|---|---|---|---|
| 1 | ABC statement `ABCConjecture` | LeanFormal/IUT/ABCBridge/Statement.lean:32 `ABCConjecture` | TREE（olean；定义级） | T0-abc-target / iutiv-abc:G0 / iut-pre-mainline:T0 | DEF/已定义 |
| 2 | ABC 不等式 `ABCInequality`、`IsABCTriple`、`radical` | Statement.lean:28/…/radical | TREE（olean） | 无专用节点（iut-pre-mainline:D1 计划节点） | DEF |
| 3 | rational point dictionary x=a/c | ABCBridge/Arithmetic/RationalPointDictionary.lean `abcRationalPoint`/`isABCTriple_iff_positivePrimitiveAdditiveTriple` | TREE（olean） | mainline:abc-rational-point-dictionary | CONDITIONAL（待 watchdog EXIT0） |
| 4 | arithmeticWeight/prime support | ABCBridge/Arithmetic/RationalPrimeSupport.lean `arithmeticPrimeSupport`/`arithmeticWeight_abcRationalPoint` | TREE（olean） | mainline:abc-prime-support | CONDITIONAL |
| 5 | canonical height logHeight₁ | Mathlib pinned `Height.logHeight₁` + RationalPointDictionary | TREE（Mathlib pinned） | 无专用节点（被 L2/G2.b 消费） | 资产 |
| 6 | Cor312ToABCBridgeInterface（carrier+hullData+εComparison） | Cor312ToABCBridgeInterface.lean:404 structure；:410 field | TREE（olean；stepxi 声明级验证） | iutiv-abc:G2 / T2-bridge-interface / iut-pre-mainline:T2 | conditional interface |
| 7 | interface ⇒ ABC 定理 | Cor312ToABCBridgeInterface.lean:446 `cor312ToABCBridge_abcConjecture` | TREE + `_FOUNDATIONS-IUTIV-CitableProbe` EXIT0（含此 decl，stepxi） | iutiv-abc:G1 / T1-cor312-abc-bridge / iut-pre-mainline:T1 | PROVED-conditional（proof complete） |
| 8 | height bound 定理 | Cor312ToABCBridgeInterface.lean:426 `cor312ToABCBridge_heightBound` | TREE（olean） | iutiv-abc:G2.b / iut-pre-mainline:L1 | PROVED-conditional |
| 9 | theta-bound ⇒ height-weight 组合 | ABCBridge/Bridge/ThetaBoundToHeightWeight.lean:67 `heightWeightBound_of_normalizedVolumeComparison` | TREE（olean） | iutiv-abc:G2.c / iut-pre-mainline:L2 | PROVED（组合） |
| 10 | per-ε comparison structure | Cor312ToABCBridgeInterface.lean:224 `Cor312EpsilonArithmeticComparison` | TREE（olean） | iutiv-abc:G2.e / iut-pre-mainline:D6 | conditional interface |
| 11 | gap1: height ≤ (1+ε)·regionVolume | 同文件 field `height_le_normalizedRegionVolume` | TREE（field 定义；**无证明**） | iutiv-abc:N1 / e-deep:E5.comparisonGaps / iut-pre-mainline:N1 | NAMED（class-B） |
| 12 | gap2: regionVolume ≤ (1+ε)·weight+θ+D | 同文件 field `regionVolume_le_normalizedWeight` | TREE（field 定义；**无证明**） | iutiv-abc:N2 / iut-pre-mainline:N2 | NAMED（class-B） |
| 13 | comparison region normalizedComparisonRegion | Cor312ToABCBridgeInterface.lean:201 | TREE（olean） | iut-pre-mainline:D5 | DEF（真实定义） |
| 14 | IQHullLogVolumeInterface（hull/logVolume） | IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean（interface）；LocalFieldProductHull.lean（real） | TREE（olean） | iutiv-abc:IQHull / iutiv-abc:LFP | conditional interface / TREE |
| 15 | ABC ⇔ log form | ABCBridge/Bridge/IUTToABC.lean `abcConjecture_iff_abcLogConjecture` | TREE（olean） | iutiv-abc:G0.iff_log / iut-pre-mainline:L4 | PROVED equivalence |
| 16 | ABC ⇔ height-weight form | IUTToABC.lean `abcConjecture_iff_abcArithmeticWeightHeightBound` | TREE + citable probe（stepxi） | iutiv-abc:G0.iff_hw / iut-pre-mainline:L3 | PROVED equivalence |
| 17 | additive V2 contract + 等价 | ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:158/167 | TREE（olean） | iutiv-abc:HW.add / iut-pre-mainline:T5/D7/L5 | CONDITIONAL（V2 未证；iff 已证） |
| 18 | Cor 3.12 paper target | IUTIII/Corollary312/Comparison.lean（tree 陈述）+ Routes.lean | TREE（olean） | iutiii:IUTIII.COR312.TARGET / iut-skeleton:Cor312 / iut-pre-mainline:T3 | CONDITIONAL（陈述层） |
| 19 | Theorem 3.11 paper target | IUTIII/Theorem311/SourceTheorem311Assembly.lean（t1/t2/t3/output:81-93）+ Output/MultiradialAlgorithm*.lean + Ind1/2/3 | TREE（olean） | iutiii:IUTIII.THM311.OUTPUT_ALGORITHM/TWO_ACTION/ARITH_HOLO_LANDING/CONCRETE_FINITE_MODEL/IND1-3 / iut-pre-mainline:T4 | CONDITIONAL/TREE（source inputs named） |
| 20 | StepXI contract / Cor312Conclusion | IUTIII/Corollary312/StepXI/Contract.lean:32/46（qSigned/thetaSigned + ipl/she/apt evidence） | TREE（olean） | iutiii:IUTIII.STEPXI.CONTRACT / iutiv-abc:StepXI | conditional interface（evidence fields） |
| 21 | Thm 1.10 display terms/inputs | tmp/sheaf/xif/paper/S3171IUTIVSection1DisplayActual.lean:52/69/72/77/82/88/96 | paper-layer EXIT0（checker CITABLE per stepxi） | e-deep:E5.display / iut-pre-mainline:D12/L8 | CONDITIONAL（hCor312+hSlack） |
| 22 | IUT IV (b) UndilatedHeightBound | tmp/sheaf/xif/paper/S3131PaperRouteHeightReductionActual.lean:21 | paper-layer（olean/EXIT0 per inventory） | e-deep:E5.uniformHeightConsumer（consumer）/ iut-pre-mainline:N4 | NAMED（class-B） |
| 23 | IUT IV (c) UndilatedRegionBound | tmp/sheaf/xif/paper/S3131PaperRouteRegionReductionActual.lean:20 | paper-layer（olean/EXIT0） | iut-pre-mainline:N5 | NAMED（class-B） |
| 24 | IUT IV ArithmeticDivisorDegree（Def 1.9/height box） | LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean | TREE（olean；_FOUNDATIONS-IUTIV-CitableProbe 覆盖 deg_pullback 等） | iutiv-abc:IUTIV.ADD / T4-iut4-arithmetic-degree / iut-pre-mainline:D13 | TREE/PROVED（tree） |
| 25 | IUT IV Section1（Prop 1.7 weighted averages） | IUTIV/Estimates/Section1.lean | TREE（olean；citable probe R1-R19 覆盖 iutIVProp17） | iutiv-abc:IUTIV.S1 / T5-iut4-prop17 / iut-pre-mainline:D13 | TREE/PROVED |
| 26 | IUT IV Section2（theta two-sided bounds） | IUTIV/Estimates/Section2.lean | TREE（olean；citable probe 覆盖 iutIVProp21ii） | iutiv-abc:IUTIV.S2 / T6-iut4-theta-two-sided / iut-pre-mainline:D13 | TREE/PROVED |
| 27 | IUT IV Step V averages | IUTIV/Estimates/StepVProcessionAverage.lean `processionAverage_le` | TREE（olean；citable probe 覆盖 processionAverage/stepVPaperLogVolumeBound） | e-deep:E5.stepV / iut-pre-mainline:D14 | TREE/PROVED |
| 28 | IUT IV Different tower estimates | IUTIV/Estimates/DifferentDegreeUpperBound/TameEquality/Tower.lean | TREE（olean per inventory） | 无专用节点（iut-pre-mainline:D15 计划） | TREE（未挂节点） |
| 29 | Cor312 comparison gap reduction（split point/unit-region inputs） | ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:306/:367 | TREE（olean） | iutiv-abc:GapReduction / GapSupply / PointwiseResidual / iut-pre-mainline:D16/N10/L6/L7 | CONDITIONAL |
| 30 | ABCFrontier（等价强度 frontier） | ABCBridge/Bridge/ABCFrontier.lean:187/:213 | TREE（olean） | T3-abc-frontier / iutiv-abc:G3/G3.f / iut-pre-mainline:D17/L10 | CONDITIONAL + **premise refuted（DAG-BLOCKED）** |
| 31 | ABCFrontier 附加变量拒绝（additive-factorization refutation） | ABCBridge/Bridge/ABCFrontierHeightWeightRefutation.lean `not_FrontierHeightWeightClause` | TREE（olean） | mainline:abc-frontier-heightweight-refutation | CONDITIONAL（negative result） |
| 32 | Frey 模型（integral model/curve/discriminant） | ABCBridge/Geometry/FreyOddReduction.lean `freyPadicIntegralModel`/`freyPadicCurve`/`freyPadicCurve_discriminant` | OLEAN_FRESH；`_MainlineFreyProbeActual` **EXIT0（trio）** | mainline:frey-odd-reduction | PROVED（tree；probe trio） |
| 33 | Frey split multiplicative / residue | FreySplitMultiplicativeReduction.lean `FreyResidueField`/`freyResidue_prime_eq_zero`/`freyMultiplicativeSplittingPolynomial` | OLEAN_FRESH；同 probe **EXIT0** | mainline:frey-split-multiplicative | PROVED（probe trio） |
| 34 | Frey 2-adic minimal model/conductor | FreyTwoAdicMinimalReduction.lean `freyTwoAdicHalvingModel`/`_discriminant`；FreyConductorOdd/TwoAdic/TwoAdicMinimalDiscriminantValuation | OLEAN_FRESH；probe trio 覆盖 2-adic | mainline:frey-two-adic-minimal / frey-conductor-odd / frey-conductor-two-adic / frey-two-adic-* | PROVED/TREE（probe 部分） |
| 35 | Frey J product/denominator criteria | ABCBridge/Bridge/ABCEllipticHeightCriterion.lean `abcConjecture_iff_freyJProductHeightCriterion` 等 | OLEAN_FRESH；`_MainlineABCEquivProbeActual` EXIT0（trio） | mainline:abc-freyj-criteria | PROVED（iff；criteria 本身未证） |
| 36 | ABC residue discriminant | ABCBridge/Geometry/ABCResidueDiscriminant.lean `abcResidueDiscriminant`/`..._eq_zero_iff_dvd_discriminant` | OLEAN_FRESH（未 probe） | mainline:abc-residue-discriminant | CONDITIONAL（待 watchdog EXIT0） |
| 37 | Cor312 ⇔ S2717UpperGap（single analytic endpoint） | tmp/sheaf/xif/paper/S2717Cor312FullTargetActual.lean:81/103/185 | paper-layer（olean/EXIT0） | e-deep:E5.s2717 | CONDITIONAL |
| 38 | Thm 3.11 source inputs（H1/H2/LGP/source bundle） | Theorem311/Source*Assembly/SourceH1H2… + S3128Stage1SourceAssemblyInputActual | TREE（olean per inventory） | iutiii:IUTIII.THM311.* / iut-pre-mainline:N3 | NAMED/TREE |
| 39 | H5 O^x/hull-det + H7-Ob9 深输入 | 树 Hull 系列 + tmp Hull08/09/12/13 + 我的 Hull closure/ray/det laws | mixed：树 TREE；tmp 部分 CITABLE/EXIT0 | e-deep:E2.* / E3.*（含本轮 PROVED hullClosure/hullRay/sandwich/kernelLattice） | 部分 PROVED，深输入 NAMED |
| 40 | EtTh 深行（EtTh02/EtTh11） | tree EtaleThetaQuotient/Example36*；tmp EtTh07-13、Example36Correspondence | tree TREE；tmp EXIT0（correspondence CITABLE 10） | e-deep:E4.* / theta-etth:R* | 部分 PROVED；3 行 named |

## 覆盖/复用/真缺口统计
- **覆盖 paper 前置对象：40 项**（T0–T6 + 定义对象 + 桥 + named inputs + Frey/conductor + additive/comparison/frontier 路线）。
- **复用现有 DAG 节点：约 75 个不同 node id**（上述表中 T0-T6/iutiv-abc/iutiii/iut-skeleton/e-deep/mainline 节点，全部已存在，无需重建）。
- **真缺口（无现有 Lean 对象或无证明）**：
  1. **hCor312（gap1）**：只有 Prop field，无任何构造/证明；IUT IV §2 paper link。
  2. **hSlack（gap2）**：同上；需 split point bound + unit-region bound 的具体值（N10）。
  3. **IUT IV §1 display → §2 comparison 的语义桥**（Thm110DisplayInputs ⇒ hCor312/hSlack）：无 Lean 定理，仅 statement 层记录（GAP.sec1_to_sec2）。
  4. **Thm 3.11 source inputs（H1/H2/LGP/P1P2 bundle）实际构造**：tree 只有条件 assembly + named layers。
  5. **Frey/conductor 算术输入**：模型/判别式/准则已有，但 paper 所需的 conductor 指数实际计算与 ABC 外部桥仅 tree（N7）。
  6. **H5 O^x normalization/hull≤image-volume、H7 both-sided、EtTh deep rows**：named class-B（部分临时文件已证 wrapper/局部律，非深输入）。
  7. **IUT IV (b)/(c) 与 paper-route 最终不等式**：仅 named props/consumer（无证明）。
  8. **ABCFrontier 路线**：premise 已被 refuted（ABCFrontierHeightWeightRefutation）→ 不可用（DAG-BLOCKED）。
- **结论**：目标链核心对象（T0-T6、interface、epsilon comparison、等价、IUT IV estimates、gap reduction、Frey 模型）**仓库已有**，我上一轮 iut-pre-mainline fragment 的 40/50 对象应挂到现有节点上（复用），只对上面 8 个真缺口建 named/statement 节点；不需要重建任何已存在对象。

## 备注（证据口径）
- TREE = LeanFormal 树内 olean 存在（prior inventory / checker 记录），未在本次调研重编译；CITABLE/EXIT0 标注仅用于 mainline 曾实际验证过的文件（如 `_MainlineFreyProbeActual`、`_MainlineABCEquivProbeActual`、`_FOUNDATIONS-IUTIV-CitableProbe`、S3171 display 等）。
- 本调研未写 Lean、未建节点、未编译；GATE NOT PASSED；binding HOLD；V150@18248/CFC6CE08；registry 14041。
## 50 个 iut-pre-mainline 节点 → 现有 DAG 节点映射（A470 补充）

| 旧新节点 id | 现有 DAG 节点（复用） |
|---|---|
| T0 | T0-abc-target / iutiv-abc:G0 |
| T1 | iutiv-abc:G1 / T1-cor312-abc-bridge |
| T2 | iutiv-abc:G2 / T2-bridge-interface |
| T3 | iutiii:IUTIII.COR312.TARGET / iut-skeleton:Cor312 |
| T4 | iutiii:IUTIII.THM311.OUTPUT_ALGORITHM / iut-skeleton:Thm311 |
| T5 | iutiv-abc:HW.add |
| T6 | iutiv-abc:G0.iff_hw / G0.iff_log / G0.log |
| D1 | mainline:abc-rational-point-dictionary |
| D2 | mainline:abc-prime-support |
| D3 | (Mathlib pinned; consumed by iutiv-abc:G2.b) |
| D4 | iutiv-abc:IQHull |
| D5 | (covered by iutiv-abc:G2.e statement) |
| D6 | iutiv-abc:G2.e |
| D7 | iutiv-abc:HW.add |
| D8 | iutiv-abc:G0.log |
| D9 | iutiii:IUTIII.STEPXI.CONTRACT |
| D10 | iutiii:IUTIII.HULL.DET_LOG_VOLUME |
| D11 | iutiii:IUTIII.THM311.* / iut-skeleton:Thm311 |
| D12 | e-deep:E5.display / iutiv-abc:IUTIV.S1.display |
| D13 | iutiv-abc:IUTIV.ADD / T4-iut4-arithmetic-degree |
| D14 | e-deep:E5.stepV / iutiv-abc:IUTIV.S1 |
| D15 | (TREE asset; no dedicated node — genuine minor gap: node optional) |
| D16 | iutiv-abc:GapReduction / GapSupply |
| D17 | T3-abc-frontier / iutiv-abc:G3 |
| D18 | mainline:frey-odd-reduction |
| D19 | mainline:frey-conductor-odd/two-adic/...  |
| D20 | mainline:abc-freyj-criteria |
| D21 | mainline:abc-residue-discriminant |
| L1 | iutiv-abc:G2.b |
| L2 | iutiv-abc:G2.c |
| L3 | iutiv-abc:G0.iff_hw |
| L4 | iutiv-abc:G0.iff_log |
| L5 | iutiv-abc:HW.add |
| L6 | iutiv-abc:GapReduction |
| L7 | iutiv-abc:GapSupply |
| L8 | e-deep:E5.display |
| L9 | e-deep:E5.uniformHeightConsumer / iutiv-abc:E5.regionConsumer |
| L10 | iutiv-abc:G3.f |
| L11 | iutiii:IUTIII.COR312.WIRING / THM311.OUTPUT_ALGORITHM |
| L12 | iutiv-abc:G3.pw |
| N1 | iutiv-abc:N1 / iut-skeleton:hCor312 |
| N2 | iutiv-abc:N2 |
| N3 | iut-skeleton:Thm311 / iut-pre-stage4 source nodes |
| N4 | iutiv-abc:S3131.heightReduction / e-deep:E5.uniformHeightConsumer |
| N5 | iutiv-abc:S3131.regionReduction / iutiv-abc:E5.regionConsumer |
| N6 | e-deep:E5.display / iutiv-abc:GAP.sec1_to_sec2 |
| N7 | mainline:frey-* (model/conductor/criteria; arithmetic input itself residual named) |
| N8 | e-deep:E2.h5Gap / E3.deepOb9 |
| N9 | e-deep:E4.etthGap |
| N10 | iutiv-abc:GapReduction / GapSupply / PointwiseResidual |

结论：**50/50 个节点对象均已有现有 DAG 节点或树资产覆盖**；无真正需要新建的重复节点。唯一可选新增：`D15` IUT IV Different tower estimates（TREE asset，无专用节点）与 `N7` Frey arithmetic input 的 residual named 部分，均非关键路径，故 iut-pre-mainline fragment 清空，仅在本文档保留映射。

## A475 仓库穷尽搜索证据（2026-11-11；禁止'数学突破'说法）

搜索范围：LeanFormal 全树、tmp/（sheaf 等）、.lake/packages/Mathlib、papers、coord、dag/declarations-index.json。工具：ripgrep（tools.grep）。

| 搜索词 | LeanFormal | tmp Lean | 结论 |
|---|---|---|---|
| f4b | 0 | 34（多为无关子串） | 无 f4b numMaxP 实现；tmp 仅有 gap statement（Mzk1StepProviderGapStatementsActual） |
| fixedBetaChoice | 0 | 3 | 仅 gap/adapted 文件；StepProviderFixedBetaChoiceInput 为 named 接口 |
| schemeSideMaps | 0 | — | 无精确标识符 |
| sectionMap | 265 | — | InitialTheta 通用 section map；无 scheme↔function-field 桥构造 |
| placePoint | 0 | 110 | tmp consumer 文件有 placePoint 语句；无构造 |
| ProblemDApplicability | — | 38 | GenEll21 consumer 语句存在；未绿 |
| HTLink | — | 20 | HodgeTheater transport 语句存在 |
| bothSided | — | 6 | Hull13 both-sided 语句/输入存在（Mzk1Hull13BothSidedBaseActual） |
| arbitraryIterate | — | 6 | H7/Ob9 arbitrary-iterate named（Mzk1Cor312ToABCConsumerActual） |
| Ominus | — | 2 | H5 O(-)^{-1} named placeholder only |
| qPilot | 17,577 tmp 命中 | | q-pilot 树对象齐全（ArithmeticQPilot*） |

结论：上述'缺口'在仓库中**均有 NAMED/statement/接口层资产**（非'需数学突破'）；缺的是从 named 接口到具体构造的证明体，属已知 class-B 层。证据已同步为 Lean 记录文件 `Mzk1RepoSearchEvidenceActual`（node mainline:repoSearchEvidence）。
## A477 只读核对：区域已有资产清单（file:decl，LeanFormal / tmp/sheaf）

- ABC 层：`ABCBridge/Statement.lean`(`ABCConjecture`, `ABCInequality`, `IsABCTriple`)；`RationalPointDictionary.lean:97`(`abcRationalPoint`)；`RationalPrimeSupport.lean:34/71`(`arithmeticWeight`, `arithmeticWeight_abcRationalPoint`)；
- 等价层：`IUTToABC.lean:36/64`(`abcConjecture_iff_abcLogConjecture`, `abcConjecture_iff_abcArithmeticWeightHeightBound`)；`ABCHeightArithmeticWeightComparison.lean:158/173`(`ABCHeightWeightAdditiveBoundV2`, `exists_constant`)；`LogarithmicBoundEquivalence.lean:63`(`ABCLogConjecture`)；
- Cor3.12/Bridge：`Cor312ToABCBridgeInterface.lean:201/224/256/267/404/426/446`（`normalizedComparisonRegion`, `Cor312EpsilonArithmeticComparison`, `comparisonRegion`, `comparisonRegion_logVolume_lt_top`, `Cor312ToABCBridgeInterface`, `cor312ToABCBridge_heightBound`, `cor312ToABCBridge_abcConjecture`）；`S2717Cor312FullTargetActual.lean:81/103`(`S2717UpperGap`, `PaperCor312Full`)；`Cor312ComparisonRegionV2Actual.lean:26`(`Cor312ToABCBridgeInterfaceV2`)；
- StepXI/Thm311：`StepXI/Contract.lean:32/46`(`StepXIContract`, `Cor312Conclusion`)；`Theorem311/SourceTheorem311Assembly.lean:47`(`SourceTheorem311Layers`)；`StepXI/APT.lean:163/308`(`SourceAlgorithmicParallelTransport`, `SourceAPTStatement`)；
- IUT IV 输入：`S3131PaperRouteHeightReductionActual.lean:21`、`S3131PaperRouteRegionReductionActual.lean:20`、`S3131PaperRouteSkeletonActual.lean:31/66`（`UndilatedHeightBound`, `UndilatedRegionBound`, `PaperRouteResidualData`, `abcConjecture_of_paperRouteResiduals`）；`S3171IUTIVSection1DisplayActual.lean:52/88/96`(`Thm110DisplayTerms`, `Thm110DisplayInputs`, `thm110_final_display`)；
- 其余：`ABCFrontier.lean:187`；`ABCEllipticHeightCriterion.lean:61`(`abcConjecture_iff_freyJProductHeightCriterion`)；`FreyOddReduction.lean:22`(`freyPadicIntegralModel`)；`ABCResidueDiscriminant.lean:20`；`SourceThetaLinkGraphAutomorphismReduction.lean:84`(`FrobeniusPictureGraphAut`)；`CThetaPaper`(tmp S2715:11)；`StepProviderFixedBetaChoiceInput`(tmp Mzk1StepProviderPrimeActual:100)；`ThetaPilotIQ`(tmp Mzk1AbsTopIIIDeepStatementLayerActual:46)；`HTLink`(tmp Mzk1HodgeTheaterLinkLawsActual:8)；`SchemeSideMaps`/`ProblemDApplicability`(tmp Mzk1Stage4GapRegistrationsActual:23/26)；`HullEH5NamedInputs`/`HullEH7NamedInput`(tmp Mzk1HullEInputsActual:56/65)；
- 附带大型既有资产族：`ABCBridge/Geometry/ABCInvariant{Coprimality,LocalValuations,RadicalBridge}.lean`（~80 条 J-不变量/赋值/根式桥定理）；`ABCNonemptyOddBadSupport.lean`（~15 条 odd-bad-support 定理）；

**统计**：核对 25 个关键对象 → **23 个仓库已有**（file:decl 如上）；**真缺失（仅 2 项）**：`hCor312`/`hSlack`（仓库只有 structure fields，无独立定理声明）、`IJData`（无声明；tmp 仅有引用）；其余深输入（hull O^- normalisation、H7 Ob9 arbitrary iterate、EtTh deep）均为 named input 层，仓库有接口/语句文件。
