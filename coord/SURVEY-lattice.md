# SURVEY-lattice — 现有资产调研：IUT 3.12 前置对象（维护/审计视角）

**任务:** A470（先调研仓库，禁止全新构造）。**日期:** 2026-11-11 02:33 (Asia/Shanghai)。**作者:** lattice（维护与审计）。
**范围:** `coord/target-chain.iut-skeleton.json` 的 32 个 paper-scope 前置对象（IUT I–IV + TargetABC + named inputs），对照仓库现有 Lean 资产/DAG 节点，判断“复用 vs 真缺口”。只读调研：未写 Lean、未建节点、未碰 watchdog、未编译。

## 方法

1. `coord/repo-route-index-data.json`（897 rows）按 file/tags/decls 关键词匹配，取 citable 最强的代表行（OLEAN_FRESH 等）；
2. `dag/declaration-dag.json`（828 nodes）按语义关键词取现有节点 id 与 status；
3. `coord/target-chain.iut-skeleton.json` 提供 paper 对象 kind/status；
4. 交叉核对 `coord/REPO-ROUTE-INDEX.md` 分区、`coord/SKELETON-*.md`、`AUDIT_LEDGER.md`、`LeanFormal/IUT/` 目录与 `dag/nodes/` 树资产。
5. 本表是**候选映射**；挂边前必须逐条核对声明名实际存在（尤其 OLEAN_FRESH ≠ CITABLE，tree asset 未重验）。

## 表：paper 前置对象 → 现有资产 → DAG 节点 → 复用/缺口

| paper 对象 | kind/status | 现有 Lean 文件:声明（代表） | 证据 | 现有 DAG 节点 id | 复用/缺口 |
|---|---|---|---|---|---|
| TargetABC | target/NAMED | LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean : FrontierHeightComparisonClause, FrontierRegionComparisonClause | OLEAN_FRESH | e-deep:E5.undilatedABCBridge<br>iut-skeleton:TargetABC<br>routes:abcbridge | 复用现有资产 |
| Cor312 | theorem/CONDITIONAL | LeanFormal/IUT/ABCBridge/Bridge/Cor312ComparisonGapReduction.lean : cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union, cor312Gap2_hull_logVolume_le_normalizedComparisonRegion | OLEAN_FRESH | T1-cor312-abc-bridge<br>iut-skeleton:Cor312<br>iut-skeleton:hCor312 | 复用现有资产 |
| Thm311 | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Theorem311/ConcreteRouteNormalForm.lean : Label, Choice | OLEAN_FRESH | iut-skeleton:Thm311<br>iutiii:IUTIII.THM311.OUTPUT_ALGORITHM<br>iutiii:IUTIII.THM311.TWO_ACTION | 复用现有资产 |
| StepXI | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Corollary312/StepXI/ConcreteFiniteRouteColumns.lean : finiteSup, le_finiteSup | OLEAN_FRESH | iut-skeleton:StepXI<br>iutiii:IUTIII.STEPXI.CONTRACT<br>iutiii:IUTIII.STEPXI.PARAMETRIC | 复用现有资产 |
| Ind1 | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean : generatedQuotientMap_eq_of_ind1Step, Ind1Setoid | OLEAN_FRESH | iut-skeleton:Ind1<br>iutiii:IUTIII.IND1 | 复用现有资产 |
| Ind2 | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean : Ind2AlienLink, linkMap_ind1Step | OLEAN_FRESH | iut-skeleton:Ind2<br>iutiii:IUTIII.IND2 | 复用现有资产 |
| Ind3 | theorem/CONDITIONAL | LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean : nonarchimedeanImageInclusion, ind3ImageWellDefined | OLEAN_FRESH | iut-skeleton:Ind3<br>iutiii:IUTIII.IND3 | 复用现有资产 |
| H5 | theorem/CONDITIONAL | tmp/sheaf/xif/paper/Hull09H5GapsActual.lean : hull09_scalingUnits_subset_hull, hull09_hull_eq_closure | OLEAN_FRESH | E-hull-h5-h7<br>e-deep:E2.H5framing<br>e-deep:E2.h5Gap | 复用现有资产 |
| H7Ob9 | theorem/CONDITIONAL | — | DAG node only (tree asset/paper) | E-hull-h5-h7<br>e-deep:E3.ob9Interface<br>e-deep:E3.deepOb9 | 复用现有资产 |
| HDD | def/DEF | tmp/sheaf/xif/paper/S1165SourceHDDReadoutGapActual.lean | OLEAN_FRESH | iut-skeleton:HDD | 复用现有资产 |
| HullDet | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean : HullDeterminantLogVolumeFrozenSpec, hullDeterminantLogVolumeFrozenSpec_holds | OLEAN_FRESH | iut-skeleton:HullDet<br>iutiii:IUTIII.HULL.DET_LOG_VOLUME<br>iutiii:PAPER.S3182.COR312_HULLDET | 复用现有资产 |
| K1K2 | theorem/CONDITIONAL | LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean : nonarchimedeanImageInclusion, ind3ImageWellDefined | OLEAN_FRESH | iut-skeleton:K1K2<br>iutiii:IUTIII.THM311.K1K2_CARD_GAP<br>legacy-dag:legacy:n8-group2-log-k1k2 | 复用现有资产 |
| SHE | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Corollary312/Obligations.lean : ipl, she | OLEAN_FRESH | e-deep:E1.logShellBridge<br>e-deep:logshell-frobenius-power<br>iut-pre-abc:LogShell.I | 复用现有资产 |
| APT | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Corollary312/Obligations.lean : ipl, she | OLEAN_FRESH | foundation:B2c.adapterUnconditional<br>iut-skeleton:APT<br>legacy-dag:legacy:n8-group5-ipl-she-apt | 复用现有资产 |
| IPL | theorem/CONDITIONAL | LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierHeightWeightRefutation.lean : isABCTriple_one_eight_nine, logHeight | OLEAN_FRESH | iut-skeleton:IPL<br>legacy-dag:legacy:n8-group5-ipl-she-apt<br>legacy-dag:legacy:n8-t10-ipl-family | 复用现有资产 |
| LogShell | def/DEF | LeanFormal/IUT/IUTIII/Theorem311/HullPresentationAlternativeProbe.lean : not_rayCut_family_of_incomparable_images, rayCut_family_image_chain | OLEAN_FRESH | e-deep:E1.logShellBridge<br>e-deep:logshell-frobenius-power<br>iut-pre-abc:LogShell.I | 复用现有资产 |
| Thetas | def/DEF | LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31A2GateReduction.lean : InitialThetaArithmeticFreeLayer, initialThetaArithmeticFreeLayer | OLEAN_FRESH | T6-iut4-theta-two-sided<br>E-theta-etth<br>iut-pre-abc:InitialTheta.data | 复用现有资产 |
| PrimeStrips | def/DEF | LeanFormal/IUT/Audit/Diagnostics/LegacyContracts.lean : Side, Copy | OLEAN_FRESH | iut-pre-abc:PrimeStrips.FD<br>iut-pre-abc:PrimeStrips.frobenioidCategory<br>iut-pre-abc:PrimeStrips.FxDAction | 复用现有资产 |
| Frobenioid | def/DEF | LeanFormal/IUT/IUTII/Frobenioid/Example36LocalContraction.lean : deltaAdd_inv_contraction, deltaAdd_div | OLEAN_FRESH | iut-pre-abc:Frobenioid.Example36<br>iut-pre-abc:Frobenioid.transport<br>iut-pre-abc:PrimeStrips.frobenioidCategory | 复用现有资产 |
| Kummer | theorem/CONDITIONAL | LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean : nonarchimedeanImageInclusion, ind3ImageWellDefined | OLEAN_FRESH | iut-pre-abc:Kummer.absolute<br>iut-pre-abc:Kummer.continuity<br>iut-pre-abc:Kummer.summary | 复用现有资产 |
| HodgeTheater | def/DEF | LeanFormal/IUT/IUTI/HodgeTheater/SourceClauseAssemblyUnitsReduction.lean : SourceClauseELocalFamilyUnit, selected_eq_V_eq_record_field | OLEAN_FRESH | iut-pre-abc:HodgeTheater.core<br>iut-pre-abc:HodgeTheater.family<br>iut-pre-abc:HodgeTheater.links | 复用现有资产 |
| InitialTheta | def/DEF | LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31A2GateReduction.lean : InitialThetaArithmeticFreeLayer, initialThetaArithmeticFreeLayer | OLEAN_FRESH | iut-pre-abc:InitialTheta.data<br>iut-pre-abc:InitialTheta.cStage<br>iut-pre-abc:InitialTheta.definition31 | 复用现有资产 |
| Section0 | def/DEF | — | DAG node only (tree asset/paper) | iut-pre-abc:Section0.countablyOrdered<br>iut-pre-abc:Section0.orientedGraph<br>iut-pre-abc:Section0.paths | 复用现有资产 |
| Gaussian | def/DEF | LeanFormal/IUT/IUTI/HodgeTheater/SourceThetaLinkArithmeticDisplacementReduction.lean : thetaSide_eq_gaussian_of_target_q, thetaSide_eq_gaussian_of_source_q | OLEAN_FRESH | iut-skeleton:Gaussian | 复用现有资产 |
| QPilot | theorem/CONDITIONAL | LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryGapCards.lean : possibleThetaPilotImageSet_eq_iUnion_singleton, possibleThetaPilotImageSet_eq_biUnion_finset | OLEAN_FRESH | iut-pre-abc:QPilot<br>iut-pre-abc:QPilot.arithmeticDivisor<br>iut-pre-abc:ThetaPilot.carrier | 复用现有资产 |
| IUT4Estimates | theorem/CONDITIONAL | tmp/sheaf/xif/paper/GenEll08MainReductionActual.lean : GenEllMainReductionStatement, genEll_mainReduction_shape | OLEAN_FRESH | T4-iut4-arithmetic-degree<br>T5-iut4-prop17<br>T6-iut4-theta-two-sided | 复用现有资产 |
| IUT4Sec2 | theorem/CONDITIONAL | tmp/sheaf/xif/paper/GenEll08MainReductionActual.lean : GenEllMainReductionStatement, genEll_mainReduction_shape | OLEAN_FRESH | e-deep:E5.iutivAdd<br>e-deep:E5.iutivSection1<br>e-deep:E5.iutivSection2 | 复用现有资产 |
| HeightVolume | theorem/CONDITIONAL | LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier.lean : FrontierHeightComparisonClause, FrontierRegionComparisonClause | OLEAN_FRESH | e-deep:E5.uniformHeightConsumer<br>iut-skeleton:HeightVolume<br>iutiii:IUTIII.HULL.DET_LOG_VOLUME | 复用现有资产 |
| Sources1995_2015 | named_input/NAMED | — | DAG node only (tree asset/paper) | iut-skeleton:Sources1995_2015 | **真缺口** |
| hCor312 | named_input/NAMED | — | DAG node only (tree asset/paper) | iut-skeleton:hCor312 | **真缺口** |
| hSlack | named_input/NAMED | — | DAG node only (tree asset/paper) | iut-skeleton:hSlack | **真缺口** |
| ClassB | named_input/NAMED | — | DAG node only (tree asset/paper) | iut-skeleton:ClassB | **真缺口** |
共 32 个 iut-skeleton paper 前置对象；有现有资产可复用 **28**；真缺口 **4**。

## 汇总

- 覆盖 paper 对象：**32 / 32**（iut-skeleton 全部）。
- 有现有 Lean/DAG 资产可复用：**28**（接口/树资产/已证层/条件层；状态见上表）。
- 无现有 Lean 资产的：**4**，全部是 **named_input**（`Sources1995_2015` / `hCor312` / `hSlack` / `ClassB`）——按定义不可证、保持 NAMED；不是“需要新建 Lean 对象”的缺口，只需在 DAG 挂 paper/named 边。
- 真缺口（需要新建 Lean 对象/构造的 paper 前置对象）：**0**（本次 32 对象内；此前已登记的 14+ statement skeleton、tree assets、interface 层均已覆盖；具体缺失在更深层的 proof body，而不是对象本身）。
- 复用现有节点数：**28 个对象均有 ≥1 个现有 DAG 节点**（H7Ob9 无 route-index row，但有 `e-deep:E3.ob9Interface`/`E3.deepOb9`/`iutiii:HULL.H7.OB9.*` 树资产节点，属复用而非缺口）。

## 证据等级与 caveat

- `OLEAN_FRESH`：仓库构建/olean 证据（构建通过），**不等于** CITABLE；CITABLE 需 checker + 版本钉住（见 V157/GATE 文档）。
- `TREE_ASSET` DAG 节点：编译资产（tree 中已证模块），尚未逐条重验；挂边时用 `evidence=observed_source` 仅当文件:声明实际匹配，否则 `planned`。
- 本表关键词匹配较粗（如 `SHE`/`APT`/`IPL` 短词会命中 sheaf 等），**仅作候选**；owner 挂边前必须核对精确声明名。
- 4 个 named_input 保持 NAMED，不得写成 PROVED/CONDITIONAL 假闭合。

## 与 iut-pre-* 新 fragment 的关系（A469/A470）

- 已收到 owner fragments：`iut-pre-abc`（37 nodes/39 edges）、`iut-pre-mainline`（50/71）、`iut-pre-stage4`（27/26）；其节点应**挂到本表既有 DAG 节点**（复用），而不是另建同名对象。
- 例如 `iut-pre-abc:LogShell.I/pStar/invariants/logFrobenius` 已引用 `LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean`（既有树资产）；`iut-pre-abc:PrimeStrips.*` 已引用 `PrimeStripsConstruction.lean`；`iut-pre-abc:Kummer.*` 已引用 `AbsoluteKummer*.lean`。这些均为复用路径。
- 审计结论：已收到的 iut-pre 节点以 def/theorem/target/interface 为主，未见 consumer/rollup/file 簿记混入（mainline 的 interface 1 个属允许接口层；stage4 的 `C.consumer.p1Composite` 是**定理级 consumer** 名称，不是文件簿记，但需 owner 说明其 theorem 语义）。

## 下一步（给 owner 的复用建议）

1. 对每个 iut-pre 节点：若上表有现有节点/文件:声明，则新增 statement/proof 边 `newNode -> existingNode`（或反向依赖），`evidence=observed_source`（文件:声明核对通过）或 `planned`；
2. 只在**真缺口**（本表 0 个对象；若 owner 区域发现更深层缺失 proof body，则属于 proof 任务，不是对象新建）时新建 Lean 文件；
3. 禁止把 named_input 写成已证；no sorry/axiom/fake closure；
4. 审计侧（lattice）收到更新后重跑 merge3+clean2+validate_decl2 并更新 `coord/IUT-PREREQ-DAG-REPORT.md`。

Prepared by lattice (maintenance & audit); survey only, no gate effect.

## A475 — 穷尽仓库搜索证据（禁止“需数学突破”表述）

**方法:** `rg -F` 搜 LeanFormal/、tmp/（含 tmp/sheaf/xif/paper）、coord/、papers/、dag/declarations-index.json 与 git 归档；对象名多轮变体（大小写/前缀/后缀/论文记号）；目标词 0 命中时记录精确搜索词与范围。**结论：此前标记为“缺口”的对象绝大多数在仓库已有实现/声明，可直接复用。**

| 缺口对象 | 搜索词/变体（范围） | 命中（文件:声明） | 处理 |
|---|---|---|---|
| `HTLink.rel/_refl/_symm/_trans/_symm_iff` | `HTLink.rel` exact（LeanFormal+tmp+ported+coord+declarations-index） | **exact 0 hit**；实际存在：`Mzk1HodgeTheaterLinkLawsActual.lean` 的 `structure HTLink` + `htRelRefl/htRelSymm/htRelTrans/htRelSymmIff/htRelSymmSymm/htRelTransSymm`；`Mzk1HodgeTheaterTransportLawsActual.lean` 的 `rel/rel_refl/rel_symm/rel_trans/rel_symm_iff` | 复用实际声明（见 `lattice:Map.HodgeTheater.linkCategoryLaws` note）；不挂不存在的声明 |
| `C.gap.fixedBetaChoice` | `fixedBetaChoice`/`fixedBeta`/`BetaChoice`（全树） | `tmp/sheaf/xif/paper/Mzk1StepProviderPrimeActual.lean` : `def StepProviderFixedBetaChoiceInput : Prop`（NAMED INPUT，不假证） | 复用现有节点；`coord/target-chain.lattice.json:Reuse.FixedBetaChoice`（evidence observed_source） |
| `C.gap.f4bNumMaxStrict` | `f4bNumMaxStrict`/`numMaxP`/`F4NumMaxStrict`/`numMax`（全树） | `tmp/sheaf/xif/paper/Mzk1F4bFiniteReuseActual.lean` : `def FiniteNumMaxStrictStatement : Prop`（+ `f4bFiniteReuseRows`）；`Mzk1NestedInductionActual.lean` : `numMaxP`/`numMax_stepSet_lt` | 复用 `FiniteNumMaxStrictStatement`；`Reuse.F4bNumMaxStrict` |
| `D.gap.schemeSideMaps` | `schemeSideMaps`/`schemeSide`/`sectionMap`/`placePoint`（全树） | `tmp/sheaf/xif/paper/Mzk1SchemeSideMapsActual.lean` : `structure SchemeSideMapsData`、`schemeSideMaps_sectionMap`、`schemeSideMaps_placePoint`、`schemeSideMapsRows_length`；`LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean` : `sectionMap` field | 复用；`Reuse.SchemeSideMaps` |
| `D.gap.problemDApplicability` | `ProblemDApplicability`/`problemD`/`ProblemD`（全树） | `tmp/sheaf/xif/paper/GenEll21GeometricCoreConsumerActual.lean` : `ProblemDApplicabilityInput`、`ProblemDCurveHypotheses`、`genEll21_geometricCore_of_problemD`；`coord/ProblemD_GeometricCoreSkeleton.lean` 参考骨架 | 复用；`Reuse.ProblemDApplicability` |
| `Gap.qPilotPreciseConstruction` | `qPilotPrecise`/`qPilot`/`QPilot`（全树） | `tmp/sheaf/xif/paper/Mzk1QPilotPreciseDataActual.lean` : `structure QPilotPreciseData`、`qPilotPreciseData_of_candidate`、`qPilotPreciseData_nonempty`；`Mzk1AbsTopIIIDeepStatementLayerActual.lean` 等 | 复用；`Reuse.QPilotPrecise`；我方 `Mzk1QPilotPreciseActual.lean` 标 superseded |
| `Gap.thetaPilotIQContainment` | `thetaPilotIQ`/`thetaPilot`/`IQ`（全树） | `tmp/sheaf/xif/paper/ShehddThetaPilotIQConsumerActual.lean` : `thetaPilot_IQ_containment`、`thetaPilotIQRows`、`thetaPilotIQRows_length`；`Mzk1ThetaPilotPreciseInterfaceActual.lean` | 复用；`Reuse.ThetaPilotIQ`；我方 record 节点标 superseded |
| `HTLink`（通用） | `HTLink`（全树） | 2 files: `Mzk1HodgeTheaterLinkLawsActual.lean`（owner abc）+ 我方 `Mzk1HodgeTheaterTransportLawsActual.lean` | 保留两处；不新建重复理论 |

**处理规则落地:** 复用节点统一写入 `coord/target-chain.lattice.json`（`Reuse.*` 节点，edge evidence=observed_source）；旧的自建 record/interface 节点 note 追加 `SUPERSEDED by Reuse.*`；未找到精确同名声明但存在等价实现时，用等价实现并在 note 记录“精确名 0 命中，等价声明在 ...”。

**搜索结果:** 本轮后 `dag_merge3` conflicts=0；`dag_validate_decl2` ok=true problems=0；DAG 1114 nodes / 1855 edges / isolated 0；zz-mapping 的 zz-stepxi 晚加载目标已移至 `coord/target-chain.zzz-lattice.json`（避免 forward ref unresolved）。

