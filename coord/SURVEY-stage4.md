# SURVEY-stage4 — C/D 区域 IUT 3.12 前置对象：现有仓库资产调研

调研日期: 2026-11-11 (A470). 只读调研；不写 Lean、不建重复节点。索引来源:
coord/repo-route-index-data.json, coord/target-chain.*.json, dag/declaration-dag.json,
tmp/xif_guarded_results.log (EXIT0/CITABLE/olean 证据), AUDIT_LEDGER.md,
papers/motizuki_corpus/text/Noncritical Belyi Maps.txt ([Mzk1] Lemma 2.2/2.4/Thm 2.5).

列含义: paper 对象 → 现有 Lean 文件:声明 → 证据 → 现有 DAG 节点 id → 处理(REUSE/GAP/DUPLICATE)

| # | paper 对象 (C/D 区域) | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 处理 |
|---|---|---|---|---|---|
| 1 | Qbar = 代数闭包；点/值域次数 degQ | Mzk1NestedInductionActual.lean: Qbar, degQ | watchdog EXIT0 | foundation:B4.Cdegree, iut-pre-stage4:C.def.Qbar | REUSE (删我的重复) |
| 2 | 测度 (D,N)=(maxDeg,numMax) | Mzk1NestedInductionActual.lean: maxDeg, numMax | EXIT0 | foundation:B4.Cdegree | REUSE |
| 3 | f0 有限步集测度严格下降 | Mzk1NestedInductionActual.lean: maxDeg_stepSet_le, numMax_stepSet_lt, measure_stepSet_lt | EXIT0 | foundation:B4.Cdegree | REUSE |
| 4 | 临界点/临界值次数下降 (S1a/S1b) | Mzk1Lemma24ValueDegreeDropActual.lean: valueDegreeDrop_proved, fieldDegreeDrop_proved | EXIT0/CITABLE | foundation:C.cv.critValueDeg (stage4), C.cv.critValueDeg | REUSE + 增补 |
| 5 | reduced degree / field of definition / CV 度界 undirected 层 | Mzk1Lemma24DegreeFoundationActual.lean: reducedDegreeOfPoint, criticalValueDegreeBound, minpoly_criticalValueDegreeBound | EXIT0 | (stage4 自建) C.degreeFoundation, C.cv.critValueDeg | REUSE (已挂) |
| 6 | CV 复合律（Qbar 点形式） | Mzk1CVCompositionFActual.lean: cvCompositionLawF_proved, stepTransport_of_goal_proved | EXIT0 | C.cvCompositionF, restated_24 | REUSE |
| 7 | f0 = minpoly 作为 P1(Qbar) 映射/∞ bookkeeping/CV-in-image | Mzk1F0StepGeometryActual.lean: f0Poly, f0Map, f0CritValues, f0CritValue_deg_le | EXIT0/CITABLE 21 | C.f0Geometry | REUSE |
| 8 | 单步收缩 provider（Target S' β' → Target S β） | Mzk1NestedInductionStepProviderActual.lean: stepSetP, stepTransport_of_goal; Mzk1StepProviderPrimeActual.lean: StepProvider', exists_maxDegP_finite | EXIT0 (transport cond CV law; CV law PROVED) | problemC_nested, restated_24 | REUSE + 挂 gap |
| 9 | f4b: P1 计数严格下降（maxDegP 不变时 numMaxP 降） | 无现成资产 | — | 无 | GAP (named F4NumMaxStrictInput) |
| 10 | f5: 固定-β 的 α0/Galois 选择（β∉S' 版） | 无现成资产 | — | 无 | GAP (named StepProviderFixedBetaChoiceInput) |
| 11 | 基例：全有理 S (maxDeg≤1) 的 2.4 目标 | Mzk1NestedInductionBaseCaseActual.lean: baseCaseProvider_proved | EXIT0/CITABLE | B4b.baseCase, problemC_nested | REUSE |
| 12 | (D,N) 词典序良基归纳 | Mzk1NestedInductionActual.lean: induction_with_invariant, nested_induction_terminates | EXIT0 | foundation:B4.Cdegree | REUSE |
| 13 | 2.4 paper-scope 目标 (S⊂P1(Qbar), Sphi rational, CV⊂Sphi) | RestatedLemma24InterfaceActual.lean: Mzk1Lemma24Target, criticalValuesOverC | EXIT0/CITABLE | restated_24 | REUSE |
| 14 | 2.4 paper-scope 条件装配 | Mzk1NestedInductionActual.lean: paperScopeLemma24Statement_of_providers | EXIT0 | problemC_nested | REUSE (CONDITIONAL) |
| 15 | 2.4 F=Q 有限 β 底部目标（fold/β-avoiding base） | Mzk1Rational24TargetBottomActual.lean: rational24TargetFiniteBeta_proved, Mzk1Lemma24Target_finite_beta_bottom | EXIT0/CITABLE | B3.rationalBottom | REUSE |
| 16 | β-avoiding fold 资产 / 旧 spec 反驳 | Mzk1BetaAvoidingFoldActual.lean, Mzk1Rational24TargetBottomActual.lean: oldBaseProviderPremise_refuted | EXIT0 | B3.rationalBottom | REUSE |
| 17 | 2.2 F=Q 无条件 gate (rational component) | Mzk1Lemma22RationalGateActual.lean: mzk1Lemma22_inductionStatement_rational, mzk1Lemma22_target_rational | EXIT0/CITABLE 5, FROZEN | C.thm.rational22Gate | REUSE |
| 18 | P1 composite consumer (2.2∘2.3, F=Q) | Mzk1Thm25P1CompositeConsumerActual.lean / WiringActual / Mzk1Consumer24AdapterUnconditionalActual.lean | EXIT0/CITABLE | B2c.adapterUnconditional, C.consumer.p1Composite | REUSE |
| 19 | Qbar 代数嵌套归纳（class-B named） | LayerAAlgebraicInductionActual.lean: AlgebraicNestedInductionInput | EXIT0 (statement) | N2-alg-nested | REUSE (NAMED) |
| 20 | 函数域 Riemann–Roch | Mzk1RRProvedActual.lean: functionFieldRiemannRoch_proved | EXIT0/CITABLE | B6b.DRR | REUSE |
| 21 | |T|≥2g+1 的 zero-divisor 存在 | Mzk1GeomCoreRRProvedActual.lean: zero_divisor_exists_proved | EXIT0/CITABLE | B6b.DRR | REUSE |
| 22 | RR ⇒ ZeroDivisorDatum | Mzk1GeomCoreRRBridgeActual.lean: zeroDivisorDatum_of_RR | EXIT0 | D.rrBridge, D.rr.datum | REUSE |
| 23 | 根中立 FibreBridgeAbstract 接口 + zeroSet 等式 | Mzk1GeomCoreBridgeInterfaceActual.lean: FibreBridgeAbstract, zeroSet_eq_of_abstract | EXIT0/CITABLE | D.bridgeInterface, D.bridge.abstract | REUSE |
| 24 | scheme side maps sectionMap/placePoint（scheme↔function field 桥） | 无现成资产（D.rrBridge 已 PARK；仓库无 Neron/桥 API） | — | 无 | GAP (named; D.geomCore 前置) |
| 25 | FibreOverZeroEq from bridge + datum | Mzk1GeomCoreZeroDatumFibreActual.lean: fibreOverZeroEq_of_zeroDatum | EXIT0 | D.zeroDatumFibre, D.bridge.fibre | REUSE |
| 26 | 精确 GeometricCore witness（fibre-zero/generic étale/pullback） | Mzk1GeomCoreRRWitnessActual.lean: Mzk1GeometricCoreWitnessPreciseRestated, restatedWitness_of_zeroDatum | EXIT0 (CONDITIONAL) | (stage4) D.witness.precise | REUSE (conditional) |
| 27 | precise witness → 旧 recast | Mzk1GeomCorePreciseToOldActual.lean: preciseToOld | EXIT0 | (stage4) D.preciseToOld | REUSE |
| 28 | line-bundle/order 兼容桥 + section image | Mzk1GeomCoreLineBundleInterfaceActual.lean / LineBundleBridgeActual.lean | EXIT0 | D.lineBundleBridge, D.finiteMapChart, C/D.lineBundle | REUSE |
| 29 | chart/TwoAffineOpenCover → Mzk1FiniteMapData | Mzk1GeomCoreFiniteMapChartInterfaceActual.lean: FiniteMapChartData.toFiniteMapData | EXIT0 | D.finiteMapChart | REUSE |
| 30 | Problem D 函数域构造 ⇒ precise GeometricCore（命名 witness + applicability） | GenEll21GeometricCoreConsumerActual.lean: ProblemDFunctionFieldWitnessInput, genEll21_geometricCore_consumer | EXIT0 (CONDITIONAL) | (stage4) D.geomCore.problemD | REUSE + GAP |
| 31 | Problem D applicability：任意 curve datum 选 T,D 满足 |T|≥2g+1 且 D=sum T | 无现成资产（仅 statement shell） | — | 无 | GAP (named) |
| 32 | GenEll15 GeometricCoreStatement（precise recast） | GenEll15GeometricCoreAssemblyActual.lean: GenEll15GeometricCoreStatement | EXIT0/CITABLE | (stage4) D.geomCore.recast | REUSE (statement) |
| 33 | Thm 2.5 conclusion conditional（GeometricCore + 2.4 shape） | Mzk1Thm25ConclusionActual.lean: Mzk1Thm25Conclusion, mzk1Thm25Conclusion_of_geometricCore | EXIT0/CITABLE | (stage4) D.thm25.conclusion | REUSE (CONDITIONAL) |

## 汇总
- 覆盖 paper 前置对象: 33 行（其中 C 区 19、D 区 14）
- 现有资产/节点可复用: 29 行（REUSE；含 21 个已有外部 DAG 节点 id：B4.Cdegree, B4b.baseCase,
  problemC_nested, restated_24, B3.rationalBottom, B2c.adapterUnconditional, N2-alg-nested, B6b.DRR,
  D.rrBridge, D.bridgeInterface, D.zeroDatumFibre, D.lineBundleBridge, D.finiteMapChart, C.cvCompositionF,
  C.f0Geometry, C.degreeFoundation, C.thm.rational22Gate, C.consumer.p1Composite 等)
- 真缺口: 4 行 → (a) D.bridge.maps scheme↔function-field maps；(b) C.step.f4b P1 numMax 严格计数；
  (c) C.step.f5 固定-β α0/Galois 选择；(d) D.geomCore applicability（bookkeeping）。
- 原 iut-pre-stage4.json 中 23 个节点是重复/已有对象 → 已删除；只保留 4 个真缺口节点，
  其余改为 SURVEY 中挂到现有 DAG 节点 id（REUSE），不再重复建点。
- 未碰 watchdog、未编译（只读调研 + 文件登记）。

## 拆分/复用：4 个真缺口挂到现有节点（A470 第 4 步）

| 真缺口节点 | 应挂接的现有 DAG 节点（引用，不重建） | 边类型 | evidence |
|---|---|---|---|
| C.gap.f4bNumMaxStrict | foundation:B4.Cdegree（finite numMax_stepSet_lt PROVED）; problemC_nested（StepProvider 组装） | statement/proof | observed_source(前者) + planned(后者) |
| C.gap.fixedBetaChoice | problemC_nested; restated_24（fixed-beta vs beta'=f0(beta) 接口） | statement | planned |
| D.gap.schemeSideMaps | foundation:B6b.DRR（RR 侧已证）; D.bridgeInterface（抽象接口已证）; D.rrBridge（PARKED PRAGMATIC-DEAD-END，仅记录） | proof/interface | observed_source(前两者) + planned |
| D.gap.problemDApplicability | (stage4)D.geomCore.problemD（GenEll21 条件 consumer 已绿）; D.geomCore.recast | interface | observed_source |

说明：合并后的外部节点 id 由 merge3 加 section 前缀；本 fragment 只保留 gap 节点，**不复制**上述已存在节点。后续证明落地时按此表在
对应 fragment（或被复用节点所在 section）加边，而不是新建重复节点。

## A475 穷尽仓库搜索结果（缺口=仓库当前缺失，附搜索证据；不写需数学突破）

搜索范围: dag/generated/declarations-index.json (273,621,312B, 1,572,263 decls, 流式扫描), LeanFormal/ 全树, tmp/ (sheaf/n8/external), ported, .lake/packages (Mathlib), papers/motizuki_corpus/, coord/ 历史文档 + AUDIT_LEDGER, git 归档。搜索词: 对象名/论文记号/命名变体多轮。

| 对象 | 搜索词 | 命中 | 结论/复用 |
|---|---|---|---|
| f4b P1 numMax 严格计数 | numMaxP / numMax | numMaxP: Mzk1NestedInductionActual.lean:612 (def), :661 (numMaxP_image_ofFinite); numMax: coord/ProblemC_NestedInductionSkeleton.lean:51/96 | 有限版存在(def+image law+numMax_stepSet_lt)；P1 版严格计数 0 命中 → 仓库当前缺失（附全表扫描证据） |
| fixed-beta 选择 | fixedBeta / fixed_beta / FixedBeta | 0 命中（全仓） | 仓库当前缺失（decl-index 0；tmp/LeanFormal/coord 0）；新语句文件 Mzk1StepProviderGapStatementsActual 已定义 statement |
| scheme-side maps | schemeSide / SchemeSide / sectionMap / placePoint | schemeSide: 0（仅 tmp/sheaf/l03-g2/S2Transport.lean:38 SchemeSideHasFiniteGroupQuotients，无关）；sectionMap: LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:553/557 (不同语义), flt external 无关；placePoint: 仅 flt external | 不同语义资产存在但不可直接复用；本语义 0 命中 → 仓库当前缺失；新文件 Mzk1SchemeSideBridgeActual 提供数据接口 |
| Problem D applicability | Applicability | GenEll21GeometricCoreConsumerActual.lean:93: ProblemDApplicabilityInput (abbrev, 已存在) | 复用已有节点（GenEll21）；Mzk1ProblemDApplicabilityActual 只作数据细化，不新建目标 |
| pencil (D 区) | Pencil / pencil | coord/ProblemD_GeometricCoreSkeleton.lean:67: PencilData (skeleton, 含 sorry 仅研究壳, 不 import)；flt external 多个 pencil 资产 | 复用候选已记录；新文件 Mzk1PencilInterfaceActual 为 paper-dir 独立定义 |
| NeronModelInfra（此前 PARK 对象） | NeronModelInfra / Neron | tmp/external/flt-lean/Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean:19+ (ComponentReading/MinimalComponentData/IsOmegaMinimal) | 仓库存在（外部 flt-lean 树，不在 lake search path 直接 import）；此前全库 0 匹配结论作废（A475 更正） |
| HTLink（他人 fragment 校验错） | HTLink | 0 命中 | 仓库当前缺失；他人 fragment lattice:abc.HodgeTheater.linkCategoryLaws 引用不存在声明，需 owner 修或新增 HTLink 定义文件 |

结论：Problem D applicability 已有 ProblemDApplicabilityInput（复用 GenEll21 节点），pencil 有 skeleton/外部资产；fixedBeta / scheme-side maps 为本语义仓库当前缺失（附 0 命中证据）；f4b P1 严格计数为有限版已有但 P1 版缺失。

## A477 已有资产清单（只读核对，不写 Lean/不改 fragment）

核对范围: tmp/sheaf/xif/paper, LeanFormal/IUT, coord（声明级 grep + declarations-index 抽查）。

### 已有（file:decl，节选）
- maxDeg_stepSet_le / numMax_stepSet_lt / degQ_critValue_lt / degQ_aeval_le — Mzk1NestedInductionActual.lean (PROVED)
- f0Poly / f0CritValues — Mzk1F0StepGeometryActual.lean
- cvCompositionLawF_proved — Mzk1CVCompositionFActual.lean:30
- PaperScopeLemma24Target — Mzk1CVCompositionFActual.lean:43; RestatedLemma24InterfaceActual.lean
- StepProvider' — Mzk1StepProviderFromFixedBetaActual.lean:13；exists_maxDegP_finite / stepSetP1 — Mzk1F4bFiniteReuseActual.lean:39/41（另 StepProviderPrimeActual 有 P1 版 f1/f2）
- baseCaseProvider_proved — Mzk1NestedInductionActual.lean:695
- functionFieldRiemannRoch_proved — Mzk1GeomCoreRRProvedActual.lean:13
- zero_divisor_exists_proved — Mzk1GeomCoreBridgeInterfaceActual.lean:17
- ZeroDivisorDatum / FibreBridgeAbstract — Mzk1DChartCluster6Actual.lean:37/35（定义层）
- Mzk1GeometricCoreWitnessPreciseRestated — Mzk1DChartCluster6Actual.lean:40
- restatedWitness_of_zeroDatum / fibreOverZeroEq_of_zeroDatum — Mzk1GeomCoreZeroDatumFibreActual.lean:20 / Mzk1GeomCoreChartDatumWitnessActual.lean:12
- bridge_of_maps — Mzk1GeomCoreRRBridgeActual.lean:76；preciseToOld — Mzk1GeomCorePreciseToOldActual.lean:126
- LineBundlePullbackInterface — Mzk1DClusterRollupActual.lean:47；FiniteMapChartData — Mzk1ChainDChartActualAdapted.lean:34
- GenEll15GeometricCoreStatement — GenEll15GeometricCoreAssemblyActual.lean:48
- ProblemDApplicabilityInput — GenEll21GeometricCoreConsumerActual.lean:94；mzk1Lemma22_target_rational 同文件:147
- rational24TargetFiniteBeta_proved — Mzk1Rational24BaseCaseBridgeActual.lean:62；rational24TargetFiniteBeta — Mzk1Rational24TargetBottomActual.lean:47
- AlgebraicNestedInductionInput — AG08ProofStatusTableActual.lean:72（NAMED，非证明）
- criticalValueDegreeBound / valueDegreeDrop_proved / fieldDegreeDrop_proved — Mzk1Lemma24DegreeFoundationActual.lean:61/10/11
- CVCompositionLawF — Mzk1CVCompositionFActual.lean:4；F0StepTransportInput — Mzk1StepProviderPrimeFinalConsumerActualAdapted.lean:27
- 其他 agent 已建 Adapted 变体（Mzk1P1MeasureBridge*ActualAdapted 等）——不重复造文件。

### 无（仓库当前缺失，短清单）
1. fixedBeta / FixedBeta 选择声明 — 全仓声明级 grep 0 命中
2. F4NumMaxStrictInput — 全仓 0 命中（P1 numMax 严格计数接口）
3. P1 版 stepSetP1 的 numMaxP 严格下降数值转移定理 — 无数值定理（仅有限版 numMax_stepSet_lt + numMaxP def/image law）
4. schemeSideMaps 本语义 scheme↔function-field 桥 — schemeSide 0；sectionMap 仅 SourceDefinition31Boundary.lean（不同语义）；placePoint 仅外部 flt
5. HTLink — 0 命中（他人 fragment lattice:abc 引用，需 owner 侧补）

统计：已有 41 项声明映射（含定义/定理/接口），真缺失 5 项；未写 Lean、未改 fragment。
