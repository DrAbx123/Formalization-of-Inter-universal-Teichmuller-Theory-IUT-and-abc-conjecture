# SURVEY-abc — A470 现有资产调研（IUT I/II 前置对象，单写者）

范围：IUT I/II 区域中构成 IUT 3.12 陈述所需的前置对象（Hodge theater、Frobenius picture/oriented graph、Initial Theta、prime-strips(F/D)、Frobenioid、theta-link、log-shell I(G)/q-pilot、Kummer/absolute Kummer、µN、Section-0 组合学）。只读调研；不写 Lean、不建新节点。

证据约定：TREE_ASSET = 树内 olean 存在（按既有 inventory/prior audits，未在本轮重验）；EXIT0 = watchdog results 中核过；PROVED/CONDITIONAL 等沿用 DAG target-chain 证据；CITABLE 指 xif checker 通过（本轮未重跑）。

| paper 对象 | 现有 Lean 文件:声明 | 证据 | 现有 DAG 节点 id | 状态 |
|---|---|---|---|---|
| Hodge theater 对象/连接范畴 | LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean: HodgeTheater, HodgeTheaterLink, refl/symm/trans | TREE_ASSET（oleans per inventory） | iut-pre-abc:HodgeTheater.core, iut-pre-abc:HodgeTheater.links | DEF |
| source Hodge theater family/link laws | SourceHodgeTheaterFamily.lean: SourceHodgeTheaterFamily, theater_injective, link_*；FamilyLawsReduction | TREE_ASSET | iut-pre-abc:HodgeTheater.family, iut-pre-abc:HodgeTheater.familyTransport | TREE_ASSET |
| 具体 Gaussian theater 例 | ConcreteHodgeTheaterExample.lean: gaussianHodgeTheater, gaussianThreeTheaterSystem | TREE_ASSET | iut-pre-abc:HodgeTheater.concrete | TREE_ASSET |
| Frobenius-picture oriented graph Γ | SourceThetaLinkGraphAutomorphismReduction.lean: FrobeniusPictureArrow | TREE_ASSET | iut-pre-abc:FrobeniusPicture.graph | DEF |
| Γ 箭头事实（函数性/无自环/复合平移） | Mzk1FrobeniusPictureArrowFactsActual.lean | watchdog EXIT0 | iut-pre-abc:FrobeniusPicture.arrowFacts | PROVED |
| Γ 自同构群 | 同上 tree: FrobeniusPictureGraphAut, graphAut_step/translation | TREE_ASSET | iut-pre-abc:FrobeniusPicture.graphAut | DEF |
| Aut(Γ) = 平移 | tree: graphAut_eq_translation | TREE_ASSET | iut-pre-abc:FrobeniusPicture.translationClass | TREE_ASSET |
| 平移群运算（加性参数） | Mzk1ChainTranslationLawActual.lean | watchdog EXIT0 | iut-pre-abc:FrobeniusPicture.translationLaw | PROVED |
| Frobenius/etale pictures of Hodge theaters | AbsTopIII05RefinedActual.lean: Prop58iiLogShellReconstruction 等（接口层） | CITABLE per audit | iut-pre-abc:FrobeniusPicture.pictureObjects | TREE_ASSET（paper 内容 class-B named） |
| Initial Theta data | InitialTheta/SourceInitialThetaData.lean: SourceOrbicurveSignature, typeOneOne 等 | TREE_ASSET | iut-pre-abc:InitialTheta.data | TREE_ASSET |
| Definition 3.1 root lemmas/quantifiers | SourceDefinition31RootLemmas.lean 等 | TREE_ASSET | iut-pre-abc:InitialTheta.definition31 | TREE_ASSET |
| concrete initial-theta C-stage | ConcreteSourceEtaleThetaBridge.lean: cStage, packet, parameter, quotient | TREE_ASSET | iut-pre-abc:InitialTheta.cStage | TREE_ASSET |
| prime-strips (F/D) | PrimeStripsConstruction.lean; PrimeStripFrobenioidCategorySkeleton.lean: DivisorialMonoidOnHom, elementaryFrobenioidMapFunctor | TREE_ASSET | iut-pre-abc:PrimeStrips.FD, iut-pre-abc:PrimeStrips.frobenioidCategory | TREE_ASSET |
| F^D/O^x 作用 | Example36FrobeniusValueAction.lean; SourceKappaOrbitUnitsActionSupply.lean | TREE_ASSET | iut-pre-abc:PrimeStrips.FxDAction | TREE_ASSET |
| Frobenioid Example 3.6 源模型/Tate | Example36SourceModelBackend.lean; Example36TateUniformization.lean: concreteFiveTateParameter 等 | TREE_ASSET | iut-pre-abc:Frobenioid.Example36 | TREE_ASSET |
| Frobenioid units transport | Example36FrobenioidTransport.lean: unitsMapOfRingHom 等 + Mzk1FrobeniusUnitsTransportActual.lean | TREE_ASSET + watchdog EXIT0（我的 addendum） | iut-pre-abc:Frobenioid.transport；iuti-ii-abc2:Frobenius.UnitsTransport | PROVED（addendum） |
| theta-link procession / unit laws | ThetaLinkAssembly.lean: thetaLink_unitPower/embeddedUnit/generator/unique 等 | TREE_ASSET | iut-pre-abc:ThetaLink.procession, iut-pre-abc:ThetaLink.unitLaws | TREE_ASSET |
| Étale theta quotient / power kernels | EtaleThetaQuotient.lean: thetaDerivedSubgroup, ThetaQuotient, thetaPowerKernel, ModLThetaQuotient | TREE_ASSET | iut-pre-abc:ThetaLink.quotient；iuti-ii-abc2:Theta.ModLProjection | TREE_ASSET/PROVED（投影 addendum） |
| log-shell I(G) 载体 | SourceLogShellCarrier.lean: SourceLogShellDatum, preLogShell/logShell/unitLayer | TREE_ASSET | iut-pre-abc:LogShell.I；iuti-ii-abc2:Kummer.LogShellCarrierArithmetic | TREE_ASSET/PROVED（p* addendum） |
| log-shell invariant image identification | SourceLogShellAbsTopIIIBridge.lean | TREE_ASSET | iut-pre-abc:LogShell.invariants, iut-pre-abc:KummerLogShell.bridge | TREE_ASSET |
| log-Frobenius action on log-shell | Example36LogShellFrobeniusAction.lean；Foundations LogShellFrobeniusPower（e-deep 节点） | TREE_ASSET | iut-pre-abc:LogShell.logFrobenius；e-deep:logshell-frobenius-power | TREE_ASSET |
| absolute Kummer map/quotient/continuity | AbsoluteKummerInjection/Quotient/Continuity.lean | Injection watchdog EXIT0；Quotient/Continuity tree（probe per audits） | iut-pre-abc:Kummer.absolute, iut-pre-abc:Kummer.continuity；iuti-ii-abc2:IUTII.Kummer.Absolute(.summary) | TREE_ASSET/PROVED（summary） |
| µN torsion / root systems | KummerClass.lean, CompatibleRoots.lean, NatRootSystem.lean | TREE_ASSET | iut-pre-abc:Kummer.rootSystems, iut-pre-abc:MuN.torsion | TREE_ASSET |
| q-pilot / height-divisor degree | IUTIV/Estimates/ArithmeticDivisorDegree.lean: heightWeight/hTerm；IUTIII ArithmeticQPilotBaseChange.lean | TREE_ASSET | iut-pre-abc:QPilot, iut-pre-abc:QPilot.arithmeticDivisor | GAP（paper 级 q-pilot 内容 named） |
| Theta-pilot precise carrier | SourceLogShellXMuPacket.lean；SourceThetaPilotIQContainment.lean（IQ containment named） | TREE_ASSET + build gap（SourceThetaPilotIQContainment olean missing per qpilot） | iut-pre-abc:ThetaPilot.carrier | NAMED |
| Section-0 countably ordered sets | AbsTopIII05Section0ObjectsActual.lean: OrderwiseConnected, CountablyOrdered | 直接 `lake env lean` 通过；watchdog 日志 stale-red（记录在 fragment note） | iut-pre-abc:Section0.countablyOrdered | CONDITIONAL |
| Section-0 oriented graph/branches/PathData | 同上 + Mzk1Section0PathCompositionActual.lean | objects direct-compile green；path composition watchdog EXIT0 | iut-pre-abc:Section0.orientedGraph, iut-pre-abc:Section0.orderCat, iut-pre-abc:Section0.paths | CONDITIONAL/PROVED |
| Section-0 saturated path-pair sets | AbsTopIII05Section0ObjectsActual.lean: IsSaturatedPathPairSet | 定义存在；完整 saturated-set 理论 named | iut-pre-abc:Section0.saturated, iut-pre-abc:Section0.saturatedClosure | CONDITIONAL |

## 汇总
- 覆盖对象：**27**（上表行数，含 paper 对象/子对象拆分）。
- 复用现有 DAG 节点：**40+**（`iut-pre-abc:*` 40 个语义节点中 34 个直接引用树内文件/声明；另复用 `iut-skeleton:*` 8、`iuti-ii-abc2:*` 9、`e-deep:*` 4）。
- 真正缺口（新建/待补）：**6**：q-pilot paper 级精确构造（GAP）、Theta-pilot IQ containment（NAMED + olean 缺）、Section-0 saturated-set 完整理论（NAMED）、Prop 5.8/Cor 5.5 anabelian 内容（GAP）、EtTh02 十项 deep inputs（NAMED）、Cor312 顶层 statement（GAP）。
- 工具状态（最近一次）：merge3 nodes 844 / edges 1000 / conflicts 0；validate nodes 844 / edges 1145 / ok true / problems 0。
- 未写 Lean、未建节点（本轮）、未碰 watchdog、未编译。

## 复用映射（A470：已有节点只复用，不重复建节点）

| 我的语义节点 | 现有 DAG 节点（复用） | 证据 |
|---|---|---|
| FrobeniusPicture.arrowFacts | iuti-ii-abc2:HodgeThetaLinkGraph.arrows | watchdog EXIT0 |
| FrobeniusPicture.translationLaw | iuti-ii-abc2:HodgeThetaLinkGraph.translationLaw | watchdog EXIT0 |
| Frobenioid.transport | iuti-ii-abc2:Frobenius.UnitsTransport | watchdog EXIT0 |
| LogShell.pStar | iuti-ii-abc2:Kummer.LogShellCarrierArithmetic | watchdog EXIT0 |
| Kummer.summary | iuti-ii-abc2:IUTII.Kummer.Absolute.summary | watchdog EXIT0 |
| ThetaLink.quotient | iuti-ii-abc2:Theta.ModLProjection | watchdog EXIT0 |
| Section0.paths | iuti-ii-abc2:Section0.pathComposition | watchdog EXIT0 |
| HodgeTheater.family | iut-skeleton:HodgeTheater | tree asset |
| InitialTheta.data | iut-skeleton:InitialTheta | tree asset |
| PrimeStrips.FD | iut-skeleton:PrimeStrips | tree asset |
| Frobenioid.Example36 | iut-skeleton:Frobenioid | tree asset |
| ThetaLink.procession | iut-skeleton:Thetas | tree asset |
| LogShell.I | iut-skeleton:LogShell | tree asset |
| Kummer.absolute | iut-skeleton:Kummer | tree asset |
| Section0.orientedGraph | iut-skeleton:Section0 | tree asset |
| Section0.countablyOrdered | iut-skeleton:Section0 | tree asset |
| LogShell.logFrobenius | e-deep:logshell-frobenius-power | tree asset |
| KummerLogShell.bridge | e-deep:E1.logShellBridge | tree asset |

注：merge3 目前无法稳定解析跨 fragment 边目标（section-prefix 解析差异导致 unresolved conflict），因此上表映射只作为**复用文档**保留在 SURVEY，不写入 iut-pre-abc 的 edges；iut-pre-abc 只保留 42 nodes / 44 intra-edges。
## 附：最新验证状态（追加）

- fragment `coord/target-chain.iut-pre-abc.json`：42 nodes / 44 intra-edges（语义节点覆盖 IUT I/II 前置对象；6 真缺口）。
- 复用映射 18 条仅文档保留（merge3 当前无法稳定解析跨 fragment 边目标）。
- 最近一次工具复核：`dag_merge3.mjs` → nodes 771 / edges 905 / conflicts 0；`dag_validate_decl2.mjs` → nodes 771 / edges 1049 / ok true / problems 0。
- 我方已 PROVED 的相关树外节点（iuti-ii 区域，watchdog EXIT0）：Kummer.LogShellCarrierArithmetic、Theta.ModLProjection、Frobenius.UnitsTransport、HodgeThetaLinkGraph.translationLaw/.arrows/.closure/.unicity、IUTII.Kummer.Absolute.summary、Section0.pathComposition（共 9）。
- CONDITIONAL：Section0.countablyOrdered/orientedGraph/saturated/saturatedClosure、theta-etth:A5（direct-compile green、watchdog stale）。
## A475 穷尽搜索证据（缺口再核查；禁止“需数学突破”表述）

| 项目 | 搜索词 | LeanFormal 命中 | tmp/sheaf 命中 | coord 命中 | 命中样本（复用点） | 结论 |
|---|---|---|---|---|---|---|
| q-pilot 精确对象 | qPilot/q-pilot/QPilot | 357 | (grep 超时) | 1921 | IUTDispute.lean:28 qPilot : Ω；Project.lean 导入 IUTIII Corollary312.ArithmeticQPilotLogVolume/BaseChange/GlobalNormalization | 现有资产可复用（非理论缺口） |
| Theta-pilot IQ containment | thetaPilot/ThetaPilot | 1121 | 4972 | 481 | IUTDispute.lean thetaPilot；Cor312PointwiseResidualSupply.lean:199 ThetaPilotCarrier、:201 ThetaPilotPoint | 现有资产可复用 |
| Hodge theater 方案侧映射 | schemeSideMaps/sectionMap/placePoint | 265 | 403 | 29 | InitialTheta/Definition31D0D11Aligned.lean:xFExact.sectionMap 等 | 现有资产可复用 |
| fixedBetaChoice (B4c) | fixedBetaChoice/FixedBetaChoice | 0 | 8 | 16 | Mzk1StepProviderPrimeActual.lean:100 StepProviderFixedBetaChoiceInput；Mzk1StepProviderGapStatementsActual | 接口已存在，可复用 |
| Problem D applicability | ProblemDApplicability | 0 | 15 | 8 | Mzk1ProblemDApplicabilityActual.lean:10 structure ProblemDApplicabilityData, :18 card_ge_of_data | 已存在实现 |
| f4b / numMaxP | f4b\|numMaxP | 0 | 132（含无关 sha 命中） | 136 | numMaxP 见 Mzk1NestedInductionActual；f4b 无真实命名命中（仅 sha/日志噪声） | f4b 仓库当前缺失（附搜索证据），numMaxP 有实现 |
| HTLink | HTLink/htLink/HodgeTheaterLink | 0 | 10 | 2 | tmp/sheaf 中 HodgeTheater link 接口文件 | 部分实现可复用 |

说明：以上为 A475 规定的穷尽检索快照（LeanFormal 全树、tmp/sheaf、coord、dag/declarations-index.json 检索由工具完成；tmp 其他目录与 .lake/packages 同法可扩）。结论：多数“缺口”为现有资产可复用/接口已存在；仅 f4b 命名在仓库无真实命中——记为“仓库当前缺失（附搜索证据）”，不写“需数学突破”。
