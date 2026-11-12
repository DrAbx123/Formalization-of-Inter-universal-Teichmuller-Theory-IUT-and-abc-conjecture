# A482 LADDER：按 Mochizuki《Formalization of IUT (2026-04)》§4 的物种/变换阶梯

来源：`papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt`（§2 五阶段；§3 逻辑结构；§4 skeletal Lean 码）。

## 官方五阶段（原文）
1. Stage 1: [IUTchIII] Theorem 3.11 ⇒ Corollary 3.12
2. Stage 2: Theorem 3.11 modulo [IUTchI-II]
3. Stage 3: [IUTchI-II] modulo 1995–2015 结果
4. Stage 4: 1995–2015 结果（[pGC],[GeoAn],[AbsAnb],[NCBel],[AbSc],[SemiAn],[QuCnf],[CbGC],[Config],[FrdI-II],[EtTh],[GenEll],[NodNon],[AbsTopI-III]）
5. Stage 5: 数值部分（[IUTchIV], [ExpEst]）

## §4 四个三角（species/mutations）与 Lean 资产对应

| # | 变换 | 论文语义 | 现有 Lean 资产 | 状态 |
|---|---|---|---|---|
| 1 | BPS --mlt. algo.→ mlt. rep. | 多radial算法：以 BPS 为输入产出多radial表示 | `SourceLogShellCarrier`, `PrimeStripsConstruction`, `SourceHodgeTheater*`, `SourceDThetaConstruction`, `SourceH1H2Construction`, `MultiradialAlgorithmReduction`, `SourceFiniteMultiradial` | 对象部分有；算法打包待做 |
| 2 | mlt. rep. --(dsc)→ BPS+0-col(etHT) | descent：Ind1/2/3 下从 etHT 构造多radial表示 | `Ind1Reduction`, `Ind2Reduction`, `K1K2BoundaryReduction`(Ind3), `SourceColumnCarrierIdentification`, `SourceProcessionStepXI`, `SourceAdjacentColumnProcessionIsomorphism` | dsc 组件有；四三角合成待做 |
| 3 | mlt. rep. --(hull+det)→ rep+hull+det | hull+det：取拓扑模的 determinant 得到 hull/体积 | `HullDeterminantLogVolumeReduction`（FrozenSpec）、`PaperIQCarrierActual`（actualIQInterface）、`S2723GlobalIQHullActual`（globalIQUnitRegion_compact/globalIQHaar）、`S3129IQHullLogVolumeSourceActual` | 组件有；literal 载体上的 hull 有限性待证 |
| 4 | (HDD)◦(SHE)：q-plt+etHT | 第4三角：q-pilot 与 Θ-pilot 同时比较 → 3.11.5⇒3.12 | `ArithmeticQPilot*`, `CardHullRealGeometryGapCards`, `S1929LiteralIQCarrierActual`, `SourceSHETransportObligations`, `Obligations.lean`(ipl/she), `StepXI/APT.lean`, `CertificateHullWiring`, `ConcreteFiniteRouteColumns`, `StepXIContract` | 目标 rung；literal 载体上 3.11.5⇒3.12 待组装 |

## 关键定义（paper）
- BPS = “basic prime-strip” = `F ⊩▶ × µ`-prime-strip（原文 IUT I/II 的 F×µ-prime-strip）
- etHT = étale Hodge theater（IUT I 的 Hodge theater 的 étale 部分）
- 多radial表示 = 对 0-column 的 quotients（Ind1,2,3）
- (hull+det)：对多radial表示中的拓扑模取 determinant
- (SHE)：simultaneous holomorphic expressibility（q-pilot 的可表达性）
- Thm 3.11：(dsc) + APT + IPL ⇒ 第1/2/3三角
- Thm 3.11.5：(hull+det)∘(dsc) + SHE + IPL ⇒ 第4三角
- Cor 3.12：q-pilot 与 Θ-pilot 的比较

## 本轮起的分工（不得再走 value-model/抽象接口路线）
- **abc**：literal IQ 载体真实构造（completion packets 的 log-shell tensor 区域的受限乘积），证明 `LiteralCarrierAxioms`（unit Haar 有限、缩放归一、hull⊆scaled unit、单调）由 product Haar 给出。
- **hull**：literal 载体上的 hull 有限性 = Cor 3.12 内容：用 `globalIQUnitRegion_compact`/紧性 + Haar 归一化证明 `literalHull` log-volume 有限；编译 `GlobalIQHullInterfaceActual`/`GlobalIQHullThetaPilotActual`。
- **qpilot**：etHT → q-pilot（`S1929` rootExtensionProductThetaImage）+ (SHE) 箭头；产出 q-pilot/Θ-pilot 双像。
- **mainline**：四三角合成（(HDD)=(hull+det)∘(dsc)），把 3.11.5⇒3.12 陈述成 literal 载体上的定理并证明（用上面三个 rung）。
- **stepxi**：Stage 5 数值部分（IUTchIV/[ExpEst]）：在 literal 比较形式上做 log-volume 估计 → ABC。
- **stage4**：Ind1/2/3 与 det 簿记（hull+det 所需的 determinant 层）。
- **lattice/shehdd**：审计 rung 完整性、禁止 value-model 结论当 rung；维护 `dag/PREREQ-SCOPE-LITERAL.md`。

## 状态约束
- 每 rung 必须有真实 Lean 文件（无 sorry/axiom），入 extra-targets → watchdog 编译 → olean 自动进 DAG。
- 任何以 value-realized/model-carrier hull 有限性为前提的结论按 OBSTRUCTION 记录（F2 已证），不得登记为 IUT 对象。

## A483 可构造性同步（lattice + shehdd 合并；详表见 `coord/GAP-CONSTRUCTIBILITY-A483.md`）

说明: 下表为 §4 四个三角 rung + 五个 gap 组的三分类结论（①可拼装 / ②需补缺失构造 / ③已证不可行）；①②③ 的证据、file:decl 路径与缺失对象逐项列在 GAP-CONSTRUCTIBILITY-A483.md。

| rung / gap 组 | 可构造性 | 一行结论 | 关键依据 |
|---|---|---|---|
| §4 #1 BPS --mlt. algo.--> mlt. rep. | R1_multiradial | ① 可拼装 | 9 个编译资产可接成 consumer；缺唯一 assembly theorem，无缺失对象 |
| §4 #2 mlt. rep. --(dsc)--> BPS+0-col | R2_descent | ① 可拼装 | Ind1/2/3 + K1K2 边界 + 0-column carrier 识别可复用；2 个文件待编译 |
| §4 #3 mlt. rep. --(hull+det)--> rep+hull+det | R3_literal_IQ | **② 需补缺失构造** | 缺 literal product-Haar 归一化 + literalHull 紧性/有限性定理；A481/hull 文件编译失败点已记录 |
| §4 #4 (HDD)∘(SHE)：q-plt+etHT | R4_four_triangles | ① 可拼装 | APT/IPL/SHE 方图→iqHullRealVolume→QCMPComparisonSupply→StepXIContract→Cor312；缺单一组装定理 |
| fixed_beta | ① 可直接复用 | fold+corrected finite-β base 已证；β=∞ 旧版反例 | `Mzk1BetaAvoidingFoldActual.betaAvoiding_all`; `Mzk1BetaAvoidingBaseActual.betaAvoidingBelyiBaseInputCorrected_proved` |
| scheme_side | ① 可拼装 | Definition 3.1 scheme-side 组件齐全 | `SourceDefinition31Boundary.{sectionMap_injective,sectionMap_surjective}`；InitialThetaData；HodgeTheaterBridge；S2Transport.SchemeSideHasFiniteGroupQuotients |
| fiber_functor | **③ 已登记不可行（BLOCKED）** | S1794 五字段 + S2432 slice-push 为真实阻塞 | `coord/DAG-BLOCKED.json` xif-sorry:*；AUDIT-MANIFEST-2026-11-03.md:19；Mathlib 缺 API |
| qpilot | ① 可拼装 | θ-pilot scaled region/IQ containment/finite hull 有 olean；缺全局双像+SHE 组装 | `GlobalIQHullThetaPilotActual` 待编译；组件见 GAP-CONSTRUCTIBILITY 汇总表 |
| iut4_compare | ① 可拼装 | rooted QC/HC + undilated height/region + endgame 条件可拼装 | `S3131CanonicalRootedQC/HC`; `UndilatedHeightBound`/`UndilatedRegionBound`; `endgame_conditional`；class-B named 输入 |

统计: ① ×7（R1/R2/R4/fixed_beta/scheme_side/qpilot/iut4_compare）, ② ×1（R3_literal_IQ）, ③ ×1（fiber_functor, BLOCKED）。F2 审计依据不变（value-model 结论禁作 rung）。

