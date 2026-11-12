# ROUND29-PLAN — 按 COR312-THREE-ROUTES 交接稿开工（v2，交接稿已更新）

Date: 2026-11-13 04:20 (Asia/Shanghai). Lead: lead. 依据：用户 goal round 29 + `D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md`。

## 0. 交接稿版本更正（重要）

交接稿在 04:06 被更新为 **1623 行 / 69,144 bytes**：现含 **§1–§9**（§6 路线三全文、§7 原文对象与边界、§8 P0–P7 顺序任务包、§9 接口与验收），只缺 TOC 承诺的 §10–§12（资产定位/原文定位/交付记录）。此前“止于 §5.13”的判断作废。

关键节：§8.2 P0–P7 推荐顺序；§8.3 陈述依赖/证明依赖分列；§8.5 何为有意义进展；§9.2/§9.3/§9.4 三条路线接口形状。

## 1. 仓库已有可复用绿色工具（11 个核心文件，oleans 新鲜）

IntegralTraceDualLattice / IntegralTraceDualTensorInclusion / PadicLatticeIndexFormula / DifferentTraceProduct / IntegralLogShellHaarIndex / FinitePadicHaarScaling / CompactOpenAddSubgroupIndex / ProductIntegerLattice / LocalFieldIntegralHullSpan（integralSpan_eq_hull）/ FinitePlaceIntegralTensorCovolume / HolomorphicHull 系列。

## 2. 本轮派工与 P0–P7 对应

| P 步 | 内容 | 本轮 lane/task | 状态 |
|---|---|---|---|
| P0 | 固定目标与归一化（对象表/读数/权重） | hull task-74 → coord/HANDOFF-OBJECT-TABLE.md | **完成**（发现 c_norm vs c_root 目标冲突 → 需 P0-fix） |
| P0-fix | 修正 c_norm/c_root 归一化与 paper 目标陈述；j=0 标签偏差 | hull task-83(A)；待定 lane 做归一化接口 | 进行中 |
| P1 | 真实张量块 + 作用矩阵（非平凡方向/整闭包修正） | hull task-83(B)：Ind2/Ind3 在正确载体的 enlargement | 进行中 |
| P2 | 同一 G 做路线一/二联合诊断；判定 §4.8 是否覆盖、是否够 q 尺度 | qpilot task-78（判别）+ stage4 task-77（A8 工具） | 进行中 |
| P3 | 选一个真定量引理（A-Index 或 B-Estimate） | lattice task-75（B2-B5 工具）；abc task-76→82（B6/B7 实质化）；stage4 task-77（A1-A4+A8） | 进行中 |
| P4 | 全部允许像统一有界容器（有限性） | 待派（下一轮） | — |
| P5 | 路线三来源检验：字典 + 扭点乘积函数+除子 | stepxi task-81（字典 PARTIAL 完成）→ task-85（C-Divisor） | 进行中 |
| P6 | 全局范数/比较态射 | 未开始 | — |
| P7 | 完整组装与验收 | mainline/shehdd 修构建 gate + 最终 gate | 进行中 |

## 3. 已确认的实质判定（写入审计）

- **§4.8 停止引理判定（hull）**：实际 `rootThetaHull` 含 j=0 → 含 q-无关 R·O_hol，非公共标量族；paper 非零标签像 `paperRootThetaImageNZ = F(c_root)·O_hol` 是公共标量族（c_root=m/(2l)），**相对 index 不随 m 增长**。真正增益只能来自 Ind2/gap 源结构，而 qVFam 块无 Ind 作用、无 Ind3 stage→hull map（Ind3StageToOutputHullGap, Ind3OutputHullQPilotActual:156-164）。
- **归一化冲突（hull）**：green 链 qPilotNormRegion/qPilotClassicalLog 用 c_norm=m；paper 用 c_root=m/(2l)。Ind3OutputHullQPilotActual:97 的 q≤hull **不是** paper |log q| ≤ −|log Θ|。
- **路线三语义关口（stepxi）**：root-unit/μ2l 字典可建（probe2 lake env lean exit 0）；full etale theta-value 字典不可建（Kummer class 未识别，Example36SourceThetaDivisor:97-119）。Phase 独立、j 相位独立（IUT II Rem 2.5.1:4272-4343）。
- **ABC 全局仍远**：V150 gate HOLD、S3135 条件组装需 hP ↔ ABC；本轮路线均为结构性研究路线，无无条件结论。

## 4. 纪律

- 不改题目/目标；不新增假设换 green；不 toy/PUnit/True；不用未构造对象判不等式；lana 仅参考。
- 先内容搜索核对已有覆盖；申报“已有/缺口/新增”；交付带 file:line 与 build 证据。
- Lead 不编译；编译由 lane 做。审计/ledger 及时追加，不覆盖历史。

## R29-PLAN v3 — 执行状态（2026-11-13 ~04:56）

交接稿版本：D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md 现为 **1854 行/90,001B，含 §1–§12**（TOC 完整；§10 资产定位、§11 原文定位、§12 交付记录齐全）。

### watchdog 统一绿（DONE EXIT=0，均有 olean；以 dag/watchdog/watchdog.log 为准）
P0/P0-fix：Mzk1PaperTargetNormalizationActual（paper c_root 接口）、Mzk1PaperFaithfulHullActual（paper-faithful hull 定义+等式；P4 追加仍在修）。
P1/P2：Mzk1MultiFactorBlockActual（P1 实体 green：多因子块/整数格/Qp基/迹对偶基/factorPermutationBlockEquiv；P2 scaffold 修复中）、Mzk1LatticeOrbitIndexActual（A1/A2/A3单步/A8集合核）、Mzk1Route1OrbitLatticeActual（路线一无增益判定）。
P3：Mzk1StepVReductionActual（目标⟺显式不等式链）、Mzk1S3050ConstantSourceActual（局部 2l 换算）、Mzk1StepVProcessionActual（S3014ProcessionData 条件实例）、Mzk1StepVAlignmentActual（S3029AlignmentData 实际化）。
P4：Mzk1Ind2EnlargementActual（Ind2/Ind3 orbit 定义+无有限 index 判定）、Mzk1PaperFaithfulHullActual 的 P4 部分（紧性/正有限，修中）。
P5：Mzk1Route3DivisorActual（fP/仿射 XYIdeal）、Mzk1CThetaComparisonActual（乘法移位 θ 恒等式；C7 一般版未证）、Mzk1PhaseEquivarianceActual（独立相位判定 + 2l 幂代价）。
P6：Mzk1NormDeterminantToolsActual（C13/C15/C16）、Mzk1ProductFormulaDegreeActual（product formula + Arakelov degree 接口）、Mzk1DegreeBridgeActual（q 侧条件桥）、Mzk1QPilotPlaceDegreeActual（place map + 逐位 valuation 等式）。
B/A 工具：Mzk1TensorDualCorrectionActual（B6/B7/B8）、Mzk1TraceDualVolumeActual（B3/scalar B4/B5）。
最小验收：Mzk1MinimalAcceptanceActual（§9.6：Λ_G⊆paper hull、条件 μ 比值）。
构建 gate：Mzk1PlaceEqSpecializationActual、GlobalThetaPilotPlaceMapActual、BadToC3TensorMapActual、Mzk1RouteBBridgeActual、Mzk1S1487SourceRootIdentityActual、Mzk1CompletionMapIdActual、Mzk1StructuralLineBundleActual、Mzk1SourceRootIdentityActual、Mzk1SignedLogVolumeActual、Mzk1ActualFinalLDataActual、Mzk1GreenChainAssemblyActual、Mzk1OurAccurateTargetActual、Mzk1TensorRegionNormalizationActual、Mzk1QPilotPrincipalActual、Mzk1StepVAlignmentActual 等。

### 判定与停止条件（已记录 AUDIT_LEDGER / coord 文档）
- 路线一/二在 qVFam 单因子块：paper 非零标签像 = F(c_root)·O_hol 公共标量族，相对 index 不随 m 增长；Ind2(μ2l 单位) index=1、Ind3(全 K^×) 无有限 index；无跨载体 norm/trace 桥 ⇒ 局部生成机制不足（HANDOFF §8.2 P2 停止条件），增益须来自来源/全局（P5/P6）。
- P0：paper 系数 = c_root = m/(2l)（IUT I Ex3.2(iv) / II Rem2.5.1 / III Def3.8 / Cor3.12）；green 链 c_norm=m 是 deviation；旧 Ind3OutputHullQPilot 比较是混合口径，保留标 deviation。
- 路线三：root-unit 字典可建（green probe），etale theta 字典缺（Kummer class 未识别）；C-Divisor C1 partial、C3/C4/C5 BLOCKED（Mathlib 无 order-at-O/WeilDivisor/principal divisor API）；C-Theta 乘法移位版 green、一般 Z±P 缺线丛平凡化；C-Phase 独立相位需等变族或 2l 幂（读数乘 2l，不能当原比较）。
- P6 缺：GAP-DEGREE-CARD/SUM/BRIDGE（theta 侧）、GAP-NORM-ARCH、GAP-ARB-ELEMENT。
- ABC 仍无无条件结论；V150 HOLD、S3135 条件组装（hP↔ABC）不变。

### 下一步（按 HANDOFF §8.2）
P1/P2：G 行满秩 + S/X_G 联合诊断 + 因子置换打破公共标量判定（stage4）。
P3：StepVExtraNonneg 实际来源、StepV scalar↔normalized log-volume per-label 等式、S3019MissingBridge、DExactLowerTarget（qpilot/lattice）。
P4：paper hull 正/有限收尾（hull）。
P5：label-indexed 相位 torsor + C-Theta 等变（stepxi）；etale theta Kummer 识别为长期缺口。
P6：GAP-DEGREE-SUM（全 bad 求和）、theta-side degree、arch 归一化（abc）。
P7：mainline/shehdd 继续清 red；最终 assembly comparator 未到达。
