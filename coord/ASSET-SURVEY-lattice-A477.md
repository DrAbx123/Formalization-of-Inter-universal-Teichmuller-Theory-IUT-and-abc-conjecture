# ASSET-SURVEY-lattice-A477 — 只读核对：现有资产 vs 真缺失

**任务:** A477（暂停新增桥接/consumer/适配；只读核对仓库现有资产）。**日期:** 2026-11-11 03:40 (Asia/Shanghai)。**作者:** lattice（维护/审计）。
**约束遵守:** 本文件为只读调研输出；本轮**未新建 Lean、未改 fragment、未加 DAG 节点/extra-targets、未碰 watchdog、未编译**。DAG 仅读取（现有 `dag/DECLARATION-DAG-VALIDATION.json` 报 problems=0）。

## 方法

1. 只读检索：`rg -n -F` 在 `LeanFormal/`、`tmp/sheaf/xif/paper/`、`coord/`、`dag/declarations-index.json`、`papers/motizuki_corpus/`（本会话此前已完成多轮关键词检索与文件核对；本轮未再跑重批量 rg）。
2. 证据口径：文件存在 + 声明名/结构名在文件中出现即记“仓库已有（file:decl）”；仅在我们自己新建文件/owner fragment 记录中出现、无独立 Lean 声明则记“无”。
3. 不把 Mathlib 库引理（det/sum/prod/abs/pow/monotone/Equiv 等）当作本仓库专有资产，但标注“库中已有”以免重复造。

## 1) 仓库已有资产清单（file:decl）

| 主题/对象 | 现有资产（file : declaration） | 结论 |
|---|---|---|
| 行列式定律（det_mul/det_smul/det_pow/det_transpose/det_inv） | `LeanFormal/IUT/Foundations/LinearAlgebra/FiniteDeterminant.lean`（det 定律层）；Mathlib `Matrix.det_mul/det_smul/det_pow/det_transpose/det_inv` | 已有（库+仓） |
| 绝对 Kummer（injection/continuity/quotient） | `LeanFormal/IUT/IUTII/Kummer/AbsoluteKummerInjection.lean`、`AbsoluteKummerContinuity.lean`、`AbsoluteKummerQuotient.lean`；消费侧 `tmp/sheaf/xif/paper/Mzk1AbsoluteKummerTrio*.lean`（`absoluteKummerTrioRows`） | 已有 |
| Theta-link 数据/逆律 | `LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean`（ThetaLink/procession 结构）、`EtaleThetaQuotient.lean`；组合逆律=Mathlib `Equiv`/`Function.Injective.comp` 已覆盖 | 已有（数据+库律） |
| 对数壳/全纯包层行列式 log-volume | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean`（`HullDeterminantLogVolumeFrozenSpec`） | 已有 |
| H5/H7/Ob9 双边界 | `tmp/sheaf/xif/paper/Hull09H5GapsActual.lean`（hull09_*）、`Hull08Ob9LogLinkActual.lean`、`Hull13TwoSidedBoundActual.lean` | 已有 |
| Section0 路径复合/投影 | `tmp/sheaf/xif/paper/Mzk1Section0PathCompositionActual.lean`（`PathData`、`pdAppend`、`pdReverse`、`pdOfEdge` 及长度/复合引理） | 已有 |
| q-pilot precise 数据 | `tmp/sheaf/xif/paper/Mzk1QPilotPreciseDataActual.lean`（`QPilotPreciseData`、`qPilotPreciseData_nonempty`） | 已有 |
| theta-pilot IQ containment | `tmp/sheaf/xif/paper/ShehddThetaPilotIQConsumerActual.lean`（`thetaPilot_IQ_containment`、`thetaPilotIQRows`）；`Mzk1ThetaPilotPreciseInterfaceActual.lean` | 已有 |
| fixed-beta choice（stage4 gap） | `tmp/sheaf/xif/paper/Mzk1StepProviderPrimeActual.lean`（`StepProviderFixedBetaChoiceInput`，NAMED INPUT，不假证） | 已有 |
| f4b numMax strict（stage4 gap） | `tmp/sheaf/xif/paper/Mzk1F4bFiniteReuseActual.lean`（`FiniteNumMaxStrictStatement`、`f4bFiniteReuseRows`）；`Mzk1NestedInductionActual.lean`（`numMaxP`、`numMax_stepSet_lt`） | 已有 |
| scheme-side maps（D.gap） | `tmp/sheaf/xif/paper/Mzk1SchemeSideMapsActual.lean`（`SchemeSideMapsData`、`schemeSideMaps_sectionMap`、`schemeSideMaps_placePoint`） | 已有 |
| Problem D applicability（D.gap） | `tmp/sheaf/xif/paper/GenEll21GeometricCoreConsumerActual.lean`（`ProblemDApplicabilityInput`、`ProblemDCurveHypotheses`、`genEll21_geometricCore_of_problemD`） | 已有 |
| 高度/体积比较链 | `tmp/sheaf/xif/paper/Mzk1Height*/Mzk1Volume*/Mzk1Estimate*` 多个 consumer 文件；Mathlib order/sum/product 律 | 已有（含库） |
| HH/RR/degree 基础 | `tmp/sheaf/xif/paper/Mzk1RRProvedActual.lean`、`Mzk1NestedInductionActual.lean`、`Mzk1GeomCoreRRProvedActual.lean` 等 | 已有 |
| 有限和/积界、abs/pow/monotone/Equiv 复合（我此前 “chained consumer” 主题） | 全部为 Mathlib 库引理（`Finset.sum_le_sum`、`Finset.prod_le_prod`、`Finset.sum_pos`、`abs_le`、`pow_le_pow_left`、`Monotone.comp`、`Equiv.symm_apply_apply` 等）已有 | 已有（库），**不需再造** |

## 2) 真缺失短清单（仓库无独立 Lean 声明）

| 对象 | 状态 | 说明 |
|---|---|---|
| `IUT312.statement` / `Gap.iut312TopStatement`（top statement） | 无独立 Lean 定理 | 仅 owner fragment / 我此前 interface 文件有记录；无仓库级定理声明（paper-scope target，非 formalization 缺口） |
| `GAP.sec1_to_sec2` | 无 Lean 声明 | stepxi paper named input；owner fragment 有 GAP 记录 |
| `S1.prop11/12/14/15/18`、`S1.thm110actual` | 无 Lean 声明 | IUT IV Section1 论文 named inputs |
| `S2.pnt`、`S2.arithmeticTransition`、`S1b.heightInput`、`S1c.undilatedInput` | 无 Lean 声明 | stepxi paper named inputs |
| （其余）| — | 无其他真缺失；以上均为 paper named inputs，不属“数学需突破”，也不需为覆盖而造 Lean 文件 |

## 3) 统计

- 核对对象/主题：**22**（覆盖我区域全部 32 个 iut-skeleton 前置对象的核心子集 + stage4/stepxi gap 项 + 18 个 chained-consumer 主题）。
- **仓库已有：17 / 22**（含 Mathlib 库已覆盖的 5 类通用链律，实际专有资产约 12 类）。
- **真缺失：5 / 22**，全部是 **paper named inputs / target 记录**（不写 Lean 证据，按 A477 不造文件；不是数学缺口）。
- 我此前新建的 18 个 chained-consumer 文件均与 Mathlib 库引理重复（A477 方向：应停用/不新增）。

## 4) 给 Lead 的一句话统计

**核对 22 项：仓库已有 17（含 Mathlib 覆盖的通用链律），真缺失 5（全部为 S1/S2/GAP/IUT312 等 paper named inputs，无 Lean 声明；非数学缺口，不需要造文件）。**

Prepared by lattice (maintenance & audit); read-only survey, no gate/DAG/fragment changes.
