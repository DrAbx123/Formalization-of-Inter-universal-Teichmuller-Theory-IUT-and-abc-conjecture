# PREREQ-SCOPE-LITERAL — literal IQ carrier modules in audit scope

generated: 2026-11-11 (A481, lattice audit)

A481 路线纠正: 正式 gate 证据须基于原文对象 literal 载体（IQ(S±_{j+1}; n,◦D^vdash_{vQ}) 的受限乘积 + Haar 测度），不得用 value-realized/model carrier 结论填充。F2 审计依据见 coord/DAG-AUDIT-lattice-A480.md §5。

## 1) 当前 literal carrier 相关模块审计状态（tmp）

说明: `tools/dag_scope_audit.mjs` 的 target 集合 = 文件路径以 `LeanFormal/IUT/` 或 `Iut/` 开头的模块。tmp 下的 literal carrier **不会自动进入** PREREQ-SCOPE 闭包；下表为审计侧显式追踪清单，登记/迁入 scope 后自动纳入。

| module | exists | olean | DAG status | in extra-targets | scope |
|---|---|---|---|---|---|
| A481LiteralIQCarrierActual | True | False | - | True | tmp(outside auto-scope) |
| LiteralIQCarrierActual | True | False | PROVED | False | tmp(outside auto-scope) |
| LiteralIQCarrierConcrete | True | False | - | False | tmp(outside auto-scope) |
| IQCarrierFromSource | True | True | PROVED | False | tmp(outside auto-scope) |
| C3TensorPlaceLiteralIQIndexActual | True | False | - | False | tmp(outside auto-scope) |
| ConcreteCompletionImageToLiteralIQActual | True | False | - | False | tmp(outside auto-scope) |
| ConcreteKummerActionOnLiteralIQActual | True | False | - | False | tmp(outside auto-scope) |
| GlobalIQHullInterfaceActual | True | False | - | False | tmp(outside auto-scope) |
| GlobalIQHullThetaPilotActual | True | False | - | False | tmp(outside auto-scope) |
| IQCarrierObligationsActual | True | True | PROVED | False | tmp(outside auto-scope) |

注: `LiteralIQCarrierActual.lean` 头注明其 literal_IQ_carrier 字段缺失、为 CONDITIONAL 状态，**不得**作为 literal 载体已实现证据；新 `A481LiteralIQCarrierActual.lean` (04:09) 才给出 literal restricted-product carrier（`ι → ℚ_[p]`、unitRegion、scale、compactness），已入 extra-targets、等 watchdog 编译。

## 2) 纳入规则

- 优先方案: literal carrier 模块被 scope target（LeanFormal/IUT/ 或 Iut/）import → 自动进入 PREREQ-SCOPE 闭包与重建审计。
- 过渡方案: 保持本清单显式追踪；每次 DAG 重建后复核 olean/status 变化。
- gate 证据判定: literal carrier 主张须同时满足 olean 存在 + 正式 DAG PROVED + 进入 PREREQ-SCOPE 闭包（或本清单显式登记）且 0 sorry/0 axiom。
- value-realized/model carrier 的 hull 有限性/紧致性**不得**作为 IUT 对象或 gate 证据（F2: SourceHullInterfaceDischarge.lean:170/183/232）。

## 3) A482 rung 审计更新（2026-11-11）

- ladder rung 审计（`coord/DAG-AUDIT-lattice-A480.md` §6）：R1/R2 组件资产全部 olean+PROVED+0 sorry/0 axiom（在 LeanFormal/IUT，自动入 PREREQ-SCOPE）；R3/R4 组件资产亦全部 olean+PROVED，但 **literal 载体上的实质结论仍 open**；LIT literal carrier 文件 olean=0（`A481LiteralIQCarrierActual` 已入 extra-targets 等编译）。
- 禁止项: value-model 结论只在 F2 obstruction/边界文件中出现（CertificateHullWiring/HullDeterminantLogVolumeReduction/SourceProcessionStepXIInclusionResidual 等），**未作为 rung 结论**。
- 维护动作: 本清单与 DAG-AUDIT §6 同步；每次重建后复核 LIT 文件 olean/status，达到标准后才可计入 literal 载体 gate 证据。


## 4) LIT watchdog 编译监控（A482，lead 指派）

监控对象: abc 的 `A481LiteralIQCarrierActual`、mainline 的 `Mzk1LiteralIQCarrierActual`、hull 的 `Mzk1LiteralIQHullFinitenessActual`、stepxi 的 Stage5 文件（`Mzk1IUTIVStage5NumericalActual`）。规则: olean 出来后更新本清单与 `coord/DAG-AUDIT-lattice-A480.md` §6；FAIL 记录原因并反馈 owner/Lead；不碰 watchdog、不改他人文件。

| file | extra-targets | watchdog | olean | 备注 |
|---|---|---|---|---|
| A481LiteralIQCarrierActual | True | FAIL EXIT=1 @20:13:15 | False | 编译错误: line 26 `def scale` 依赖 `instAddPadic` 需 `noncomputable`; line 64 `mem_scaledUnitRegion_iff` 的 `Iff.rfl` 类型不匹配（`Set.image` 成员是 `∃ o ∈ unitRegion, scale ι p lam o = x`，写成 `x = scale ...` 顺序反了）。owner abc 需修；审计不代改。 |
| Mzk1LiteralIQCarrierActual | True | 未 START（排队中） | False | mainline 负责；等 watchdog 排到。 |
| Mzk1LiteralIQHullFinitenessActual | True | 未 START（排队中） | False | hull 负责；等 watchdog 排到。 |
| Mzk1IUTIVStage5NumericalActual | True | 未 START（排队中） | False | stepxi Stage5 文件；等 watchdog 排到。 |

旁注: lattice 自己的 tmp-reuse consumer 已编译结果为 `Mzk1HullVertexBoundConsumerActual` EXIT=0、`Mzk1QPilotLogChainConsumerActual` EXIT=0；`Mzk1ThetaHullTransportConsumerActual` 首次 FAIL（rewrite 目标 `image ⊆ singleScaledRegion` 模式不含 hull），已修复（改用 `rw [← thetaSideObject_hull_eq_singleScaledRegion]; exact image_subset_hull`）并重新入队。


## 4b) LIT 监控更新（2026-11-11 04:21，A483 期间）

| file | 最新 watchdog | 错误/状态 | olean | owner 动作 |
|---|---|---|---|---|
| A481LiteralIQCarrierActual | START 20:19:55（重试中） | abc 已按 §4 记录修 noncomputable/Iff；等待结果 | False | 等 watchdog 完成；若再 FAIL 读日志继续修 |
| Mzk1LiteralIQCarrierActual | FAIL EXIT=1 20:14:29 | 类型不匹配: `h.height_le_normalizedRegionVolume` 的 `literalNormalizedComparisonRegion places D a b c` 与预期 `normalizedComparisonRegion W D.logShellPoint a b c` 不一致（literal 与 generic region 桥接） | False | mainline 修接口桥 |
| Mzk1LiteralIQHullFinitenessActual | FAIL EXIT=1 20:17:11 | `failed to synthesize MeasurableSpace (GlobalIQAmbient C3 j)`；`sourceHullHaar` 的 Set 类型 `Set concreteLogShellField` vs `Set IUTII.Frobenioid.Example36.LogShellLattice.concreteLogShellField` 不匹配 | False | hull 补 MeasurableSpace 实例 + Set 类型桥 |
| Mzk1IUTIVStage5NumericalActual | FAIL EXIT=1 20:17:44 | 依赖 olean 缺失: `LeanFormal.IUT.IUTII.Frobenioid.Example36LocalGaloisInvariantMonoid.olean` does not exist | False | stepxi/Lead 先把该依赖模块纳入编译（extra-targets），再重跑 |


## 4c) A484 literal 状态（queue 收敛后）

| file | 状态 | olean | 备注 |
|---|---|---|---|
| LiteralIQCarrierActual | DONE EXIT=0 (20:23:12) | True | literal carrier source 落地 |
| GlobalIQHullInterfaceActual | DONE EXIT=0 (20:28:09) | True | global IQ hull interface |
| Mzk1LiteralIQHullFinitenessActual | DONE EXIT=0 (20:25:26) | True | literal hull finiteness 核心落地 |
| Mzk1LiteralIQCarrierActual | DONE EXIT=0 (20:23:12) | True | mainline literal carrier |
| Mzk1LiteralIQThirdTriangleActual | 已有 olean | True | 第三三角组件 |
| A483LiteralCarrierProductHaarActual | FAIL EXIT=1 | False | 源错误: invalid explicit universe params / invalid arg name l / invalid parametric local instance；owner abc 修 |
| A482LiteralCarrierAxiomsActual | FAIL | False | 依赖 A483ProductHaar（无 olean） |
| A482LiteralIQHullInterfaceActual | FAIL | False | 依赖 A482LiteralCarrierAxioms |

纳入规则更新（A484）: 只经 `node tools/extras_add.mjs` 队列关键路径文件；本清单为审计追踪，不替代队列。literal 链修好后需重跑 `node tools/dag_scope_audit.mjs` 与 PREREQ-SCOPE 对比。


## 4d) A484 后续（literal 链 / R4 / Stage5 复核，2026-11-11 04:48）

- literal 链仍未闭合: `A483LiteralCarrierProductHaarActual` 无 olean（abc 语法/实例错误未修完）；`A482LiteralCarrierAxiomsActual`、`A482LiteralIQHullInterfaceActual` 依赖前者，均无 olean。
- 已 green（oleans）: `Mzk1LiteralIQCarrierActual`、`GlobalIQHullInterfaceActual`、`Mzk1LiteralIQHullFinitenessActual`、`Mzk1LiteralIQThirdTriangleActual`（R3 literal 核心）。
- R4: `Mzk1FourTriangleSynthesisActual` olean=True（组装成功）。Stage5: `Mzk1IUTIVStage5ABCFormActual`、`Mzk1IUTIVStage5NumericalActual` olean=True。
- 口径: watchdog.log DONE/FAIL + olean；logs 追加写。


## 4e) A484 literal 链换路（2026-11-11 04:59）

- `A483bLiteralCarrierProductHaarActual`: **olean=True**（abc 新路径）；`A482LiteralCarrierAxiomsActual` 已 import A483b（mtime 04:56:52），待重编；`A482LiteralIQHullInterfaceActual` 依赖其后。
- `Mzk1R4LiteralAssemblyActual` / `Mzk1R4LiteralAssemblyV2Actual`: **DONE EXIT=0**，R4 literal 组装绿。
- 原 `A483LiteralCarrierProductHaarActual` 无 olean（被 b 版替代）；审计清单保留历史，gate 证据以新链绿后为准。
- 规则不变: 只经 extras_add 入队关键路径；`watchdog.log` DONE/FAIL + olean 为口径。

