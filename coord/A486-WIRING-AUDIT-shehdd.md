# A486 接线审计（shehdd，配合 lattice）

时间: 2026-11-11 05:05–05:12 snapshot。方法: 只读核对 src 存在、.lake olean、队列/priority 归属、源码类型签名；未修改任何他人文件、未碰 watchdog、未手动编译。

## 0. 结论摘要

1. **主链类型是真正匹配的**（不是名字接近）: qpilot 的 `qThetaFourTriangleSynthesis` 返回类型就是 `Mzk1R4LiteralAssemblyActual.FourTriangleSynthesis`（imports+open 同一模块，green olean 已由 Lean 类型检查器验证）；mainline 的 `Mzk1Step3115ComparisonActual.qThetaFourTriangleSynthesis` 同样填 R4 的 structure，且 `step3115_comparison := step3115_comparison_proved`（已证定理填充，非裸字段）；endgame 的 `r4_endgame_composition (S : FourTriangleSynthesis ...)` 直接消费 R4 类型。
2. **hull 车道与 R4 接口不是同一类型**（HullDetStep3115 用 `Mzk1FourTriangleSynthesisActual.FourTriangleSynthesis`，其 `hdd : HDDDecomposition`；R4 用自身 `HDDDecomp`）。但 mainline 已在 `Mzk1Step3115ComparisonActual` 中提供适配器 `hullLaneHDD : HDDDecomp Real Real (HullDetState labelT)` + `step3115_comparison_hullDet_concrete`，可把 hull 证据适配进 R4 合成——**接线可行，但存在两条并行接口/重复证明**（见 §3）。
3. A486 计划中 qpilot 的 `Mzk1QThetaHullDetAlignActual` **尚未创建**；mainline 的 `Mzk1Step3115WiringActual`、hull 的 `Mzk1HullDetFourTriangleActual` 已存在、类型正确、待编译。
4. **重复证明/定义存在**（R4 Actual/V2 两份、FourTriangleSynthesis 三份、S650 Adapted 副本），**有限载体 3.12/S650/S3139 等已有资产未被当前接线引用**（详见 §4）。

## 1. 文件状态矩阵（src/olean/队列/priority）

| 文件 | 角色 | src | olean | queue | priority | 备注 |
|---|---|---|---|---|---|---|
| Mzk1QPilotR4Stage5AlignActual | qpilot: qTheta readouts/contract + R4 synthesis | ✔ | ✔ 20:59 | ✔ | — | src 21:02 更新后 olean 稍旧（重编中） |
| Mzk1HullDetStep3115Actual | hull: HullDetState/hullReadout/detReadout/hullDetHDD | ✔ | ✘ | ✔ | — | src 21:05，队列待编译 |
| Mzk1Step3115ComparisonActual | mainline: filled step3115 + hullLaneHDD 适配器 | ✔ | ✘ | ✔ | — | 依赖 hull olean，待链式编译 |
| Mzk1Step3115WiringActual | mainline: wiring(i)(ii)(iii)+Step3115WiringEvidence | ✔ | ✘ | ✔ | — | 类型正确（R4 类型），待编译 |
| Mzk1HullDetFourTriangleActual | hull: hullDetFourTriangle(+_cor312/concrete) | ✔ | ✘ | ✔ | — | 用 hull 车道重复接口，待编译 |
| Mzk1R4LiteralAssemblyActual | canonical R4 rung: HDDDecomp/FourTriangleSynthesis/r4_literal_assembly | ✔ | ✔ 20:59 | ✔ | — | 被 qpilot/endgame/comparison/wiring import |
| Mzk1R4LiteralAssemblyV2Actual | **重复副本**（同内容、不同 namespace） | ✔ | ✔ 20:59 | ✔ | — | 零 importer；archive 候选 |
| Mzk1FourTriangleSynthesisActual | hull 车道并行接口（FourTriangleSynthesis 第二份） | ✔ | ✔ 20:46 | ✔ | ✔ | 仅被 hull 文件 import；重复证明 |
| Mzk1HDDObjectActual | HDDDecomposition 基础结构 | ✔ | ✔ | ✔ | — | 被 hull 车道使用 |
| Mzk1R4EndgameCompositionActual | stepxi: r4_endgame_composition（消费 R4 类型） | ✔ | ✔ 21:02 | ✔ | — | green；消费 R4 合成 |
| S650ActualSignedCor312Contract | 有限载体 3.12 参考（s650ActualSignedCor312Conclusion） | ✔ | ✘ | — | — | **未入队/未编译** |
| S650ActualSignedCor312ContractAdapted | **Adapted 重复副本** | ✔ | ✘ | — | — | archive 候选 |
| FiniteAlignmentSocketInstance | tree 有限载体 3.12 参考（finiteAlignmentConclusion） | ✔ | ✔ | — | — | green；无 importer（参考实现） |
| FiniteAlignmentStrictSocketInstance | tree strict 变体（finiteAlignmentStrictConclusion 等） | ✔ | ✔ | — | — | green；仅 import 上一文件 |

## 2. 类型匹配核对（真正签名）

| 接线对 | 期望接口 | 实际类型（源文件） | 判定 |
|---|---|---|---|
| qpilot → R4 | R4 `FourTriangleSynthesis` | `qThetaFourTriangleSynthesis : FourTriangleSynthesis (Bad (nativePlaceSelection T)) (Bad (nativePlaceSelection T))`（open R4 namespace） | **MATCH**（green olean 证明类型检查通过） |
| qpilot contract → R4.contract | `StepXIContract` | `qThetaStepXIContract ... : StepXIContract`（StepXI/Contract.lean） | **MATCH** |
| hull → R4 | R4 `HDDDecomp` | hull 直接给 `HDDDecomposition`（不同 structure）；mainline 适配器 `hullLaneHDD : HDDDecomp Real Real (HullDetState labelT)`（hullReadout/detReadout 赋值） | **适配后 MATCH**（需 adapter；直接传 type mismatch） |
| mainline comparison → R4 | R4 `FourTriangleSynthesis` + 已证 step3115 | `qThetaFourTriangleSynthesis` 填 `step3115_comparison := step3115_comparison_proved T b` | **MATCH**（待 olean） |
| R4 → endgame | R4 `FourTriangleSynthesis` | `r4_endgame_composition (S : FourTriangleSynthesis DSC SHEOut) (j) (hcomp) : ...` | **MATCH**（green） |
| R4 → 有限载体参考 | `Cor312Conclusion contract` | `finiteAlignmentConclusion : Cor312Conclusion finiteAlignmentContract`；`s650ActualSignedCor312Conclusion : Cor312Conclusion (s650ActualSignedContract places tuple μ hneg l N)` | **类型一致**（参考实现；未接线） |

## 3. 重复证明/重复定义（审计发现）

- `FourTriangleSynthesis` 三份: R4LiteralAssemblyActual（canonical，被 4 文件 import）、R4LiteralAssemblyV2Actual（同内容副本，0 importer）、FourTriangleSynthesisActual（hull 车道，仅 hull 文件 import，`hdd` 类型为 HDDDecomposition）。
- `r4_literal_assembly` 两份（Actual + V2）；`cor312Conclusion_of_fourTriangleSynthesis` 三份；`HDDDecomp` 两份（Actual+V2）；`HDDDecomposition` 多份（HDDObjectActual + Adapted 副本 + V2 变体）。
- `s650ActualSignedCor312Conclusion` 两份（Contract + Adapted，均未编译）。
- 结论: canonical 应为 R4LiteralAssemblyActual（mainline/qpilot/stepxi/wiring 都消费它）；V2 与 Adapted 及 hull 并行接口为重复/历史资产，建议 archive（保留历史、不再引用），由 owner 决定，不在此改文件。

## 4. 遗忘/未接线的已有资产（有限载体 3.12、S650、S3139）

- **有限载体 3.12**: `LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteAlignmentSocketInstance.lean` 的 `finiteAlignmentConclusion : Cor312Conclusion finiteAlignmentContract`（green，经 `cor312Conclusion_of_QCMPWithIPL`）与其 strict 变体 `finiteAlignmentStrictConclusion` 等（green）。A486 主链未消费它们（无 importer）——作为参考实现/消费端可用，但**不是**接线链的一部分。
- **S650**: `tmp/sheaf/xif/paper/S650ActualSignedCor312Contract.lean` 的 `s650ActualSignedCor312Conclusion : Cor312Conclusion (s650ActualSignedContract ...)`（有限列 signed certificate 参考）；src 存在但**无 olean、未入队**，Adapted 副本同状态 → 属于"未编译的遗忘参考资产"，如主链要用应经 owner 用 extras_add 入队（当前非关键路径，不建议）。
- **S3139**: `tmp/sheaf/xif/paper/S3139*.lean` 有 ~18 个 green 文件含 `Cor312Conclusion` 生产者（如 S3139FirstTriangleRouteConclusionActual、S3139RouteFinalCompositionHardenedActual、S3139StageOneFourthTriangleConsumerActual、S3139FirstTriangleFinalCompositionLightActual 等）；**当前 A486 接线文件引用 S3139 数量 = 0**，S3139 在 queue/priority 数量 = 0（早已编译的 prior art，未被当前 rung 复用）。建议作为 prior-art 证据在接线文档中引用，避免重复证明；是否纳入 critical path 由 Lead/lattice 决定。

## 5. 缺口/待办（不改文件，仅报告）

1. 待编译（queued）: `Mzk1HullDetStep3115Actual`、`Mzk1Step3115ComparisonActual`、`Mzk1Step3115WiringActual`、`Mzk1HullDetFourTriangleActual`（src 均 21:05，watchdog 排队）。
2. 待创建: qpilot 的 `Mzk1QThetaHullDetAlignActual`（A486 计划，src 不存在）。
3. owner 去重决定: V2/Adapted 副本、hull 并行 FourTriangleSynthesis；建议 canonical 统一到 R4LiteralAssemblyActual，hull 侧经 `hullLaneHDD` 适配（mainline 已实现）。
4. prior-art 引用: S3139 系列 + FiniteAlignment(SocketInstance/StrictSocketInstance) 应在接线说明中登记为已复用/参考，避免后续重复证明。
5. 全部 A486 接线文件真实 sorry = 0（词法扫描 9 文件）；green 文件的旧日志错误均为 stale（oleans 已是成功编译产物）。

本记录为 shehdd 审计输出，供 lattice 合并进 A486 接线判定；未修改任何他人文件。

## 6. A487 中间态复核实况（05:12 snapshot，配合 lattice 监督表）

### 6.1 共享接口切换状态（核实）

- **canonical = Mzk1FourTriangleSharedActual**：src 21:08:25，olean 未出（已入 queue+priority）。定义 HDDDecomp、FourTriangleSynthesis（hdd : HDDDecomp Real Real DSC）、cor312Conclusion_of_fourTriangleSynthesis。
- **mainline 三文件已切换**：Mzk1R4LiteralAssemblyActual（src 21:08:30，import+open Shared，自身不再定义结构、r4_literal_assembly 用 Shared 类型）、Mzk1Step3115ComparisonActual（src 21:08:30）、Mzk1Step3115WiringActual（src 21:08:30）均 import Shared。
- **hull 两文件未迁移（证实 lattice）**：Mzk1HullDetStep3115Actual（src 21:07:44）与 Mzk1HullDetFourTriangleActual（src 21:05:28）仍 import/open Mzk1FourTriangleSynthesisActual（A 版）。类型差异: A 版 FourTriangleSynthesis.hdd : HDDDecomposition，Shared 版 hdd : HDDDecomp → 迁移需适配器（mainline 已有 hullLaneHDD : HDDDecomp Real Real (HullDetState labelT) 模式: HDDDecomp.mk (fun x => hullReadout x) (fun x => detReadout x)）。
- **qpilot 的 Mzk1QThetaHullDetAlignActual 仍缺**（src 不存在）。

### 6.2 True/trivial 占位审计（词法级，去注释）

- Mzk1HullDetFourTriangleActual.lean L70-75：hullDetContract 内 ipl := True / she := True / apt := True + ipl_evidence/she_evidence/apt_evidence := trivial（6 处）。
- 其余 A487 接线文件 0 处 True/trivial 占位（Shared/R4/Comparison/Wiring/HullDetStep3115/QPilot 均无）。
- 建议（owner 决定）: hull 车道不自行构造 StepXIContract，改为接收 qpilot 车道的 qThetaStepXIContract（或由主链接线传入的 contract），避免 True 槽位。

### 6.3 当前真实编译失败诊断（供 owners）

1. **Mzk1HullDetStep3115Actual**（log 05:07）: L67/L81 universe metavariable 错误——HullDeterminantLogVolumeFrozenSpec.log_eq_log_det/det_eq_prod 在 HullDetState label（仅 universe u）下留下 universe metavars。修法建议: 改用 Volume.lean 的 concrete packetLogVolume_eq_log_det : packetLogVolume p = Real.log (packetDet p)（无 universe 参数）替代 frozen spec 调用；或对 FrozenSpec 显式指定 universe / 将 label 固定为 Type。
2. **Mzk1QPilotR4Stage5AlignActual**（log 05:07，src 21:02）: L74 lt_div_iff 在 Mathlib v4.32 已改名 lt_div_iff₀（仓库用法: FinitePlaceNormalizedIntegers.lean:37、RigidTateSeries.lean:150）；goal qPilotLogImage < qPilotLogImage/(2*l) 可由 rw [lt_div_iff₀ hden] + nlinarith [hq, hden1] 得（q<0, 2l>1 ⇒ q*(2l)<q）。
3. **Mzk1R4LiteralAssemblyActual**（log 04:55）为旧版错误（OriginalInput universe），已随 import 修复，现等 Shared olean；迁移顺序建议: Shared → R4LiteralAssemblyActual → Step3115Comparison/Wiring → hull 两文件。
4. 备注: queue/priority 中 A487 关键文件均已入队（Shared/Comparison/Wiring/HullDet*/R4 均在）；本轮审计未改任何文件。
