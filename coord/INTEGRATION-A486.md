# A486 接线计划：把已有 3.12 组件接成一条链

现状：零件已齐（有限载体 3.12、hull/det 读法、q/Θ 双像、R4 组装、literal 比较、step3115、endgame），缺的是**接口对接**。分工如下，每人只写自己的接线文件。

## 主链（从 3.11.5 到 3.12）
1. `Mzk1QPilotR4Stage5AlignActual`（qpilot，已绿）：qThetaHullReadout/qThetaDetReadout + qThetaReadout_ordered + qThetaStepXIContract
2. `Mzk1HullDetStep3115Actual`（hull，已入队）：具体 hullReadout=packetLogVolume、detReadout=-log|q|、det 归一化比较 ↔ packetDet*q≤1
3. `Mzk1Step3115ComparisonActual`（mainline，已入队）：qThetaHDD + step3115_comparison_proved + qThetaFourTriangleSynthesis（字段填充）
4. `Mzk1R4LiteralAssemblyActual`（mainline，绿）：literal 比较族 + FourTriangleSynthesis ⇒ Cor312Conclusion ∧ ABC ∧ hull 有限
5. `Mzk1R4EndgameCompositionActual`（stepxi，绿）：R4 + Stage5 数值读出 ⇒ Cor312Conclusion ∧ ABC ∧ hull 有限 ∧ ABCForm
6. 有限载体已证 3.12：`finiteAlignmentConclusion`（FiniteAlignmentSocketInstance）与 `s650ActualSignedCor312Conclusion`，作为**参考实现/消费端**

## 接线任务（A486）

| owner | 接线任务 | 交付文件 |
|---|---|---|
| mainline | 读 hull 的 `Mzk1HullDetStep3115Actual`，把其具体读法作为 `step3115_comparison_proved` 的实例证据；用 `qThetaFourTriangleSynthesis` 填充的实例去消费 `r4_literal_assembly`（传入 `hcomp` 时用 qpilot 的 QTheta 数据） | `Mzk1Step3115WiringActual.lean` |
| hull | 把 `Mzk1HullDetStep3115Actual` 的 `hullDetHDD`/`hullDetDsc`/`hullDetSheOut` 组装成 `FourTriangleSynthesis` 实例，并证明其 `step3115_comparison`（用你的 `hullReadout ≤ detReadout ↔ packetDet*q ≤ 1` 引理），交给 mainline 消费 | `Mzk1HullDetFourTriangleActual.lean` |
| qpilot | 证明 `qThetaHullReadout = hullReadout ∘ qThetaState`、`qThetaDetReadout = detReadout ∘ qThetaState`（hull 读法与 q/Θ 双像读法对齐），把 `qThetaReadout_ordered` 接到 hull 的比较引理 | `Mzk1QThetaHullDetAlignActual.lean` |
| abc | A482b 绿后把 literal axioms 交给 mainline：`LiteralCarrierAxiomsV3` + `literalCarrierAxiomsV3_holds` 作为 `r4_literal_assembly` 的载体数据（hcomp 的来源） | 直接交付已绿文件 + 说明 |
| stepxi | 把 endgame 文件升级为消费 mainline 的**填充版** `FourTriangleSynthesis`（不再用裸字段版本），并接 Stage5 读出 | `Mzk1R4EndgameCompositionActual.lean` 更新 |
| stage4 | 查 source-level 两个 alignment socket：`FiniteCertificateLinkEvidenceWiring` 的 `hq_align`/`hth` 是否有 source 证据（`SourceColumnCarrierIdentification`、`SourcePolyIsoTransportDischarge` 等）；写 `socket_source_evidence_report.md`（只读报告，不改文件） | `coord/SOCKET-SOURCE-EVIDENCE.md` |
| lattice/shehdd | 审计接线：验证每对接口的类型签名真正匹配（不是名字接近），维护本表状态；检查是否重复证明 | 审计记录 |

## 纪律
- 只写接线文件；不改别人组件内容；入队用 `node tools/extras_add.mjs`；不碰 watchdog。
- 每个接线文件必须真实 Lean、无 sorry；若类型不匹配，写清缺口而不是伪造。

## A486 接线审计状态（lattice，2026-11-11 05:08；详表 `coord/INTEGRATION-A486-AUDIT.md`）

| # | 接线 | owner | 当前 olean | 签名匹配 | 备注 |
|---|---|---|---|---|---|
| 1 | qpilot QTheta 读法 → mainline step3115 | qpilot/mainline | qpilot ✓ green；mainline step3115 no-olean | **✓ 匹配** | qThetaHullReadout/DetReadout 类型一致；`step3115_comparison_proved` 由 `qThetaReadout_ordered` 填充 |
| 2 | mainline step3115 → R4 literal assembly | mainline | step3115 no-olean；R4 ✓ green | **✓ 匹配** | B 型 `FourTriangleSynthesis` + `hcomp` 类型完全一致 |
| 3 | R4/endgame → Stage5 | mainline/stepxi | R4 ✓ / endgame ✓ | **✓ 匹配** | `abcFormAdditiveHeightBound_of_literalEstimates` 参数逐一对应 |
| 4 | hull step3115 → mainline step3115 | hull/mainline | 双方 no-olean | **✗ 不匹配** | hull 用 A 型 `HDDDecomposition`，mainline 用 B 型 `HDDDecomp`；mainline 以重复包装绕过 |
| 5 | hull wiring → R4/endgame | hull | hull wiring no-olean | **✗ 不匹配** | hull 产出 A 型 `FourTriangleSynthesis`，R4/endgame 需 B 型；且 `ipl/she/apt := True` 占位违规 |
| 6 | mainline wiring → R4/endgame | mainline | wiring no-olean；R4/endgame ✓ | **✓ 匹配** | 但为重复实现（见审计 §3） |
| 7 | qpilot A486 对齐文件 `Mzk1QThetaHullDetAlignActual` | qpilot | **缺文件** | 待交付 | 需证明 qThetaHullReadout = hullReadout ∘ qThetaState 等 |

审计要点: (a) 主链 B 家族内部签名匹配 ✓；(b) hull A 家族与 B 家族不互通，需单一定义来源；(c) 存在多组重复定义/证明（`FourTriangleSynthesis`、`HDDDecomp`、`qThetaFourTriangleSynthesis`、`qThetaHDD`、step3115 包装）；(d) hull `hullDetContract` 的 True 占位必须替换。**只看不改**：本表由 lattice 维护，修复由各 owner 处理。


## A487 结构统一监督（lattice，2026-11-11 05:09）

| # | 监督项 | 当前状态 | 证据 | 判定 |
|---|---|---|---|---|
| ① | mainline 抽出 `Mzk1FourTriangleSharedActual` | **已建立**（05:08:25，B 版 `HDDDecomp`/`HDD`/`fourTriangleReadout`/`FourTriangleSynthesis`/`cor312Conclusion_of_fourTriangleSynthesis`，签名与旧 R4 完全一致）；已在 extra-targets，尚无 olean | `Mzk1FourTriangleSharedActual.lean` 内容核对 | ✓ 创建完成；待编译 |
| ①-a | R4LiteralAssemblyActual 改用共享定义 | **已改**（05:08:30 import 共享模块；本地 `structure HDDDecomp`/`FourTriangleSynthesis` 已移除；r4_literal_assembly 用共享类型） | 源文件 import 行 + 无本地 structure 声明 | ✓ 完成；R4 olean 为改前产物，需重编 |
| ①-b | Step3115Comparison/Wiring 用共享命名空间 | **已改**（两者均 `open ...Mzk1FourTriangleSharedActual`；类型引用共享 B 版） | 源文件 open 行 | ✓ 完成；待 olean |
| ①-c | hull 两个文件迁移共享定义 | **未迁移**：`Mzk1HullDetStep3115Actual` 仍 `import/open Mzk1FourTriangleSynthesisActual`（A 版 `HDDDecomposition`）；`Mzk1HullDetFourTriangleActual` 仍 open A 版 | 源文件 import/open 行（05:07/05:05 版本） | **✗ 待迁移**（类型不匹配仍在，需 hull owner 改 import + 字段类型到 B 版；`hullLaneHDD` 只能临时适配） |
| ② | hull `True/trivial` 占位清除 | **未清除**：`Mzk1HullDetFourTriangleActual` 仍有 `ipl/she/apt := True` + `*_evidence := trivial`（lines 70-75） | grep 结果 | **✗ 待清** |
| ③ | qpilot align `Mzk1QThetaHullDetAlignActual` 交付 | **仍缺文件** | 目录检查 | **✗ 未交付** |
| ④ | A 版重复结构删除/归档 | 未删；`Mzk1FourTriangleSynthesisActual` 仍被 hull 两文件 import；V2 副本仍在 | import 扫描 | 待 hull 迁移后由 owner archive（审计建议） |
| ⑤ | 类型匹配即时报告 | 主链 B 家族（shared/R4/qpilot/mainline/endgame）匹配 ✓；hull A 家族 ✗ 未迁移 | 见 `coord/INTEGRATION-A486-AUDIT.md` §7 | 无新增不匹配；hull 旧 mismatch 持续 |


### A487-2 hull 两文件迁移（lattice 代管后，2026-11-11 05:19）

| 文件 | 迁移内容 | 状态 |
|---|---|---|
| Mzk1HullDetStep3115Actual | 已 import/open `Mzk1FourTriangleSharedActual`（B 版）；`hullDetHDD : HDDDecomp`；删除 FrozenSpec 投影改用 Volume.lean concrete 引理；加 `[DecidableEq label]`；修正 `inv/div` 比较证明 | 源码完成，**待 watchdog 编译** |
| Mzk1HullDetFourTriangleActual | 已 import shared B；`FourTriangleSynthesis`/`fourTriangleReadout`/`cor312Conclusion...` 用共享版；`hullDetContract` 的 `True/trivial` 已删除，改为显式 named hypotheses（`ipl/she/apt : Prop` + 证据），其中 `she` 用 qpilot 已证的 `SHEArrowStatement T` / `sheArrowStatement_proved T` | 源码完成，**待 watchdog 编译**（依赖 HullDetStep3115 olean） |

签名匹配判定: B 版共享结构接管后，两文件与 R4/endgame 类型一致（待编译确认）。A 版 `Mzk1FourTriangleSynthesisActual` 在 hull 两文件中已无引用（grep 0），迁移完成后可归档。占位扫描: 两文件 `True/trivial` 仅文档说明，无实际占位。


### A487-3 hull 编译结果（lattice 代管，2026-11-11 05:26）

- `Mzk1HullDetStep3115Actual`：**DONE EXIT=0，olean 已生成**（54s）；共享 B 版迁移、concrete Volume 引理、DecidableEq 修复均通过。
- `Mzk1HullDetFourTriangleActual`：共享 B 版 + 去 True 占位源码已完成；最新一轮因 `DecidableEq label` 缺失失败，已加 `[DecidableEq label]` 并重新入队，等 watchdog 重编。


### A494 读法对齐新 mismatch（lattice，2026-11-11 05:34）

- `Mzk1QThetaHullDetAlignActual`（qpilot，mtime 05:10:54）**仍按旧 hull API 编写**：
  - 其 `qThetaHullDetSynthesis` 返回 `Mzk1FourTriangleSynthesisActual.FourTriangleSynthesis`（A 型）；
  - 调用 `...Mzk1HullDetFourTriangleActual.hullDetFourTriangleConcrete (qThetaState) (hneg) (hcmp)`（旧 3 参）。
  - A487 迁移后，hull 侧已改为 **shared B 型** `Mzk1FourTriangleSharedActual.FourTriangleSynthesis`，且 `hullDetFourTriangleConcrete` 需要显式 `(ipl hipl apt hapt)` 证据（去掉 True 占位）。两处均不匹配 → QThetaAlign 编译会失败（当前 blocked by HullDetFourTriangle olean 且 API 已变）。
- 修复建议（qpilot 或授权 lattice）：import `Mzk1FourTriangleSharedActual`；返回 shared `FourTriangleSynthesis`；调用新 `hullDetFourTriangleConcrete (qThetaState) hneg ipl hipl apt hapt hcmp`（`she` 用 qpilot `SHEArrowStatement T`/`sheArrowStatement_proved T`，ipl/apt 显式传入）；`cor312Conclusion_of_fourTriangleSynthesis` 用 shared 版。
- 其余读法对齐引理（`hullReadout_qThetaState`、`detReadout_qThetaState`、`qThetaReadout_ordered_iff_packetDet_mul_le_one`、`qThetaPacketDet_mul_q_le_one`）数学上仍成立，只需类型/签名跟进。

