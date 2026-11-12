# A486 接线审计（lattice，只读验证）

generated: 2026-11-11 05:08 (lattice)

范围: 对 `coord/INTEGRATION-A486.md` 主链逐对验证**接口类型签名真正匹配**（不是名字接近），并检查重复证明/重复结构；只看不改组件。证据 = 源文件声明 + olean 存在性 + watchdog.log DONE/FAIL。

## 1) 当前文件状态（ole an 口径）

| 文件 | owner | olean | 角色 |
|---|---|---|---|
| tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean | qpilot | **True** | q/Θ 双像读法 + R4 签名契约 |
| tmp/sheaf/xif/paper/Mzk1R4LiteralAssemblyActual.lean | mainline | **True** | R4 literal assembly（B 型 FourTriangleSynthesis） |
| tmp/sheaf/xif/paper/Mzk1R4EndgameCompositionActual.lean | stepxi | **True** | endgame：R4 + Stage5 读出 |
| tmp/sheaf/xif/paper/Mzk1HullDetStep3115Actual.lean | hull | False | 具体 hull/det 读法（A 型 HDDDecomposition） |
| tmp/sheaf/xif/paper/Mzk1Step3115ComparisonActual.lean | mainline | False | step3115 比较（B 型） |
| tmp/sheaf/xif/paper/Mzk1Step3115WiringActual.lean | mainline | False | A486 接线（B 型） |
| tmp/sheaf/xif/paper/Mzk1HullDetFourTriangleActual.lean | hull | False | A486 接线（A 型） |
| tmp/sheaf/xif/paper/Mzk1QThetaHullDetAlignActual.lean | qpilot | **缺文件** | A486 qpilot 对齐任务未交付 |

## 2) 逐对签名验证

| # | 对 | 期望接口 | 实际类型 | 结论 |
|---|---|---|---|---|
| 1 | qpilot → mainline step3115 | `qThetaHullReadout/qThetaDetReadout : Bad → Real`，供 `HDDDecomp Real Real (Bad ...)` | `qThetaHullReadout := qPilotLogImage`、`qThetaDetReadout := thetaPilotLogImage`；`qThetaReadout_ordered : qThetaHullReadout ≤ qThetaDetReadout`（`Mzk1QPilotR4Stage5AlignActual:91-101`） | **匹配 ✓** |
| 2 | mainline step3115 → R4 literal assembly | `r4_literal_assembly (S : B FourTriangleSynthesis DSC SHEOut) (j) (hcomp) → Cor∧ABC∧fin` | mainline `qThetaFourTriangleSynthesis : B FourTriangleSynthesis (Bad) (Bad)`，`step3115_comparison_proved` 填充 B 字段（`Mzk1Step3115ComparisonActual:33,50`） | **匹配 ✓** |
| 3 | R4/endgame → Stage5 | `abcFormAdditiveHeightBound_of_literalEstimates (logVolume) (hullVolume) (hheight) (hmain) : ABCFormAdditiveHeightBound` | endgame 以完全相同参数调用（`Mzk1R4EndgameCompositionActual:r4_endgame_composition`; Stage5 `Mzk1IUTIVStage5ABCFormActual:54`） | **匹配 ✓** |
| 4 | hull step3115 → mainline step3115 | mainline 应消费 hull 的 `step3115_comparison_hullDet`/`hullDetHDD` | hull 用 **A 型** `HDDDecomposition`（`Mzk1HDDObjectActual:13`）；mainline 用 **B 型** `HDDDecomp`（`Mzk1R4LiteralAssemblyActual:31`）——两个不同 structure，字段同形但类型不同；mainline 只能通过自己重包装的 `hullLaneHDD : HDDDecomp` + `step3115_comparison_hullDet_concrete` 复用引理 | **不匹配 ✗**（靠重复包装绕过） |
| 5 | hull wiring → R4/endgame | `r4_literal_assembly`/`r4_endgame_composition` 需要 **B 型** `FourTriangleSynthesis`（`HDDDecomp` 字段） | `Mzk1HullDetFourTriangleActual.hullDetFourTriangle : FourTriangleSynthesis_A (HullDetState label) Unit`（A 型，`fourTriangleReadout` 用 `HDDDecomposition`，`Mzk1FourTriangleSynthesisActual:55`） | **不匹配 ✗**：hull 接线实例无法喂给 R4/endgame；且 `hullDetContract` 的 `ipl/she/apt := True` + `trivial` 是占位，违反 A486“无假证/无 True 占位” |
| 6 | mainline wiring → R4/endgame | Step3115Wiring 的 qTheta 分支应直接消费 qpilot 实例（B 型） | `Mzk1Step3115WiringActual.qThetaFourTriangleSynthesis` 解析到 mainline 自己的 B 型实例；hull 证据部分用 B 型 `hullLaneHDD` 重包装 | 类型 **匹配 ✓**（但为**重复实现**，见 §3） |
| 7 | 参考实现 `finiteAlignmentConclusion` / `s650ActualSignedCor312Conclusion` | 作为消费端参考 | 未与主链出现直接类型配对调用 | **待接线/未验证**（记录，不宣称） |

## 3) 重复证明 / 重复结构（应合并或删除）

- **两个 `FourTriangleSynthesis` / `fourTriangleReadout`**: `Mzk1FourTriangleSynthesisActual:29,55`（A 型，字段 `hdd : HDDDecomposition`）与 `Mzk1R4LiteralAssemblyActual:46,53`（B 型，字段 `hdd : HDDDecomp`）——同名不同命名空间，是 §2#4/#5 类型不匹配的根因。
- **两个 HDD structure**: `Mzk1HDDObjectActual.HDDDecomposition` 与 `Mzk1R4LiteralAssemblyActual.HDDDecomp`，字段完全相同（hullReadout/detReadout），属重复定义。
- **两个 `qThetaFourTriangleSynthesis`**: `Mzk1QPilotR4Stage5AlignActual:225`（`dsc := qThetaDSC`）与 `Mzk1Step3115ComparisonActual:50`（`dsc := id`）；两者都用 `qThetaReadout_ordered` 填 `step3115_comparison`，实质重复。
- **重复 step3115 包装**: qpilot `qTheta_step3115_comparison`（`Mzk1QPilotR4Stage5AlignActual`）vs mainline `step3115_comparison_proved`（`Mzk1Step3115ComparisonActual:33`）；hull `step3115_comparison_hullDet`（`Mzk1HullDetStep3115Actual:131`）vs mainline `step3115_comparison_hullDet_concrete`（`Mzk1Step3115ComparisonActual`）——后两者是同一引理的不同包装。
- **重复 HDD 打包**: qpilot `qThetaHDD`（`Mzk1QPilotR4Stage5AlignActual:204`）与 mainline `qThetaHDD`（`Mzk1Step3115ComparisonActual:29`）同字段；mainline `hullLaneHDD` 与 hull `hullDetHDD` 同字段。
- **占位风险**: `Mzk1HullDetFourTriangleActual.hullDetContract` 用 `ipl := True`, `she := True`, `apt := True` + `trivial`（文件内 `she_evidence := trivial` 等）→ 必须改为真实命题/证据或显式 named hypotheses（参考 qpilot `qThetaStepXIContract` 的 `ipl hipl apt hapt` 传参方式）。

## 4) 审计结论/建议（不改组件）

1. **主链 B 家族（mainline/qpilot/R4/endgame/Stage5）内部签名匹配 ✓**，A486 接线在这些点可按现有类型完成。
2. **hull 家族 A 与主链 B 不互通 ✗**：hull 的两个文件（HullDetStep3115/HullDetFourTriangle）用 A 型；要么 hull 改用 B 型（import R4LiteralAssembly 的 `HDDDecomp`/`FourTriangleSynthesis`），要么把 B 型定义迁到共享模块并让双方都引用（不能两套同名结构并存）。
3. **重复过多**：至少合并 `FourTriangleSynthesis`/`HDDDecomp` 结构（单一来源）、合并 `qThetaFourTriangleSynthesis`、`qThetaHDD`、step3115 包装；合并前 A486 的“接线”只是重复包装，不是真实增长。
4. **占位违规**: hull `hullDetContract` 的 `True` 槽必须替换为真实数据，否则即使类型对齐也不能作为 rung 证据。
5. 文件状态以 olean 为准：qpilot/R4/endgame 已绿；hull step3115、mainline step3115/Wiring、hull wiring 仍无 olean；qpilot 的 `Mzk1QThetaHullDetAlignActual` 未交付。

## 7) A487 结构统一监督（2026-11-11 05:09）

**mainline 报告核对**:
- `Mzk1FourTriangleSharedActual.lean` 已创建（05:08:25），内容为 B 版 `HDDDecomp`/`HDD`/`fourTriangleReadout`/`FourTriangleSynthesis`/`cor312Conclusion_of_fourTriangleSynthesis`，与旧 R4 定义逐字一致；已入 extra-targets，**无 olean**。
- `Mzk1R4LiteralAssemblyActual.lean` 已 import 共享模块（05:08:30），**本地 `structure HDDDecomp`/`FourTriangleSynthesis` 已移除**，`r4_literal_assembly` 使用共享类型；R4 现有 olean 是改动前产物（stale），需重编。
- `Mzk1Step3115ComparisonActual` / `Mzk1Step3115WiringActual` 已 `open ...Mzk1FourTriangleSharedActual`（05:08:30）；类型引用 B 版。
- **hull 两文件未迁移**: `Mzk1HullDetStep3115Actual` 仍 import/open `Mzk1FourTriangleSynthesisActual`（A 版 `HDDDecomposition`）；`Mzk1HullDetFourTriangleActual` 仍 open A 版。因此 A487 后 B 版共享结构已存在、但 hull 车道仍在 A 版 → 类型不匹配**未消除**（仅 mainline 的 `hullLaneHDD` 临时适配）。
- **占位未清除**: `Mzk1HullDetFourTriangleActual` lines 70-75 仍 `ipl/she/apt := True`, `ipl/she/apt_evidence := trivial`。
- **qpilot align 未交付**: `Mzk1QThetaHullDetAlignActual` 仍不存在。
- **qpilot align olean stale**: `Mzk1QPilotR4Stage5AlignActual` src 05:02:23 vs olean 04:59:47，已入队待重编（R4 定义变化后必须重编）。

**shehdd A486 审计合并要点**（`coord/A486-WIRING-AUDIT-shehdd.md`）:
- canonical 统一到 `Mzk1R4LiteralAssemblyActual`（现共享模块为其定义来源）；`Mzk1R4LiteralAssemblyV2Actual` 同内容副本（0 importer）、`Mzk1FourTriangleSynthesisActual`（hull 并行 A 版，仅 hull import）为 archive 候选。
- 未接线 prior-art: `FiniteAlignmentSocketInstance.finiteAlignmentConclusion`（green，无 importer）、`S650ActualSignedCor312Contract`（无 olean/未入队，+Adapted 副本）、`S3139*` ~18 green 文件含 `Cor312Conclusion` 生产者（当前 A486 接线引用 0，queue/priority 0）→ 建议在接线文档登记为 prior-art 证据，避免重复证明。
- 全部 A486 接线文件真实 sorry = 0（词法扫描）；green 文件旧日志错误为 stale。

**结论**: A487 结构统一处于“共享模块已建立、mainline 侧已切换、hull 侧未迁移”的中间态；待 hull 迁移 + 清占位 + qpilot align 交付后，才能判定 A 版重复可归档、hull↔R4 签名真正匹配。

