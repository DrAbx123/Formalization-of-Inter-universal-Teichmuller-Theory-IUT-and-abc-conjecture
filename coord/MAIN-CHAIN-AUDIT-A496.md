# MAIN-CHAIN-AUDIT-A496 — 回归审计我们自己的主链（LANA 仅参考）

generated: 2026-11-11 05:35 (lattice, 只读)

方向: A496 决定 LANA 不再作接线/目标；本文件回归审计我们自己的 3.12 主链（Step3115/R4/endgame）的 olean、无 sorry、无 True。

## A498 合并裁决（A497 VACUITY 审计结论并入）

**本文件的状态表以本节裁决为准（与 `coord/VACUITY-AUDIT-A497.md` 一致）:**
1. **qTheta 链 = VOID（空转）**：`Mzk1QPilotR4Stage5AlignActual` 的 `thetaPilotLogImage := qPilotLogImage/(2ℓ)`；`qPilotLogImage_lt_thetaPilotLogImage`/`qThetaReadout_ordered`/`qThetaStepXIContract`/`qThetaFourTriangleSynthesis`、`Mzk1Step3115ComparisonActual.step3115_comparison_proved`/`qThetaFourTriangleSynthesis`、`Mzk1Step3115WiringActual.qTheta_r4_literal_assembly` 的 Cor312 分量、`Mzk1QThetaHullDetAlignActual` 的 qTheta 对齐均为 VACUOUS；**不得计 3.12 进度**。
2. **`Cor312Conclusion` 单独不可作 3.12 证据**：`StepXIContract` 的 `qSigned/thetaSigned/targetSigned` 自由，`targetSigned:=thetaSigned` + `target_le_theta:=rfl` 使 `Cor312Conclusion` 自动成立；必须附 contract provenance（q/θ/target 固定到 paper 对象并证明两条 IUT IV 比较）。
3. **唯一 named 真内容 = `hcomp` 两条 IUT IV §2 比较**：`Cor312ToABCBridgeInterface.height_le_normalizedRegionVolume` 与 `regionVolume_le_normalizedWeight`；`named-gap:independent-theta-pilot-readout`（literal θ-hull 真实 log-volume）是构造缺口；两者均登记 DAG-BLOCKED。
4. 仍可用候选: HullDetStep3115 的真实 hull/det 数值比较（`HullDetState` 抽象，非 paper 源对象）、R4/endgame（条件于 hcomp）、literal hull finiteness、ExplicitABC⇒ABCConjecture。


## 1) 主链文件状态（ole an 口径）

| 文件 | 角色 | olean | fresh | 源码 sorry/True/axiom | 状态/风险 |
|---|---|---|---|---|---|
| `Mzk1FourTriangleSharedActual` | canonical B 版 HDDDecomp/fourTriangleReadout/FourTriangleSynthesis/cor312Conclusion | True | ✓ | 0（仅 doc） | 绿；所有主链消费者统一引用它 |
| `Mzk1R4LiteralAssemblyActual` | `r4_literal_assembly : FourTriangleSynthesis DSC SHEOut → j → hcomp → Cor∧ABC∧hullFin` | True | ✓ | 0 | 绿；消费 shared 类型 |
| `Mzk1R4EndgameCompositionActual` | `r4_endgame_composition`：R4 + Stage5 `abcFormAdditiveHeightBound_of_literalEstimates` | True | ✓ | 0 | 绿；消费 R4 shared 类型 |
| `Mzk1QPilotR4Stage5AlignActual` | q/Θ 双像读法 + qThetaStepXIContract/qThetaReadout_ordered | True | ✗ stale | 0（仅 doc） | **qTheta 链 VOID（A497/A498）**；olean stale；仅 `qPilotLogImage` 等真实部分可用 |
| `Mzk1HullDetStep3115Actual` | 具体 hull/det 读法（shared B 版，`hullReadout`/`detReadout`/`hullDetHDD`/比较） | True | ✓ | 0（仅 doc） | 绿；Step3115/读法对齐前置已就绪 |
| `Mzk1HullDetFourTriangleActual` | hull 读法 → shared B `FourTriangleSynthesis`（`hullDetFourTriangle`/`_cor312`/`hullDetContract`/`_Concrete`） | **False** | — | 0（真实 named hypotheses，无 True/trivial） | 源码已迁 shared B + 去占位 + `[DecidableEq label]`；等下一轮 plan 重编 |
| `Mzk1Step3115ComparisonActual` | `step3115_comparison_proved`、`qThetaFourTriangleSynthesis`、`hullLaneHDD` | **False** | — | 0 | **VOID（qTheta 空转）**；`hullLaneHDD` 为真实模型层辅助；无 olean |
| `Mzk1Step3115WiringActual` | qTheta 填充实例 + hull evidence + `r4_literal_assembly` 消费 | **False** | — | 0 | **Cor312 分量 VOID（qTheta 空转）**；ABC 分量条件于 hcomp；无 olean |
| `Mzk1QThetaHullDetAlignActual` | 读法对齐（工程化 qThetaPacket/qThetaState） | **False** | — | 0（仅 doc） | **qTheta 对齐 VOID（A497/A498）**；补丁签名虽匹配 shared B，但被对齐读法空转；无 olean |

## 2) 依赖链（当前）

1. `Mzk1FourTriangleSharedActual` → 绿（05:10:46 olean）。
2. `Mzk1R4LiteralAssemblyActual` → 绿（05:18:53 olean）。
3. `Mzk1R4EndgameCompositionActual` → 绿（05:02:36 olean）。
4. `Mzk1HullDetStep3115Actual` → 绿（05:18:48 olean）。
5. `Mzk1HullDetFourTriangleActual` → 源码完成；无 olean（待 plan reload）。
6. `Mzk1Step3115ComparisonActual` / `Wiring` → 依赖 4/5（及 QPilotR4Stage5Align 重编）；无 olean。
7. `Mzk1QThetaHullDetAlignActual` → 依赖 QPilotR4Stage5Align（重编）+ HullDetFourTriangle（无 olean）；无 olean。

## 3) 审计要点

- **无 LANA 依赖**: 主链 9 文件 `import tmp.sheaf.lana` = 0；LANA 已移出队列（queue 466，lana-lines=0），仅磁盘参考。
- **无真实 sorry/True/axiom**: 源码扫描 `sorry|\bTrue\b|PUnit|axiom` 的命中均为 docstring 说明（“No sorry/axiom/True placeholder”/“supplied evidence (no True/trivial placeholders)”），无代码级占位/兜底。
- **QThetaAlign 已按新 API 对齐**: qpilot 补丁（05:34:03）imports shared、返回 shared `FourTriangleSynthesis`、调用 `hullDetFourTriangleConcrete (T:=T) (qThetaState T b) (hullReadout_qThetaState_neg T b) ipl hipl apt hapt (qThetaPacketDet_mul_q_le_one T b)`；与我们 hull 文件签名一致 ✓（待 olean 验证）。
- **风险**: `Mzk1QPilotR4Stage5AlignActual` olean stale（src 05:24:14 > olean 04:59:47）→ 重建前不能作为 gate 证据；`Step3115Comparison/Wiring` 需下一轮重试；`HullDetFourTriangle` 的失败 state 的 mtime 早于 touch，当前 plan 不重试，等 plan reload。

## 4) 行动/建议（只读审计，不改组件）

1. 等 watchdog 下一轮 plan：优先重编 `HullDetFourTriangle` → `Step3115Comparison/Wiring`、`QThetaAlign`（它们已在 priority/queue）。
2. `Mzk1QPilotR4Stage5AlignActual` 需重编（stale）；主链下游若引用其旧 olean 需在重建后复核。
3. 复核 green 文件时以 **ole an mtime ≥ src mtime** 为准；stale olean 不计 gate 证据。
4. LANA 审计（`FAITHFULNESS-AUDIT-A491.md`、`NUMERICAL-WALL-PLAN.md`）标记为 **reference-only**；不再引用 LANA `NumericalWall/Wall/rhs` 作 rung。
5. 后续若 QThetaAlign/Step3115 编译 FAIL，按 per-file 日志迭代（不手动编译）。

## 5) **A497 更正：qTheta/step3115 链为空转（VACUOUS），不计 3.12 进度**

- 根因: `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage := qPilotLogImage/(2ℓ)`；`qPilotLogImage_lt_thetaPilotLogImage`/`qThetaReadout_ordered` 只是负数除法算术；`qThetaStepXIContract.targetSigned := thetaSigned`、`target_le_theta := rfl`。
- 因此: `Mzk1Step3115ComparisonActual.step3115_comparison_proved`、`qThetaFourTriangleSynthesis`、`cor312Conclusion_of_qThetaSynthesis`、`Mzk1Step3115WiringActual.qTheta_r4_literal_assembly` 的 Cor312 分量、`Mzk1QThetaHullDetAlignActual` 的 qTheta 对齐均为 **VACUOUS，不得作 3.12 证据**（详见 `coord/VACUITY-AUDIT-A497.md`）。
- `StepXIContract`/`Cor312Conclusion` **结构过弱**（target 可等于 theta；无独立对象约束），单独不构成 3.12 证据。
- 仍可用的条件/模型候选: `Mzk1HullDetStep3115Actual` 的真实 hull/det 数值比较（但 `HullDetState` 是抽象输入）、`Mzk1R4LiteralAssemblyActual`/`Mzk1R4EndgameCompositionActual`（条件于 `hcomp` 显式 named input）、`Mzk1LiteralIQHullFinitenessActual`、`Mzk1ExplicitABCWeakeningActual`。
- 真实 named 缺口见 `coord/NAMED-GAPS-A497.md`: (i) `named-gap:hcomp-iut4-comparisons`（两条 IUT IV §2 比较）；(ii) `named-gap:independent-theta-pilot-readout`（用 literal θ-hull 真实 log-volume 定义，非 q/(2ℓ)）；(iii) contract provenance。
- DAG-BLOCKED 已登记 CHAIN-BROKEN vacuity 4 条 + named gap 2 条（blocked_total=73）。**空转声明不计入 3.12 进度。**

