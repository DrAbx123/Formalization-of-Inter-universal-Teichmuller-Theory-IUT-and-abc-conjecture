# 重复项与旧缺口台账（避免重复造轮子，2026-11-14 01:25 Lead）

## 背景
用户指出“之前有做过，感觉眼熟”——核对属实：当前若干“新缺口”其实是**旧缺口换名**，且已有大量供体。

## 旧缺口 ↔ 当前名 ↔ 供体

| 旧名（文件） | 当前出现处 | 已有供体 | 状态 |
|---|---|---|---|
| `GAP-DET-HAAR`（`Mzk1GeneralDualVolumeActual`） | `p2TensorHaarDetTransportMissing`（`Mzk1P2TensorDetFactorActual`） | `Mzk1CanonicalDiagUncondFinalActual`（B4 对角比，无条件）；`Mzk1MatrixHaarBaseActual`（GL_d(ℤp) 保持 coordLattice）；`Mzk1SNFToolActual`/`Mzk1SNFMatrixUWActual`/`Mzk1SNFMatrixDiagActual`/`Mzk1GeneralSNFVolume3Actual`；Haar 唯一性 `MeasureTheory/Measure/Haar/Unique.lean` | **可攻**：B4+GL 不变+SNF+标量 ⇒ det-Haar 律 |
| `GAP-DUAL-TRANSPOSE`（`Mzk1GeneralDualVolumeActual`） | 路线二 det 对偶 | `Mzk1TraceDualVolumeActual`、`Mzk1GeneralDualVolumeActual.relativeHaarVolume_product_of_scaling` | 条件接口 green；数值待接 |
| `GAP-B4`（`HullDetObjectActual` 谱系） | P3 det/net | `Mzk1CanonicalDiagUncondFinalActual`（14:44Z DONE）、`Mzk1P3NetGain*` | B4 对角情形已完成 |
| `MissingLocalizedIsPrincipal`（P1） | 已关闭 | `Mzk1P1LocalizedFractionalIdealActual.localizedLine_isPrincipal_actual`（15:38Z） | **DONE** |
| 旧 C3 `SourcePilotRegionData` 类型 | 旧 C3 表面文件 | S1429 `sourcePilotRegionData_isEmpty` | **vacuous/historical**；P0 native 是有效锚点 |

## 纪律
1. 新缺口命名前先查 `AUDIT_LEDGER.md`、`coord/*GAP*`、本台账与旧文件 rows；同名/同内容一律复用旧名并合并。
2. 旧文件（`HullDetObjectActualV3`、`Mzk1LiteralHullDetCompositionActual`、`Mzk1MatrixHaarBaseActual`、`Mzk1GeneralDualVolumeActual`、SNF 工具链）**不在 watchdog 名单的仍可 import 复用**（olean 已存在）；如需重编再加。
3. 只有真正新内容才立新文件；duplicate 文件应标记“re-export/历史”而非重证。
