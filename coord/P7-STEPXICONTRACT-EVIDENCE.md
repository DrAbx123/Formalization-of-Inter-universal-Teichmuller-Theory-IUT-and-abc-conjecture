# P7/#6 — StepXIContract evidence 映射（审计 + 结构草案）

日期：2026-11-13；abc。只读审计，不改数学文件。

## 1. 现状

| 项 | 状态 | file:line |
|---|---|---|
| WallObligation enum（holomorphicHull/determinantNormalization/logVolumeComparison） | 仅 enum，无 evidence 字段 | `Mzk1HolomorphicHullLogVolumeReconciliationActual.lean:16/17/18`（“contract enum only; no StepXIContract field”） |
| S3137 assembly 临时 contract | `contractOfS3137Comparison` 只设 qSigned/thetaSigned/targetSigned, ipl/she/apt=True, `target_le_theta:=h` | `Mzk1Cor312S3137AssemblyActual.lean:35-49` |
| 审计行 | `hullLogReconRows` 12 行；`hullLogReconMissing` 7 条 | `Mzk1Holomorphic…ReconciliationActual.lean:15-44` |
| N3 bridge | `paperGap_iff_qThetaComparison` / `paperGap_iff_paper312Statement` | `Mzk1N3SharedContainerBridgeShaActual.lean:46/52` |

## 2. 结构草案（Lean）

`tmp/sheaf/xif/paper/Mzk1StepXIEvidenceInterfaceActual.lean`（新文件，header GAP）：
```lean
structure StepXIEvidenceInterface where
  holomorphicHullEvidence : Prop
  determinantNormalizationEvidence : Prop
  logVolumeComparisonEvidence : Prop
```
这是**目标 schema**，不是 evidence：inhabitant 需要实际三义务（GAP-P7-CONTRACT）。

## 3. 缺口

```
GAP-P7-CONTRACT：StepXIContract 无 holomorphicHull/determinantNormalization/logVolumeComparison
  的字段或 linkage；当前只有 enum + S3137 assembly 临时 contract（target=q，ipl/she/apt=True）。
```