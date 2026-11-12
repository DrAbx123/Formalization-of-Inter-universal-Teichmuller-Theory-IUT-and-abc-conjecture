# ROUTE-A-REUSE — Route A 标量 S2717QPilotLogVolume = -A 的复用审计

日期：2026-11-13；qpilot（A1066）。只读 grep/读文件；未编译。olean 状态为 .lake/build/lib/lean/... 实际存在性。

## 1. 声明/引理清单

| 声明 | 文件:行 | 陈述（摘要） | olean |
|---|---|---|---|
| S2717QPilotLogVolume | S2717Cor312FullTargetActual.lean:69-76 | def ... = sourceQPilotSignedLog (S2711I ...).initial | 有（91,472B） |
| sourceQPilotSignedLog_eq_neg_badQAbsLog | OrigXiFPaperQPilotObjectActual.lean:114-117 | sourceQPilotSignedLog S = -OrigXiFPaperBadQAbsLog S | 有（384,720B） |
| OrigXiFPaperBadQAbsLog | 同上 :97-100 | Σ_{b:bad} abs(log(qParameter b)) | 有 |
| OrigXiFPaperBadQAbsLog_eq_source | 同上 :103-105 | = sourceBadQAbsLog S（rfl） | 有 |
| qPilotLogVolume_eq_neg_abs_sum | 同上 :248-252 | O.qPilotLogVolume = -OrigXiFPaperBadQAbsLog I.initial | 有 |
| paperQAbsLog | S2691ExactQNormalizationActual.lean:55 | = qNormFactor l * logQ，qNormFactor=1/(2l) | 有（1,380,520B） |
| paperQAbsLog_eq / paperQAbsLog_pos | 同上 :67-80 | = (1/(2l))logQ；正性 | 有 |
| localQrootLogVolume | HullDetObjectActual.lean:78 | = log ||rootNormedElement T b|| | 无 olean |
| localQrootLogVolume_constructed | 同上 :81-82 | rfl | 无 |
| localThetaPilotLogVolume_eq_gaussExponent_mul | 同上 :97-103 | = gaussExponent j * localQrootLogVolume | 无 |
| thetaPilotLogVolume_eq_gaussExponent_mul_sum | 同上 :117-126 | global sum = gaussExponent × Σ localQroot | 无 |
| localQrootLogVolume_eq | CrossNormLogVolumeActual.lean:64-65 | log||rootNormedElement|| = log(rootNormedElementNorm)（rfl） | 无 olean |
| rootNormedLogVolume | PaperRootCompletionTensorActual.lean:126-127 | = log||rootNormedUnit|| | 有（333,600B） |
| QPilotVolumeScalarTarget | Mzk1QPilotVolumeScalarActual.lean:34 | sourceQPilotSignedLog S = -A（Route A scalar） | 无 olean |
| sourceQPilotSignedLog_eq_neg_badQ | 同上 :38-40 | 同上，port | 无 |
| qPilotVolumeScalarTarget_iff_badQ | 同上 :43-47 | target ↔ OrigXiFPaperBadQAbsLog S = A | 无 |
| S3050Unit_eq_log_norm_div | 同上 :55-65 | S3050Unit = log||x||/(2l) | 无 |
| S2717UpperGap / PaperCor312Full | S2717...:81-123 | 只用不等式 S2717QPilotLogVolume ≤ theta... 与 CTheta 上界 | 有（S2717 olean） |
| QPilotHaarRegionData.volume_eq | Mzk1QPilotHaarBridgeActual.lean:63-72 | S2717QPilotLogVolume = -haarLogVolume(region)（target data，无 inhabitant） | 无 olean |
| qPilotLogVolume_le_thetaHullLogVolume_of_bridge | 同上 :77-96 | 条件不等式，不是 = -A | 无 |
| S3056_hxi_iff_hull_le_magnitude | S3056XiFSignActual.lean:44-58 | 给定 hQ,hH 的符号转换 | 有（100,616B） |
| S3056_hxi_forces_eq_of_inclusion | 同上 :64-82 | 条件等号 | 有 |

## 2. 可推出的链

已有（green olean）链：

    S2717QPilotLogVolume ...        --def-->  sourceQPilotSignedLog I.initial
    sourceQPilotSignedLog I.initial --theorem--> -OrigXiFPaperBadQAbsLog I.initial
    OrigXiFPaperBadQAbsLog I.initial --rfl--> -sourceBadQAbsLog I.initial

因此：若取 A := sourceBadQAbsLog I.initial（或 OrigXiFPaperBadQAbsLog I.initial），则
S2717QPilotLogVolume = -A 已足够由 definition + green theorem 推出，无需新数学。

但若题目中的 A 是 paper 的 absLogQ = logQ/(2ℓ) 或 paperQAbsLog l logQ，则只到
S2717QPilotLogVolume = -OrigXiFPaperBadQAbsLog I.initial 为止；缺：

    OrigXiFPaperBadQAbsLog I.initial = paperQAbsLog l logQ    （或 = absLogQ）

即 GAP-SOURCE-ROOT：source q-parameters 的 Σ abs(log q_b) 与 2ℓ-root/paper q 的规范化 logQ/(2ℓ) 的识别。

## 3. 各文件能否补上该缺口

| 文件 | 已有内容 | 是否补 SOURCE-ROOT |
|---|---|---|
| OrigXiFPaperQPilotObjectActual | source signed log = -badQ sum；OrigXiFPaperBadQAbsLog = sourceBadQAbsLog | 否，只到 badQ sum |
| S2691ExactQNormalizationActual | paperQAbsLog 的 1/(2l) 定义/等式 | 否，没有源 q 的和 |
| HullDetObjectActual | localQrootLogVolume = log||rootNormedElement||；theta=gaussExponent×qroot | 否，没有与 source signed/badQ 的等式 |
| CrossNormLogVolumeActual | 交叉范数可加性；localQrootLogVolume_eq rfl | 否 |
| PaperRootCompletionTensorActual | rootNormedLogVolume 定义 | 否 |
| S3016StepVQPilotIdentificationActual | S3016IdentificationTarget（StepV=weighted global） | 否（本身是 Prop/gap） |
| Mzk1QPilotHaarBridgeActual | QPilotHaarRegionData.volume_eq 把 S2717...=-haarLog 作为 target data | 否/循环 target data，无 inhabitant |
| S3055/S3056 | 给定 hQ/hH 的符号/等号代数 | 否，不产生 = -A |
| Mzk1QPilotVolumeScalarActual（A1065 新文件） | QPilotVolumeScalarTarget 归约到 badQ；GAP-SOURCE-ROOT/GAP-S2691/GAP-S3016 明示 | 明确标 GAP；且无 olean |

## 4. 结论

1. 对 A=sourceBadQAbsLog/OrigXiFPaperBadQAbsLog：S2717QPilotLogVolume = -A 已由 green olean 可直接推出（definitional + theorem）。
2. 对 paper 的 A=absLogQ/paperQAbsLog l logQ：不够。缺 OrigXiFPaperBadQAbsLog initial = paperQAbsLog l logQ（GAP-SOURCE-ROOT）。
3. localQrootLogVolume/rootNormedLogVolume/crossNorm 文件没有与 sourceQPilotSignedLog/OrigXiFPaperBadQAbsLog 的等式；它们只构造 root 侧量。
4. Mzk1QPilotVolumeScalarActual 是 Route A scalar 专门文件，但无 olean，且自身把 SOURCE-ROOT 标为 GAP；不能算已有 green 的 = -A 证明。
5. S2717 的 PaperCor312Full/S3056 只用 ≤ thetaHull 的上界/符号转换，不能推出 scalar = -A。

## 5. 若要闭合 Route A scalar 的最小缺口

    theorem sourceBadQAbsLog_eq_paperQAbsLog
        (S : SourceDefinition31Data l) (logQ : Real) :
        OrigXiFPaperBadQAbsLog S = paperQAbsLog l logQ

（或 = absLogQ 的等价形式）。得到它后，与 sourceQPilotSignedLog_eq_neg_badQAbsLog + S2717 def 立即得
S2717QPilotLogVolume = -paperQAbsLog l logQ。
这需要 source q-parameter 的 abs(log q_b) 求和与 Tate/2ℓ-root 归一化的识别；当前 HullDetObject/CrossNorm/PaperRoot 只给 root 侧定义，没有该求和等式。

## 6. olean 状态附注

- 有 olean：S2717Cor312FullTargetActual, OrigXiFPaperQPilotObjectActual, S2691ExactQNormalizationActual, PaperRootCompletionTensorActual, S3055PaperCor312Assembly, S3056XiFSignActual；
- 无 olean：Mzk1QPilotVolumeScalarActual, HullDetObjectActual, CrossNormLogVolumeActual, Mzk1QPilotHaarBridgeActual。

## 文件

- 本文件 coord/ROUTE-A-REUSE.md；grep 只读，无编译。