# P0-CNORM-CONSUMERS — 仍消费 c_norm 的 green 断言与 paper-faithful 替代接口

日期：2026-11-13；hull（P0-A）。只读审计 + 新增安全替代文件；不改旧 green 文件。

## 0. 判定基线

- `c_norm`：green 链的建模归一化 `qVFamNormalizedCoefficient = order(qVFamily)`
  (`QVFamNormalizedCoefficientActual.lean:48-57`)；在 `RootNormalizedContainmentActual.lean:53-58`
  以 `rootNormCoefficient` 出现，`rootHalfCoefficient = rootNorm/(2l)`。
- `c_root`：paper q_v 系数 `qVFamPaperRootCoefficient = order(qVFamily)/(2l)`
  (`QVFamRootFactorCorrectionActual.lean:56-57`；`qVFamPaperThetaTensorCoefficient j = j² c_root` :59-63)。
- 注意：`rootHalfCoefficient` 用的是 **supply** `qVFamNormalizedCoefficient`（-logb norm）
  除以 2l，不自动等于 `qVFamPaperRootCoefficient = order/(2l)`。`S1074SupplyCNormOrderActual:42-56`
  表明 `supply c_norm = order` 需 `S1074NormCompatibilityOne` / `e=1`；未证。任何 c_root/c_norm 互换必须显式记录此 GAP。

## 1. 仍使用 c_norm 的 green 消费者（只读清单）

| consumer | file:line | 实际对象 | paper-faithful? | 建议 |
|---|---|---|---|---|
| qVFam normalized coefficient | QVFamNormalizedCoefficientActual.lean:48-57 | c_norm=order | 否（建模归一化） | 保留；不用于 paper q 读数 |
| rootNormCoefficient/rootHalfCoefficient | RootNormalizedContainmentActual.lean:52-58 | rootNorm=supply c_norm; rootHalf=supply/2l | 否（e=1 才等于 order/2l） | 保留；paper 用 QVFamPaperRootCoefficient |
| qPilotClassicalRegion / qPilotClassicalLog | RootHullContainmentInequalityActual.lean:58-75, :105-123 | F(c_norm)O_hol; log at c_norm | 否 | green 的 c_norm 模型；paper q 用 S800 qPilotPaperRegion/qPilotPaperRegionLog |
| actualQPilotLogShellRegion | Ind3OutputHullQPilotActual.lean:74-75 | qPilotNormRegion = F(c_norm)O_hol | 否 | 名字易误读；paper-faithful 替代应为 qPilotPaperRegion |
| actualQPilotLogShellRegion_subset_ind3OutputHull | Ind3OutputHullQPilotActual.lean:79-82 | c_norm q ⊆ rootNormHull | 否 | 保留为 c_norm 结论；不能当 paper q⊆Θ |
| actualQPilotLog_le_ind3OutputHullLog | Ind3OutputHullQPilotActual.lean:97 | c_norm q log ≤ c_norm root hull log | 否 | 不是 paper `-|log q|≤-|log Θ|` |
| qPilotNormRegion_measure_pos_lt_top | RootHullMeasureActual.lean:139 | c_norm region pos/fin | 否 | 可用于 c_norm 侧；paper 正性用 S1023/S778 |
| qPilotPaperRegion (S778) | S778PaperQPilotHalfRegionActual.lean:48-50 | F(rootHalf)C_hol (supply/2l) | 半 paper（非 order/2l） | 保留；若需 order/2l 用 S800/QVFamPaperRootCoefficient |
| qPilotPaperRegionLog / paperHullLog | S800LeastLambdaOHullActual.lean:111-131 | least lambda-O hull at rootHalf | 半 paper（supply/2l；含 j=0） | 本块目标；其 pos/fin 已由 Mzk1PaperBlockTargetActual 无条件 discharge |
| paperTargetNormalization_of_pos_fin | Mzk1PaperTargetNormalizationActual.lean:81-87 | PaperTargetNormalization 条件于 pos/fin | 目标陈述 c_root/supply | 条件版保留；无条件版见新文件 |
| BadPlace* normalized 文件（S13 等） | 例 BadPlacePaperNormalizedActual.lean:65-87, BadPlaceNormalizationSourceActual.lean:56-93 | supply c_norm | 否（模型） | 保留；改 paper 需 e=1/S1074 或显式重写 |
| paper-faithful NonzeroHull | Mzk1PaperFaithfulHullP4Actual.lean（P4） | PaperNonzeroLabel, paperRootCoefficient order/2l | 是（非零标签） | 不要与 S800 leastLambdaOHull 混用；两者不同 object |

## 2. 安全替代接口（已新增，watchdog DONE EXIT=0 @21:51:48Z；olean 53512B）

`tmp/sheaf/xif/paper/Mzk1PaperTargetNormalizationUnconditionalActual.lean`：
- `paperTargetNormalization_unconditional : PaperTargetNormalization`；
- `paperM_nonneg_unconditional : 0 ≤ paperM`；
- 证明用 S778 `qPilotPaperRegion_measure_pos` + green `Mzk1PaperBlockTargetActual.paperHull_measure_lt_top`；
- 不触碰旧条件定理，不用系数桥，不新增目标假设；
- build 证据：source 67 行/2655B，olean 53512B mtime 2026-11-12T21:51:48Z。

## 3. 结论 / 后续

- 所有仍用 c_norm 的 green 断言都有明确 file:line；没有发现需要立即删除的错误陈述，但
  `Ind3OutputHullQPilotActual` 的命名/读数必须标为 c_norm 模型，不能当 paper q-pilot。
- paper q 读数应走 S800 `qPilotPaperRegionLog`/`paperHullLog`（c_root/supply 半系数）或
  `Mzk1PaperTargetNormalizationUnconditionalActual`；若要用 order/(2l) 而非 supply/2l，需先补 S1074 e=1。
- P4 `paperFaithfulThetaHull` 与 S800 least hull 是不同对象；本文件不声称二者相等。
## 4. Canonical P0 target vs historical S800/S801 vs qVFam P4 (2026-11-13 update)

最新 canonical 链：**S3137 → Mzk1Paper312StatementActual → S3135**。

| 链 | 对象/读数 | file:line | 状态 | P0 验收 |
|---|---|---|---|---|
| canonical q 侧 | `qPilotLogVolumeReading P = -|log ‖q‖|` | S3137QThetaPilotLogVolumeReadingsActual.lean:77-85 | GREEN | 是 |
| canonical Θ 侧 | `thetaPilotHullLogVolumeReal C3 = log(actualC3LogShellTensorHaar C3 (actual tensor region))` | S3137:128-135 | GREEN（raw Haar；hull=actual region） | 是 |
| canonical target | `Paper312Statement C3 P` | Mzk1Paper312StatementActual.lean:49-50 | REAL_PROP | 是；P0 验收就是它 |
| canonical equivalence | `Paper312Statement ↔ qThetaPilotLogVolumeComparison` | Mzk1Paper312StatementActual.lean:52-54 | PROVED | 是 |
| canonical gap | `qThetaPilotLogVolumeComparison C3 P` | S3137; Mzk1Paper312StatementActual:114 | PENDING | 唯一剩余 gap |
| S3132 paper hull set | `actualPaperHull_eq_unitRegion`; `paperHullRealLogVolume` | S3132PaperHullSetPropertiesActual.lean:97-99,128-135 | GREEN | 旁证，不是 S3137 Θ 读数 |
| historical S800 | `paperPossibleImages = rootThetaImageSet` (SignedLabel incl j=0); `paperHullLog` | S800LeastLambdaOHullActual.lean:91-131 | GREEN but **degenerate**: hull=R*O=O_hol; `paperHullLog=0` | 否；历史对象 |
| historical S801 | 正确 NonzeroLabel `paperLeastLambdaOHull`; `paperHullLog=paperQPilotRegionLog` | S801PaperHullLogActual.lean:36-57 | GREEN historical | 否；不是 canonical P0 |
| qVFam P4 | `paperFaithfulThetaHull` (PaperNonzeroLabel, qVFam block) positive/finite | Mzk1PaperFaithfulHullP4Actual.lean | GREEN side result | 否；不是 C3 log-shell 载体 |

结论：
- P0 的验收对象必须改为 S3137 两个读数 + `Paper312Statement`；不是 S800/S801 的 qVFam 旧 hull，也不是 P4 qVFam hull。
- S800 的 `paperHullLog` 被 j=0 项撑成 O_hol（log=0），因此 `Mzk1PaperTargetNormalizationUnconditionalActual` 的 unconditional target 是**历史链的弱化结论**，不能作为 P0 验收。
- S801 在 historical NonzeroLabel 上给出 region-log 等式（trivial equality），也不等于 canonical S3137 的 q/Θ 读数比较。
- P0 唯一实质 gap：`qThetaPilotLogVolumeComparison`（S3137 PENDING）；按 Mzk1HolomorphicHullLogVolumeReconciliationActual 的 6/7 表，缺 paper normalization、IQ carrier、(Ob3-3)、multiradial comparison、theta raw Haar vs paper normalized V、exact hull V 上界。

## 5. 旧的 P4-A/P4-B 结果如何归档

- P4-A（paperFaithful 正/有限）仍是 qVFam 块上的 side result，保留但不进入 P0 验收。
- P4-B（S800 pos/fin discharge）只对 historical S800 hull 有意义；因 S800 hull 退化，它是弱化结论。
- P0-A 的 `Mzk1PaperTargetNormalizationUnconditionalActual` 应标为 historical/S800-based，不作为 P0 canonical。
## 4. P0 唯一剩余 inhabitant：PaperQPilotObjectActual（2026-11-13 更正）

**更正**：C2/logKummer/logKummer_eq 不是缺失：`C2Actual.sourceLogKummerDataActual` 提供实际 C2；`QPilotLineActualConstruction.paperQPilotObjectActual` 已从 `NativeC1PaperSource P` + donor D + strip + oneColumn 条件构造 PActual（C2 实际、logKummer:=C2、logKummer_eq:=rfl）。

本轮 `Mzk1PaperQPilotActualInhabitantOfPacketActual` 给出无额外字段版本：
- `P : NativeC1PaperSource` + `D : SourcePilotRegionDonors (I:=P.input)` + `ind3TimesMuStrip 1 0` + `sourceOneColumnActual P` → `PaperQPilotObjectActual (I:=P.input)`；
- `paperQPilotObjectActualOfPacket_nonempty`。

真正剩余：`NativeC1PaperSource` packet、donor D、以及 `P.input`（V=NativePlaces）与 `S2711I`（V=FinitePrimePlace 2 7）的 **input alignment**；对齐未证（`Mzk1PaperQPilotActualInputMismatchActual`）。

## 5. #7 exact hull V upper bound：实际定理（2026-11-13）

- `Mzk1ExactHullVLocalZeroActual.localBallLog_sub_unit_le_zero`：每 place log μ(ball)-log μ(unit)≤0（rootImageRadius≤1）。
- `Mzk1ExactHullVMainTermActual.normalizedLog_hull_nonpos`：hull⊆unit ⇒ normalizedLog≤0。
- `Mzk1MainTermActualNonnegActual.mainTerm_nonneg_actual`：`CurveData.disc/cond : Nat` 非零 ⇒ log≥0 ⇒ mainTerm=(1/4)l(log disc+log cond)≥0。
- `Mzk1MainTermActualBoundActual.normalizedLog_hull_le_actualMainTerm`：
  `normalizedLog_hull ≤ (1/4)l(log disc+log cond)`，C0=0。
- 这关闭了 exact hull V 上界的**算术主项非负来源**；但 V 仍是 normalizedLog，不是 raw paper V；paper normalization 字典仍是独立 gap。
