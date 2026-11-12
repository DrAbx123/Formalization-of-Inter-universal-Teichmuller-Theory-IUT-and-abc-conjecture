# CANONICAL-TARGET-MAP — 当前锁定目标链 vs 历史/旁支（2026-11-13 06:03）

依据：Mzk1Paper312StatementActual.lean（import S3137QThetaPilotLogVolumeReadingsActual）、S3136/S3135 gate、Mzk1HolomorphicHullLogVolumeReconciliationActual。

## 1. Canonical（当前锁定目标）

- S3137QThetaPilotLogVolumeReadingsActual：
  - qPilotLogVolumeReading P = -|log ‖P.line.C3.q.q‖|（GREEN）
  - thetaPilotHullLogVolumeReal C3 = log ((actualC3LogShellTensorHaar C3)(actualC3LogShellTensorRegion C3)).toReal（GREEN, raw unnormalized；hull = region）
  - qThetaPilotLogVolumeComparison C3 P（PENDING）
- Mzk1Paper312StatementActual：
  - Paper312Statement C3 P := qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3
  - iff qThetaPilotLogVolumeComparison（rfl）
  - iff -|log‖q‖| ≤ log Haar(region)
  - 下游 Mzk1SignedCor312ContractActual → Mzk1Cor312S3137AssemblyActual → S3135 条件组装
- 义务表（Mzk1HolomorphicHullLogVolumeReconciliationActual，12 行）：
  - 6 discharged：S3137 raw readings、det identities、hull adjunction(interface)、final CTheta≥−1 算术、paperGap↔qTheta bridge(N3)、conditional Cor312 assembly
  - 7 missing：paper normalization (raw Haar → paper V)、paper IQ carrier 实现、(Ob3-3) 源识别、multiradial comparison、theta raw Haar vs paper normalized V（[C3 block:Q_p] 因子与 C3-vs-D 字典）、StepXIContract linkage、exact hull V 上界（V ≤ (1/4)l(log d+log f)+C0）

## 2. 历史链（已过时，不作为 P0 依据）

S779（NonzeroLabel、zero_region_subset_old_paperRootThetaHull）→ S793（paperLeastLambdaOHull、OldUnionEqualsLeastLambdaOHull:Prop）→ S800（paperPossibleImages = rootThetaImageSet = ⋃ SignedLabel 含 j=0 的旧 hull；paperHullLog 基于它）→ S801（对 S793 hull 证 paperHullLog = paperQPilotRegionLog；PaperHullLogFormulaData；paperQPilotLogPaperOrder ≤ paperHullLog）→ S868/S874/S875/S900/S909/S915/S3128 消费者。

- 旧 S800 paperHullLog 的退化：Mzk1PaperHullZeroLabelActual（DONE 22:01:09Z）证 least hull = R*O = O_hol、paperHullLog = 0、与 q 阶数无关 —— 仅作为历史记录（引用 S779/S793）。
- 旧 S801 的 equality 是 S793 hull 的 log 相等（不是 paper 的 (s−1)A ≤ V+gap）。

## 3. 旁支（本轮 P4/qVFam 工作，仍可复用但不等于 canonical 目标）

- qVFamTensorBlock 上的 paperFaithfulThetaHull = F(c_root)·O_hol（Mzk1PaperFaithfulHullActual/P4）：正性/有限性 green；与 canonical C3 log-shell tensor region 是不同的载体（qVFam vs C3 block），无已证识别。
- Mzk1PaperTargetNormalization/Unconditional、Mzk1PaperBlockTargetActual 基于旧 S800 hull：标历史/旧口径。
- Mzk1PaperCorrectedTargetActual：已改写为 canonical P0CanonicalTarget=Paper312Statement（P0Gap=qThetaPilotLogVolumeComparison）。

## 4. 使用规则

- 任何新工作引用 paper 目标时，必须用 S3137/Mzk1Paper312StatementActual 的读数；S800/S801 只能作为历史对照。
- qVFam P4 hull 结果可以用于 qVFam 载体上的独立定理，但不得当作 canonical target 的进展。
- 报告任何“paper target 无条件”前，先对照 reconciliation 的 7 missing。
