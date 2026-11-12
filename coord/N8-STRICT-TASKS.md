# N8 strict stage3 task records (SHEAF template)

Reduced fields per coord/TASK_TEMPLATE.md; one leaf one owner.

## S3-C0 / N8-C0 / owner primespine

- 目标节点 / SHEAF 阶段：n8-c0-target-signature / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C0Base.lean / C0-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：C0 N8TargetOutput actual base: place, realization, hull_finite, hull_positive, qPilot_mem_hull, q_le_theta
- 实际消费者：C10 base
- statement_dependencies：C1 SourceInputBinding; SourceTheorem311Realization production constructor; sourceHullVolume positivity/finite donors; sourceThetaPilotPoint_mem_sourceHolomorphicHull
- proof_dependencies：C1 SourceInputBinding; SourceTheorem311Realization production constructor; sourceHullVolume positivity/finite donors; sourceThetaPilotPoint_mem_sourceHolomorphicHull
- 自然语言证明：先审计四字段对任意 OriginalInput 是否真；若需原文条件，写反例并修正 C0；否则用 production donors 构造 place/realization/hull 字段。
- 可复用 Mathlib / 项目供体：SourceRealizationLifting.realization; SourceProcessionFromContract.sourceTheorem311RealizationOfDefinition31Data; sourceThetaPilotPoint_mem_sourceHolomorphicHull; sourceHullVolume finite/positive lemmas
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C0 零 sorry 或 exact false counterexample + corrected target
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-C1 / N8-C1 / owner qside

- 目标节点 / SHEAF 阶段：n8-c1-source-input-binding / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C1Actual.lean / C1-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual SourceInputBinding: SourcePlaceRealization placeEquiv/selected/selected_realization/fiberMonEquiv
- 实际消费者：C2/C3/C7
- statement_dependencies：OriginalInput; NumberFieldPlaceIndex; finitePlaceValueGroup/archimedeanValueGroup; A1 selected/R donors
- proof_dependencies：OriginalInput; NumberFieldPlaceIndex; finitePlaceValueGroup/archimedeanValueGroup; A1 selected/R donors
- 自然语言证明：construct actual place equivalence and selected R/fiber monoid equiv; no arbitrary Equiv
- 可复用 Mathlib / 项目供体：SourceInputBinding fields/donors; NumberFieldPlaceIndex
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C1 零 sorry 或 exact missing donor
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-C2 / N8-C2 / owner logdescent

- 目标节点 / SHEAF 阶段：n8-c2-source-log-kummer / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C2Actual.lean / C2-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual SourceLogKummerData: local log, torsion kernel, logShell/preLogShell, G_v/Kummer/K1K2
- 实际消费者：C4/C5/C9
- statement_dependencies：SourceInputBinding C1; sourceLocalLogShellDatum; IntegralUnitLogarithmKernel
- proof_dependencies：SourceInputBinding C1; sourceLocalLogShellDatum; IntegralUnitLogarithmKernel
- 自然语言证明：use production local log datum; prove kernel/logShell equalities; retain K1K2 as named subgaps if missing
- 可复用 Mathlib / 项目供体：sourceLocalLogShellDatum; sourceLocalLogShell
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C2 zero sorry or exact subgaps
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-C3 / N8-C3 / owner kummer

- 目标节点 / SHEAF 阶段：n8-c3-source-pilot-region / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C3Actual.lean / C3-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual SourcePilotRegionData: q completion, thetaPacket, qUnit, roots/rootChange, tensorPlaces/tensorTuple/tensorUnit/tensorLanding/q
- 实际消费者：C4/C7
- statement_dependencies：FiniteThetaPacket; FinitePlaceQCandidate; ArithmeticTensorTupleBlock; C1
- proof_dependencies：FiniteThetaPacket; FinitePlaceQCandidate; ArithmeticTensorTupleBlock; C1
- 自然语言证明：build q completion and theta packet from source; construct tensor landing; no Real q proxy
- 可复用 Mathlib / 项目供体：FinitePlaceQCandidate; FiniteThetaPacket; tensorLanding
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C3 zero sorry or exact donor gap
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-C5 / N8-C5 / owner iplsheapt

- 目标节点 / SHEAF 阶段：n8-c5-algorithm-compatibility / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C5Actual.lean / C5-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual SourceAlgorithmCompatibilityData: IPLFamilyData, SHE, APT, permitted/pilot
- 实际消费者：C7/C10
- statement_dependencies：IPLFamilyData T10; SourceSHETransportLaws; APT; C4
- proof_dependencies：IPLFamilyData T10; SourceSHETransportLaws; APT; C4
- 自然语言证明：construct actual shared algorithm instance; SHE square/APT transport; permitted family
- 可复用 Mathlib / 项目供体：SourceSHETransportLaws; APT; T10 IPLFamilyData
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C5 zero sorry or exact donor gaps
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-C7 / N8-C7 / owner volumedet

- 目标节点 / SHEAF 阶段：n8-c7-holomorphic-hull / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C7Actual.lean / C7-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual SourceHolomorphicHullData (T) (n): theta image containment, hull log-volume positive, qPilot=tensorUnit membership
- 实际消费者：C8/C9
- statement_dependencies：C6ActualIQData.actual; T11; C5 permitted
- proof_dependencies：C6ActualIQData.actual; T11; C5 permitted
- 自然语言证明：prove image containment via T11/TensorLanding; prove log-volume positivity from measure positivity; prove tensorUnit membership
- 可复用 Mathlib / 项目供体：arithmeticTupleCanonicalHull; IQHullLogVolumeInterface; sourceThetaPilotPoint_mem_sourceHolomorphicHull analogues
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C7 zero sorry or exact missing donors
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-C9 / N8-C9 / owner transport

- 目标节点 / SHEAF 阶段：n8-c9-pilot-approximation-iq / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/C9Actual.lean / C9-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual q approximation: sourceQ=-log||C3.q||, donor identity to C8 signed hull, Values bounded/approx
- 实际消费者：C10
- statement_dependencies：C8 actual theorem; C7; C3 q
- proof_dependencies：C8 actual theorem; C7; C3 q
- 自然语言证明：construct actual q Real; prove donor identity; derive bounded/epsilon
- 可复用 Mathlib / 项目供体：SourceQRealReadout; C8 actual; qPilotPoint
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：C9 zero sorry or exact donor gap
- 停止边界：leaf returns proof or exact missing donor; no proxy

## S3-T11 / N8-T11 / owner multiradial

- 目标节点 / SHEAF 阶段：n8-t11-theta-to-iq / stage3 (stage1-2 audit)
- 集成负责人 / 构建负责人：lead / lead
- 文件：tmp/sheaf/n8/closure/T11Actual.lean / T11-STAGE3.md
- 共享接口与冲突：freeze current stage2 files; leaf may add proof file only
- 数学目标：actual Real theta -> completion map and C4 value-monoid -> IQ alignment
- 实际消费者：C7/C8/C9
- statement_dependencies：C3 qUnit/thetaPacket; C6 IQ carrier; C4 SourceImageRealization
- proof_dependencies：C3 qUnit/thetaPacket; C6 IQ carrier; C4 SourceImageRealization
- 自然语言证明：construct thetaCompletion from actual qUnit/thetaPacket; prove thetaScale compat; C4 alignment or no-go
- 可复用 Mathlib / 项目供体：ThetaValueCompletion; C3 qUnit; C4 SourceImageRealization
- 本包自主决定：proof body / equal-strength local API repair
- 不能暗改：final objects/quantifiers/hypotheses/conclusions; target semantics; other owners' files
- 验收：T11 zero sorry or exact no-go
- 停止边界：leaf returns proof or exact missing donor; no proxy
