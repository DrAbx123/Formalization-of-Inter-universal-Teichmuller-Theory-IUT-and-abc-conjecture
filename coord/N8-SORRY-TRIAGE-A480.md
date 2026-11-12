# A480-A: tmp/sheaf/n8 legacy 31 个 sorry 模块修复优先级（只读 triage）

来源: dag/SORRY-AUDIT.md（n8 31 模块, 全部 olean 已编译且含 sorry）+ dag/declaration-dag.json import 边（olean 真源）统计。判定: 是否被 n8 外部模块 import = 是否进入 IUT 主链的可达路径。

## 结论（一行）

- 31 个中 **4 个被 n8 外部模块引用**（Tier1，主链可达，优先修）；6 个仅被 n8 内部高频引用（Tier2，n8 route 修复才有意义）；18 个仅少量内部引用（Tier3）；3 个零引用（Tier4，死端，建议 DAG-BLOCKED/归档）。
- 无任何 LeanFormal/IUT 主链模块直接 import n8 sorry 模块；Tier1 的外部引用均来自 tmp/sheaf/xif/paper 的 paper 层链（C3/native、P6、S2xxx 等）。故修复价值取决于 paper 层消费者链是否进入 Cor 3.12 / ABC 主链。

## Tier 1（有外部消费者；优先修）

| 模块 | sorry | 外部消费者（数量） | 修复理由 |
|---|---|---|---|
| NativeC3 | ? | 18（tmp/sheaf/xif/paper/BasePlaceQCandidateActual, tmp/sheaf/xif/paper/BaseQNormActual, tmp/sheaf/xif/paper/C3DonorFieldsFromSource, tmp/sheaf/xif/paper/NativeQNormActual） | 被 paper 层引用，修好后可把 paper 层 consumer 链闭合（C3/native 或 P6 路线） |
| P6ChainA | ? | 2（tmp/sheaf/xif/paper/S2556CorrectedPaperC9OutputActual, tmp/sheaf/xif/paper/S2557GlobalLqDonorAuditActual） | 被 paper 层引用，修好后可把 paper 层 consumer 链闭合（C3/native 或 P6 路线） |
| C3TensorConstruction | ? | 2（tmp/sheaf/xif/paper/FmodTensorLandingActual, tmp/sheaf/xif/paper/TensorUnconditionalActual） | 被 paper 层引用，修好后可把 paper 层 consumer 链闭合（C3/native 或 P6 路线） |
| SourceAllowedOutputActualAttempt | ? | 1（tmp/sheaf/xif/paper/S2561SourceAllowedMeasureIntegrationActual） | 被 paper 层引用，修好后可把 paper 层 consumer 链闭合（C3/native 或 P6 路线） |

注: 31 个模块的 sorry 数见 dag/SORRY-AUDIT.md（C3CompleteSourceReduction 3、C5Native 2、C9PaperClosure 2、N8RouteClosure 2，其余各 1）。

## Tier 2（n8 内部高频 hub；仅当 n8 route 重启时修）

| 模块 | n8 内部使用者数 |
|---|---|
| P6L | 21 |
| P6Comparison | 15 |
| C9PaperClosure | 10 |
| P6Bridge | 8 |
| SourceAlgorithmCompatibility | 7 |
| IPLFamilyData | 5 |

## Tier 3（少量内部引用；保持 CONDITIONAL/登记）

| 模块 | n8 内部使用者数 |
|---|---|
| P6ChainB | 4 |
| PaperNormalizedVolume | 4 |
| TargetSignature | 4 |
| P6RelaxedGlobalReadout | 3 |
| UnitSphereReadoutDonorActual | 3 |
| C5Native | 2 |
| N8RouteClosure | 2 |
| FiniteObservationHull | 2 |
| P6EllOutBridgeAttempt | 2 |
| P6SHEInd | 2 |
| PaperValuesBoundedReduction | 2 |
| SourcePilotApproximationIQ | 2 |
| C3CompleteSourceReduction | 1 |
| C1InfiniteUnitQuotientAttempt | 1 |
| C3SourceGaloisActionAttempt | 1 |
| C9P6Closure | 1 |
| P6IndInvarianceAttempt | 1 |
| P6SourceVolumeCarrierMapAttempt | 1 |

## Tier 4（零引用；建议 DAG-BLOCKED 归档）

| 模块 |
|---|
| C1QuotientConsumerProbe |
| C3GaloisUnitFixedAttempt |
| SourcePilotApproximation |

## 建议动作

1. P1（Tier1）：先修 NativeC3（外部 18 个消费者，C3/native q-pilot donor 链）、C3TensorConstruction（FmodTensorLanding/TensorUnconditional 消费）、P6ChainA（S2556/S2557 paper 路线）、SourceAllowedOutputActualAttempt（S2561）；每个用真实证明/已编译 tree 资产替代 sorry，不能则登记 DAG-BLOCKED。
2. P2（Tier2）：C9PaperClosure/P6L/P6Comparison/P6Bridge/SourceAlgorithmCompatibility/IPLFamilyData 等 n8 内部 hub 暂不修，等 Tier1 链路恢复后再评估。
3. P3（Tier4）：C1QuotientConsumerProbe/C3GaloisUnitFixedAttempt/SourcePilotApproximation 等零引用模块登记 DAG-BLOCKED（原因: n8 legacy route 无消费者、非 IUT 主链可达）并保留历史。
4. 不删除任何历史文件/条目。

## A480 执行更新（与 coord/DAG-BLOCKED.json 对齐）

- 核对: coord/DAG-BLOCKED.json 已有 31 条 sorries:n8-closure:* 条目（hull owner 登记的 OBSTRUCTION 原因），与本 triage 的 31 模块一一对应，无需重复登记。
- 已修复: FiniteObservationHull、IPLFamilyData（A480 真实证明），C5Native 部分修复；其余 n8 sorry 模块维持 CONDITIONAL + blocked 原因（缺 production donor / 缺 actual data package），不删历史。
- 修复优先级不变: Tier1 = NativeC3, C3TensorConstruction, P6ChainA, SourceAllowedOutputActualAttempt（有 n8 外部 paper 层消费者）；Tier2 仅在 n8 route 重启时处理；Tier4 三模块由 blocked 记录归档。
