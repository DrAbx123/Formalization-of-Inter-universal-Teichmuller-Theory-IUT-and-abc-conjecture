# SURVEY-hull-gap-search — A475 穷尽仓库搜索证据（缺口不是"数学突破"）

作者: hull (single-writer). 时间: 2026-11-11T02:5x+08:00. 只读搜索，无编译、无 watchdog 操作。
目的: 对 hull/pre-312 区域及跨区域先前标记的"缺口"做穷尽搜索，找到即适配复用；找不到则记录精确证据清单（搜索词/范围/命中）。

## 0. 搜索范围与方法
- 范围 A: `LeanFormal/` 全树（190 IUTIII + 全 IUT 树）。
- 范围 B: `tmp/`（排除 bulk `tmp/sheaf/xif/**` 12k 文件与 `tmp/external/**` 移植根；含 tmp/sheaf、tmp/n8-*、archive 目录）。
- 范围 C: `coord/`（历史文档、SKELETON、AUDIT_LEDGER、SURVEY-*）。
- 范围 D: `papers/motizuki_corpus/`（论文原文，对象记号搜索）。
- 范围 E: `.lake/packages/`（Mathlib + 依赖 lean 源）。
- 工具: ripgrep 15.2.0，`rg -l -i --max-count 1 -g '*.lean' -g '*.md' [--glob 排除]`；两轮：对象名/论文记号 + 命名变体（大小写/前缀/后缀）。
- 说明: `tmp/sheaf/xif/**` 是 paper-layer 交付区（含我们自己的 statement 文件），单独排除以免把"自己的 stub"当成 donor；这些文件在表格中作为"自有 paper-layer 证据"单列。

## 1. 第一轮命中（对象名）
| 搜索词 | 命中数 | 关键 donor（文件:声明） | 决策 |
|---|---|---|---|
| `SourceThetaPilotIQContainment`（文件名） | 1 文件 | LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean: `possibleImage_subset_sourceThetaPilotIQPacket`:126, `sourceThetaPilotProductMap_image_subset_tensorIQPacket`:141, `sourceThetaPilotIQPacket`:119, `sourceLogShellOnePlaceFamily`:76 | **复用**（已写 adapter） |
| `thetaPilot` / `ThetaPilot` | 376 文件 | 同上 + SourceLogShellXMuPacket.lean + SourceThetaPilotIQContainment | **复用**（θ-pilot IQ containment 非缺口） |
| `QPilot` / `qPilot` | 577 文件 | IUTIII/Theorem311/SourceArithmeticHolomorphicLanding.lean; SourceLogShellXMuPacket.lean; Corollary312/ArithmeticQPilot* ; TateQPilotJComparison | **复用** donor 层 |
| `SourceLogShellDatum` | 82 文件 | IUTII/Kummer/SourceLogShellCarrier.lean; SourceThetaPilotIQContainment; SourceLogShellXMuPacket; SourceLogShellIQTensorPacket | **复用**（IUTII→IUTIII link 有真实 carrier） |
| `SourceLogShellIQTensorPacket`（文件） | 1 | IUTII/Kummer/SourceLogShellIQTensorPacket.lean: `sourceLogShellIQDirectSumPacket`:113, `..._single_mem`:135, `..._pStar_inv_mul_mem`:148 | **复用** |
| `sourceSHETransport` | 40 文件 | IUTIII/Corollary312/StepXI/SourceSHETransportObligations.lean: `SourceSHESquareSupply`:165, `sheStatement_evidence`:191, `sheSlot_evidence`:197, `oneColumnTheater_arithmetic`:257 | **复用**（SHE 证据非缺口） |
| `IPLFamilyData` | 14 文件 | tmp/archive_sorry_20261028/n8/closure/AlgorithmCompatibilityProof.lean; tmp/sheaf/n8/closure/ACTUAL-IQ-STAGE1.md | **复用（归档 donor）**；tree 侧类 FPrimeStripLink/toLink 在 SourceSHETransportObligations:98 |
| `matrixLogDet` | 4 文件 | IUTIII/.../HullDeterminantLogVolumeReduction.lean: `matrixLogDet`:173, `matrixLogDet_mul_posDef`:179, `matrixLogDet_smul_posDef`:187, `matrixLogDet_kronecker_posDef`:197, `matrixLogDet_pow_posDef`:213, `packetLogVolume_tensorPower`:302 | **复用**（det tensor 定律非缺口；已写 adapter） |
| `packetLogVolume` | 37 文件 | 同上 + ABCBridge/Geometry/FinitePlaceArithmeticPacketVolume.lean + IUTII/Theta/ConcreteSourceHistoryLinkBridge.lean | **复用** |
| `stepXIContractConstruction` | 4 文件 | IUTIII/Corollary312/StepXI/Contract.lean（Obligation 定义）; tmp/sheaf/n8/closure/C9IUTBridgeProbe.lean | **复用现有 Obligation/接口**（构造内容仍在 Contract.lean:61 具名） |
| `f4b` | 65 文件 | LeanFormal/IUT/ABCBridge/Bridge/Cor312PointwiseMembershipWeakening.lean; ABCFrontierReductions.lean; ABCFrontierSingletonReduction.lean（f4b 相关 clause/reduction） | **复用**（stage4 f4b 类目标有 ABCBridge donor） |
| `placePoint` | 3 文件 | tmp/external/flt-lean P2M Sol 文件（函数名 sectionValue 系） | 不同语义；hull 侧用自有 BridgeInterface 的 placePoint 字段 |
| `sectionMap` | 38 文件 | LeanFormal/IUT/IUTI/InitialTheta/*（sectionMap 为 initial-theta 语义） | 语义不同；hull 侧自有接口已实现（Mzk1SchemeSideMapsActual） |
| `imageSet_logVolume_le_hull` | 10 文件 | SourceHullCompactnessReduction.lean:88（image⊆hull 已证）; CardAMPLThetaBoundSupply | **已证现有**（方向为 image≤hull，不是 hull≤image） |
| `hull_le_image`（严格拼写） | 0（范围 A+B，xif 排除） | —（我们自己的 Mzk1H5GapStatementActual/xif 中有 hull≤image 的 statement 记录） | 见 §3 G2 |
| `OminusInverseNormalization` | 0（范围 A+B，xif 排除） | —（仅自有 xif 文件 Mzk1H5GapStatementActual:OminusInverseNormalization） | 见 §3 G1 |
| `HullDetAssembly`/`hullDetAssembly` | 0 Lean（范围 A+B）；7 coord 文档 | coord/ENDGAME-DEPENDENCY-LEDGER.md 等；Lean 侧自有 S3182Cor312HullDetAssemblyActual（xif） | 见 §3 G4 |
| `deepOb9` | 1（tmp/survey_table.md）；0 Lean | Hull13/Hull10 paper files 在 xif 内（自有） | 见 §3 G3 |
| `Frey`/`frey` | 5934 文件 | LeanFormal/IUT/ABCBridge/Geometry/*, Arithmetic/*（Frey 条件链完整） | **复用**（mainline Frey 非缺口） |

## 2. 第二轮：命名变体
| 搜索词 | 命中 | 结果 |
|---|---|---|
| `fixedBeta` / `betaChoice` / `BetaChoice` | 8 文件（全 coord 文档） | Lean 代码中无同名 donor；仓库当前缺失（coord/FOUNDATION-FIRST-PLAN.md, IUT-PREREQ-DAG-REPORT.md 为需求记录） |
| `numMax` / `maxP` / `f4bNumMax` | 9/22/4（全 coord 文档） | Lean 代码中无同名 donor；仓库当前缺失（需求记录: coord/IUT-PREREQ-DAG-REPORT.md） |
| `ProblemD` / `DApplicability` / `applicability` | 12/7/20（全 coord 文档） | Lean 代码中无同名 donor；仓库当前缺失（需求记录: coord/SURVEY-stage4.md, IUT-PREREQ-DAG-REPORT.md）；语义上见 existing `Mzk1SchemeSideMapsActual`/bridge interfaces |
| `HTLink` | 5（coord SURVEY-abc/lattice）; `HT_link` 0 | Lean 代码中无同名 donor；theta-link 相关真实资产在 LeanFormal/IUT/IUTII/Theta/*（`ThetaLinkAssembly`, `ConcreteSourceHistoryLinkBridge`, `SourceVerticalDThetaProjection`）→ 语义复用这些 |
| `hodge.*theta.*link` | 79 文件 | LeanFormal/IUT/IUTII/Theta/* + IUTIII/Theorem311/SourceVerticalDThetaProjection → 复用 |
| `EtaleThetaKummer`（严格） | 4（coord 文档）; `KummerClass` 121 文件 | 严格名无 Lean donor；语义 donor = LeanFormal/IUT/IUTII/Kummer/*（AbsoluteKummer*, SourceLogShell*）→ 复用 |
| `schemeSide` / `sideMaps` | 8/9（coord 文档） | Lean 代码中无同名 donor；hull 侧已有 `Mzk1SchemeSideMapsActual`（自有实现）+ BridgeInterface 的 placePoint/sectionMap 字段 |
| `parallelTransport` | 26（coord 文档 + MASTER-SKELETON） | APT 语义 donor 层：IUTIII/Corollary312/StepXI/{APTConsumer? APT.lean, SourceSHETransportObligations}；tree APT.lean 为 90B stub |
| `poly.*isomorph` | 278 文件 | FPrimeStripLink/poly-isomorphism 类 donor: IUTII/Kummer/SourceLogShellXMuPacket.lean; IUTIII StepXI SourceSHETransportObligations `FPrimeStripEquiv`/`toLink` → 复用 |
| `qPilot.*precise` / `precise.*qPilot` | 8/8（coord 文档） | Lean 无同名对象；语义 donor = SourceLogShellXMuPacket（XMu packet）+ SourceThetaPilotIQContainment（ThetaPilotObject/IQ packet）→ 复用 |
| `le_imageSet` | 4 | CardHullRealEdgeNormalizationReduction.lean（sourcePointVolume_le_sourceImageVolume 等，实为点体积≤像体积）→ 部分相关，语义不同 |
| `imageSet.*le.*hull` | 28 | SourceHullCompactnessReduction:88 等（反向）→ 已证反向，非 hull≤image |
| `schemeSide` 等 | 见上 | — |

## 3. 缺口决策表（附证据；无"数学突破"表述）
| 缺口 | 搜索证据（范围/词/结果） | 决策 |
|---|---|---|
| G1 H5 O(-)^{-1} normalization on arithmetic line bundle | 范围 A+B+E（不含 xif）: `Ominus` 3 命中（coord/SURVEY-hull.md、TauCeti Spin Structure）；`OminusInverse` 1（SURVEY-hull.md）；`OminusInverseNormalization` 0 Lean donor | 仓库当前缺失独立 Lean donor（附搜索证据）；hull 侧保留自有 statement（xif）+ Named 状态，不称数学突破 |
| G2 H5 hull log-volume ≤ image log-volume | 范围 A+B: `hull_le_image` 0（xif 排除）；`imageSet_logVolume_le_hull` 10 全为反向已证；`le_imageSet` 4 为点体积≤像体积（CardHullRealEdgeNormalizationReduction） | 仓库当前缺失该方向 lean 定理；仅自有 statement；不称数学突破 |
| G3 H7/Ob9 deep two-sidedness | 范围 A+B: `deepOb9` 1 非 Lean（tmp/survey_table.md）；`Ob9` 相关 Lean 在 xif Hull08/10/12/13（自有 paper-layer）；tree Hull*: `HullEnvelopeConditionsDischarge` 等 | 仓库当前缺失"deep arbitrary-iterate both-sided"独立 Lean 证明；tree 仅有接口/条件输入（附证据）；不称数学突破 |
| G4 HDD decomposition | 范围 A+B: `HullDetAssembly`/`hullDetAssembly` 0 Lean（仅 coord 文档 7）；自有 xif S3182 条件组装 | 仓库当前缺失独立 Lean HDD 分解定理；自有 paper-layer 条件形式存在（附证据） |
| G5 det tensor additivity | `matrixLogDet` 4 文件、`matrixLogDet_mul_posDef`:179、`matrixLogDet_kronecker_posDef`:197、`matrixLogDet_pow_posDef`:213、`packetLogVolume_tensorPower`:302 | **非缺口：复用 donor**（已写 adapter Mzk1DonorReuseAdaptersActual） |
| G6 StepXI IPL/SHE/APT 内容 | SHE: SourceSHETransportObligations:165/191/197/257; IPL: tmp archive IPLFamilyData + FPrimeStripLink/toLink:98; APT: tree APT.lean stub + parallelTransport coord 文档 | SHE/IPL **有 donors（复用）**；APT tree 为 stub，仓库当前缺失独立 Lean APT 实现（附证据） |
| G7 StepXIContract construction | `stepXIContractConstruction` 4 文件：Contract.lean Obligation + tmp C9IUTBridgeProbe.lean | 仓库已有 Obligation/桥接 probe 记录；构造内容仍具名（附证据） |
| G8 IUTII→IUTIII link | `SourceLogShellDatum` 82 文件；SourceThetaPilotIQContainment/IQTensorPacket | **非缺口：真实 carrier donors 存在（复用）**；tree 中无 import 边（SKELETON GAP1）属结构问题，非理论缺失 |
| G9 θ-pilot IQ containment | SourceThetaPilotIQContainment.lean:126/141/119/76 | **非缺口：复用 donor**（已写 adapter） |
| G10 Cor312 unconditional target | 现有：T1-cor312-abc-bridge + ABCFrontier/Audit 链；unconditional assembly 仍 conditional | 仓库当前缺失"从三公理无条件"的 Lean 组装；主体条件链/接口存在（附证据）；不称数学突破 |
| 跨区域：fixedBetaChoice / f4bNumMaxStrict | 范围 A+B: 仅 coord 文档 8/4/9 命中，Lean 0 同名 | 仓库当前缺失 Lean 对象（需求记录在 coord/IUT-PREREQ-DAG-REPORT.md）；不称数学突破 |
| 跨区域：D.gap.problemDApplicability | 范围 A+B: `ProblemD` 12、`DApplicability` 7 全 coord 文档；Lean 0 同名 | 仓库当前缺失 Lean 对象（需求记录 coord/SURVEY-stage4.md）；语义相关实现：Mzk1SchemeSideMapsActual/桥接层 |
| 跨区域：HTLink / EtaleThetaKummerClass | 严格名 Lean 0；语义 donors: IUTII/Theta/* + IUTII/Kummer/*（79/121 文件） | 严格名当前缺失；**语义 donor 存在（复用）**，不称数学突破 |

## 4. 复用适配动作（本轮）
- 新增 `tmp/sheaf/xif/paper/Mzk1DonorReuseAdaptersActual.lean`（A475 adapter）：`theorem donor_* := @<donor-decl>` 复用以下 donor（不复制理论、无新 axiom）:
  - SourceThetaPilotIQContainment: possibleImage_subset_sourceThetaPilotIQPacket, sourceThetaPilotProductMap_image_subset_tensorIQPacket
  - SourceSHETransportObligations: sheStatement_evidence, sheSlot_evidence
  - ABCFrontierReductions: ABCFrontier.reduce_gapReductionInputs, abcConjecture_of_frontierGapReduced, ABCFrontier.reduce_pointwiseResidual, abcConjecture_of_frontierPointwiseReduced
  - HullDeterminantLogVolumeReduction: matrixLogDet_mul_posDef, matrixLogDet_kronecker_posDef, matrixLogDet_pow_posDef, packetLogVolume_tensorPower
- DAG: 新节点 `hull:X.DONOR.REUSE.ADAPTERS` 挂到 iut-pre-abc:ThetaPilot.carrier / Gap.thetaPilotIQContainment、iut-skeleton:SHE、iutiii STEPXI.OBLIGATIONS/HULL.DET_LOG_VOLUME、e-deep:E2.det*/E5.comparisonGaps、mainline:abc-frontier-*、T1-cor312-abc-bridge（15 条边，evidence=observed_source）。
- 未编译、未碰 watchdog；GATE NOT PASSED / binding HOLD / pins 14041；无 closure 声称。