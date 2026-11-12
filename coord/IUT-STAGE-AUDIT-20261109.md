# IUT Stage 1–5 映射与缺口审计（2026-11-09）

依据：`coord/IUT-PAPER-ROUTE.md`；`papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt`（Stage 1–5: :116–125；§4: :443–621）；原文 III Cor 3.12、IV Thm 1.10/§2；`Explicit estimates in IUTeich.txt`。本文件只审计，不新增代码/不宣称新证明。

状态口径：
- **FRESH**：源码有声明且 olean 比源码新（本审计只做 mtime 检查，未重跑 build_guard/未重查 axioms）。
- **SOURCE-ONLY**：有源码，无 olean。
- **ABSENT**：无对应源码文件/声明。
- **INTERFACE/孤岛**：命名接口/等价包装，不是论文路线 milestone（按 route §4）。

## 1. Stage 1–5 与 Lean 文件映射

| Stage | 论文内容 | 现有 Lean 文件（代表） | 状态 | 缺口 |
|---|---|---|---|---|
| 1 | [IUTchIII] Thm 3.11 ⇒ Cor 3.12；四三角形 | `MultiradialProcessionActual`, `IPLAPTActual`, `IPLAPTDataActual`, `S916PaperMultiradialSActual`, `S1204SHEOneColumnReadoutActual`, `S1215SourceSHEHDDCompatibilityActual`, `S1300HDDHullDetActual`, `S1385HDDHullDetActual`, `GlobalThetaHullVsQPilotComparisonActual` | 组件 FRESH，但论文对象多数 ABSENT/仅载体 | BPS / etHT / mlt rep / dsc / HDD / SHE / APT+IPL⇒3.11 / 3.11.5⇒3.12 均无完整箭头 |
| 2 | Thm 3.11 modulo [IUTchI–II]；log-theta lattice、log-shell、q/Θ-plots | `LogThetaLatticeActual`(SOURCE-ONLY), `PaperThetaLinkDataActual`, `OrigXiFThetaLinkActual`, `ConcreteQPilotLogIdentificationActual`, `S1297Ind3LogShellActual`, `S1303IntegralLogShellContractActual`, `S1345Ind3LogShellProcessionActual`, `GlobalThetaPilotLogVolumeActual` | 多数组件 FRESH；核心 lattice SOURCE-ONLY | log-theta lattice 未编译；Θ-link 具体模型缺 olean；Thm 3.11 整体证明 ABSENT |
| 3 | [IUTchI–II] modulo 1995–2015 结果 | `S3123FiberEquivalenceActual`, `S3123*`, `C3LogShellTensorPacketActual`, `PaperC3ThetaRootActual`, `GlobalFrobenioidPresentationActual` | host/基础组件 FRESH | 无 IUTchI–II 的定理级表述；与 Stage 4 的接口未组装 |
| 4 | 早期结果：[pGC],[GeoAn],[AbsAnb],[NCBel],[AbSc],[SemiAn],[QuCnf],[CbGC],[Config],[FrdI-II],[EtTh],[GenEll],[NodNon],[AbsTopI-III] | `GlobalFrobenioidPresentationActual`, `LGPFrobenioidPresentationActual`, `GlobalRealifiedFrobenioidActual`, `S1983EtThSignatureBridgeActual`, `S543ConditionalEtThRecipeActual`, `S3127CoverBridgeGapActual`, `S3123FiberEquivalenceActual`, `S2070AbsTopIIIAlgorithmGap` | 少量 surrogate FRESH；具名论文结果 ABSENT | [pGC]/[GeoAn]/[AbsAnb]/[NCBel]/[AbSc]/[SemiAn]/[QuCnf]/[CbGC]/[Config]/[GenEll]/[NodNon]/[AbsTop] 无具名 Lean；[FrdI-II] 仅 presentation；[EtTh] 条件/gap |
| 5 | [IUTchIV],[ExpEst] 数值/effective | `BaseQLogVolumeActual`, `DeterminantLogVolumeActual`, `GlobalQPilotNormalizedLogVolumeActual`, `Cor312ComparisonRegionV2AdditiveActual`, `S2727V2AssemblyActual` | 算术/log-volume 组件 FRESH；ExpEst ABSENT | 无 [ExpEst] 的显式常数/有效估计；V2 additive/ABC 路线是 INTERFACE，不是 Stage 5 |

## 2. Stage 1 关键对象逐项

| 对象 | 论文含义 | Lean 现状 | 缺口 |
|---|---|---|---|
| BPS | 基本 prime-strip（Θ-link 的 gluing data，F⊩▶×μ-prime-strip） | **ABSENT 具名**；只有 `FPrimeStrip`（IPLAPTDataActual）、`PrcMember/PrcTransition`（MultiradialProcessionActual）等载体 | 无 BPS species/结构，无 Θ-link 两端 BPS gluing |
| etHT | 纵向 coric 的 étale Hodge theater，多 radial 算法目标 | **ABSENT 具名**；仅有 `S2918ThetaLinkHodgeUpperAudit`、`S3087GenericSourceHodgeFamilyAttempt`（audit/attempt） | 无 etHT species、无 domain/codomain 对称性、无 radial algorithm 输出到 etHT |
| multiradial representation | BPS --mlt algo--> mlt rep | `MultiradialProcessionActual`（PrcMember/Transition/Automorphism/Ind1TensorAction）、`S916PaperMultiradialSActual`、`S1126MultiradialAuditActual` | 无“BPS → mlt rep”的实际 mutation；Procession 是载体，未与 paper BPS 连接；`S1148MultiradialCarrierAuditActual` 无 olean |
| descent (dsc) | mlt rep 经 dsc 降到 BPS+etHT | 现有 `*Descent*` 文件（22 个）多为 base-q/effective descent（Stage 2/NF），不是 Stage 1 dsc | 无 Stage 1 dsc 箭头；需区分 dsc 与 base-q descent |
| hull+det (HDD) | hull+det∘dsc，给 mlt rep+hull+det | `S1204SHEOneColumnReadoutActual`, `S1215SourceSHEHDDCompatibilityActual`, `S1300HDDHullDetActual`, `S1305HDDLatticeFromHullDetExact`, `S1356HDDHullDetSourceActual`, `S1385HDDHullDetActual`, `S1418HDDConsumerActual` FRESH；`S1268HDDLatticeActual` NO_OLEAN | 组件存在，但未与 dsc 组合成 HDD 箭头；S1268 未编译 |
| APT | algorithmic parallel transport | `IPLAPTActual`（`APTActualEvidence`, `toTransport`）、`APTComparisonFromSource`、`S2566CanonicalMapTransportActual` | 只有 evidence/transport 结构，无定理“APT ⇒ 2nd/3rd triangle” |
| IPL | input prime-strip link | `IPLAPTActual`（`IPLActual`, `ipl_compatibility`）、`IPLAPTDataActual`（`selfIplActual`, `selfIplActual_factorization`）、`ThetaLinkIPLFactorizationActual` | 有 factorization/兼容性，但未与其他 triangle 的输入输出组装 |
| SHE | simultaneous holomorphic expressibility | `S1204SHEOneColumnReadoutActual`（oneColumnLogReadout/theta/positivePacket）、`S1215SourceSHEHDDCompatibilityActual`、`S1275SHEDDNonLatticeFieldsActual` | 仅 one-column readout；无 q-pilot/Θ-pilot simultaneous comparison 的共同 ring/SHE 箭头 |
| 4th triangle / 3.11.5⇒3.12 | q-pilot 与 Θ-pilot simultaneous comparison | `GlobalThetaHullVsQPilotComparisonActual`（`qPilotThetaHullComparison: Prop`, `GlobalComparisonCondition`, `GlobalHullQPilotComparisonData`）、`ConcreteQPilotLogIdentificationActual` | comparison 是条件/数据假设，不是由 (HDD)∘(SHE) 推出的定理 |
| Cor 3.12 | −|log(Θ)| ≥ −|log(q)| | `S1000FinalCor312AssemblyActual` 等旧 assembly；`S2817ClauseDFActual`/`S2823ClauseDEFActual`/V2 additive 文件为 scaffold/interface | 无 paper-level Cor 3.12 证明；V2 additive/ABCFrontier 按 route §4 是 INTERFACE，不是 milestone |

## 3. Stage 2–5 缺口（重点）

- Stage 2：`LogThetaLatticeActual` 有源码但无 olean（SOURCE-ONLY），这是 IUTchI–II 的 core；`ConcreteThetaLinkActual` 无 olean；`S1346StageLogShellMapActual` 无 olean。Thm 3.11 的整体证明 ABSENT。
- Stage 3：无 IUTchI–II 定理级对象；只有 `S3123` fiber equivalence、`C3` theta packet、Frobenioid presentation 等基础设施，未组装成 Stage 3。
- Stage 4：[pGC]/[GeoAn]/[AbsAnb]/[NCBel]/[AbSc]/[SemiAn]/[QuCnf]/[CbGC]/[Config]/[GenEll]/[NodNon]/[AbsTop] 全部 ABSENT 具名；[FrdI-II] 只有 presentation（`GlobalFrobenioidPresentationActual` 等）；[EtTh] 只有条件 recipe/gap（`S543ConditionalEtThRecipeActual` 等）。
- Stage 5：无 [ExpEst] 显式估计；log-volume 组件存在，但不构成 Stage 5 numerical/effective 证明。

## 4. 孤岛/接口（不得当主线）

- `ABCFrontier`、`Cor312ToABCBridgeInterface`、`FrontierHeightComparisonClause`、`FrontierRegionComparisonClause`、`cor312Gap1_*`、`cor312Gap2_*`：route §4 明令禁止当路线。
- `Cor312ComparisonRegionV2AdditiveActual`、`S2727V2AssemblyActual`、`S2727ABCConjectureOfActualInputs`：等价/命名接口，不是 Stage 1–5 对象；只能作为下游孤岛。
- `S2918ThetaLinkHodgeUpperAudit`、`S3087GenericSourceHodgeFamilyAttempt`：audit/attempt，不是 etHT。
- `S3127CoverBridgeGapActual`、`S3123...`、S3128 OfH/fiber 基础设施：Stage 4 anabelian/Frobenioid host，不是 Stage 1；且 route §5 明确指出“需接 fiber functor/etHT/BPS”。
- `S2070AbsTopIIIAlgorithmGap`：gap audit，不是 [AbsTopIII]。

## 5. 优先缺口（审计结论）

1. BPS/etHT 具名结构缺失：Stage 1 的四三角形没有 paper-level 输入对象。
2. multiradial algorithm（BPS→mlt rep）缺实际 mutation；只有 Procession 载体。
3. dsc 箭头缺失；现有 descent 文件服务 Stage 2/base-q，不能代替。
4. APT/IPL 只有 evidence/factorization；缺 `Thm 3.11: (dsc) APT+IPL ⇒ 1st/2nd/3rd triangle` 的定理。
5. hull+det 组件 FRESH，但未与 dsc 组装；S1268 HDD lattice NO_OLEAN。
6. SHE 只有 one-column readout；缺 q-pilot/Θ-pilot 的 simultaneous holomorphic expressibility。
7. 3.11.5⇒3.12 的 comparison 是条件/接口；缺由 (HDD)∘(SHE) 推出 q/Θ comparison。
8. Stage 2 log-theta lattice SOURCE-ONLY；ConcreteThetaLink/S1346 无 olean。
9. Stage 4 具名输入几乎全缺；Frobenioid 仅 presentation，EtTh 仅条件 recipe。
10. Stage 5 无 ExpEst；V2 additive/ABC 为孤岛。

## 6. 审计边界

- 本审计只读 route/report/原文与源码/olean mtime；未重跑 build_guard，未重查 axioms，故 FRESH 仅表示“源码后有新 olean”，不是 kernel_closed 重证。
- 未运行全 Project 构建；未宣称任何新证明完成。
