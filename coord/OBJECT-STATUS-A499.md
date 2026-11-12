# OBJECT-STATUS-A499 — 3.11.5⇒3.12 对象总表（对象 1–12 × 状态 × file:decl）+ 构造 gate

generated: 2026-11-11 05:41 (lattice，只读盘点)

来源: `coord/OBJECTS-3115-312-A498.md`（对象清单）、`coord/COR312-STATEMENT-AUDIT.md`（忠实命题草案）、`coord/VACUITY-AUDIT-A497.md`（空转裁决）。

## 0) Gate（写死）

**每个对象必须有一个 `_constructed` 定理（对象从真实数据定义、非参数传入、非接口占位）后，其上层接线文件才能计入进度。** 当前扫描: 仓库中不存在对象级 `*_constructed` 定理（`cor312_of_constructed_stepXI` 等只是 contract 消费，不是对象构造）；因此 **对象 1–12 全部未过 gate**，所有上层 wiring（qTheta/step3115/R4/endgame/QThetaAlign 等）**不得计入进度**，直到对应对象 `_constructed` 定理出现。

## 1) 对象总表

| # | 对象（A498 清单） | 状态 | file:decl（证据） | `_constructed` 定理 | 上层 wiring（受 gate 约束） |
|---|---|---|---|---|---|
| 1 | BPS（value/pilot 两条：q-pilot 与 Θ-pilot；value monoid、pilot、Θ-link） | **接口 + 部分真实构造** | `LeanFormal/IUT/IUTII/Frobenioid/PrimeStripsConstruction.lean:46 FPrimeStrip`, `:65 FPrimeStripLink`（BPS link 结构；abstract W/V）；`tmp/sheaf/xif/paper/QPilotZeroLocusDivisorActual.lean:55 qVFamily`（实际 q_V family）；`tmp/sheaf/xif/paper/Mzk1QPilotSHEDoubleImageActual.lean:65 rootExtensionProductThetaImage`（实际 θ 像） | **无** | Step3115/Wiring、QThetaAlign、R4 消费链 |
| 2 | multiradial algorithm（Steps 1–9：多radial 环境、indeterminacy 兼容、Kummer 类标） | **接口/缺失** | `LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithm.lean:5 def multiradialAlgorithm : Obligation`；`SourceFiniteMultiradial.lean:20 core`, `:95 profile`（模型 kernel，不是算法构造） | **无** | Step3115Comparison（qTheta 填充）→ R4 |
| 3 | mlt representation（Hodge theater D-Θ±ellNF、log-shell、tensor packets、q/Θ pilots、log-volumes） | **接口 + 部分真实** | `LeanFormal/IUT/IUTIII/Theorem311/SourceHodgeTheaterBridge.lean:40 SourceHodgeTheaterSystem`（接口）；`LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean:86 SourceLogShellDatum`（真实 log-shell 定义）；`HolomorphicHull/Volume.lean:23 PositivePacket`, `:27 packetDet`, `:32 packetLogVolume`（真实有限 packet/log-vol）；`GlobalQPilotProcessionLogVolumeActual.*`（候选 q-pilot 全局） | **无** | R4LiteralAssembly/Endgame（literal IQ 接口 + hcomp） |
| 4 | D-scaling `dsc` + Ind1/2/3 indeterminacies | **接口/模型** | `LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean:96 Ind1Setoid`, `:104 ind1QuotientMap`；`Ind2Reduction.lean:69 Ind2AlienLink`, `:128 secondLinkDescent`；`LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean:140 nonarchimedeanImageInclusion`, `:194 archimedeanTargetLift`（抽象 Label/Choice，不是 paper 的 scheme-theoretic procession） | **无** | FourTriangleSynthesis.dsc 字段、Step3115 |
| 5 | etHT（étale theta/Kummer 类、Gauss 指数、2ℓ-th roots） | **部分真实构造 + 接口** | `LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean:23 gaussExponent`（真实 j²）；`tmp/sheaf/xif/paper/S1929LiteralIQCarrierActual.lean`（literal completion IQ）；`Mzk1QPilotSHEDoubleImageActual.lean:89 SHEArrowStatement`（2ℓ-th root 关系，已证）；Hodge theater étale 部分仍是 `SourceHodgeTheaterSystem` 接口 | **无** | QThetaAlign/SHE 槽、R4 |
| 6 | 0-column、etHT 传输（SourceProcession/AdjacentColumn 等） | **接口/缺失** | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteSourceColumnTrunkBridge.lean: sourceColumnCarrierIdentification`（接口式识别）；`SourceProcessionStepXI.lean` / `SourceAdjacentColumnProcessionIsomorphism.lean` 存在但无实际 0-column 构造（此前无 olean） | **无** | Step3115/R4 的 dsc/SHE 组合 |
| 7 | hull（least region a·O、packet hull、archimedean hull） | **部分真实构造 + 接口** | `tmp/sheaf/xif/paper/Mzk1LiteralIQCarrierActual.lean:38 literalHull`, `:33 literalUnitRegion`；`A483bLiteralCarrierProductHaarActual.lean:27 litUnitRegion`, `:36 litHaar`；`Mzk1LiteralIQHullFinitenessActual.lean:51 literalGlobalIQHull_measure_lt_top`, `:64 literalGlobalIQHull_logVolume_lt_top`（literal hull 有限性）；paper 的 holomorphic hull 仍由 `HullDeterminantLogVolumeReduction` 的 hull system 接口承载 | **无** | HullDetStep3115/HullDetFourTriangle、R4/endgame 的 hull finiteness |
| 8 | det（2ℓ 次根归一化、det 线、log 体积归一化） | **真实构造（有限 packet 层）+ 接口（paper det line）** | `HolomorphicHull/Volume.lean:27 packetDet`, `:32 packetLogVolume`, `:123 packetLogVolume_rescale`；`HullDeterminantLogVolumeReduction.lean:173 matrixLogDet` + frozen spec laws；`S3137ThetaHullVolumeScalingActual.lean:70 thetaPilotHullLogVolumeReal_eq_actualRegion`（实际 C3 Haar log-volume） | **无** | det 读法、HullDet、R4 comparison |
| 9 | Holomorphic hull（复解析 hull） | **部分真实构造 + 接口** | `S3137ThetaHullVolumeScalingActual.lean` 的 `thetaPilotHull`/`thetaPilotHullLogVolumeReal`（实际 C3 tensor log-shell region + Haar log-volume）；`AbsTopIII09ThetaHullScalingActual.lean:52+` theta hull scaling；但 paper 的复解析 holomorphic hull 本身未构造（只有 C3 region 模型） | **无** | S3137/Cor312 comparison、object 12 |
| 10 | HDD decomposition（hull/det 分解读法） | **接口/模型** | `tmp/sheaf/xif/paper/Mzk1FourTriangleSharedActual.lean:15 HDDDecomp`, `:22 HDD`, `:31 fourTriangleReadout`, `:38 FourTriangleSynthesis`（泛型结构）；`Mzk1HullDetStep3115Actual.lean:57 hullDetHDD`（具体 hull/det 读法但 `HullDetState` 是抽象输入） | **无** | R4LiteralAssembly/Endgame、HullDetFourTriangle、QThetaAlign |
| 11 | SHE（Hodge theater transport / 全纯 transport） | **部分真实构造 + 接口** | `Mzk1QPilotSHEDoubleImageActual.lean:89 SHEArrowStatement`, `:95 sheArrowStatement_proved`（literal carrier 上的 2ℓ-th root simultaneity，已证）；Hodge theater transport 本体未构造（`SourceHETransportObligations` 接口） | **无** | Step3115/R4 的 she 槽 |
| 12 | q/Θ-pilot 的 hull log-volume 比较 → Cor 3.12 | **缺失 + 接口（named same-C）** | `S3137ThetaHullVolumeScalingActual.lean qThetaPilotLogVolumeComparison`（定义）+ `S3137NativeToC3SameCReadoutActual.lean:76 qThetaPilotLogVolumeComparison_of_nativeIdentification`（依赖 unconstructed `NativeToC3SameCReadoutIdentification`）；`GlobalThetaPilotLogVolumeActual.lean:75 thetaValueFromQ`, `:106 globalThetaPilotLogVolume`（q^{j²} 候选公式）；**qTheta 链已 VOID** | **无** | Step3115Comparison/Wiring、R4/endgame 的 Cor312 分量 |

## 2) 状态统计（按 12 对象）

- **真实构造（完整）: 0/12**。
- **接口 + 部分真实构造: 1,3,5,7,8,9,11（7 个）**。
- **接口/模型: 2,4,10（3 个）**。
- **接口/缺失: 6（1 个）**。
- **缺失 + named 接口: 12（1 个）**。
- **`_constructed` 定理: 0/12**（对象级）。

## 3) Gate 影响（上层 wiring 不得计进度）

| 对象（未过 gate） | 受影响 wiring（不得计入 3.12 进度） |
|---|---|
| 1–5,7–12（全部） | `Mzk1QPilotR4Stage5AlignActual`（qTheta 链已 VOID）、`Mzk1Step3115ComparisonActual`、`Mzk1Step3115WiringActual`、`Mzk1QThetaHullDetAlignActual`、`Mzk1HullDetFourTriangleActual`、`Mzk1R4LiteralAssemblyActual` 的 Cor312 分量、`Mzk1R4EndgameCompositionActual` 的 Cor312 分量（ABC 分量仍条件于 hcomp） |

注: `Mzk1HullDetStep3115Actual` 的 hull/det 数值比较、`R4LiteralAssembly`/`R4Endgame` 的 conditional 结构、`ExplicitABC⇒ABCConjecture` 等**作为候选组件**可保留；但在对象 `_constructed` 定理出现前，不能宣称 3.11.5⇒3.12 或 Cor 3.12 进度。

## 4) 下一步（对象优先）

1. 为对象 1–12 各写一个 `_constructed` 定理：从真实数据定义对象（非参数传入/接口占位），并给出构造证据。
2. 优先缺少真实构造的对象: 2（multiradial algorithm）、4（dsc/Ind）、6（0-column transport）、10（HDD decomposition 的 paper 对象）、12（独立 Θ-pilot readout + hull comparison）。
3. 对象 12 建议使用 `S3137` 的 `thetaPilotHull`/`thetaPilotHullLogVolumeReal`（实际 C3 Haar log-volume）+ `GlobalThetaPilotLogVolumeActual` 的 q^{j²} 候选，明确 named same-C 缺口；qTheta 链保持 VOID。
4. 只有对象 `_constructed` 后，才允许重写四三角合成与 3.11.5⇒3.12 比较（wiring 后行）。
