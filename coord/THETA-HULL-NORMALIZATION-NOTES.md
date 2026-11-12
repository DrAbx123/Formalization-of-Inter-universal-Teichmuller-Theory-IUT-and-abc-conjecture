# THETA-HULL NORMALIZATION — 给 hull 的一页说明（A498）

日期: 2026-11-11。范围: tmp/sheaf/xif/paper 既有 theta hull / θ-pilot log-volume 资产（只读整理，不改代码）。
背景: A497 已判定 `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage := qPilotLogImage/(2*l.value)` 是空转定义（q<theta 只是负数除法恒等式）；以下全部是**不依赖 q/(2l)** 的真实 theta 侧资产与归一化约定。

## 1. 真实 Theta-hull readout（定义链）

- `S3137ThetaHullVolumeScalingActual.lean:70`
  `thetaPilotHullLogVolumeReal_eq_actualRegion : thetaPilotHullLogVolumeReal C3 = log Haar(actualC3LogShellTensorRegion C3)`
- `AbsTopIII09ThetaHullScalingActual.lean:62` 同式（`absTopIII_thetaPilotHullLogVolumeReal_eq_actualRegion`）。
- 即：Theta-hull 的 log-volume = **actual tensor log-shell region 的 Haar 测度之 log**，不是 q 的派生量。
- `S3137QThetaPilotLogVolumeReadingsActual.lean:102/106/115/122`：`thetaPilotHull_eq_region`、`thetaPilotHull_compact`、`thetaPilotHullLogVolume_eq_regionLogVolume`、`thetaPilotHullLogVolume_ne_top`（紧性 + 有限性）。

## 2. 归一化/缩放律（Theta 侧 p_v-adic）

- `S3137ThetaHullVolumeScalingActual.lean:59`
  `thetaPilotHull_log_measure_prime_smul (hpos) : log Haar(p_v • thetaPilotHull) = -(c3TensorBlockDimension C3 : ℝ) * log p_v + thetaPilotHullLogVolumeReal C3`
  （AbsTopIII09:52 的同名 re-export；符号为负、乘维数因子 dim，不除以 2l）
- `S3137C3LogShellPacketNormalizedLogVolumeActual.lean`：
  - `:64` `c3Tensor_measure_prime_smul`；`:75` `c3Tensor_log_measure_prime_smul`
  - `:95` `c3PacketNormalizedLogVolume_prime_smul`；`:126` `c3TensorRegion_packetNormalizedLogVolume_prime_smul`
  - 归一化体积在 p_v-缩放下的线性律（packet-normalized 版本）
- `GlobalThetaPilotLogVolumeActual.lean:99/105/150`：
  `localThetaLogVolume` = (gaussExponentSum / card(SignedLabel)) * baseQLogMagnitude 的卷积形式；`globalThetaPilotLogVolume = Σ_b localThetaLogVolume T b`；
  `globalThetaPilotLogVolume_eq` 给出 procession-normalized 公式（card 分母来自 SignedLabel 平均，不是 2l）
- `GlobalPositiveThetaHullLogVolumeActual.lean:42` `thetaPositiveLogVolumeAt`：逐 vertex 的 theta positive log-volume（hull 型）

## 3. q vs theta 的比较（obligation 形式，非定义式）

- `S3137QThetaPilotLogVolumeReadingsActual.lean:145/149` `qThetaPilotLogVolumeComparison` / `_iff`：把 q-pilot reading 与 theta hull log-volume 的比较写成 obligation（含 `qPilotLogVolumeReading_eq_neg_abs_qParameter` :82）。
- `S3137ThetaHullVolumeScalingActual.lean:79` `qThetaPilotLogVolumeComparison_iff_actualRegion`：obligation ↔ actual-region 读数。
- 结论：Cor 3.12 的比较内容是**真实读数间的 obligation**，不是把 theta 定义为 q/(2l) 后的恒等式。

## 4. 禁止项（hull 使用注意）

- 禁止把 `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage`/`qThetaReadout`/`qThetaStepXIContract` 当 3.12 证据（A497）。
- 禁止把 `Mzk1QPilotActual.thetaPilotLogVolume : ℚ` / `qPilotLogVolume` 结构字段的 `comparison` 当证据（结构字段是假设，不是证明）。
- Theta-hull 归一化以 **Haar 测度 + dim(c3TensorBlockDimension) 缩放律**为准；Θ 侧不出现 `/(2l)` 除子。

## 5. 与 stage4 C/D 区关系

f4b/f5 链（`NestedInduction/PaperScopeLemma24/F0StepGeometry/StepProviderPrime/CVCompositionF/P1FinitePart/F0StepTransportProved/Assembly3`）对上述 theta/q 符号 grep **0 命中**（A497 审计），完全独立；本说明仅供 hull 组装 theta hull/Cor 3.12 读数。
