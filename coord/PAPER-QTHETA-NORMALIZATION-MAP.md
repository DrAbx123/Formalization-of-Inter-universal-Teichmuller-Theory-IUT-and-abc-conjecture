# PAPER-QTHETA-NORMALIZATION-MAP — q/theta 两读数的精确定义与 normalization 对应

日期：2026-11-14；hull lane（只读定位，不改旧读数定义）。

## 0. 结论先行

1. S3137 的 raw q/theta 读数是 **raw Haar / raw q norm**，不是 paper 3.12 的 procession-normalized 读数。
2. Paper 3.12 的 q/theta 两读数应使用 `BadPlaceProcessionNormalizedComparisonActual` 中的
   `processionNormalizedQPilotLog` / `processionNormalizedThetaLog`；该文件已经证明 signed 形式
   `-processionNormalizedQPilotLog ≤ -processionNormalizedThetaLog`。
3. `s1915ClosedForm` 的 `+1` 来自 **S1902 归一化 `exp 1 / μ(unitBall)`**（S1915 文件头 :59），
   是 S1902 normalized hull log-volume 的 additive constant；`s1915A0 = max 0 s1915ClosedForm`
   （ENNReal clipping），不是 paper 3.12 的负 theta 读数。
4. `paperNetSlack` 的 `Σ(d_b-1)(-log r_b) ≤ 1` 是 raw s1915ClosedForm 比较的数值条件，
   不是 paper 3.12 的正确形态；**暂停该路线**。

## 1. Raw S3137 读数

### q 侧
- 文件：`tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean:77-90`
- 定义：
  ```lean
  noncomputable def qPilotLogVolumeReading (P : PaperQPilotObject ...) : ℝ :=
    -|Real.log (‖P.line.C3.q.q‖)|
  ```
- 定理 `qPilotLogVolumeReading_eq_neg_abs_qParameter`（:82-85）：等于 `-|log (‖C3.q.q‖)|`。
- 性质 `qPilotLogVolumeReading_nonpos`（:88-90）：`≤ 0`。
- 注意：`P.line.C3 : SourcePilotRegionData` 是空类型（S1429），该 raw 读数的实际构造是 vacuous；**不能作为 paper 3.12 的 q 侧实际对象**。

### theta 侧
- 文件：`S3137QThetaPilotLogVolumeReadingsActual.lean:128-135`
- 定义：
  ```lean
  noncomputable def thetaPilotHullLogVolumeReal (C3) : ℝ :=
    (haarLogVolume (thetaPilotHullHaar C3) (thetaPilotHull C3)).toReal
  ```
- 定理 `thetaPilotHullLogVolumeReal_eq_regionLogVolume`：等于 raw Haar log-volume（不是归一化、不是负值）。

## 2. Paper-faithful procession-normalized 读数（已有 GREEN）

文件：`tmp/sheaf/xif/paper/BadPlaceProcessionNormalizedComparisonActual.lean`

- `processionNormalizedQPilotLog`（:55-59）：
  ```lean
  ∑ b, nativeBadLocalWeight T b *
    (qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : ℝ))
  ```
- `processionNormalizedThetaLog`（:62-66）：同一 c_norm，额外 `/ (2*l.value)`：
  ```lean
  ∑ b, nativeBadLocalWeight T b *
    ((qVFamNormalizedCoefficient T b / (2*l.value)) * Real.log (qVFamTensorP T b))
  ```
- 恒等：
  - `processionNormalizedQPilotLog_eq_actual : = actualQPilotMagnitudeClassical`（:69-71）
  - `processionNormalizedThetaLog_eq_s13 : = s13ThetaCoefficientSum`（:73-74）
- **比较定理**：
  - `processionNormalizedComparison : ThetaLog ≤ QPilotLog`（:77-92）
  - `processionNormalizedComparison_signed : -QPilotLog ≤ -ThetaLog`（:94-96）
    —— 这就是 paper 3.12 的 `-|log q| ≤ -|log Θ|` 方向。
- `ProcessionNormalizedTarget` / `processionNormalizedTarget_actual`（:115-123）。

## 3. `s1915ClosedForm` 的 `+1` 从哪来

- 文件：`S1915ThetaHullA0Actual.lean`
  - `s1915A0 := (s1902LogVolume T (s1902Hull T)).toReal`（:120-121）
  - `s1915ClosedForm := 1 + ∑ b d_b log r_b`（:134-136）
  - `s1915_a0_eq_max : s1915A0 = max 0 s1915ClosedForm`（:335-336）
- 文件头 `:59` 明说：`+1` 来自 **S1902 normalization `exp 1 / μ(O).toReal`**（additive constant），
  不是 paper 3.12 的负 theta。r_b≤1 使 `s1915ClosedForm≤1`；ENNReal clipping 使 a0=0（负时），
  故 `a0` 不是 paper theta 的负读数。

## 4. 正确 #1 目标

- **不要把 raw `nativeThetaReadout`（单因子 tensor raw Haar）当 paper theta**；
- **不要用 `s1915ClosedForm` 的 slack 条件**；
- 正确 paper 3.12 形态已经是 GREEN：
  ```text
  processionNormalizedThetaLog ≤ processionNormalizedQPilotLog
  -processionNormalizedQPilotLog ≤ -processionNormalizedThetaLog
  ```
- 若必须与 S3137/S1902 具体对象连接，需要单独建立
  `actualQPilotMagnitudeClassical` ↔ `qPilotLogVolumeReading` 和
  `s13ThetaCoefficientSum` ↔ theta normalized hull 的等式；但 S3137 的 `P.line.C3` 空类型使 raw 侧不可用，
  因此应使用 procession-normalized pair 作为 paper 3.12 的实际读数。

## 5. 待办

1. 在 `BadPlaceProcessionNormalizedComparisonActual` 已 GREEN 基础上，为 #1 写一个 `Paper312Comparison` 消费者接口（不重新证明）；
2. 明确 `nativeQReadout` 与 `processionNormalizedQPilotLog` 的定义差（raw local vs procession-weighted global），不再混用；
3. 若需 paper 3.12 的 raw `-|log q|` 与 `-|log Θ|`，需要新的实际 q/Θ 对象；旧 C3 raw 读数 vacuous，不能使用。
