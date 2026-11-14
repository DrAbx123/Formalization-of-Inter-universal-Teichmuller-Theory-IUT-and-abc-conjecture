# L 侧 normalized/product readout canonicality 审计（只读）

日期：2026-11-14；hull lane。状态：官方编译待确认（`Mzk1P0LNormReadoutActual`/`Mzk1P0LNormReadoutProductActual` 当前无 olean，已入 WL）。

## 1. 两层 readout

### raw tensor readout（非 canonical）
文件：`Mzk1P0LThetaMeasureReadActual.lean:14-21`
- `thetaReadActual I place = Real.log (actualC3LogShellTensorHaarL region).toReal`（rfl）；
- `actualC3LogShellTensorHaarL = Measure.addHaar`（raw additive Haar）；
- 因此 raw theta 读数只确定到任意 additive constant。

### canonical normalized tensor readout
文件：`Mzk1P0LNormReadoutActual.lean`
- `actualUnitBallL := {x | ∀i, ‖x i‖ ≤ 1}`；
- `actualUnitMassL := (haar actualUnitBallL).toReal`；
- **`thetaNormReadL := actualC3LogShellTensorLogVolumeL − Real.log actualUnitMassL`**；
- `thetaNormReadL_eq_raw_sub_log_unitMass`（rfl）；
- `thetaNormReadL_eq_log_div`（需要 region/unitMass 正值）；
- doc 明说 `unitMass = 1` 不假设（S1902 UnitMassCitizen rows GAP）。

### canonical product normalized readout
文件：`Mzk1P0LNormReadoutProductActual.lean`
- `thetaNormReadProduct := Real.log (s1915HullMass).toReal − Real.log (s1915UnitMass).toReal`；
- **`thetaNormReadProduct_eq_sum : = Σ_b d_b · log r_b`**；
- **`thetaNormReadProduct_eq_closedForm_sub_one : = s1915ClosedForm − 1`**；
- `thetaNormReadProduct_eq_neg_sum_coefficient`：
  `= Σ_b −((d_b·c_norm_b)/(2l))·log p_b`；
- 不假设 `unitMass=1`；tensor-map scaling constant 在 normalized ratio 中抵消。

## 2. q 侧 canonical readout
文件：`Mzk1P0LReadoutLogActual.lean` / `Mzk1P0LQReadoutSignActual.lean`
- `qReadActual_eq_logNorm : qReadActual = Real.log ‖q.q‖`；
- `qReadActual_neg : qReadActual < 0`；
- `qReadActual_eq_neg_localLogMagnitude : qReadActual = −localLogMagnitude q`；
- 即 `qReadActual` 是 paper `−|log q|` 的 L 载体版本，canonical（无 unit mass arbitrary constant）。

## 3. canonicality 结论
- **product readout 是 canonical 的**：只用 `s1915HullMass`/`s1915UnitMass` 比值，等于 `s1915ClosedForm−1=Σ d log r`；无需 raw tensor additive constant，无需 `unitMass=1`。
- **tensor readout canonical 化必须显式减 `log actualUnitMassL`**；`thetaNormReadL` 的定义就是这样；raw `thetaReadActual` 不能单独作 signed theta。
- q 读数 `qReadActual` 是 canonical signed log，无 additive constant。

## 4. 对象不匹配（唯一结构 gap）
`Mzk1P0LNormReadoutProductActual` 末尾记录：
- L 载体是 single-place/local tensor object；
- `thetaNormReadProduct` 是全局 `Bad (nativePlaceSelection T)` 求和；
- 需：
  1. arithmetic data 识别（`C3LAt I place` ↔ `qVFamTensor` 数据）；
  2. `Bad` index ↔ `tensorIndex` 对应；
- 现有 `LGlobalLocalObjectLock`（structure）只记录这两点，无 inhabitant。

## 5. LQThetaSourceArrow 不可用于 theta≥0
- `Mzk1P0LQThetaArrowObstructionActual.lQThetaSourceArrow_isEmpty_of_theta_nonneg`（GREEN 01:08:02）：
  `0 ≤ thetaReadActual → IsEmpty (LQThetaSourceArrow I place)`。
- 原因：`normalization_eq` 会强制 `lThetaNormFactor=0`，与 `lThetaNormFactor > theta ≥0` 矛盾。
- 实际 nonempty 路线用 `Mzk1P0LPaperInstanceActual.LPaperInstance_of_theta_nonneg`，不用 arrow。

## 6. 待确认
- 两 L 文件当前无 olean；已入 WL，等官方编译确认上述 canonical 定理。
- 不修改旧 S3137 raw P（已证 empty）。
