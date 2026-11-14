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

## 7. 编译级只读核对（mainline fixing，勿改）

### `Mzk1P0LNormReadoutProductActual`（FAIL 01:13:13）
- 已 import/open `QVFamTensorCoefficientActual`，`qVFamTensorP` 有来源；
- **缺** `import/open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual`：
  `qVFamNormalizedCoefficient` 定义在该 namespace（当前文件只用 `QVFamNormalizedCoefficientBridgeActual`，不 re-export 该名）。
- 剩余 proof errors：
  - `:77 rw [Real.log_mul (by positivity) (by positivity)] at hnorm` 模式不匹配（`s1915_log_normalized_hull` 的表达式需先 `rw [show ...]`/`ring_nf` 或用显式非负证明）；
  - `:84/:85 Function expected` 与 `qVFamNormalizedCoefficient` autoImplicit 连带。

### `Mzk1P0LNormReadoutActual`（FAIL 01:13:57）
- `thetaNormReadL`/`actualUnitMassL`/`qReadActual` 是 section 变量自动隐式参数；
  `thetaNormReadL I place`/`qReadActual I place` 会 Function expected；需 `thetaNormReadL (I := I) (place := place)` 或把 def 的 I/place 显式化。
- `:80 deterministic timeout at whnf` 出现在 `LNormComparisonTarget_iff_log_div` 的 `actualC3LogShellTensorHaarL` 大项展开；可加 `set_option maxHeartbeats 1000000` 或 `change` 成显式表达式。

### 结论
- 两文件 canonical 定理内容正确，但当前 **未 official GREEN**；audit 中标为待编译。
- 不改 mainline；等其 owner 修 import/open 与隐式参数。

## 8. mainline 修复后 tail（只读，2026-11-14）

### `Mzk1P0LNormReadoutProductActual`（仍 FAIL 01:23:01）
- `:83 unfold thetaNormReadProduct s1915ClosedForm at hnorm ⊢`：
  `hnorm` 中不一定含 `thetaNormReadProduct`，`at hnorm` 会失败；
  建议改成 `simp only [thetaNormReadProduct, s1915ClosedForm] at hnorm ⊢`。
- `:84/:85 Function expected`：`thetaNormReadProduct T` 与 `qVFamNormalizedCoefficient T b`/`qVFamTensorP T b` 为自动隐式，
  需 `(T := T)`/`(b := b)` 或显式 binder。
- `:96 rw [Real.log_rpow ...]` 模式不匹配：需先把 `rootNormedElementNorm_eq_p_rpow` 后的表达式 `change` 成 `Real.log ((p:ℝ).rpow e)` 或用 `Real.log_rpow` 的显式等式。

### `Mzk1P0LNormReadoutActual`
- 01:21:12 START，结果待 watchdog。

## 9. `SourceUnitBridge` 与 L readout 接口（只读）

### SourceUnitBridge 提供什么
`Mzk1Ind1SourceUnitBridgeActual.lean`：
- `SourceUnitQuotientIdentification (W) (K) : Type` = `W ≃* ((Integers K)ˣ ⧸ torsion)`；**无 inhabitant**（源码 doc 明说 missing source-level identification）。
- `sourceUnitLogRangeEquiv (idK idL β) : (unitLogHom K).range ≃* (unitLogHom L).range`；
- `sourceUnitLogRangeEquiv_apply`（rfl）；只处理 **integral units 的 log range**，不含 measure/theta hull。

### L readout 提供什么
- `thetaNormReadL`/`thetaNormReadProduct`：analytic `Real.log` of Haar mass ratio / product hull；
- `qReadActual`：`Real.log‖q.q‖`（signed log）；
- `thetaNormReadProduct = s1915ClosedForm−1 = Σ_b d_b log r_b`（全局 Bad 求和）。

### 接口缺口（精确）
1. **对象层级不同**：SourceUnitBridge 是 `Integers K` 的单位群/对数 range；L readout 是 completion field 的 q 元素/Haar 测度。
2. **缺 SourceUnitQuotientIdentification inhabitant**：`W` ↔ integral units 的实际源单位识别；
3. **缺 q 单位/测度对应**：`q.q`（或 tensorUnit）与 integral unit representative 的对应，及 unitLog 值到 `log‖q‖` 的桥；
4. **缺 product/global 版本**：SourceUnitBridge 是单个 normed field K/L；L product readout 是全局 `Bad` product hull，没有逐 block 单位 log range 的乘性装配。

### 现有可复用接口
- `Mzk1Ind1UnitQuotientActual.unitLogQuotientEquivOfMulEquiv`：
  给定 `(Integers K)ˣ/torsion ≃* (Integers L)ˣ/torsion`，得到 log range equiv；
  仍需要“源单位 → 整单位 quotient”的 identification 和 L 侧 readout 的 log 值对齐。

### 结论
- SourceUnitBridge 不能直接给 `LQThetaSourceArrow.normalization_eq` 或 `thetaNormReadL` 的规范化；
- 它是 **Ind1 unit-log** 层，L theta readout 是 **measure/analytic log** 层；
- 要做接口需新增：`SourceUnitQuotientIdentification` inhabitant + q/单位对应 + product 装配；当前均无。
