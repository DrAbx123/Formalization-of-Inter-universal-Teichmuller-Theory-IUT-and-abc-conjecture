# S45 qVFamNormRatio=1：norm-instance 现状（只读审计）

## 定义
- `qVFamNormalizedNorm T b := ‖qVFamNormalizedGenerator T b‖`
  （`QVFamNormalizedGenerator := (qVFamily T b).q`，`QVFamNormalizedGeneratorSupplyActual:56`）；
- `qVFamDefaultNorm T b := ‖(qVFamily T b).q‖`
  （`QVFamNormalizedCoefficientBridgeActual:59`）；
- `qVFamNormRatio := qVFamNormalizedNorm / qVFamDefaultNorm`。

两个定义在语法上都是 `‖(qVFamily T b).q‖`，但 elaborated under **different local norm instances**：
“normalized spectral norm” vs “default valuation/adic norm”。树里没有 theorem 说明这两个 instance 一致。

## 现有等价（不是证明）
- `BadPlaceSourceFieldsObstructionActual.qVFamNormRatio_eq_one_iff_norm_eq`：
  `qVFamNormRatio = 1 ↔ qVFamNormalizedNorm = qVFamDefaultNorm`；
- `Mzk1P2QHatNormAgreementUnconditionalActual.p2QHatNormStandardAgreement_iff_ratio_one`：
  同样把 ratio=1 与 norm equality 互译；
- `Mzk1P2QHatNormAgreementUnconditionalActual.p2QNativeReading_defaultNorm`：
  `localLogMagnitude (qVFamily) = −log qVFamDefaultNorm`（unconditional，by rfl）。

这些只是把 S45 条件改写成 norm equality，**没有提供 equality 的证明**。

## 唯一直接尝试
`Mzk1P2QHatNormCoherenceAttemptActual.qHatNormCoherence_attempt`：
- 目标 `‖c0QHat‖ = qVFamNormalizedNorm`；
- 用 `c0QHat_eq_q` + `norm_algebraMap'` 试图归约到两个 completion norm instance 相等；
- **当前 FAIL 11-14 03:40:42**：`rw [norm_algebraMap']` 模式不匹配；
- 该 ATTEMPT 未建立任何定理。

## CommonPrime norm compat
- `Mzk1P0LQThetaComponentActual.CommonPrimeNormInstanceCompat` structure：
  `norm_eq : ∀ x : Completion place, ‖x‖ = ‖(x : CommonPrimeCompletion place)‖`；
- `Mzk1P0LCommonPrimeNormActual.commonPrimeNormGap : Prop := CommonPrimeNormInstanceCompatRequired I place`；
- 无 inhabitant；记录为 gap。

## 是否存在反例/分离 regime
- `BadPlaceCorrectionSignActual.SeparatedNormRatioRegime` structure：
  `gap_ne : paperNormalizedCoefficient b ≠ qVFamNormalizedCoefficient b`；
- `separated_ratio_ne_one (R) : qVFamNormRatio T R.b ≠ 1`（PROVED）。
  即存在分离参数 regime 使 ratio≠1。

## 结论
- 树里 **没有任何 theorem 证明** `qVFamNormalizedNorm = qVFamDefaultNorm`（或 ratio=1）；
- 现有 theorem 只是把 ratio=1 与 norm equality 互译；
- `qHatNormCoherence_attempt` 未成功；`CommonPrimeNormInstanceCompat` 无 inhabitant；
- 存在分离 regime 使 ratio≠1；
- 因此 **ratio=1 是真实的 S45 source 条件/未解 norm-instance coherence**，不能在当前树无条件证明；
- 若要证，需要新增 `Completion` vs `CommonPrimeCompletion` 的 norm instance coherence（或对 qVFamily 的具体 norm 计算），当前没有。

## 状态
- 未改源；不 fake equality；不把 ratio=1 当定理。

## 11. Donor `generalNormalizedNormFormula` 对照（2026-11-14）

### donor 给出什么
`LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormFinal.lean:73-83`：
- `generalNormalizedNormFormula (x : NormalizedCompletion place) :
  ‖x‖_norm = absNorm ^ (-(nu x)/d)`，其中 `nu x = -WithZero.log (Valued.v x)`（:52）；
- `generalNormalizedLogFormula` 同式取 log。

### default completion norm
`FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow`：
- `‖x‖_def = absNorm ^ (toAdd(unzero(valuation)))`；
- 而 `nu = -WithZero.log(Valued.v)`，即 `toAdd(unzero(valuation)) = -nu`；
- 所以 `‖x‖_def = absNorm ^ (-nu)`。

### 由 donor 得到的 exact relation
在同一个 `NormalizedCompletion` 元素上，两个 norm instance 分别给：
```text
‖x‖_norm = absNorm^(-nu/d)
‖x‖_def  = absNorm^(-nu)
```
因此（d>0，absNorm>1，正数 rpow）：
```text
‖x‖_norm = (‖x‖_def) ^ (1/d)
```
这是 **exact power relation（norm-instance mismatch 的精确形式）**，不是 equality。

### 是否 close norm-instance compat
**不。**
- `norm-instance compat` 要求 `‖x‖_norm = ‖x‖_def`；
- donor 给的是 `‖x‖_norm = ‖x‖_def^(1/d)`；
- 二者相等仅在 `‖x‖_def = 1`（或 d=1 且无其他 scaling）时成立；
- `BadPlaceCorrectionSignActual.SeparatedNormRatioRegime` 已证明存在 ratio≠1 的 regime。

### 结论
- donor 不能把 `qVFamNormRatio=1` 证明出来；
- 它给出的是 mismatch 的 **power formula**，可用来精确表达 ratio：`ratio = default^(1/d-1)`；
- S45 条件 `ratio=1` 仍是真实 source condition，不能由 donor 无条件关闭。

### 仍需的桥
要把 donor 用到 qVFam 上，需显式建立：
1. qVFamNormalizedGenerator 的 `NormalizedCompletion place` 身份；
2. 该元素的 `nu`/`absNorm` 与 qVFam 系数的对应；
3. `qVFamDefaultNorm` 用 default instance 的识别。
这些桥当前也未形式化；但即使形式化，结论仍是 power formula，不是 equality。

## 12. donor 官方编译状态（只读，2026-11-14）

- `GeneralNormalizedNormBySpectralUniqueness.lean`：**FAIL 04:00:55**（依赖 `BaseScalarValuationRelation.olean` 缺失）；
- `BaseScalarValuationRelation.lean`：**FAIL 04:08:14**（real proof errors：rewrite pattern、typeclass instance not definitionally equal、unsolved goals、application type mismatch）；
- `GeneralNormalizedNormFinal.lean`：无 olean、无 watchdog 记录；
- `GeneralizedNormalizedNormConsumer.lean`：无 olean；
- `FinitePlaceCompletionNormTransport.lean`：有旧 olean（10-16），但 donor 链上方 red。

因此：
- §11 的 power formula 是 **源码级/文本级** 对照，不是官方编译结论；
- donor 目前 **不可用于机器检验**；
- 在 donor 变绿前不能把 `||x||_norm = ||x||_def^(1/d)` 当 official theorem。

未改源。

## 13. donor/L-side fresh 复核（2026-11-14）

### BaseScalar
- `BaseScalarValuationRelation.lean`：src 05:19:38，olean 05:22:40，**DONE EXIT=0 05:22:40**；
- 已 fresh GREEN。

### Spectral uniqueness
- `GeneralNormalizedNormBySpectralUniqueness.lean`：src 03:57:02，**FAIL 05:32:21**；
- errors：
  * `Unknown identifier NumberFieldFinitePlace.relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg`；
  * type expected got `L : FinitePlace → Type`（多处）；
  * `failed to synthesize instance`；
  * `introN` no binders（可能 source 有未完成 tactic 分支）。
- 即使 BaseScalar olean 已存在，spectral 文件仍 red。

### Final donor
- `GeneralNormalizedNormFinal.lean`：无 olean、无 watchdog 记录（依赖 spectral red）。

### L readout
- `Mzk1P0LNormReadoutActual`：src 01:54:11，olean 01:57:31，**DONE 01:57:32** fresh GREEN；
- `Mzk1P0LNormComparisonConditionalActual`：src 02:08:41，olean 02:08:47，**DONE 02:08:48** fresh GREEN。

### 结论
- BaseScalar 已 fresh；但 spectral/final donor 仍不可用；
- §11 power formula 仍不能 official；
- L side readout/comparison fresh GREEN，不受 donor red 影响；
- 未改源。
