# P6-S3137-READINGS-AUDIT — S3137 canonical 读数 vs 我们 green 的 q/Θ 公式（巡检审计）

日期：2026-11-13；abc。**只读审计**；不改数学文件；不声称任何未证内容。

## 0. 结论先行

1. **q 侧**：S3137 的 `qPilotLogVolumeReading P = P.signedQPilotLogVolume = -|log‖P.line.C3.q.q‖| = Real.log‖P.line.C3.q.q‖`（负值）与我们 green 的 `paperQPilotLogVolume_multi D = sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial` **在同一 q/索引/归一化下相等**；S1487 canonical 一 place 情形已由 `S1487Faithful_sourceBadQAbsLog = localLogMagnitude S1487Cand` 具体化。
2. **Θ 侧**：S3137 的 `thetaPilotHullLogVolumeReal C3 = Real.log ((actualC3LogShellTensorHaar C3)(thetaPilotHull C3)).toReal`，且 `thetaPilotHull = actualC3LogShellTensorRegion`；我们 green 的 `RTarget μ θ = -Real.log ((μ θ).toReal)`、`S2807_thetaHullVolume_eq_haarRegion = -(haarLogVolume …).toReal` 与 `RTarget_eq_neg_haarLogVolume` 表明：**S3137 Θ 读数 = -RTarget = -S2717ThetaHullLogVolume**（纯符号约定差，不是数值差）。
3. **比较**：`qThetaPilotLogVolumeComparison C3 P : qRead ≤ θRead` 在 qRead = -A、θRead = -R 的约定下 **等价于** `A ≥ R`，即 `0 ≤ MTarget`（`M=A-R`）。这是等价，不是证明；S3137 的 comparison 本身仍是 pending Prop。
4. **归一化因子**：S3137 读数直接是 `|log q|` / `log μ`，**不含** `1/(2l)` 或 `1/[K:Q]`；我们 q 侧 paper 单位 `ATarget = paperQAbsLog l logQ = logQ/(2l)` 与 `qRead` 的换算需要 canonical `logQ = 2l·|log q|`（`paperQAbsLog_two_l_mul`，`Mzk1S1487SourceRootIdentityActual:35`）；`1/[K:Q]` 在树中仍无实际对象（GAP-NORM-ARCH-C）。

## 1. S3137 读数（精确 file:line）

| 对象 | file:line | 定义/内容 |
|---|---|---|
| `qPilotLogVolumeReading` | `S3137QThetaPilotLogVolumeReadingsActual.lean:77` | `P.signedQPilotLogVolume` |
| q 读数 = `-|log q|` | 同上 `:82` `qPilotLogVolumeReading_eq_neg_abs_qParameter` | `= -|Real.log (‖P.line.C3.q.q‖)|` |
| q 读数 = `log‖q‖` | `Mzk1S3137ReadoutBridgeActual.lean:33` `qPilotLogVolumeReading_eq_log_norm` | `= Real.log ‖P.line.C3.q.q‖`（因 ‖q‖<1 两式一致） |
| q 读数 = signed | `Mzk1S3137ReadoutBridgeActual.lean:27` | `= P.signedQPilotLogVolume`（rfl） |
| `thetaPilotHull` | `S3137QThetaPilotLogVolumeReadingsActual.lean:97` | `actualHolomorphicHull C3 (actualUnitRegion C3)` |
| hull = region | 同上 `:102` | `thetaPilotHull C3 = actualC3LogShellTensorRegion C3` |
| `thetaPilotHullLogVolume`（ENNReal） | 同上 `:112` | `haarLogVolume (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)` |
| **`thetaPilotHullLogVolumeReal`** | 同上 `:128` | `Real.log ((actualC3LogShellTensorHaar C3)(thetaPilotHull C3)).toReal` |
| comparison | 同上 `:145` | `qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`（named Prop, pending） |
| 审计 obligation | 同文件 `LeanFormal.IUT.Audit.qThetaPilotLogVolumeComparison`（文件末尾） | status pending |

## 2. 我们 green 的 q 侧（精确 file:line）

| 对象 | file:line | 内容 |
|---|---|---|
| `paperQPilotLogVolume_multi` | `S2708MultiPlaceQPilotActual.lean:146` | `-(∑_b |log(D.qFamily b)|)` |
| multi = signed | 同上 `:153` | `paperQPilotLogVolume_multi D = sourceQPilotSignedLog I.initial` |
| multi = -badQAbsLog | 同上 `:161` | `= -sourceBadQAbsLog I.initial` |
| `-|log qProduct| = volume` | `S2717StageAMultiQActual.lean:190` | Stage A 端点 |
| `stageAQParameterSigned_multi = volume` | 同上 `:212` | Stage A signed q |
| native 逐位 | `Mzk1QPilotPlaceDegreeActual.lean:64` `nativeBadPlace_abs_log_eq` | `|log(qVFamDefaultNorm b)| = order_b·log(residueNormBase place_b)` |
| native 求和 | 同上 `:108` `nativeBadQAbsLogSum_eq_valuationSum` | `nativeBadQAbsLogSum = valuationSum` |
| degree = absLogSum | `Mzk1DegreeSumActual.lean:102` | `globalPrimeStripWeight nativeBadExplicitDivisorSum = nativeBadQAbsLogSum` |
| **条件 q 桥** | `Mzk1DegreeBridgeActual.lean:79/84` | `QPilotDegreeBridge d ⇒ paperQPilotLogVolume_multi = -globalPrimeStripWeight d` |
| S1487 canonical | `S1487OQPilotScalarEqualityActual.lean:586` | `sourceBadQAbsLog S1487FaithfulSourceData = localLogMagnitude S1487Cand` |
| S1487 q 参数值 | `Mzk1SourceNativeQActual.lean:45` | `(S1487FaithfulSourceData).reduction.qParameter b = ‖S1487Cand.q‖`（rfl） |
| S1487 单 index 桥 | 同上 `:82` | `[Unique (Bad …)]` + `hsrc` ⇒ `OrigXiFPaperBadQAbsLog S1487FaithfulSourceData = nativeBadQAbsLogSum`（条件式） |

## 3. q 侧逐项对照

### 3.1 等价/差值

记 S3137 的 q 候选为 `q_S := P.line.C3.q.q`，我们 S1487 canonical 候选为 `S1487Cand.q`。

| 项 | S3137 | 我们 green | 关系 |
|---|---|---|---|
| q 读数 | `log‖q_S‖ = -|log‖q_S‖|` | `paperQPilotLogVolume_multi D = -sourceBadQAbsLog`（一 place = `-localLogMagnitude S1487Cand`） | 若 `q_S` 与 S1487Cand（或 donor qFamily）同一 q、且单 place：**相等**（两者都 = `-|log q|`） |
| 多 place | 单 q | `-∑_b |log q_b|` | 一般**不等**；需 `qProduct D = ‖q_S‖` 或逐 b 乘积识别 |
| paper 单位 | 无 `1/(2l)` | `ATarget = paperQAbsLog l logQ = logQ/(2l)` | `qRead = -ATarget` 当且仅当 `logQ = 2l·|log q|`（canonical；`Mzk1S1487SourceRootIdentityActual:35 paperQAbsLog_two_l_mul`） |
| StageA | 无 | `stageAQParameterSigned_multi`（S2717StageA:212） | 与 `paperQPilotLogVolume_multi` 相等（green） |
| degree | 无 | `globalPrimeStripWeight = nativeBadQAbsLogSum`（Mzk1DegreeSum:102） | `paperQPilotLogVolume_multi = -degree` 在 `QPilotDegreeBridge` 下（Mzk1DegreeBridge:84） |

### 3.2 q 侧缺口（精确）

```
GAP-S3137-Q-INHABIT：S3137 q 读数消费 `P : N8Closure.PaperQPilotObjectActual I`；该类型无 green 构造（Mzk1S3137ReadoutBridgeActual 头注：C1/C2/C3/strip/oneColumn/logKummer 是 paper source obligation）。读取是 implications from P，不是 inhabitant。
GAP-S3137-QID：`P.line.C3.q`（单个 actual q）与 S1487Cand / donor `D.qFamily b` 的索引-值识别未构造；单 place 情形需要 `q_S = S1487Cand`（或与 donor 一致），多 place 需要乘积识别。
GAP-S3137-C3：P 的 C3 是 `PaperQPilotObjectActual.line.C3`（N8Closure）；与我们 green 的 `SourcePilotRegionData` C3（S2717C3 / S1487FivePlace）是否同一实例未证。
```

## 4. Θ 侧逐项对照

| 项 | S3137 | 我们 green | 关系 |
|---|---|---|---|
| Θ 读数 | `thetaPilotHullLogVolumeReal = log μ(H)`（`:128`） | `RTarget μ θ = -log ((μ θ).toReal)`（`Mzk1OurAccurateTargetActual.lean:32`） | **S3137 Θ = -RTarget**（符号约定差） |
| hull | `thetaPilotHull = actualC3LogShellTensorRegion`（`:102`） | S2807 的 `actualC3LogShellTensorRegion (S2717C3 … D)`（`S2807…:42`） | 需 C3 = S2717C3(…D) 的实例识别（GAP-S3137-C3） |
| S2717 Θ | — | `S2717ThetaHullLogVolume = -(haarLogVolume …).toReal`（`S2807…:40`） | S2717 Θ 体积 = `RTarget`（`Mzk1OurAccurateTargetActual:83 RTarget_eq_neg_haarLogVolume`，在 `1≤μ` 下） |
| 归一化 | 无 `1/[K:Q]`、无 `1/(2l)` | `RTarget` 无因子；`1/(2l)` 在 q 侧 `paperQAbsLog`；`1/[K:Q]` 无实际对象 | 因子差必须显式记录（GAP-NORM-ARCH-C） |

### Θ 侧缺口

```
GAP-S3137-THETA：S3137 C3（PaperQPilotObjectActual.line.C3，N8Closure）与 S2717C3(…D) / S1487 C3 的实例识别未证；识别后 S3137 Θ = -S2717ThetaHullLogVolume = -RTarget（符号差）。
GAP-S3137-THETA-INHABIT：同上，P 的 C3 依赖 P，无 green inhabitant。
GAP-NORM-ARCH-C（继承）：`1/[K:Q]` 与 `1/(2l)` 进入 arch/Θ 读数的归一化未构造；S3137 读数本身是 raw log-volume（无 paper factor）。
```

## 5. 比较的等价翻译（Paper312Statement 验收口径）

在 q 侧 `qRead = -A`（A = `paperQAbsLog = |log q|`）且 Θ 侧 `θRead = -R`（R = `-log μ = RTarget`）的约定下：

```
qThetaPilotLogVolumeComparison C3 P      -- qRead <= thetaRead（S3137:145）
  <=> -A <= -R
  <=> A >= R
  <=> 0 <= A - R = MTarget               -- Mzk1OurAccurateTargetActual:36
  <=> 0 <= MTarget（our variant M = A - R；非负判定的 green 路径：normalized containment ⇒ 1<=μθ ⇒ R<=0, A>=0）
```

注意方向：S3137 的 `q ≤ Θ` 对应我们 `M >= 0`（不是 `M <= 0`）；`MTarget_nonneg_of_one_le`（`Mzk1OurAccurateTargetActual:54`）正是该方向。

## 6. 结论 / 验收口径

1. S3137 q/Θ 读数与我们 green 的 q/Θ 公式**在显式 q 识别、C3 实例识别、以及（q 侧）canonical logQ 因子识别下逐项相等**；
2. 已知差异只有**符号约定**（Θ 侧 `log μ` vs `-log μ`）和**归一化因子**（S3137 raw；我们 `paperQAbsLog = logQ/(2l)`；`1/[K:Q]` 无对象）；
3. **比较本身**（`qThetaPilotLogVolumeComparison`）仍是 pending Prop；我们的 `0 <= MTarget` 判据是等价的 green 归约，不是比较的证明；
4. **Paper312Statement 验收**必须引用：S3137 q/Θ 读数定义（:77/:128）、本审计 §3–§5 的等价/差因子、以及 GAP-S3137-Q-INHABIT / QID / C3 / THETA / NORM-ARCH-C 缺口；不得把 waiting Prop 当已证。
