# P3-S3019-BRIDGE — StepV q-pilot ↔ native global q-pilot 判定

日期：2026-11-13；qpilot（task-106）。**Status: READ-ONLY + source analysis；不自行编译。**

## 0. 结论先行

**不能在现有实际对象上证明 S3019MissingBridge / S3019 的 log/sum 等式。**

原因是两侧属于**不同的对象系统**：
- 左：`S3016StepVQPilot a b c = S2736QPilotLineBundleLogVolume (qPilotLineBundleExtended J)`，即 Gaussian 数域上固定四个坏素理想（5,2161）乘 ABC support `J` 的**全局 line-bundle log**；
- 右：`S3016WeightedGlobalQPilot T = nativeGlobalQPilotNormalizedLogMagnitude T = Σ_b nativeBadLocalWeight T b * baseQLogMagnitude T b`，即 native 输入 `T` 的 bad 家庭按局部次数权重的**log-magnitude 和**；
- 树内没有把 `qPilotLineBundleExtended` 的素因子指数（尤其 J）映射到 native bad places、也没有把 `nativeBadLocalWeight`/`baseQLogMagnitude` 与 Gaussian qPilot ideal 对齐的定理。

因此 `S3019_target_iff_log_sum` 只是把目标重写成 log/sum 等式（green），**不是**该等式的证明；`S3019MissingBridge`（∀ T,a,b,c）不仅未证，且其量词形状（左边不依赖 T、右边依赖 T）本身就是可疑的过强陈述。

## 1. 精确定义（file:line）

| 对象 | 定义 | file:line |
|---|---|---|
| StepV q-pilot | `S3016StepVQPilot a b c := S2736QPilotLineBundleLogVolume (S2752J ...)` | `S3016StepVQPilotIdentificationActual.lean:29-34` |
| native global q-pilot | `S3016WeightedGlobalQPilot T := nativeGlobalQPilotNormalizedLogMagnitude T` | 同上 `:36-39` |
| target | `S3016IdentificationTarget := StepV=WeightedGlobal` | 同上 `:41-43` |
| log/sum reduction | `S3019_target_iff_log_sum` | `S3019StepVQPilotIdentificationProofActual.lean:30-41` |
| MissingBridge | `∀ T [Fintype] a b c, S3016IdentificationTarget T a b c` | 同上 `:56-60` |
| line-bundle log | `log absNorm (qPilotLineBundleExtended J)` | `S2736QPilotLineBundleHweightvol.lean:19-22` |
| native weights | `nativeBadLocalWeight` / `nativeGlobalQPilotNormalizedLogMagnitude` | `VbadPlaceIndexingActual.lean:89-97`；`NativeGlobalQPilotNormalizedLogVolumeActual.lean:96-110` |
| qPilot ideal | 四个 Gaussian 坏素理想乘积；absNorm = 5*5*2161*2161 | `S2735QPilotLineBundleActual.lean:26-40,116-122` |

## 2. 等式的精确形状

`S3019_target_iff_log_sum` 给：
```
S3016IdentificationTarget T a b c
  ↔ log( absNorm(qPilotLineBundleExtended (J a b c)) )
      = Σ_b nativeBadLocalWeight T b * baseQLogMagnitude T b
```
左端可展开为：
```
log absNorm(qPilotIdeal * J)
  = log absNorm(qPilotIdeal) + log absNorm(J)
  = log(5*5*2161*2161) + log absNorm(J)
```
（`qPilotIdeal_absNorm`；multiplicativity of absNorm；J 为有限 support ideal）。
右端是 native 的加权 base-q 绝对 log 和，权重 `nativeBadLocalWeight = 1/[K_w:F_v]`，`baseQLogMagnitude = order(q_b)*log residueNormBase`。
两者一般没有函数关系：左端由固定的 5/2161 与任意 J 决定；右端由 `T` 的 bad places、局部次数、q 的 order、剩余范数共同决定。

## 3. 为什么现有树不能证

### 3.1 缺对象：qPilotIdealExtended 的素因子指数 → native bad places
`qPilotLineBundleExtended J = qPilotIdeal * J` 的有限素因子指数是 Gaussian `SourceOK` 的理想指数；
native 右端是 `Bad (nativePlaceSelection T)` 的 `nativeBadLocalWeight` 与 `baseQ`。
树内没有：
1. `qPilotIdeal` 的四个素理想到 native bad places 的映射；
2. `J` 的每个素因子到 native bad places（或 `J` 作为额外 support 项）的映射；
3. `nativeBadLocalWeight` 与 qPilot ideal 指数/局部次数的一致性。

### 3.2 缺对象：Gaussian arithmetic ↔ native `T` 的识别
`S3016StepVQPilot` 用 `S2771FiveLabel`（固定 l=5）与 `S2752J`；
`S3016WeightedGlobalQPilot` 用任意 `T : SourceNativeInitialThetaData l`。
没有定理把 `S2735Arithmetic`（Gaussian `InitialThetaArithmeticData`）与某个 native `T` 的初始 Theta 数据识别起来；
也没有定理把 `qPilotIdeal` 的阶 `m` 与 `baseQ` 的 order/权重对齐。

### 3.3 `S3019MissingBridge` 的量词问题
它要求 **∀ T** 成立，而左端不依赖 T、右端依赖 T；除非 native 全局和恰好为常数（未证且一般不可能），这个 ∀ 命题不能作为“桥”的合理形式。
正确形式应是：固定一个实际 `T`，并给出 `T` 与 Gaussian qPilot/`J` 的来源识别数据，再逐 T 证明等式；不是对所有 T 统一断言。

## 4. 精确缺口（最小补充对象）

1. `S3019SourceQIdentification`：一个实际对象，包含
   - `T : SourceNativeInitialThetaData l`（或固定 Gaussian 输入与 `T` 的对应）；
   - `qPilotIdealExtended` 的每个素因子指数到 `Bad (nativePlaceSelection T)`（或额外 support）的映射；
   - 每个 b 的 `nativeBadLocalWeight b` 与 qPilot 局部指数/局部次数的等式；
   - `J` 的 support 项到右端额外项的等式。
2. `S3019AbsNormLogSum`：在上述数据下证明
   `log absNorm(qPilotLineBundleExtended J) = Σ_b w_b * baseQLogMagnitude b + supportJ`；
3. 若要把 `S3019MissingBridge` 改成可证命题，必须去掉 `∀ T`，改为“存在/给定实际 T 与上述 source identification”。

## 5. 判定

| 命题 | 判定 | 依据 |
|---|---|---|
| `S3019_target_iff_log_sum` | **GREEN（等价重写）** | S3019:30-41 |
| `S3019MissingBridge` | **不能证；量词过强** | 左端不依赖 T、右端依赖 T；无 source map |
| 等式本身（固定 T/固定 J） | **缺 source identification** | qPilot ideal/J → native bad/weights 映射缺失 |
| 当前能否构造 Lean 真证明 | **否** | 没有实际映射对象，不能造假设换 green |

## 6. 下一步

最小下一包：先定义 `S3019SourceQIdentification` 的实际字段并检查是否有 inhabitant（尤其 Gaussian qPilot ideal 到 native bad places 的映射）；
若没有，必须记录为 named input，不得把 `S3019MissingBridge` 当已证。之后才能把 S3016/S3019 接入 S3014/S2807 链。

## 文件
- 本文件 `coord/P3-S3019-BRIDGE.md`；未新增 Lean 文件（不能证明，不写 fake constructor）。