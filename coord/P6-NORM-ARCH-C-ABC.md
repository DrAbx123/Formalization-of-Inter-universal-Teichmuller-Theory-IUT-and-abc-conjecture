# P6-NORM-ARCH-C-ABC — abc 基域 K 与 arch 因子 1/[K:Q]

日期：2026-11-13；abc。**巡检 + 可证化**。新 Lean：`Mzk1NormArchCAbcActual.lean` **watchdog DONE EXIT=0**（22:13:45Z，31s；olean 存在）。

## 0. 结论

1. **abc 应用路线的基域是 ℚ**：`ABCBridge/Statement.lean:26` `IsABCTriple := PrimitiveAdditiveTriple`（纯 Nat），`:28` `ABCInequality` 的常数/ε 是 Real，`:25` `abcJInvariant : ℚ`（`ABCInvariantCoprimality.lean:25`）；ABC 链没有一般数域对象 K。
2. IUT IV 的 arch 归一化因子实际对象是 `heightWeight F = 1/[F:Q]`、`toricHeightWeight F = 1/(2[F:Q])`（`LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean:1214/1217`），分别进入 `hArc`（`:1224-1225`）与 `hToricArc`（`:1235-1236`）。对 ℚ：`[ℚ:ℚ]=1`，所以 arch 因子 = **1**（toric = 1/2）。
3. 一般 degree-one K：`RationalDifferent.lean:27-40` 给出 `ratAlgEquivOfFinrankOne : Module.finrank ℚ K = 1 → ℚ ≃ₐ[ℚ] K`；条件式 arch 因子 = 1（Lean 中已写 `heightWeight_eq_one_of_finrank_one`）。
4. **精确缺口**：ABC statement/route 层面没有显式 K 对象与 `[K:Q]` 实例；只有 ℚ 语句。如果 IUT→ABC 步骤用一般数域 F，则 arch 因子是 `1/[F:Q]`，等于 1 仅在 [F:Q]=1（或 F=ℚ）时。该实例化未在 ABC 链接入。

## 1. 新 Lean（`tmp/sheaf/xif/paper/Mzk1NormArchCAbcActual.lean`，请 Lead 加 watchdog 名单）

```lean
theorem heightWeight_rat : heightWeight ℚ = 1           -- 1/[Q:Q]
theorem toricHeightWeight_rat : toricHeightWeight ℚ = 1/2 -- 1/(2[Q:Q])
theorem heightWeight_eq_one_of_finrank_one {K} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) : heightWeight K = 1
theorem toricHeightWeight_eq_half_of_finrank_one ... : toricHeightWeight K = 1/2
```

证明：`unfold heightWeight/toricHeightWeight` + `CommSemiring.finrank_self`（`Mathlib/LinearAlgebra/Dimension/Finrank.lean:108`）+ `norm_num`。

## 2. file:line 证据

| 内容 | file:line |
|---|---|
| ABC 三元组（Nat） | `LeanFormal/IUT/ABCBridge/Statement.lean:26` |
| ABC 不等式（Real ε/K） | 同上 `:28-29` |
| `abcJInvariant : ℚ` | `LeanFormal/IUT/ABCBridge/Arithmetic/ABCInvariantCoprimality.lean:25` |
| IUT IV arch 归一化因子 `heightWeight` | `LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean:1214` |
| toric 因子 `toricHeightWeight` | 同上 `:1217` |
| `heightWeight` 进入 `hArc` | 同上 `:1224-1225` |
| `toricHeightWeight` 进入 `hToricArc` | 同上 `:1235-1236` |
| degree-one ⇒ ℚ ≃ₐ K | `LeanFormal/IUT/ABCBridge/Arithmetic/RationalDifferent.lean:27-40` |
| 另一处 `1/[K:Q]` 归一化 | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionNormTransport.lean:471`（`log‖completionMap‖ / (finrank ℚ K)`） |

## 3. 精确缺口

```
GAP-NORM-ARCH-C-K：ABC route 没有显式 number-field 对象 K，也没有 [K:Q] 的实例；
  ABC 语句是纯 ℚ/Nat。若 IUT→ABC 的桥使用一般 F（IUT IV 的 heightWeight F），
  则 arch 因子 = 1/[F:Q]；只有 F = ℚ 或 [F:Q]=1 时等于 1。该实例化未构造。
GAP-NORM-ARCH-C-L：q 侧 c_root = 1/(2l)（S3050Unit，见 P6-CNORM §11）与 arch 侧 1/[F:Q] 是不同因子；
  ‘1/(2l) = 1/[F:Q]’ 不成立一般；本文件只处理 arch 侧。
```

## 4. 与 Paper312Statement 验收

- 若验收口径固定 abc 基域为 ℚ：arch 归一化因子 **=1**（`heightWeight_rat`），toric 项 =1/2；无需额外 K 实例。
- 若验收使用一般数域 F：必须给出实际 F 对象与 `[F:Q]` 实例，并在 arch 归一化中用 `heightWeight F`；当前 ABC 链没有该对象（GAP-NORM-ARCH-C-K）。

## 5. build 与下一步

```
watchdog: dag/watchdog/watchdog.log L204789 `2026-11-12T22:13:45.084Z DONE EXIT=0 tmp/sheaf/xif/paper/Mzk1NormArchCAbcActual.lean (31s)`
olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1NormArchCAbcActual.olean
```

下一步候选（lead 建议）：把 `heightWeight ℚ = 1` 接入 ABC 链实际 arch 项。内容搜索显示 ABCBridge 直接用 `ABCHeightWeightAdditiveBoundV2`（`ABCHeightArithmeticWeightComparison.lean:158`）等抽象 Prop，**未直接消费 `hArc`/`heightWeight`**；`hArc`/`heightWeight` 只在 `IUTIV/Estimates/ArithmeticDivisorDegree.lean` 内部定义与 `FinitePlaceCompletionNormTransport.lean:471` 出现。因此接入点应是 IUT IV → `Cor312ComparisonGap*` 的 arch 项字典（GAP），或 `RationalDifferent` 的 degree-one 实例化，而不是 ABCBridge 层直接替换。
## 6. RationalDifferent degree-one 实例化（hArc/hToricArc）

新文件：`tmp/sheaf/xif/paper/Mzk1NormArchCHArcActual.lean`：**watchdog DONE EXIT=0**（`watchdog.log` L204818，22:16:31Z，32s；olean 存在）；不 import `Mzk1DiagonalIndexActual`。

| 定理 | 内容 |
|---|---|
| `hArc_rat x` | `hArc ℚ x = ∑ w, hTerm ℚ (.infinite w) x`（`ArithmeticDivisorDegree:1224` + `heightWeight_rat`） |
| `hToricArc_rat x` | `hToricArc ℚ x = (1/2) * ∑ w, toricTerm ℚ (.infinite w) x`（`:1235` + `toricHeightWeight_rat`） |
| `hNon_rat x` | `hNon ℚ x = ∑_{v∈nonSupportFinset} hTerm ℚ (.finite v) x`（`:1220` + `heightWeight_rat`） |
| `hArc_eq_sum_of_finrank_one` | 一般 degree-one K：`hArc K x = ∑ hTerm`（条件 `Module.finrank ℚ K =1`，`RationalDifferent:27`） |
| `hToricArc_eq_half_mul_sum_of_finrank_one` | 一般 degree-one K：`hToricArc K x = 1/2·∑ toricTerm` |

精确缺口：一般 F（无 `[F:Q]=1`）保持 `heightWeight F = 1/[F:Q]` 权重；ABC 链仍未把实际 K 对象/`[K:Q]` 实例给出（GAP-NORM-ARCH-C-K，§3）。
### build 证据

```
L204818 `2026-11-12T22:16:31.761Z DONE EXIT=0 tmp/sheaf/xif/paper/Mzk1NormArchCHArcActual.lean (32s)`
olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1NormArchCHArcActual.olean
```