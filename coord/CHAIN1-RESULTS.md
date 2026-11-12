# CHAIN1-RESULTS — §14 链一（算术 Kodaira–Spencer / jet）判定实验

日期：2026-11-12；执行：qpilot（A879）。**判定实验，不是定理**；数据来源见每节。

## 0. 结论（先给）

**链一：否决（NO）。** 在显式曲线 `E : y² + xy = x³ + 5`、`p = 5`、`l = 7` 的判定实验上：

1. 在基域（e=1，tame）的 V 位，κ_σ 的整性亏量 `(j²−j′²)L/14` 为正而壳容量 `(1−1/e)L = 0`，**整性失败**；
2. 即使按 IUT 的 `K ⊃ E[30]` 取 p=5 的分歧提升 `e = 5`（壳容量 `4L/5`），使 κ_σ 在 V 位整性通过，**乘积公式仍迫使 arch 位的 Gaussian 极点精确等于 −V 位增益**（非 V 位为 0），净正项为 0（与 §9 的 0=0 同型）；按 §14 判据“极点抵消 ⇒ 否决”，链一被否决；
3. 需要什么才能翻案：一个**非零的截断 arch 项修正**，或**非 V 位的正贡献**，使 V 位增益不被整体抵消；当前数据（tame/无贡献的非 V 位 + 标准 Gaussian 极点）没有这种项。

## 1. 显式数据

| 项 | 值 | 来源 |
|---|---|---|
| 曲线 | `E : y² + xy = x³ + 5` | `LeanFormal/IUT/Foundations/Geometry/ConcreteSplitCurvePadic.lean`（green：`concreteSplitCurveLocal`） |
| 坏位 p | 5 | 同上（`concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five`） |
| 约化型 | split multiplicative（nodal, 切向 T(T+1)） | green：`concreteSplitCurveLocal_hasSplitMultiplicativeReduction`、`..._tangentPolynomial_splits` |
| `v_p(Δ)` | 1 | green：`concreteSplitCurveLocal_delta_valuation_lt_one`（minimal） |
| `c₄` | 单位（`v_p(c₄)=0`） | green：`concreteSplitCurveLocal_c₄_valuation_eq_one` |
| 基域 p 处 e, f | e=1, f=1（ℚ_5 tame） | 标准；ℚ 上坏位不分歧 |
| q 的归一化次数 | ord_p(q)=1 | 与 `v_p(Δ)=1` 一致（split mult 时 q 的阶 = 判别式指数，本文采用） |
| l | 7 | 选 l=7（≥5，l ≠ p） |
| l* | 3（(l−1)/2） | §6.1 |
| s | 4（(l+1)/2） | §6.1 |
| L | log 5 | 记号 |
| A | `log q/(2l) = L/14` | θ 值 `q^{j²/2l}` 的赋值单位 |

## 2. jet 两侧次数（j = 1,2,3）

| j | hull 侧 `−(j+1)D`，D=L | theta 侧 `−j²A = −j²L/14` |
|---|---|---|
| 1 | −2L | −L/14 ≈ −0.0714L |
| 2 | −3L | −4L/14 = −2L/7 ≈ −0.2857L |
| 3 | −4L | −9L/14 ≈ −0.6429L |
| Σ_{j=1..3} | −9L | −L（Σj²=14，14/14=1） |

要求（L6 型）：`(s−1)·A ≤ V`，即 `3·(L/14) = 0.2143L ≤ V`。

## 3. κ_σ 逐位赋值表

候选定义：`κ_σ` 的整性亏量（非交换部分）在 V 位 w 上取
`defect_w(j,j′) = (j²−j′²)·ord_w(q)/(2l)·L = (j²−j′²)L/14`；
壳容量 `capacity_w = h_w·L`，`h_w = 1−1/e_w`（tame 且 p>e+1）。

### 3.1 基域（e=1，tame）

| V 位 | e | h_w | ord(q) | defect (2,1) | defect (3,2) | defect (3,1) | capacity | 吸收? |
|---|---|---|---|---|---|---|---|---|
| p=5 | 1 | 0 | 1 | 0.2143L | 0.3571L | 0.5714L | 0 | ✗ 全部整性失败 |

### 3.2 分歧提升（IUT 的 K 含 E[30]；Tate 曲线加 n-分点给出 e=n，取 e=5）

| V 位 | e | h_w | defect (2,1) | defect (3,2) | defect (3,1) | capacity | 吸收? |
|---|---|---|---|---|---|---|---|
| p=5 | 5 | 4/5 | 0.2143L | 0.3571L | 0.5714L | 0.8L | ✓ 全部吸收（余量 0.0286L…0.2286L） |

### 3.3 非 V 位

| 位的类型 | ord(q) | different d | defect |
|---|---|---|---|
| 非 V 的有限位 | 0 | 0（tame/未分歧） | 0 |
| arch 位 | — | 标准 Gaussian 极点 | 见 §4，等于 −V 位增益 |

## 4. Gaussian 极点 / 乘积公式检查（关键否决点）

§9 的恒等式：对全体位求和，乘性位的增益与 arch 位的 Gaussian 极点精确抵消。
本数据中非 V 位贡献为 0，因此若 V 位增益为 `G := (j²−j′²)L/14 > 0`，则

```
Σ_{all w} defect_w = G_V + 0 + arch = 0   ⇒   arch = −G_V
```

即 V 位的正项在**整体次数**中被 arch 极点精确抵消，净正项 = 0（0=0 同型）。
即使 e=5 使 κ_σ 在 V 位整性通过（§3.2），没有非零的整体态射次数可得，链一的第二个箭头
（“非零整态射 ⇒ 次数不等式”）失效。按 §14 判据：**极点抵消 ⇒ 否决**。

## 5. 判定与翻案条件

| 判据 | 结果 |
|---|---|
| V 位 κ_σ 非零 | ✓（defect = (j²−j′²)L/14 > 0，j>j′） |
| V 位整性 | e=1：✗；e=5：✓（被 Ind1,2,3 型壳吸收） |
| 极点是否抵消 | ✗ **抵消**：arch = −V 增益，整体净 0 |
| **总判定** | **否决** |

**翻案所需新内容（缺一不可）**：(i) 一个**非零的截断 arch 项修正**（例如 Arakelov 归一化在 V-截断上留下比 Gaussian 极点小的 arch 项），或 (ii) 非 V 位的正贡献（不同/non-tame 处理）使其不被整体抵消。这两者在当前仓库数据与 §9 恒等式中都不存在——与 §14 作者自己的“已知障碍：Gaussian 极点”一致。

**未核**：e=5 的分歧指数来自 Tate 曲线加 5-分点的标准事实，未在仓库中逐条验证；q 的归一化阶=1 采用 split mult 标准公式；arch 项的具体 Arakelov 归一化未计算（只用了 §9 的抵消恒等式）。

## 6. Lean 接口（draft，green）

`tmp/sheaf/xif/paper/Mzk1Chain1JetActual.lean`（EXIT=0，olean=True）：
- `gradedHullDegree`, `gradedThetaDegree`；
- `kappaDefect`, `hullAllowance`, `Absorbed`；
- `tame_five_not_absorbed : ¬ Absorbed 2 1 1 (log 5) 1 7`（e=1 整性失败）；
- `ramified_absorption_iff`（分歧阈值 `(3/14) ≤ (1−1/e) log p`）；8 行状态表。
这些只是实验的算术核，不是链一的定理；文件头明确记录“设计对象、未验证”。