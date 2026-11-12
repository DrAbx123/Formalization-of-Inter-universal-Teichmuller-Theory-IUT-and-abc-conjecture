# PER-CAPSULE-COEFF — 精确表达式、v_p 系数与 UB 判定 (A1012)

| field | value |
|---|---|
| Status | PARTIAL (符号推导完成；alpha 未从 lana 源钉死 ⇒ 无条件性取决于 GAP-COEF) |
| 输入 | qpilot A1011: N<=9999 (21,027 条) per-capsule 无失效；p>3 max v=24；p=2 v=72；称 `A-T = 0.025 * sum v_p log p > 0` |
| 结论 | 若 `alpha <= 1/(2l)` 则 **无需 UB**（线性正系数）；qpilot 的 0.025 对应 l=5 下 alpha=3/40，需精确 Kummer 公式验证；候选 alpha 公式在 l=7 变号，不能直接推广 |

## 1. 精确 per-capsule 表达式

归一化（A1008, DECOMP-NORMALIZATION）唯一展开：
```
M = A + (1/nC) * sum_i H_i = (1/nC) * sum_i (A + H_i),
A = sum_v weight_v * v_p(q) * log p_v / (2l),          -- 无 1/nC
H_i = sum_v sum_c packetWeight(i,v,c) * componentVol(i,v,c),
```
因此 per-capsule 量取 `B_i := A + H_i`（**不是** `(1/nC)A + H_i`；A 只计一次，
`M = (1/nC) sum_i B_i`）。

componentVol 分解（lana 源）：
```
componentVol = componentVol_pos + componentVol_neg,
componentVol_pos = tame: sum_j (1 - 1/e_cj) * log p_v          (VcI.lean:435, >= 0)
                 + ind2Term (Gap.lean:756, >= 0) + archDefect (Gap.463, >= 0)
                 + shellDefect (Gap.442, >= 0),
componentVol_neg = - qScale  （theta 单位缩放项；见下）
```
设 qScale 的逐位系数为 `alpha`（待 (COEF) 钉死）：
```
qScale(i,v) = alpha * v_p(q) * log p_v,      -- 对 weight-1 的单个有限位
```
则
```
B_i = P_i + (1/(2l) - alpha) * sum_v v_p(q) * log p_v,
P_i := sum_v sum_c packetWeight * componentVol_pos(i,v,c)  >= 0.
```
（weight_v 一般时：`B_i = P_i + sum_v (weight_v/(2l) - alpha_v) v_p log p_v`。）

## 2. 偏导与符号

`∂B_i/∂v_p = weight_v/(2l) - alpha_v`（weight=1 时 `1/(2l) - alpha`）。

l=5（`l=5`, `2l=10`, `nC=2`, `sF = l(l+1)/12 = 2.5`, `sum_j j^2 = nC*sF = 5`）：
| alpha 假设 | 来源/公式 | `∂B/∂v_p` | 判定 |
|---|---|---|---|
| `1/(2l) = 0.1` | alpha 取满 A 系数 | 0 | v 无关（需常数项 P_i>=0） |
| `sF/(2l) = 0.25` | qScale = sF*A | **-0.15** | 需 UB（v 增大更差） |
| `1/(2l*nC) = 0.05` | 每 capsule 再除 nC | +0.05 | 无需 UB |
| **`3/40 = 0.075`** | `(sF-1)/(2l*nC)` | **+0.025** | 无需 UB；**与 qpilot 的 0.025 数值一致** |
| `1/(2l) - 0.025 = 0.075` | qpilot 反推 | +0.025 | qpilot 口径 |

数值核对：qpilot 的 `A - T = 0.025 * sum v_p log p` 在 l=5 下对应
`alpha = 1/(2*5) - 1/40 = 0.1 - 0.025 = 0.075 = 3/40`；即其 effective qScale 系数为 3/40，
不是 sF/(2l)=0.25。若精确 Kummer 重算给出 alpha=0.075，则 ∂B/∂v_p>0 且 v 增大更强，
**与 qpilot 观察一致**。但 3/40 是否等于 `(sF-1)/(2l*nC)` 或来自更细的 label 求和，
需用 e=2l=10 的精确公式复核（GAP-COEF）。

## 3. 判定

### 情形 (i): `alpha_v <= weight_v/(2l)` 对所有 v ⇒ **无需 UB**
则 `B_i = P_i + sum_v c_v v_p log p_v`，`P_i>=0`, `c_v>=0`, `v_p log p_v>=0`（v>=0）
⇒ `B_i >= 0` 无条件（纯算术）。对应 Lean 引理：
```lean
theorem perCapsuleArith_linear (K : Real) (c v : Fin m -> Real)
    (hK : 0 <= K) (hc : forall i, 0 <= c i) (hv : forall i, 0 <= v i) :
    0 <= K + sum i, c i * v i := by
  apply add_nonneg hK
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hv i)
```
（`K = P_i >= 0` 由 tame/ind2/arch/shellDefect 的 green 非负性；`c_v = 1/(2l)-alpha_v`。）

### 情形 (ii): 存在 v 使 `alpha_v > weight_v/(2l)` ⇒ 需 UB 或聚合
则 `∂B_i/∂v_p < 0`，`v_p` 任意大时 B_i 最终为负；必须补 `v_p(q) <= B_p` 的一致界
（GAP-UB）或做跨 capsule/label 的聚合（使得 sum c*v 的系数非负）。

### 关键风险：候选 alpha 公式在 l=7 变号
`alpha = (sF-1)/(2l*nC)`：`sF=l(l+1)/12`, `nC=(l-1)/2` ⇒
`(sF-1)/nC = (l(l+1)-12)/(6(l-1))`；l=5: 18/24=0.75<1 ⇒ 正系数；
l=7: 44/36>1 ⇒ `1/(2l)(1-(sF-1)/nC) < 0` ⇒ **需 UB**。
因此即使 qpilot 的 0.025 在 l=5 成立，也不能推出 l>=7 无条件；
必须用精确 e=2l 公式确认 alpha(l) 的 l-依赖，并逐 l 判号。

## 4. 结论

- **不能无条件**（当前未钉死 alpha；若 alpha 取 sF/(2l) 则需 UB）；
- **若**精确 Kummer 公式给出 alpha <= 1/(2l)（qpilot 在 l=5 的 3/40 情形），则
  **无需 UB**，由 §3(i) 的线性算术引理直接得 `B_i>=0`；
- qpilot 的 0.025 在 l=5 与 alpha=3/40 自洽；但 alpha 的 l-依赖未定，l=7 可能变负 ⇒
  需要 (COEF) 钉死后方能逐 l 判定；
- 若 alpha > 1/(2l)，需 (UB) 或聚合证明。

## 5. 下一步

1. 用 qpilot 的精确 Kummer 重算（e=2l, label 求和, 1/nC 位置）写出 alpha 的闭式；
2. 逐 l=5,7,11,13 计算 `1/(2l) - alpha`，判号；
3. 若全部 >=0：写 `Mzk1PerCapsuleArithActual.lean` 的线性引理（§3(i)）；
4. 若某些 l 为负：写 (UB) 显式假设 + 条件引理，并在 admissible 定义中找 (UB) 来源。