# LITERAL-RECALC — literal min 公式重算与 K_i 的 v 依赖

日期：2026-11-12；qpilot（A1015）。**仅 Python**。输入：N≤2000 `data/c2_invariants.jsonl`（4,154 条；样本 8778s5 取自 N≤9999 库）。

## 1. 采用的 literal 公式

按 `ALPHA-DERIVATION.md`（abc）与 A1015：
```
A := Σ_{p>3, p≠ℓ} v_p logp/(2ℓ)              （按 place 的 q-side；weight=1）
qScale_{i,j} := j² · m_i · logp/(2ℓ)
             = j² · ρ_i · A,   ρ_i = m_i/ord_ref,  m_i=min_l ord(q_{v_l})
K_i := H_tame_i + wildH_i + Ind2_i + arch_i + shellDefect_i
B_i := A − qScale_{i,j} + K_i = A + K_i − j² ρ_i A
聚合: M = (1/nC) Σ_i B_i
```
逐项归属：

| 项 | 位置/公式 | v 依赖 |
|---|---|---|
| `A` | q-side 主项，系数 1，`Σ_p v_p logp/(2ℓ)` | 线性于 v |
| `H_tame` | 每 capsule：`nC·(1−1/e)logp`，`e=2ℓ`（admissible ℓ∤v） | **不随 v 变**（e 固定；只有 ℓ|v 的 inadmissible 特殊 e 会跳） |
| `wildH` | p=2,3 的 c1 模型 H2/H3（每 capsule） | 不随 v 变（c1 设 T=0；p2/3 的 qOrder 不进入） |
| `Ind2` | `Σ_p Σ_l frac(l² v_p/(2ℓ)) logp`（每 capsule；见下） | **周期性/有界**，无线性增长 |
| `arch` | `arch_defect(i+2)`，每 capsule 常数 | 常数 |
| `shellDefect` | c1 模型 0（精确 hull 的 `orderVol`/different 未入） | 模型 0 |
| `qScale` | **T 的位置**：`j²ρA`，不是单独的 T；1/nC 只在聚合外层 | 线性于 v，系数 `j²ρ` |
| label 权重 | 当前单 label，归一化 `w=1`；非平凡时乘 `∏w` | — |

`1/nC` 只出现在聚合 `M=(1/nC)Σ_i B_i`；per-capsule `B_i` 本身不再除 nC（A 也只计一次，通过外层平均）。

## 2. 0.025 的来源

对单个 place，`B` 的 v 斜率为
```
dB/dv = (1/(2ℓ)) · (1 − j²ρ)
```
取 **j=1, ρ=3/4, l=5**：`(1/10)(1−0.75)=0.025`。因此之前 A1011 的 `0.025·Σv logp` **正是 literal 公式在 j=1、ρ=3/4 的这一项**。

- 它不是 e=2ℓ 的 H 产生的：H_tame 是 `(1−1/(2ℓ))logp` 的常数（不随 v），不产生 v 斜率；
- 也不是把 T 另加：`T` 就是这里的 qScale 项；
- 旧“uniform qScale”写法 `B=A+K−(sF−1)/(nC)·A` 在 l=5 且 j=1 时等价于 `ρ=(sF−1)/nC=3/4`（所以数值 0.025 吻合），但**对 j≥2 不对**：literal 用 `j²ρ`，旧写法用固定的 `(sF−1)/nC`；二者只在 j=1/l=5 巧合一致。

## 3. 样本（l=5, ρ=3/4）

### 858k2（p=13, v=21）
- `A = 5.626183`；`H_tame+wildH = 10.012102`；`Ind2 = 2.481422`；`arch = [0.173287, 0.397257]`；`shellDefect=0`；
- `K_1 = H+Ind+arch_1 = 12.666811`；`K_2 = 12.890781`；
- `qScale_1 = 1²·0.75·A = 4.219637`；`qScale_2 = 4·0.75·A = 16.878549`；
- `B_1 = A+K_1−qScale_1 = 14.073357`；`B_2 = A+K_2−qScale_2 = 1.638415`；
- `M = (B_1+B_2)/2 = 7.855886`。

### 8778s5（p=7, v=24；N≤9999 样本）
- `A = 6.087749`；`H_tame+wildH = 14.197822`；`Ind2 = 6.089297`；`arch = [0.173287, 0.397257]`；`shellDefect=0`；
- `B_1 = 21.982343`；`B_2 = 8.508876`；`M = 15.245609`。

## 4. K_i 的 v 依赖（关键结论）

- `H_tame`：`nC·(1−1/(2ℓ))logp`，对 admissible（ℓ∤v）**e=2ℓ 固定，不随 v 变**。只有 ℓ|v 的 inadmissible 特殊 e 会跳，但不在样本；
- `Ind2`：`Σ_l frac(l²v/(2ℓ))logp`，随 v 周期性变化，**有界**（每项 <logp），不是线性增长；
- `arch`/`shellDefect`/`wildH`：常数（模型下 shellDefect=0）；
- 因此 **`K_i` 没有随 v 的线性增长**，无法抵消 `−j²ρA` 的负斜率；若 `j²ρ>1`，`B_i` 最终为负——只能靠 (UB) 或额外正项。

## 5. 数值结果（literal 公式，ρ=3/4；N≤2000）

| l | nC | admissible | neg B_i 曲线 | min B_i | neg M 曲线 | min M |
|---|---:|---:|---:|---:|---:|---:|
| 5 | 2 | 2604 | **0** | 1.638415 | 0 | 4.596637 |
| 7 | 3 | 3015 | **0** | 1.511850 | 0 | 4.937194 |
| 11 | 5 | 3561 | **1**（`30a8`, max v=12, B=−0.719238） | −0.719238 | 0 | 7.917342 |
| 13 | 6 | 3674 | **3**（`66c4` v=10, `30a8` v=12, `210e8` v=16；min −2.517864） | −2.517864 | 0 | 8.330624 |

- **聚合 M 在所有 l 下均 ≥0**（negM=0）；
- **per-capsule B_i 在 l=11/13 已出现负值**（j 大的 capsule；负斜率所致）；l=5/7 在 N≤2000 数据内仍正，但 j≥2 的斜率已为负（l=5 j=2: -0.2/A-unit），只是样本 v 未越过临界点；
- 临界 v 方向：`B_i = K_i + c_i A`，`c_i=(1−j²ρ)/(2ℓ)`；对 l=5 j=2, `c=−0.2`，858k2 的 `B_2=1.638>0`，但 v 再增大将变负（K 有界、Ind 有界）。

## 6. 对齐结论

1. **0.025 = literal j=1,ρ=3/4,l=5**；这是 per-capsule j=1 的斜率，不是所有 j 的均匀斜率。
2. **literal j≥2 斜率为负**（`1−j²ρ`）；`K_i`（tame H、Ind2、arch、shellDefect）**没有 v 线性增长**，不能抵消；因此 j≥2 的 per-capsule 需要 (UB) 或额外正项。
3. **聚合 M 仍 ≥0**（所有 l，N≤2000）：per-capsule 失败不等于聚合失败；聚合是更弱的充分条件（如 literal min/hull 取 j=1 或 min_l）。
4. 旧 uniform qScale（0.025 对每个 capsule）只是在 l=5/j=1 的巧合；不能替代 literal `j²ρ`。

## 文件
- `coord/literal_recalc.csv`（l=5/7/11/13 合并）
- `coord/literal_recalc_l{5,7,11,13}.csv`
- `coord/literal_recalc_summary.csv`
- 本文件 `coord/LITERAL-RECALC.md`