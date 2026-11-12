# UB-TEST — qOrder/v_p(Δ) 增大时 per-capsule 是否失效

日期：2026-11-12；qpilot（A1011）。**Python + Sage（仅枚举）**；未跑 Lean。

## 1. 数据扩展 N≤9999

枚举：`cremona_curves(N)`，N=1..9999，`E.is_semistable()` 过滤；对每条曲线取 `E.minimal_model().discriminant()`，对坏素数记录 `v_p(Δ)=qOrder`。

| 指标 | 值 |
|---|---|
| 半稳定曲线 | **21,027** |
| levels | **3,627** |
| 枚举耗时 | **20.6 s** |
| 输出 | `coord/ub_curves_9999.jsonl`（N,label,bad_primes,vp_delta） |

### 1.1 最大 v 与样本

- **max v = 72**：`9546f3`（N=9546），p=2，`v_p(Δ)=72`；admissible=True（p=2 在 c1 规则中特殊保留）；
- **max v at odd p>3**: **24**：`8778s5`；p=7，`v_7(Δ)=24`；admissible=True；
- max v at p=13: **21**（`858k2`）；
- max v at p=5（ℓ）: **31**（`6555e1`，`v_5=31`；**inadmissible**，p=ℓ 是坏位）；
- v≥31 / ≥41 / ≥51 的样本 **全部在 p=2**（部分 p=5；无 p>3 且 p≠5 的 admissible 记录）：

| 阈值 | 全记录数 | admissible 记录数 | p>3 且 p≠5 | admissible p>3 且 p≠5 |
|---|---:|---:|---:|---:|
| v≥31 | 290 | 178 | 0 | **0** |
| v≥41 | 66 | 42 | 0 | **0** |
| v≥51 | 22 | 12 | 0 | **0** |

因此 v=31,41,51 的**奇数 p>3** 样本在当前数据中**不存在**；只有 p=2（wild 特殊）或 p=5（ℓ，inadmissible）能达到这些值。

### 1.2 v 分布

全部坏位（`coord/ub_vp_distribution.csv`）：v=1:24,308；2:14,630；3:6,953；4:6,840；6:3,540；5:2,864；8:2,308；7:1,438；10:1,210；12:1,139；9:965；14:543；16:517；11:480；…；`v≥30`:343；`v≥40`:88；`v≥50`:25。

admissible 曲线（12354 条）的 p>3 最大 v 只有 **24**；p=2 最大 72；p=5 最大31（不计入 admissible）。

## 2. per-capsule 计算

采用精确 e=2ℓ=10、T/nC 公式（同 A1007/A1009）：
```
A = Σ_{p>3} v_p logp/(2ℓ)          （c1 模型 p=2,3 wild 的 T=0；p=ℓ 剔除）
T = Σ_{p>3} (sF−1) v_p logp/(2ℓ)/nC
local_i = arch_i + Σ_{p>3}[(1−1/e)logp + frac(i² v_p/(2ℓ))logp] + p=2,3 的 wild H 分摊
B_i = A + local_i − T,  i=1,2
```
`arch_1=0.1732868`, `arch_2=0.3972567`（arch_defect(2/3)）；nC=2，sF=2.5。

### 2.1 结果（admissible 12354 条）

| 量 | value |
|---|---|
| `B_i` 全值最小 | **2.514418** |
| `B_i` 最大 | 13.887579 |
| median | 8.872938 |
| **B_i < 0** | **0** |

**所有 admissible 曲线、两个 capsule 的 `A+H_i` 均 ≥0；v 增大没有产生负值。**

### 2.2 为什么 v 增大不会失效（模型内恒等）

对 p>3：
```
A − T = Σ_{p>3} v_p logp/(2ℓ) · [1 − (sF−1)/nC]
      = Σ_{p>3} v_p logp/(2ℓ) · [1 − 1.5/2]
      = Σ_{p>3} v_p logp/(2ℓ) · 0.25
      = 0.025 · Σ_{p>3} v_p logp  > 0。
```
且 `arch_i>0`，`(1−1/e)logp>0`，`frac(·)≥0`；故对**任意大 v**（p>3），`B_i = A − T + arch_i + H_i + Ind_i > 0`。v 越大，`A−T` 的余量越大；**不存在临界 v**。

p=2,3 wild 在 c1 模型中 T=0、H>0，也不产生负值（但 qOrder 不进入 T，见 caveat）。

### 2.3 大 v 样本

| curve | p | v | A | B1 | B2 |
|---|---:|---:|---:|---:|---:|
| 9546f3 | 2 | 72 | 1.098304 | **9.260054** | 12.778935 |
| 8778s5 | 7 | 24 | 6.087749 | **11.529555** | 13.450963 |
| 858k2 | 13 | 21 | 5.626183 | **7.621659** | 9.334482 |
| 6555e1（inadmissible） | 5 | 31 | 0.607993 | 7.137627 | 9.185576 |

## 3. 结论

1. **max v 从 N≤2000 的 21 增到 N≤9999 的 72**（但 max 在 p=2 wild；admissible 的 p>3 最大只有 **24**，p=7）；p=5 最大31但 p=ℓ inadmissible；v=41,51 只出现在 p=2。
2. **临界 v 未找到**：在 c1 模型（精确 e=2ℓ、T/nC）下，`A−T = 0.025 Σ_{p>3} v_p logp >0`，per-capsule `B_i` 对所有 tested v 都为正且随 v 增大；admissible 12354 条 **B_i<0: 0**。
3. **per-capsule 没有失效**；但这不证明 (UB)：p=2/5 的高 v 不进入 c1 的 p>3 q-side 项（p=2 wild T=0；p=5 剔除），而 admissible p>3 数据只到 v=24。要真正检验 (UB)，需要 **p>3 的 v≥31** 数据或证明 `v_p(q)` 一致界；当前数据不支持也不反驳 UB。
4. 一致性含义：若 UB 只用于让 per-capsule 不失效，则这里是**过度要求**——per-capsule 在模型内对大 v 更强；UB 仍可能被其他分析（误差/几何项）需要，需另行处理。

## 文件
- `coord/ub_curves_9999.jsonl`（21,027 行）
- `coord/ub_per_capsule.csv`（21,027 行：N,label,admissible,max_v,max_v_prime,vp_delta,A,B1,B2,min_B,neg）
- `coord/ub_vp_distribution.csv`
- 本文件 `coord/UB-TEST.md`