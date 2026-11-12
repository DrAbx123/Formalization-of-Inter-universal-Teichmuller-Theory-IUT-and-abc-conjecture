# DATA-QUALITY-VPCHK — 半稳定曲线的 v_p(Δ_min) 核查

日期：2026-11-12；qpilot（A1016）。**Sage/Python 核查**；未跑 Lean。

## 1. 结论先行

**c2/C1 数据的 `v_p_Delta` 没有算错；不应改成 1。** 半稳定只保证局部**乘法约化**（Kodaira `I_n`），不保证 `v_p(Δ_min)=1`；导子 squarefree 只说明 `v_p(conductor)=1`，而 `v_p(Δ_min)=n` 可以任意大（`I_n`）。

**反例（Sage 直接验证，minimal model）**：

| label | conductor | p | `v_p(Δ_min)` | Kodaira | `v_p(conductor)` | semistable |
|---|---|---:|---:|---|---:|---|
| 858k2 | 2·3·11·13 | 13 | **21** | `I21` | 1 | True |
| 8778s5 | 2·3·7·11·19 | 7 | **24** | `I24` | 1 | True |
| 9546f3 | 2·3·37·43 | 2 | **72** | `I72` | 1 | True |
| 6555e1 | 3·5·19·23 | 5 | **31** | `I31` | 1 | True |
| 11a1 | 11 | 11 | **5** | `I5` | 1 | True |

`E.minimal_model().discriminant()` 与 `E.discriminant()` 在这些样本上逐 p 相同；`E.minimal_discriminant()` API 在 Sage 10.9 不存在（返回 None），故用 `minimal_model().discriminant()` + `Emin.local_data(p).discriminant_valuation()` 交叉核对。

## 2. 全库一致性检查

- `data/c2_invariants.jsonl`（4,154 条，N≤2000）与 `coord/ub_curves_9999.jsonl`（Sage 枚举时用 `minimal_model().discriminant()`）逐条比对 `vp_delta`：**4,154/4,154 完全一致，0 差分**（`coord/vp_minimal_check.csv`）。
- 因此 C1/local terms 使用的 `vp_delta` 是最小判别式 p 进赋值；没有把 qOrder 误当 v_p(Δ)（对 `I_n`，二者本来都等于 n）。

## 3. 修正后的 v 分布（实际：无需修正）

- **N≤2000（c2）max v = 63**：`910e3`，p=2，`I63`；
- **N≤9999 max v = 72**：`9546f3`，p=2，`I72`；
- admissible 中 p>3 的 max v = **24**（`8778s5`, p=7, `I24`）；p=13 max 21（858k2）；p=5 max31（6555e1，p=ℓ，inadmissible）；
- 分布：v≥30:343 条，≥40:88，≥50:25（N≤9999；含 p=2/5 特殊）。

## 4. 对局部项/LP 的影响

- 因为 `vp_delta` 正确，**不需要**把 v 改成 1，也不存在“修正后重算”：强行设 v=1 会破坏 `I_n` 数据（11a1 的 `I5`、858k2 的 `I21`、8778s5 的 `I24`、9546f3 的 `I72` 都会变成错误）。
- A1007/A1011/A1013/A1015 的 per-capsule / LP 数据基于该 `vp_delta`，其结论（admissible 负项、α/j² 斜率、literal min 等）不受影响；**数据质量不是 gap 来源**。
- 真正的问题仍是 qOrder 的无界性（(UB)）与 qScale 系数/label 归一化，而非 v_p(Δ) 字段。

## 5. 文件

- `coord/vp_minimal_check.csv`（4,154 行：N,label,bad_primes,vp_c2,vp_min,match,max_v）
- `coord/vp_minimal_check_samples.csv`（5 个样本的 Sage 核查值）
- `tmp/vpchk_samples.log`（Sage 原始输出）
- 本文件 `coord/DATA-QUALITY-VPCHK.md`