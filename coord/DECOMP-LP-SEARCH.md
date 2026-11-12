# DECOMP-LP-SEARCH — 非负局部项 LP 分解搜索

日期：2026-11-12；qpilot（A991）。**纯 Python（numpy/scipy）；未运行 Lean/Sage/WSL。**

## 1. 数据与特征矩阵

**样本**：`coord/c1_margin_v2.csv`：4154 条曲线（N 11–1995），其中 admissible 2604 条；目标 `M` 范围 **−5.570 … +5.592**，均值 2.768，中位数 2.791。
**模型常量**：`coord/c1_margin_corrected.csv` 仅提供模型层 H/T/Ind2 常量（6 行，不逐曲线对齐），用于特征命名/常数项；`S1487` 为 Lean/文档 scalar equality，无逐样本数值表。

所有候选特征 `f_k(x) ≥ 0`（可证非负的局部项/常数）：

| 特征 | 定义 | 非负性 |
|---|---|---|
| `const` | 1 | 是 |
| `arch` | `log(√2·π)`（≈1.4913） | 是（模型全局 arch 常数） |
| `logN` | `log N = Σ_{p|N} log p`（N 平方自由） | 是 |
| `nbad` | #坏素数 | 是 |
| `tame` | `Σ_{p|N} (1−1/p) log p`（tame hull buffer） | 是 |
| `invp` | `Σ_{p|N} log p / p` | 是 |
| `avg` | `log N / nbad` | 是 |
| `cnt_a_b` / `logsum_a_b` | 每个素数区间 `[a,b)` 内的坏素数个数 / `Σ log p`（区间：2–5, 5–10, 10–20, 20–50, 50–100, 100–200, 200–500, 500–1000, 1000–2000） | 是（计数/log 和） |

## 2. LP 形式

求 `λ ≥ 0, t ≥ 0`：
```
min t   s.t.   | M(x_i) − Σ_k λ_k f_k(x_i) | ≤ t   (i = 1..n)
```
等价线性约束：`Fλ − t ≤ M`，`−Fλ − t ≤ −M`，`λ,t≥0`。用 `scipy.optimize.linprog(method='highs')`。
若 `t*=0`：存在精确非负分解；若 `t*>0`：在该特征族中**不可行**，`t*` 是最优一致残差上界；HiGHS 返回对偶 marginal `y≤0`，满足 `b·y = t*`（强对偶；`Σ y = −1` 对应 t 的目标系数），可作为不可行性/残差下界的对偶证书。

## 3. 结果

### 3.1 聚合特征（const/logN/nbad/tame/invp/avg，n=4154）
- `t* = 5.577486`；残差 max 5.577、mean 2.804、RMSE 2.991；
- 覆盖率：`|resid|≤1e-6`：**0%**；`≤1e-3`：0%；`≤0.01`：0%；
- 最优 λ：只有 `avg` 非零，`λ_avg = 0.003860`（其余 0）；常数项/其它系数为 0；
- 对偶：`b·marginals = 5.577486 = t*`，marginals ≤0，Σmarginals=−1；dual 范数≈0.746。
- admissible 子集（n=2604）：`t*=4.982649`，max 4.982，mean 2.523；λ 非零：`tame` 0.009273、`avg` 0.199494；覆盖率 0%。

### 3.2 本地素数区间特征（const/arch/logN/nbad/tame/invp/avg + 9 区间计数/log和；n=4154）
- `t* = 5.570216`；max 5.570、mean 2.806、RMSE 2.993；
- 最优 λ：`logsum_20_50 = 0.006066`、`cnt_1000_2000 = 0.004555`，其余 0；
- 覆盖率：`≤1e-6`:0%；`≤1e-3`:0%；`≤0.01`:0.05%；`≤0.1`:0.31%；`≤0.5`:1.73%；
- 对偶：`b·marginals = t*`，marginals ≤0，Σ=−1。

### 3.3 结论（LP 可行性）
**在给定特征族中不存在精确非负分解**：`t*≈5.57` 与 `M` 的量级同阶，覆盖率在 1e-3 下为 0；增加局部区间计数/log 和也没有实质改善（t* 仅从 5.5775 降到 5.5702）。对偶证书给出同样的残差下界。

## 4. 候选恒等式草案（近似，不是证明）

聚合特征的最优近似：
```
M(x) ≈ 0.003860 · (log N / nbad) + R(x),   |R(x)| ≤ 5.577486
```
本地区间特征的另一种候选：
```
M(x) ≈ 0.006066 · Σ_{p∈[20,50), p|N} log p
     + 0.004555 · #{p | N : p ∈ [1000,2000)} + R(x),   |R(x)| ≤ 5.570216
```
**注意**：系数小、残差大，以上只是 LP 最优近似，不是恒等式；`R` 未被非负局部项吸收，不能作 proof-grade 分解。

## 5. 下一步（若继续）

1. 当前特征只用了 `c1_margin_v2.csv` 的 N/nbad（以及模型常量）；**真正的局部项 H_p/Ind2_p/T_p** 未逐曲线入表（`c1_margin_corrected.csv` 仅 6 行模型常量，不对齐曲线）。要得到有意义的分解，需先把 C1 计算器的逐曲线 `H_p, Ind2_p, T_p, arch, torsion` 导出为矩阵（或从 `Mzk1` 计算器生成）。
2. 有了逐项数据后，特征应为 `H_p`（或正部 `max(H_p,0)`）、`Ind2_p`、`T_p` 的局部/分组项，并显式检验每个 f_k≥0；再用同一 LP/对偶证书。
3. 若届时仍 `t*>0`，说明局部项族不足；若 `t*=0`，得到候选恒等式，再进入 Lean 的 `Finset.sum_nonneg`/`linarith` 草案。

## 文件
- `tools/decomp_lp.py`（聚合特征 LP；输出 `coord/decomp_lp_results.json`）
- `tmp/decomp_bins.py`（本地区间特征 LP；输出 `coord/decomp_lp_bins.json`）
- 本文件 `coord/DECOMP-LP-SEARCH.md`