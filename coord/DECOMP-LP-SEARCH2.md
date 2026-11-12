# DECOMP-LP-SEARCH2 — 逐曲线局部项导出 + LP/Farkas 重跑

日期：2026-11-12；qpilot（A1005）。**仅 Python（numpy/scipy）；未运行 Lean/Sage/WSL。**

## 1. 逐曲线局部项导出

新增 `tools/c1_local_export.py`（扩展 C1/c1_batch 的逐位公式），用 `data/c2_invariants.jsonl` + `coord/c1_margin_v2.csv` 导出：
- **`coord/c1_local_terms.jsonl`**：**16,701 行 / 4,154 条曲线**；字段 `N, label, p, ord_p_q, H_p, Ind2_p, T_p, arch, admissible, model, note`；`p=0` 行是全局 arch（`arch = arch_for_nC(2) = 0.28527176`），坏素数 `p>3` 为 odd semistable multiplicative（`e=1, H_p=0`），`p=2,3` 为 wild model（`H=(1−1/p)logp, T=Ind=0`），`p=ell=5` 标记 excluded。
- 所有行 `model='MODEL-PAPER'`；逐曲线 `M = arch + Σ_p (H_p+Ind2_p−T_p)` 与 `coord/c1_margin_v2.csv` 的 M **逐条核对：M_mismatch = 0**。
- 逐曲线特征汇总：`coord/c1_local_features.csv`（arch/H/Ind/T/posnet/negabs/9 个素数区间的正部 net 和）。

## 2. LP 设定与结果

特征均为**非负**：`arch`、`posbin_k = Σ_{p∈bin_k} max(H_p+Ind2_p−T_p,0)`（9 bins，2–5,…,1000–2000；`p=0` 的 arch 落入最后一 bin）、以及正部聚合/`H,Ind,T`（非负）。LP：`min t s.t. |M−Σλ_k f_k|≤t, λ≥0`，scipy HiGHS；对偶 marginal 满足 `b·y=t*`。

### 2.1 clean 子集（所有局部 net=`H+Ind2−T` ≥0）
- 子集：**3818/4154 条曲线**（全部局部 net 非负；无负部）；
- **`t* = 4.93e-7 ≈ 0`**（数值零）；`max_abs=5.6e-7`，`mean_abs=2.5e-7`；覆盖率 `|r|≤1e-6/1e-3/0.01` 均为 **100%**；
- 最优 λ：`λ_{posbin_k}=1`（k=0..8），`λ_arch≈0`（因 arch 在最后一 bin；等价于 arch 系数 1）；
- 对偶：`b·y=t*`，marginals≤0，Σ=−1。

### 2.2 全样本 / admissible
- **全 4154 条**：`t* = 5.570438`；max/mean 残差 5.570/2.809；覆盖率 ≤1e-6/1e-3 为 **0%**；最优 λ 仅两个 bin 非零（0.00849,0.00078），其余 0；对偶 `b·y=t*`。
- **admissible 2604 条**：`t* = 4.760991`；max 4.761；覆盖率 0%；对偶同样成立。

## 3. 负局部项与缺失/符号诊断

- 全样本中有 **336 条曲线**含负局部 net；合计 **340 个负项**，负部和 **−398.13**（max 单曲线负部和 **7.194**，`1870h2`）；
- 负项集中在 `p=7`（128 项）、`11`（43）、`13`（35）、`17`（28）、`19`（26）、`23`（14）、`29`（9）、`31`（8）等奇数半稳定坏位；原因：`H_p=0`、`Ind2_p` 不足以抵消 `T_p`，即 `T_p > H_p+Ind2_p`；
- **λ≥0 无法表示负项**：`M = Σ posbin − Σ negabs`，而 `negabs` 必须作为负系数项；当前非负局部特征族无法精确吸收它。故全样本 `t*=5.57` 不是数值误差，而是**符号/正性缺口**；
- clean 子集恰好无负项，故 t*≈0 并给出精确候选恒等式。

## 4. 候选非负分解（clean 子集，exact）

对 3818 条 clean 曲线：
```
M = Σ_{k=0}^{8} posbin_k,   λ_k = 1（posbin_k 为非负局部正部 net 和；arch 含于最后一 bin）
equiv: M = arch + Σ_{p>3} max(H_p + Ind2_p − T_p, 0) + wild p=2,3 的 H_p（当前模型 T/Ind=0）
```
该恒等式在 clean 子集上由 `t*=4.9e-7`、100% 覆盖率支持；它是 **MODEL-PAPER** 恒等式（arch/Ind2 为模型，不是精确 C1），不可直接作 Lean 定理。

**全样本缺失项**：需要一个**非负项**表示 `−Σ negabs` 的负贡献，或证明在负项位 `H_p+Ind2_p ≥ T_p`（模型数据显示不成立；336 条反例）。在当前局部项族中二者都没有，因此全样本无法做到 `t*=0`。

## 5. 结论/下一步

1. **clean 子集（3818）**：LP 找到精确非负分解（t*≈0，覆盖率 100%，系数=1）——可作为候选恒等式草案；但只对 clean 子集，需在 Lean 中先证明对应局部项的 `≥0` 与该子集条件。
2. **全样本**：t*≈5.57（admissible 4.76），不是可忽略残差；负局部项（336 条、340 项，p=7/11/13/…）是符号障碍，λ≥0 无法吸收；LP 对偶证书确认残差下界。
3. 若要把全样本做到 t*=0，需要：
   - 证明 `H_p+Ind2_p ≥ T_p` 对所有坏位（模型下为假，需要更精确的 H/Ind2 或额外非负缓冲项）；或
   - 引入允许负号的局部项/不等式（改变 λ≥0 设定）；或
   - 把负部作为**目标**的一部分（例如先证 `Σ posbin ≥ Σ negabs` 是另一组局部不等式）。
4. 当前数据只支持 clean 子集的 exact 恒等式；全样本仍是无精确非负分解。

## 文件
- `tools/c1_local_export.py`（逐曲线局部项导出）
- `coord/c1_local_terms.jsonl`（16,701 行）、`coord/c1_local_features.csv`（4,154 行）
- `tools/decomp_lp_local.py`（LP）、`coord/decomp_lp_local_results.json`
- 本文件 `coord/DECOMP-LP-SEARCH2.md`