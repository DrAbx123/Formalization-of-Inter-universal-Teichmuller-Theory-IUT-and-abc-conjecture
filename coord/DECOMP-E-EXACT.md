# DECOMP-E-EXACT — 精确 Kummer e=2ℓ 重算局部项

日期：2026-11-12；qpilot（A1007）。**仅 Python**。目标：把 `hullPacket_tame` 的 e 从模型简化 e=1 改为坏乘法位 q^{1/(2ℓ)} 的 local Kummer 分歧指数 **e=2ℓ**，补 1/nC 归一化与 label 权重，重算负项并重跑 LP。

## 1. 采用公式

```
nC = 2, ℓ = l = 5, 2ℓ = 10, sF−1 = 1.5
坏乘法位 p（p∤?；p ≠ ℓ）: e = 2ℓ = 10（若 ℓ ∤ v_p(q)）
H_p = Σ_{j=1}^{nC} (1 − 1/e)·log p = nC·(1 − 1/(2ℓ))·log p = 1.8·log p   (ℓ∤v_p(q))
Ind2_p = Σ_{j=1}^{nC} frac(j²·v_p(q)/(2ℓ))·log p              （不变）
T_p = (sF−1)·v_p(q)·log p/(2ℓ) / nC = 1.5·v_p(q)·log p/10/2   （1/nC 归一化）
p=2,3 wild: 保留原 H 模型 × nC，T=Ind=0（special）
p=ℓ: 剔除（0）
label 权重: 当前模型归一化权重=1，无额外因子（非平凡 label packet 时会改变 H/Ind）
M = arch + Σ_p (H_p + Ind2_p − T_p)
```

对 ℓ | v_p(q)（**inadmissible**，按定义本应剔除）的 special 记录：`e = 2ℓ/gcd(2ℓ, v_p(q))`（如 vp=10→e=1，vp=20→e=1；只作特殊记录，不影响 admissible 统计）。

**1/nC 说明**：c1 计算器原缺 `1/nC`（C-MARGIN-FIX 已登记）。按本轮要求把 `1/nC` 加在 T 上；H 已按 `Σ_j` 得 nC 倍，Ind 保留 `Σ_j`。这是关键模型选择；若不除 T（T 保持全局 `(sF−1)A`），结果见 §3 的 caveat。

## 2. 负项统计（新 e）

输出：`coord/c1_local_terms_e_exact.jsonl`、`coord/c1_local_terms_e_exact.csv`（16,701 行）；`coord/c1_local_terms_corrected.csv` 已更新为该版本（A1006 旧候选保留为 `c1_local_terms_corrected_A1006.csv`）。

| 样本 | 负项数 | 负曲线数 | 负项和 | 说明 |
|---|---|---|---|---|
| 全 4154 | **36** | 36 | **−68.367** | **全部 inadmissible**（36/36 都是 ℓ\\|v_p(q)，v_p=10/20；p=ℓ 0 项） |
| admissible 2604 | **0** | **0** | 0 | ✅ 全部归零 |

负项分布（全样本）：p=7:18, 11:5, 17:3, 13:3, 19:2, 31:2, 29:2, 61:1；`v_p(q)` 分布：10（34 项）、20（2 项）。按 C1 admissibility 规则（ℓ|ord ⇒ inadmissible）全部剔除。

**结论：在 admissible 样本中负局部项已归零；剩余 36 项全是 inadmissible 的 ℓ|v_p(q) 曲线，不是 paper 目标样本的真实符号缺口。**

## 3. LP 重跑（特征：arch + 9 个素数区间的正部 net 和）

同一 LP/Farkas：`min t s.t. |M−Σλ_k f_k|≤t, λ≥0`；scipy HiGHS；对偶 `b·marginals=t`。

| 样本 | n | t* | max/mean 残差 | 覆盖率 t* | λ | 对偶 |
|---|---|---|---|---|---|---|
| clean 子集（无负 net） | 4118 | **0.0** | 7.1e-15 / 1.7e-15 | 100% | λ_bins=1, λ_arch≈0 | `b·y=0` |
| **admissible** | **2604** | **0.0** | 3.6e-15 / 1.4e-15 | **100%** | λ_bins=1, λ_arch≈0 | `b·y=0` |
| 全样本 | 4154 | **2.384237** | 2.384/1.067 | 0% (≤1e-3: 0.05%) | 混合（posnet/H/Ind/T 非零） | `b·y=t*` |

**admissible 精确非负分解（t*=0，系数=1）**：
```
M = Σ_{k=0}^{8} posbin_k,   λ_k = 1
 （posbin_k = Σ_{p∈bin_k} max(H_p+Ind2_p−T_p,0)；arch 含于最后一 bin；
   对 admissible 所有 net≥0，故 max 可去掉）
```
即 `M = arch + Σ_{p>3} (H_p + Ind2_p − T_p) + wild p=2,3 H_p`（admissible，e=2ℓ，T/nC）。全样本 t*=2.384 完全来自 36 个 inadmissible 负项；若把 inadmissible 剔除，t*=0。

### 3.1 关键 caveat：T 的 1/nC 归一化
- 若不把 T 除 nC（保持 `T=(sF−1)A` 全局），e=2ℓ 后仍有 **40 个负项，其中 1 个 admissible**：`858k2`, p=13, v=21，net≈−2.18；
- 只有当 `T/nC` 时 admissible 负项才归零；因此本轮结论依赖 `1/nC` 归一化假设（C-MARGIN-FIX 已指出该缺口，但 paper 的 T 公式是否带 1/nC 仍需逐行核对 `LocalEstimate`/`VcI` 的 T_v 定义）。

## 4. 仍存精确定义疑点

1. **T 的 1/nC**：本轮采用 `T/nC`；paper `T_v=(sF−1)·weight_v·ord_v(q)logp/(2l)` 是否应再除 nC 未在 paper 行级确认。若不应除，保留 1 个 admissible 负项 `858k2`（p=13, v=21）。
2. **ℓ|v_p(q) 的 special e**：`e=2ℓ/gcd(2ℓ,vp)`（vp=10/20 ⇒ e=1）是 Kummer 扩张的局部分歧估算；这 36 条按定义 inadmissible，不影响目标样本，但 exact e 仍需局部域计算确认。
3. **p=2,3 wild**：仍用 c1 的 Sage-measured H 模型 ×nC，e_wild 未按 Kummer 公式；无负项落在这里，但影响 M 绝对值。
4. **label 权重**：当前 c1 模型单 label 权重=1；非平凡 packet 需 `Σ_c w_c`，会改变 H/Ind2。
5. **arch C0**：仍为 `arch_for_nC=0.28527176`，paper 全局 `log(√2π)=1.491303`；只影响全局 M，不影响逐位符号。
6. **orderVol/different**：H 只含 tame `(1−1/e)logp`；精确 `hullPacket_finite` 还含 `shellExcess+orderVol`，可能再修正 M（当前 admissible M min 5.016>0，不影响符号）。
7. **特殊 p=ℓ**：已剔除；若 admissibility 规则改用其他 ℓ，需重算。

## 5. 结论

- **用精确 e=2ℓ + T/nC + label 权重归一化后：admissible 2604 条负项 = 0**；剩余 36 个负项全部是 ℓ|v_p(q) 的 inadmissible 曲线（v=10/20），按 C1 规则本应剔除。
- **admissible LP t* = 0.0，覆盖率 100%，λ_bin=1**，得到统一非负分解；clean 子集 4118 也 t*=0；全样本 t*=2.384 只是 36 个 inadmissible 负项造成。
- 该结论对 `T/nC` 归一化敏感：若不除 T，则 1 个 admissible 负项（858k2）仍在；需 paper 行级确认 T_v 是否带 1/nC。
- 若用户接受 1/nC，则本轮的 exact e 重算已消除 admissible 负项，LP 精确可行性成立；否则记录 858k2 为唯一 caveat。

## 文件
- `tools/c1_local_e_exact.py`（重算 e=2ℓ；输出 `coord/c1_local_terms_e_exact.jsonl/.csv`）
- `tools/decomp_lp_e_exact.py`（LP；输出 `coord/decomp_lp_e_exact_results.json`, `coord/c1_local_features_e_exact.csv`）
- `coord/c1_local_terms_corrected.csv`（= e-exact 版本；A1006 旧版 `c1_local_terms_corrected_A1006.csv`）
- 本文件 `coord/DECOMP-E-EXACT.md`