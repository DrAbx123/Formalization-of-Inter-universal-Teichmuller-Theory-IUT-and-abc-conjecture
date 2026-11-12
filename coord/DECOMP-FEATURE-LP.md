# DECOMP-FEATURE-LP — 大特征库 LP 分解搜索

日期：2026-11-12；qpilot（A1034）。**仅 Python（scipy HiGHS）**；N≤2000 admissible（l=5, 2604 条）；目标 M 用 c1 e-exact 局部项：`M=arch+H+Ind2−T`。

## 1. 特征库

逐曲线聚合（由 `coord/c1_local_terms_e_exact.jsonl`，逐位 p）：

- 主项：`arch, H_tame, Ind2, T, A=Σ v_p logp/(2ℓ)`；
- 全局：`Σlogp, Σv, Σvlogp, const`；
- 逐 j：`Ind1, Ind2, Indmax, Indmin, floor1, floor2, frac1, frac2`（j=1,2）；
- 极值：`minv, maxv, minlog, maxlog`；
- 乘积/比值：`H*Ind, A*H, T*H`；
- 平移特征：`C_T=maxT+1−T`，`C_A=maxA+1−A`（非负）；
- signed 特征：`negT=−T, negA=−A, neg1=−1`（供精确线性组合）。

## 2. LP 结果

### 2.1 signed 特征库（允许负值特征，λ≥0）
```
t* = 0.0（max residual 2.1e−14，coverage 100%）
非零系数: arch=1, H=1, Ind1=1, Ind2=1, negT=1
⇒ M = arch + H + Ind1 + Ind2 − T
```
这是原 c1 公式的重写（Ind1+Ind2=Ind2_total），**不是新恒等式**；但它确认了特征库与目标一致，且精确分解需要 signed 的 `−T` 项。

### 2.2 positive 特征库（所有特征非负，λ≥0）
```
t* = 0.848852（max residual 0.848852；coverage |r|≤1e−6 = 0%）
非零: H=0.682724, Ind2=0.068620, H*Ind=0.085170, C_A=0.434607
```
**没有找到精确非负分解**；t* 0.8489 是正特征族的最优残差。

### 2.3 贪心/稀疏化（positive 库）
前向选择逐步最小化 t*：
```
H → Ind → C_A → H*Ind → Ind2 → const → arch → A → Slog → Sv → Svl ...
t*: 3.835 → 2.010 → 1.333 → 0.867 → 0.849（此后不再下降）
```
最优仍停在 **t*=0.848852**，与全 positive 库相同；没有稀疏子集达到 0。

## 3. 判定

- **t*=0 只能在允许 signed 特征（`−T`）时达到**；positive 特征族最优 t*=0.848852，不能精确分解；
- 原因是目标 M 含 `−T`（qScale 负项），而 λ≥0 + 非负特征无法产生负贡献；任一非负特征组合要表示 −T 必须引入带符号项或负常数；
- 大特征库中的 per-j/frac/floor/极值/乘积项**没有**把 positive t* 降到 0；
- 若要求 proof-grade 非负分解，需要**新的非负正项**（如 LGP/theta hull 正缩放、exact orderVol/different）来吸收 −T，或允许 signed qScale 项；当前特征库内不存在纯非负精确分解。

## 文件
- `coord/decomp_feature_lp_features.csv`（2604 条曲线 × 特征；目标 M 与主要特征）
- `coord/decomp_feature_lp_results.json`（signed/positive/greedy 的 λ、t*、coverage）
- 本文件 `coord/DECOMP-FEATURE-LP.md`