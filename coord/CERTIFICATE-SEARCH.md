# CERTIFICATE-SEARCH — 大不等式库 + LP/组合搜索

日期：2026-11-12；qpilot（A1039）。**仅 Python（scipy HiGHS）**；目标 N≤2000 admissible（l=5, 2604 条），c1 e-exact `M=arch+H_tame+Ind2−T`。

## 1. 非负项族（`tools/certificate_search.py`）

| 类别 | 项 | 形式/说明 | 可证性标签 |
|---|---|---|---|
| tame | `H` | `Σ_p nC(1−1/(2ℓ))logp` | nonneg，MODEL-PAPER（e=2ℓ） |
| ind2 | `Ind1, Ind2` | `Σ_p frac(j²v_p/(2ℓ))logp`, j=1,2 | nonneg，MODEL-PAPER |
| frac/floor | `floor_j, frac_j` | `Σ floor(...)logp`, `Σ frac(...)logp` | nonneg |
| qScale 锚 | `qscale_j` | `Σ j² vlogp/(2ℓ)` | nonneg；IUT 系数 j²/(2ℓ) |
| 全局 | `Slog, Sv, Svl, nbad, maxv, minv, maxlog, minlog` | 素数/log/序数汇总 | nonneg |
| 按素数组 | `g{0..9}_log, g{0..9}_vlog, g{0..9}_A` | 2,3,5,7,11,13,17,19,23–50,>50 | nonneg |
| IUT 锚 | `anchor_l1=((ℓ+1)/24)Slog`, `anchor_16=(1/6)Slog` | 原系数 | nonneg |
| AM-GM | `2√(H·Ind)`, `2√(A·T)` | AM-GM | nonneg（由 H,Ind,A,T≥0） |
| Young/Jensen 型 | `H²/(1+H)`, `T²/(1+T)`, `H·Ind`, `ratio_*` | 正部/凸性形态 | nonneg（MODEL，非精确 Young） |
| Hölder 型 | `√(Σ Ind_j²)·√H` | Hölder | nonneg |
| telescoping | `Σ_j ((j+1)²−j²)·Ind_j` | 差分 | nonneg |
| 1=Σw 拆分 | `Σ_p 1/nbad`, `Slog/nbad`, `Svl/nbad` | 均匀权重 | nonneg |
| 平移 | `C_A=maxA+1−A`、`C_T`、`C_H`、`C_Ind`、`C_Slog` | 保证非负的补 | nonneg（依赖数据 max） |
| signed 扩展 | `negT=−T`, `negA=−A`, `neg1=−1` | **非**非负；只用于 exact 证书 | signed（不作非负证据） |

## 2. LP 结果

### 2.1 纯非负特征库（正部 + 平移，λ≥0）
```
t* = 0.672201（max residual 0.6722；coverage 1e−6 = 0%）
非零 λ: Ind1 .05279, Ind2 .30676, g1_log .10848, g3_log .02868,
        g4_log .06586, g4_vlog .01961, g5_log .08359, g6_log .10667,
        g7_log .10766, g8_log .13128, g9_log .11820, HInd .06991,
        H2div .66368, C_A .48793
```
贪心/多轮：`amgm_HInd → H2div → C_A → HInd → Ind2 → …` 逐步 t* 2.771→...→0.6722；15 轮/随机重启后仍 **t*=0.672201**，没有非负精确分解。

### 2.2 signed 扩展（允许 `negT`）
```
t* = 0.0
证书: M = 0.28527176·1 + 1·H + 1·Ind1 + 1·Ind2 + 1·(−T)
化简: M = arch + H + Ind2 − T   （arch=0.28527176）
```
这是原 c1 公式的重写；signed `−T` 不是非负项，因此**不构成非负分解证明**。

## 3. 判定

- **纯非负特征库**：即使加入 AM-GM/Young/Hölder/Jensen/telescoping/按 j/按素数/按 e/1=Σw 与 IUT 锚，t* 仍 **0.672201**；没有 t*≈0 的非负证书。
- **signed 扩展**：t*=0 的结构就是 `M=arch+H+Ind−T`，没有新内容；说明缺口是 `−T`（qScale 负项）无法用非负项表示。
- 要得到真正非负证书，需要新的**正项**（如 LGP/theta hull 的 q^{j²} 正缩放、exact orderVol/different）或允许 signed qScale 项；当前不等式库内无解。

## 文件
- `tools/certificate_search.py`（可复跑）
- `coord/certificate_search_results.json`（positive_full / signed_full / greedy / top_univariate）
- `coord/certificate_search_features.csv`（2604 条曲线 × 70 特征 + M）
- 本文件 `coord/CERTIFICATE-SEARCH.md`