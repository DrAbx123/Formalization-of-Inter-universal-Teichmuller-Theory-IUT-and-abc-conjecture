# EXPLORATION-B-B1 — 路线 B1：最优证书搜索（N≤500 半稳定曲线）

**Status: NUMERIC**（脚本 + 数据；无 Lean 代码）。日期：2026-11-12；qpilot（A921/A928）。
**试金石（touchstone）: deferred** —— B1 只做数值判定，未做证明尝试；B2 未启动。

## 1. 做了什么

### 1.1 扩展样本
- **N ≤ 500 的全部半稳定曲线**：Sage `cremona_curves(N)` 枚举 + `E.is_semistable()` 过滤；
- 样本：**198 个 level、941 条曲线**（全部 N 为 squarefree，符合半稳定）；
- 每条：`r_f = E.congruence_number()`、`deg φ = E.modular_degree()`；总耗时 **13.57s**；
- ARC 核对：**941/941 全部 `deg φ = r_f`**（Agashe–Ribet–Stein；样本 N 均无平方因子）；
- 数据：`coord/b1_curves_500.json`（941 行）；`r_f` 分布广泛，max r_f = **21120**。

### 1.2 证书搜索
- 脚本：`tmp/b1_cert4.sage`（及前序 `b1_cert.sage`/`b1_cert2.sage`/`b1_cert3.sage`）；
- 证书定义：整系数 Hecke 多项式 `P`，使 `P(g)=0` 对所有其它新形式 `g`（同层 + 真因子的 oldforms），且 `|P(f)| = r_f`；
- 搜索策略（逐级）：
  1. 无其它形式 ⇒ 常数 `P = r_f`（support 0, degree 0）；
  2. 单变量 `Q_p(T_p) = ∏_{g≠f} minpoly(a_p(g))`，若 `val_p = Q_p(a_p(f))` 整除 `r_f`，取 `P=(r_f/val_p)Q_p`（support 1, degree = Σ deg minpoly）；
  3. 度 1 线性组合 `P = Σ c_p T_p`：把“P 杀所有其它形式”写成整数线性方程组，用整数核 + 目标 `Σ c_p a_p(f)=r_f` 求解，并贪心降 support（support ≤ 1 后停止）；
  4. 失败则记录 `found=False`（不声称不存在，只是本搜索未找到）。
- 输出：`coord/b1_certificates.csv`（941 行）：`N,curve,r_f,deg_phi,found,type,support,max_prime,degree,max_coeff,value,coeffs,primes,n_newforms,n_other,n_same_level_other,mod_min,mod_max,reason`。
- **搜索限制**：非穷尽（只到 support≤3/度≤24 的候选族；未解大整数规划）；因此 `found=False` ≠ 不存在；判定只基于“实际找到的证书”。

## 2. 数据/散点

### 2.1 证书发现率（按 N 分箱）

| N 区间 | 曲线数 | 找到证书 | 发现率 | 找到证书的平均 degree | 最大 degree |
|---|---|---|---|---|---|
| 1–99 | 146 | 101 | **69.2%** | 1.59 | 6 |
| 100–199 | 191 | 7 | 3.7% | 9.14 | 15 |
| 200–299 | 203 | 0 | **0%** | — | — |
| 300–399 | 198 | 1 | 0.5% | 24 | 24 |
| 400–499 | 203 | 0 | **0%** | — | — |

- 总计：**109/941 = 11.6%** 找到（constant 30、univariate 56、linear 23；最终 support 全部 ≤1）；
- 找到证书的 `r_f` 最大仅 **144**（样本 r_f 最大 21120）；高 `r_f`/高 N 全部未找到。

### 2.2 散点与拟合（仅 found 子集，n=109）

| 量 | 与 log N 的相关 | log–log 斜率 | 说明 |
|---|---|---|---|
| degree | **0.963** | **1.47**（n=79, degree>0） | degree 随 N **多项式增长**（≈ N^1.47），不是 `(log N)^k` |
| max_prime | 0.52 | −0.398（偏，因高 N 找不到） | 发现的证书 max prime 最大 43；高 N 缺失导致负斜率无意义 |
| max_coeff | 0.665 | — | 系数大小随 N 上升，但样本偏小 |

- 关键事实：**发现率从 69% 断崖到 ~0（N≥200）**；degree 在 found 子集上随 N 多项式增长；没有任何“不依赖曲线的构造规律”（support/最大素数/次数随 N 无稳定模式）。

### 2.3 交叉核对
- B0 的 43/43 ARC 通过；B1 扩展到 941/941 通过；
- B0/LMFDB：LMFDB API 不可用（reCAPTCHA），全部数据来自 Sage/Cremona；无需外网。

## 3. 判定：**停（STOP）**

按 `EXPLORATION-ROUTES.md` B1 判定：

- **判定（有戏）**要求：最大素数/次数随 N 至多按 `(log N)^k` 增长，且出现不依赖曲线的构造规律。
- 实测：
  1. **degree 随 N 多项式增长**（log–log 斜率 ≈ **1.47**，corr 0.963），不是 `(log N)^k`；
  2. **发现率随 N 崩塌**：<100 为 69.2%，100–199 为 3.7%，200–499 近 0；说明证书复杂度/搜索难度随 N 急剧上升（至少当前证书族不够）；
  3. 无构造规律：support 全 ≤1、max prime/degree 分布不规则；高 r_f（max 21120）完全未覆盖；
  4. 系数大小/最大素数也没有随 N 的稳定 log 型界。

**结论：B1 = 停；B2 不启动。**

**免责**：这是“在给定证书族（constant / 单变量 Q_p / 度 1 线性）下的搜索结果”，不是对“低复杂度证书不存在”的证明；但按 B1 的数值判定规则（有戏需明确 `(log N)^k` 规律），当前证据明确为“停”。

## 4. 下一步（记录，不启动 B2）

1. 若以后重启 B1：需要更一般的证书族（高 support 整数规划、多变量 Hecke 多项式、分步证书），并单独估计搜索复杂度；当前数据不足以支持 B2；
2. 记录 B1 的三个可复用产物：`coord/b1_curves_500.json`（样本）、`coord/b1_certificates.csv`（证书记录）、`tools/b0_modular.sage`（B0 管线）；
3. 试金石：**deferred**（B1 无数值→证明的桥；不写 Lean，不声称定理）；
4. 外部输入登记：Sage/Cremona/ARC 均为外部/数值输入；未进入 Lean。

### E-table（环境/外部依赖）

| 项 | 状态 | 证据/用法 |
|---|---|---|
| Sage | ✅ 10.9（WSL Ubuntu-24.04） | `cremona_curves`, `modular_degree`, `congruence_number`, `ModularSymbols`, `newforms` |
| Cremona 数据库 | ✅ 随 Sage | 941 条半稳定曲线、N≤500；`E.label()` |
| sympow | ✅ PATH 前缀已由 lead 解决 | 本批 N≤500 `modular_degree` 未显式调用/未报错；大 N 时按需 |
| ARC（Agashe–Ribet–Stein） | ✅ 数值核对 | `deg φ = r_f`：941/941；样本 N 全 squarefree |
| LMFDB API | ❌ 被 reCAPTCHA 拦截 | 本网络不可用；未使用 |
| Lean | — | B1 不写 Lean；Status=NUMERIC |

### 文件
- `coord/b1_curves_500.json`：941 条曲线样本（N, label, r_f, deg_phi）。
- `coord/b1_certificates.csv`：941 行证书搜索结果（109 found；type/support/max_prime/degree/max_coeff/coeffs/primes/…）。
- `tools/b0_modular.sage`：B0 管线；B1 使用 `tmp/b1_cert4.sage`（保留在 tmp）。