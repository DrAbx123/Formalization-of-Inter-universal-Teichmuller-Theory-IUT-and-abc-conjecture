# EXPLORATION-B-B0 — 路线 B0：计算环境与数据管线评估

日期：2026-11-12；qpilot（A915/A916）。**不写 Lean；仅数据与脚本。**

## 1. 做了什么

### 1.1 环境结论
| 环境 | 状态 | 说明 |
|---|---|---|
| Windows Python 3.13.11 | ✅ | sympy 1.14、numpy、scipy、python-flint 可用 |
| `cypari2`（Windows pip） | ❌ | `pip index versions cypari2` 有版本但 **无 Windows wheel**；`pip download --only-binary :all:` 失败；无 PARI/GP 二进制 |
| Sage | ✅ **WSL Ubuntu-24.04, SageMath 10.9** | `/opt/miniconda/envs/sage/bin/sage`；`cremona_curves`、`E.modular_degree`、`E.congruence_number`、`CuspForms(Gamma0(N),2).newforms`、`ModularSymbols(...).integral_basis`、`hecke_matrix` 均实测可用 |
| LMFDB HTTP API | ❌ 被反爬拦截 | `https://www.lmfdb.org/api/...` 全部返回 **Google reCAPTCHA challenge 页面**（含 `ec_curvedata`/`newforms`/api root）；`api.lmfdb.org` DNS 失败、`beta.lmfdb.org` 仅 JS、`cloud.lmfdb.org` DNS 失败。**本网络不可用。** |
| 离线数据库 | ✅ | Sage 自带 **Cremona 椭圆曲线数据库**（`cremona_curves(N)`）；模形式/Hecke 由 Sage 现算。仓库内无 LMFDB 离线 dump。 |

**结论：B0 可行，走 WSL Sage 10.9；不需要 LMFDB API。**

### 1.2 脚本
- `tools/b0_modular.sage`：
  - 枚举 `N ∈ [1,30]` 的 `cremona_curves(N)`，按 `E.is_semistable()` 过滤；
  - 对每个 N：`ModularSymbols(Gamma0(N),2)` 的 `cuspidal_submodule().integral_basis()`（整基，记录 ambient 坐标），`C.hecke_matrix(p)`（`p ≤ 23`，检查整性并保存矩阵），`CuspForms(Gamma0(N),2).newforms(names='a')` 的 q-展开/系数；
  - 对每条半稳定曲线：`E.label()`、`E.conductor()`、`E.congruence_number()`（`r_f`）、`E.modular_degree()`（`deg φ`）；
  - 输出 `coord/b0_modular_data.json`（33KB，全部基/矩阵/系数）与 `coord/b0_data.csv`（汇总）；
  - 已知值核对：11a1:1、14a1:1、37a1:2。

运行命令（WSL）：
```bash
wsl -d Ubuntu-24.04 -e bash -lc 'export PATH=/opt/miniconda/envs/sage/bin:/usr/bin:/bin:$PATH; cd /mnt/d/lean && sage tools/b0_modular.sage'
```
实测耗时 **2.93s**（N≤30），errors=0。

## 2. 数据表

### 2.1 样本
- **半稳定曲线**：8 个导子水平 `{11,14,15,17,19,21,26,30}`，共 **43 条曲线**；
- 这些 N 全部 **squarefree**（故全部满足 Agashe–Ribet–Stein 的 `N` 无平方因子条件）；
- 每 N 的模符号 cuspidal 维数、新形式数：

| N | #曲线 | dim S₂（cuspidal symbols） | #newforms | r_f 范围 | ARS `deg φ=r_f` |
|---|---|---|---|---|---|
| 11 | 3 | 2 | 1 | 1..5 | 3/3 |
| 14 | 6 | 2 | 1 | 1..6 | 6/6 |
| 15 | 8 | 2 | 1 | 1..4 | 8/8 |
| 17 | 4 | 2 | 1 | 1..4 | 4/4 |
| 19 | 3 | 2 | 1 | 1..3 | 3/3 |
| 21 | 6 | 2 | 1 | 1..4 | 6/6 |
| 26 | 5 | 4 | 2 | 2..14 | 5/5 |
| 30 | 8 | 6 | 1 | 2..24 | 8/8 |

- **总通过率：43/43 = 100%**（所有 N 无平方因子；`deg φ = r_f` 全部成立）。
- `T_p` 整性：所有 N、全部 `p ∈ {2,3,5,7,11,13,17,19,23}` 的 `hecke_matrix(p)` 在整基下均为**整数矩阵**（9/9 × 8 水平，`Tp_all_integral=True`）；矩阵已存 JSON。
- 整基例子（`N=15`）：`['(3,4) - (5,2) + (5,3)', '(5,1) - (5,2)']`（ambient 坐标见 JSON）。

### 2.2 已知值对照

| 曲线 | conductor | `deg φ` | `r_f` | 期望 | 结果 |
|---|---|---|---|---|---|
| 11a1 | 11 | 1 | 1 | 1 | ✅ |
| 14a1 | 14 | 1 | 1 | 1 | ✅ |
| 37a1 | 37 | 2 | 2 | 2 | ✅（N=37 超出 N≤30 样本，单独核对） |

### 2.3 明细文件
- `coord/b0_data.csv`（43 行）：`N,curve,conductor,semistable,squarefree,r_f,deg_phi,deg_eq_rf,dim_cuspidal,n_newforms,Tp_all_integral`；
- `coord/b0_modular_data.json`：每 N 的 `symbols.integral_basis`/`integral_coords`、`T_p` 整矩阵、`newforms` 的 `q_expansion`/`coeffs_1_20`；每曲线的 `r_f`/`deg_phi`；`known_checks`；`errors=[]`。

## 3. 与 B0 判定条件对照

| B0 要求 | 状态 | 说明 |
|---|---|---|
| 能对 N 计算 `S₂(Γ₀(N))` 整基 | ✅ | `ModularSymbols.cuspidal_submodule().integral_basis()`；ambient 坐标已存 |
| 能算 `T_p` 整矩阵 | ✅ | `hecke_matrix(p)`，`p≤23`；8 水平全整 |
| 能算全部新形式特征系 | ✅ | `newforms(names='a')`，q-展开/前 20 系数；N=26 有 2 个新形式 |
| 能算 `r_f` | ✅ | `E.congruence_number()`（43 曲线，errors=0） |
| 能算 `deg φ` | ✅ | `E.modular_degree()`（同上） |
| N 无平方因子时验证 ARS | ✅ | 样本 43/43 全部 `deg φ = r_f` |
| 与已知值对照 | ✅ | 11a1/14a1/37a1 全对 |
| 导子 ≤500 的全半稳定曲线核对表 | ⏳ 未做（B0 原型 N≤30） | 脚本可直接扩展 `B0_NMAX`；`congruence_number`/`modular_degree` 小 N 很快（2.93s/43 条），大 N 需测性能 |

**判定：B0 基础对象可算，管线成立。** 但样本全部 squarefree，只验证了 ARS 的适用情形；非 squarefree 的 `r_f`/`deg φ` 区分尚未覆盖（B1 应加入非平方导子的半稳定曲线，如需要）。

## 4. 下一步（B1）

1. **扩展样本**：`B0_NMAX` 调到 500（或 10⁴）并测 `modular_degree`/`congruence_number` 的耗时；必要时给 `sympow` 加 PATH 前缀（lead 提示）；Sage 的 Cremona 数据库覆盖到导子 500,000（需确认本安装数据范围）。
2. **B1 证书搜索**：
   - 用 `CuspForms` + `ModularSymbols` 整基/`T_p` 整矩阵，计算每个新形式 f 与其它形式的同余模数/特征系数；
   - 对每个 (N, curve) 求使 `|P(f)| = r_f` 的整系数 Hecke 多项式 P；记录支撑最小/次数最小两种证书；
   - 输出：用到的最大素数、P 的次数、系数大小、f 与每个其它形式的同余模数；
   - 判定：最大素数/次数随 N 至多 `(log N)^k` 增长且出现构造规律 ⇒ 有戏。
3. **数据完整性**：B1 需要 `a_p`（p 到 10⁴）、判据 `r_f` 与 `deg φ` 的交叉核对；Sage 可直接算（`E.ap(p)`、`E.modular_degree`），但大批量需缓存/并行。
4. **风险**：`E.congruence_number()` 在大导子可能慢（依赖模符号/Hecke 模）；`E.modular_degree()` 依赖 sympow（大 N 需 PATH）；LMFDB API 不可用 ⇒ 跨库核对只能用 Sage 自带 Cremona 数据（无需外网）。

**建议**：B1 先跑 N≤500 半稳定曲线，记录 `r_f`/`deg φ` 与耗时；再对 N≤10⁴ 采样。证书搜索在 N≤200 先做原型。
## A924: certificate lemma formalization (B.2)

`tmp/sheaf/xif/paper/Mzk1BCertificateLemmaActual.lean` (olean + trio):
- `BCertificateData` (c, r_f, m, quotient_action `m*r_f=c`);
- **`bcertificate_divisibility`**: `r_f ∣ c` (PROVED from the quotient-action input);
- `bcertificate_quotient_eigenvalue`, `bcertificate_rf_pos`, `EigenvalueNonzero`,
  `bcertificate_m_ne_zero`.

**External inputs registered (not faked):**
- E-B-1: on the finite quotient `Q = L/((L cap Qf)+(L cap f^perp))` (order r_f) the Hecke
  operator acts as multiplication by an integer `m`, and over Q that scalar equals `c/r_f`
  (hence `m*r_f = c`);
- E-B-2: the Hecke operator preserves the lattice `L` (integrality of the Hecke
  correspondence);
- full formalization gap: construction of `Q` via `Submodule.quotient`/finite-index and
  `m = c/r_f` over Q.

Paper statement (B.2) and assumption list are recorded; the arithmetic core `r_f | c` is
green conditional on E-B-1.

## A925: complete rank-2 construction

`tmp/sheaf/xif/paper/Mzk1BCertificateFullActual.lean` (olean + trio):
- `rfRankTwo = 5`: `L=Z^2`, `f=(1/2,1)`, `L cap Qf = Z(1,2)`, `L cap f^perp = Z(-2,1)`,
  index `|det [[1,-2],[2,1]]| = 5`;
- `RankTwoHeckeData` with integer matrix entries and the four equations
  `P(1,2)=(c,2c)`, `P(-2,1)=0`;
- **`rankTwo_certificate`**: `r_f = 5 | c`, completely proved (no E-B-1 field);
- `rankTwo_five_dvd`.

Completion status: rank-2 COMPLETE; general rank still needs the quotient/finite-index
construction (`Submodule.quotient`, finite index, `m = c/r_f` over Q) = remaining Mathlib work.
E-B-1 is removed in rank 2 (replaced by explicit integer arithmetic).
