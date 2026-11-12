# CURVES-2000-STATS — N≤2000 半稳定曲线数据库

日期：2026-11-12；qpilot（A983）。**数据文件**：`data/c2_curves_2000.jsonl`（18.9MB，4154 行）、`data/c2_primes_10000.json`（1229 个素数）。
SHA256（JSONL）：`e5db281d044307c5d6772dcd34468d8947f3b9af80d8b88873b95b032eacfb80`

## 1. 规模与生成

| 项 | 值 |
|---|---|
| 生成器 | SageMath 10.9（WSL Ubuntu-24.04），`cremona_curves(N)`，`E.is_semistable()` 过滤 |
| N 范围 | 1–2000 枚举；实际有半稳定曲线的 N：11–1995，**759 个 level** |
| 曲线数 | **4154** |
| 同源类（label 前缀） | **2296** |
| 最大同源类大小 | 8 |
| 总耗时 | **80.5s**（枚举 + Δ/Tamagawa/torsion/deg φ/a_p） |
| 错误数 | **0** |

## 2. 字段与完整度

每行一个 JSON 对象。字段：

| 字段 | 含义 | 完整度 | 备注 |
|---|---|---|---|
| `N` | 导子 | 100% (4154/4154) | |
| `label` | Cremona 曲线标签（如 `11a1`） | 100% | |
| `Delta` | 判别式绝对值 | 100% | `abs(E.discriminant())` |
| `bad_primes` | 坏素数列表 | 100% | 来自 `E.conductor().prime_factors()`；半稳定 ⇒ 全部乘法约化 |
| `v_p_Delta` | 与 `bad_primes` 对齐的 `v_p(Δ)` | 100% | 与 `bad_primes` 同长度 |
| `Tamagawa` | 与 `bad_primes` 对齐的 Tamagawa 数 | 100% | `E.local_data(p).tamagawa_number()` |
| `torsion` | `{order, invariants}` | 100% | `E.torsion_order()`, `E.torsion_subgroup().invariants()` |
| `a_p` | 对 p≤10⁴ 的 `a_p` 列表 | 100% | 长度 **1229**（所有行），顺序由 `data/c2_primes_10000.json` 固定 |
| `deg_phi` | 模参数化次数 `deg φ` | 100% | `E.modular_degree()` |
| `r_f` | 本题的 `r_f = deg φ` 数值 | 100% | 与 `deg_phi` 相同（B0/B1 已数值核对 ARC） |
| `r_f_opt` | 同源类最小 `deg φ` | 100% (4154/4154) | 按 `class`（label 去掉末尾数字）分组取 min；`r_f_opt | r_f` 全成立 |
| `class` | 同源类键（如 `11a`） | 100% | 用于 `r_f_opt` 分组 |

**完整性检查**：无缺失字段/`None`；`a_p` 长度全为 1229；`Delta` 全非零；`r_f_opt ≤ r_f` 且 `r_f_opt | r_f` **4154/4154**。

## 3. 分布

- 坏素数个数分布：1 个：129 条；2 个：932；3 个：**1818**；4 个：1275。
- `deg φ = r_f`：min 1，max **1,720,320**；`r_f_opt`：min 1，max **1,068,480**。
- 同源类大小：最大 8；每个同源类内所有曲线的 `a_p` 相同（由首条曲线取 `E.ap(p)`；半稳定 ⇒ 同源不改变 a_p）。
- N 分布（按 500 分箱）：N≤500：941 条；501–1000：1181 条；1001–1500：1072 条；1501–2000：960 条。
- torsion 阶前几：2（1735）、1（1457）、4（494）、3（227）、6（112）、8（56）、5（50）。

## 4. 用法与注意

- 读 JSONL：每行一对象；`a_p` 的第 i 项对应 `data/c2_primes_10000.json` 的第 i 个素数（素数≤9973）。
- `r_f_opt` 是**同源类最小模次数**（B 线证书搜索/ARC 用）；`r_f` 按题意为每条曲线的 `deg φ`（非最优曲线可大于 `r_f_opt`，且 `r_f_opt | r_f`）。
- `Delta` 取自曲线模型的判别式（Cremona 模型；半稳定）绝对值；`v_p_Delta` 仅对 `bad_primes` 给出。
- Tamagawa/Torsion/Δ 为逐曲线字段；`a_p`、`class`、`r_f_opt` 为同源类共享。
- 数据全部来自 Sage/Cremona；无网络/LMFDB 依赖。
- 未做字段以外的数学断言；B/C 线可复用；若需扩展 N≤9999，可复用同一生成器（`tmp/c2_build5.sage`）。