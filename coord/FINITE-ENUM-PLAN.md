# FINITE-ENUM-PLAN — 四个 GAP 的有限 label/place 枚举可行性

日期：2026-11-13；qpilot（A1061）。**仅 Python**；脚本 `tools/finite_enum_check.py`；MODEL 级枚举，未跑 Lean。

## 1. 四个 GAP（Mzk1MDecompositionActual 文件头）

| GAP | 内容 | 状态 |
|---|---|---|
| GAP-QROOT | `ordp(qroot)=qOrder/(2ℓ·ramIdx)` | **CLOSED**（A1022 源级） |
| GAP-TENSORVOL | `componentVol_tensorLogShell_eq` 的符号/缩放 | OPEN（符号恒等式） |
| GAP-IND2 | `ind2Term = V(thetaHull) − V(scaleElt·hull)` 的精确展开；V(thetaHull) m-无关 | OPEN |
| GAP-SOURCES | `tame≥0`、`archDefect≥0`、`shellDefect≥0`、`ind2Term≥0` | OPEN/源级部分 |

## 2. 参数空间估计

定义：ℓ=5, nC=(ℓ−1)/2=2, labels j=1..2；admissible = p≠ℓ 且（p>3 时）ℓ∤v_p(q)。

| 范围 | 曲线数 | bad 出现次数 | (p,j) cells | e 类（p=2/3/>3） |
|---|---:|---:|---:|---|
| **ℓ=5, N≤9999** | **12,354** | **37,617** | **75,234** | 8,253 / 6,775 / 22,589 |
| ℓ≤100（所有 ℓ 的 admissible 曲线实例） | 447,473 | 1,483,458 | **35,014,678** | 随 ℓ 变 |

N≤2000 子集（ℓ=5）：2604 curves / 约 7,932 bad / 15,864 cells。

## 3. 有限验证脚本

`tools/finite_enum_check.py`：对每个 admissible 曲线的每个 (p,j) cell 计算：

- `qroot_order = qOrder/(2ℓ)`（正、精确）；
- `qroot^{j²}` 的阶 `= j² qOrder/(2ℓ)`；
- `scaleVol = −j² qOrder logp/(2ℓ)`（负）；
- `ind2_leading = +j² qOrder logp/(2ℓ)`（正）与 `cancel = scaleVol+ind2_leading = 0`；
- `H_tame≥0`, `Ind2≥0`, `arch≥0`, `shellDefect≥0`；
- c1 e-exact `net = H+Ind−T ≥0`。

### 3.1 运行结果（ℓ=5, N≤9999）

```
curves = 12,354
cells  = 75,234
pass   = 75,234
fail   = 0
```
所有单项检查（qroot order、j² order、scaleVol 符号、ind2 leading、cancel、H/Ind/arch/shell/net 非负）**全部 pass**；输出 `coord/finite_enum_checks.csv`（75,234 行）。

## 4. 四个 GAP 的可归约性判断

| GAP | 可否有限枚举验证 | 说明 |
|---|---|---|
| QROOT | **可以（公式级）** | `qOrder/(2ℓ·ramIdx)` 是纯算术；l=5/Q 时 75,234 cells 全 pass；源级已 CLOSED |
| TENSORVOL | **仅可数值/模型测试** | 符号 `componentVol(a·O)=−ord(a)logp` 是真实 Haar 恒等式；枚举只能检查每 cell 的向量，不是符号证明 |
| IND2 | **部分** | leading `j²m` 与 cancellation 可逐 cell 检查；`V(thetaHull)` m-无关、exact expansion 需源级恒等式 |
| SOURCES | **部分** | H/Ind/arch/shell 非负可逐 cell 数值检查；源级 green 需要源引理 |

**结论：四个 GAP 中只有 QROOT 已可归约为有限纯算术；TENSORVOL/IND2/SOURCES 的有限枚举能覆盖固定参数空间并给数值证书，但不能替代通用符号证明。**

## 5. 可行有限子空间

1. **最小可行**：ℓ=5, N≤9999, 2 labels, 75,234 cells — 已全部枚举 pass（脚本秒级）；
2. **扩展**：ℓ≤100, 35,014,678 cells — 组合上有限但已大；需要分批/并行；
3. **通用**：ℓ 无界、bad set 任意、labels=nC(ℓ)、e 类随 ℓ 增长 — 不是有限空间；需要符号引理或一致界 (UB)。

## 6. 建议

- 若做“枚举证明”，先钉住 **ℓ=5, N≤9999** 有限域，用脚本生成逐 cell pass/fail 证书；
- 对 TENSORVOL/IND2/SOURCES 仍需各自符号引理（GAP-TENSORVOL 的 componentVol 符号、GAP-IND2 的展开、GAP-SOURCES 的源非负）；
- 通用 ℓ 不能靠枚举；必须回到 GAP 的符号证明 + (UB)/N5 下界。

## 文件
- `tools/finite_enum_check.py`
- `coord/finite_enum_checks.csv`（75,234 cells × checks）
- `coord/finite_enum_space.csv`（ℓ≤100 参数空间估计）
- `coord/finite_enum_summary.json`
- 本文件 `coord/FINITE-ENUM-PLAN.md`