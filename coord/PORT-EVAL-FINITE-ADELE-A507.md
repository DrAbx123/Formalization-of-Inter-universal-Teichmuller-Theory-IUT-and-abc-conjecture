# PORT-EVAL-FINITE-ADELE-A507 — `NumberTheory/NumberField/FiniteAdeleRing.lean` (4.36 → 4.32.2) 评估

源：`tmp/mathlib4-4.36.0-rc2/Mathlib/NumberTheory/NumberField/FiniteAdeleRing.lean`（103 行，作者 Mercuri；版权 Apache-2.0）。
目标：项目固定 Mathlib **4.32.2**；只做声明级转码移植，不升级。

## 1. 文件内容（真实数学）
- `hasFiniteMulSupport_norm`：单位有限 adele 的范数乘支持有限；
- `hasProd_subset_valued_one_lt`（private）：`1 < v(x)` 子集上乘积极限存在，值=有限乘积；
- `hasProd_zero_subset_lt_one_valued`（private）：非单位且处处非零 adele，在 `v(x)<1` 上乘积为 0（调和级数式发散）；
- `hasProd_zero_of_not_isUnit`：非单位 adele 的全积 `∏' v, ‖x v‖ = 0`；
- `tprod_norm_eq_finprod_of_isUnit` / `_of_unit`：单位情形 tprod = finprod（**乘积公式的 adele 范数半边**）；
- `tprod_eq_zero_of_not_isUnit`；
- `noncomputable instance Norm 𝔸ᶠ[R,K]`（`norm x := ∏' v, ‖x v‖`）、`norm_def`、`norm_eq_finprod_of_unit/_of_isUnit`、`norm_eq_zero_of_not_isUnit`；
- `[NumberField K]` 部分：`unitEmbedding_norm_apply`、`unitEmbedding_norm_apply_eq_finprod_finitePlace`——**Kˣ 嵌入有限 adele 后的范数 = 有限位函数乘积**。

## 2. 4.32.2 依赖核查（实测）

| 依赖 | 4.32.2 状态 |
|---|---|
| `import Mathlib.NumberTheory.NumberField.ProductFormula` | ✅ 存在（4.32.2 有该文件） |
| `import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing` | ✅ 存在（4.32.2 有，189 行） |
| `import Mathlib.Algebra.FiniteSupport.Basic` | ✅ 存在 |
| `hasProd_zero_of_exists_eq_zero`、`tprod_eq_finprod`、`unitEmbedding`、`infinite_valued_ne_one_of_not_isUnit` | ✅ 均在 4.32.2（Basic.lean/FiniteAdeleRing.lean） |
| `hasFiniteMulSupport_valued`、`finite_valued_one_lt`、`cofinite_mem_adicCompletionIntegers`、`ofAdicCompletion` | ❌ 4.32.2 缺失（4.36 基础文件新增的 4 个声明） |
| `FinitePlace.two_le_norm_of_one_lt_norm` | ❌ 4.32.2 缺失（用于 private `hasProd_zero_subset_lt_one_valued` 的 `grind` 步） |
| `grind` tactic | ✅ 4.32.2 Mathlib 已有（2,034 处用法） |

### 4.36 基础文件 `RingTheory/DedekindDomain/FiniteAdeleRing.lean` 的声明级 diff
- 4.32.2：189 行 / 11 decl；4.36：216 行 / 15 decl；**新增 4 个**：`cofinite_mem_adicCompletionIntegers`（`a.2` 直接转写，1 行）、`finite_valued_one_lt`（`simpa [mem_adicCompletionIntegers]`）、`hasFiniteMulSupport_valued`（用 `unitsEquiv_finite_valued_eq_one`）、`ofAdicCompletion`（`RestrictedProduct.mulSingleMonoidHom`）；**无删除/重命名**。
- 前两者移植成本极低；`hasFiniteMulSupport_valued` 需确认 4.32.2 有 `unitsEquiv_finite_valued_eq_one`；`ofAdicCompletion` 需 `RestrictedProduct.mulSingleMonoidHom`（本文件主体不用它，可跳过）。

## 3. 转码/移植步骤（4.32.2）
1. 语法转码：删 `module` 行；`public import` → `import`；`@[expose] public section` → 普通 section（或删除该指令）；
2. 先把缺失的 **2 个必要引理**补到本地 port（不放回主 Mathlib）：`cofinite_mem_adicCompletionIntegers`、`finite_valued_one_lt`（直接照搬 4.36，1-3 行证明）；
3. 补 `FinitePlace.two_le_norm_of_one_lt_norm`：在 4.36 Mathlib 中定位其定义（`HeightOneSpectrum`/`FinitePlace` 相关文件），同样照搬为本地 port 引理；或改写 private 引理省去该步（用 `Valued.toNormedField.one_lt_norm_iff` 直接给 `2 ≤ ‖x⁻¹‖` 的版本需核对 4.32.2 API）；
4. 文件 `FiniteAdeleRing.lean`（103 行）整体移植，import 改 `Mathlib...` 本地 port 路径；
5. `grind` 调用在 4.32.2 可用，无需改；若个别 `grind` 失败改 `simp`/`omega`；
6. 入队：`node tools/extras_add_closure.mjs <portfiles>`；oleans 出现后按 per-file 日志迭代。

## 4. 风险评估
- **可行性：中高**（4 个新基础声明 + 1 个 norm 引理 + 2 个语法转码；无体系性新 API 依赖）。
- 主要风险：`hasFiniteMulSupport_valued` 的 `unitsEquiv_finite_valued_eq_one` 在 4.32.2 是否同名/存在；`RestrictedProduct.mulSingleMonoidHom`（只影响 `ofAdicCompletion`，可裁）；`Grind` 在个别 `grind`-only 步可能失败。

## 5. 对我们的价值（诚实评估）
- **不直接覆盖 hcomp Gap1/2**（那是 IUT IV 两条比较，hcomp 仍为 named 缺口）。
- 可用于：**全局 log-volume/乘积公式**的范数归一化对象（`unitEmbedding_norm_apply_eq_finprod_finitePlace` 给 Kˣ 在有限 adele 中的范数 = 有限位乘积），以及 future `r4_literal_assembly` 中 adele 范数与 `litHaar` 归一化的对照；属对象层支撑，不是 Gap 证明。
- 建议：**暂缓整包移植**，优先保证现有 literal/对象链条；若需要 adele 范数对象再按上述步骤 1-3 天量级执行（约 4 个补充引理 + 1 文件转码）。
