# Mathlib 4.36.0-rc2 vs 4.32.2：真正的新数学（声明级 diff）

方法：路径 diff 会把**搬家/拆分**误判为新文件（例如 `RingTheory/DedekindDomain/AdicValuation/Valuation.lean` 是旧 `AdicValuation.lean` 的拆分）。因此做了**声明级 diff**：解析 4.32.2 的 8,264 个文件的全部声明名（181,943 个）作为基线，再看 4.36 的 478 个新路径文件中哪些声明名不在基线里。

## 结果
- 4.36 新路径文件 478；其中 **334 个含有基线中不存在的声明名**（真新数学/新 API）
- 其余为搬家/拆分/包装（同名数学）——按要求忽略
- 新数学集中在：Tactic（Interval/ToSet/Hessenberg/Simproc）、Analysis（Fredholm、Gelfand 半径、logSeries、正则超几何、Bessel、ValuativeRel Completion）、Measure（TotalVariation、VectorMeasure、BorelGrowth）、LinearAlgebra（Cartan 矩阵、AffineSpace 维数/齐次化）、NumberTheory（Carmichael、FundamentalDiscriminant、LFunction、Ramanujan、DirichletDensity、FiniteAdeleRing、Padic Measure、RiemannZetaLogDeriv）、RingTheory（Depth、Coalgebra Frobenius、MvPowerSeries 导数）、AlgebraicGeometry/Group/Affine 等

## 与 IUT 对象相关的真新数学（值得记录）
1. **`Analysis/Normed/Algebra/Logarithm.lean`（17 新声明）**：`logSeries`、`logSeries_eq_ofScalars`、`logSeries_apply_eq`——一般 normed algebra 的对数级数；可用于 p 进/解析 log 对象。依赖 `Analytic.OfScalars`（4.32.2 有）。
2. **`NumberTheory/Padics/Measure/Monoid.lean`（11）**：p 进分布代数 `D(G,R)` 的卷积环（`convolveFunRight`、`diracHom`、`monoidAlgebraHom`、Ring/Module 实例）；**AmiceTransform.lean（12）**：`amiceTransform`、`coeff_amiceTransform`、`injective_amiceTransform`、`amiceTransformEquiv`（Mahler/Amice 变换）。依赖 `Padics/Measure/Basic`（4.32.2 有）→ **可移植性较好**。
3. **`NumberTheory/NumberField/FiniteAdeleRing.lean`（13）**：有限 adele 环的范数与单位 `tprod/finprod` 公式（`tprod_norm_eq_finprod_of_unit`、`unitEmbedding_norm_apply_eq_finprod_finitePlace`、`norm_eq_finprod_of_unit`）→ 全局乘积公式/log-volume。
4. **`RingTheory/DedekindDomain/AdicValuation/Completion.lean`（12）**：`adicCompletion`、`valuationExtension_toCompletion`、`valueGroupMulEquiv`；`Ramification.lean`（3）：`intValuation_liesOver`、`valuation_liesOver`、`uniformContinuous_algebraMap_liesOver` → different/ramification/place completion（IUT IV §1 侧）。4.32.2 的 `AdicValuation.lean` 是旧合并版，**拆分/扩展**成本较高（依赖新 Valuation 拆分文件）。
5. **`Topology/Algebra/ValuativeRel/Completion.lean`（35）**：`continuousAt_valuation_of_ne_zero`、`continuous_valuation_of_surjective` 等——valuative completion 的连续/闭映射；与 4 同域。
6. 其他相关但优先级低：`NumberTheory/NumberField/DirichletDensity.lean`（14，prime ideal zeta 和）、`FundamentalDiscriminant.lean`（8）、`ModularForms/{LFunction,RamanujanFormula}`、`Measure/TotalVariation`、`VectorMeasure`。

## 结论与建议
- **没有**直接覆盖 hcomp 两条 gap / θ-hull 比较 / PNT 显式常数的新数学（NumberTheory 的 PNT/Height 目录无新文件，声明级亦无）。
- 真新数学里对**对象层**有用的是：p 进分布/Amice 测度、normed log 级数、有限 adele 范数、Dedekind adic completion/ramification。
- 策略：**不整体升级**（4.36 toolchain 未装、主构建 4.32.2 的 ~10k oleans 要重编）；需要时把这些**具体文件**转码/移植到 `tmp/newmathlib/` 用 4.32.2 编译（候选顺序：logSeries → Padic Measure/Monoid+Amice → FiniteAdeleRing → AdicValuation 拆分）。
- 这些不改变 named 缺口：hcomp 两条仍是唯一真实内容缺口。
## A507 只读确认（shehdd）

经核对（4.36.0-rc2 与 4.32.2 的 path diff：`Mathlib/NumberTheory/PrimeCounting|PrimeNumberTheorem|Chebyshev` 与 `NumberTheory/Height` 均 **0 新增/0 删除**；新增数学集中在 logSeries、p 进 Measure/Amice、FiniteAdeleRing、AdicValuation Completion/Ramification、ValuativeRel Completion），**确认 4.36.0-rc2 没有任何直接覆盖 hcomp 两条 IUT IV 比较、θ-hull/procession log-volume 或显式 PNT 常数的新声明**；上述新数学只对对象层/算术侧（p 进 log、测度、adele 范数、adic completion）有间接价值，named 缺口不变。
