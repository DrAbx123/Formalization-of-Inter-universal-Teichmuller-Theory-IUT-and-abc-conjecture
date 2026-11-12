# MATHLIB 4.36 候选模块移植可行性（A507，声明级 diff 的后续依赖扫描）

方法：对 `tmp/mathlib4-4.36.0-rc2` 中 5 个候选模块，逐条解析其 `import Mathlib.*`，检查同一路径是否存在于我们 4.32.2 的 `.lake/packages/mathlib`。缺 import = 需连带移植的拆分文件（成本高）。

## 依赖可用性表

| 4.36 候选文件 | 直接依赖 | 4.32.2 可用性 | 移植成本 / 结论 |
|---|---|---|---|
| `Analysis/Normed/Algebra/Logarithm.lean`（17 新声明，`logSeries`） | `Analysis/Analytic/OfScalars`、`Algebra/Algebra/TransferInstance` | **2/2 存在** | **可直接移植**（只需转码 4.36→4.32.2 语法；无需连带） |
| `NumberTheory/Padics/Measure/Monoid.lean`（11，p 进分布卷积环） | `Algebra/MonoidAlgebra/Basic`、`Analysis/Normed/Ring/Lemmas`、`NumberTheory/Padics/Measure/Basic` | **3/3 存在** | **可直接移植**；依赖链最短，推荐优先 |
| `NumberTheory/Padics/Measure/AmiceTransform.lean`（12，Amice/Mahler 变换） | `Padics/MahlerBasis`、`Padics/Measure/Basic`、`RingTheory/PowerSeries/Basic`、`Algebra/Order/Field/Power`、`Topology/Algebra/InfiniteSum/Module` | **5/5 存在** | **可直接移植**（在 Monoid.lean 之后）；无新拆分依赖 |
| `NumberTheory/NumberField/FiniteAdeleRing.lean`（13，adele 范数 tprod/finprod 乘积公式） | `NumberField/ProductFormula`、`RingTheory/DedekindDomain/FiniteAdeleRing`、`Algebra/FiniteSupport/Basic` | **3/3 存在** | **可直接移植**；与全局 log-volume/乘积公式相关 |
| `Topology/Algebra/ValuativeRel/Completion.lean`（35，valuative completion 连续/闭） | `Topology/Algebra/UniformField`、`ValuativeRel/ValuativeTopology`、`WithZeroTopology` | **3/3 存在** | **可直接移植**；与 adic completion 同域，优先级中 |
| `RingTheory/DedekindDomain/AdicValuation/Completion.lean`（12） | `AdicValuation/Valuation.lean`（**4.36 新拆分路径，4.32.2 无**）、`Topology/Algebra/Valued/WithVal` | **1/2** | **成本高**：须先连带移植 4.36 的 `AdicValuation/Valuation.lean`（旧 `AdicValuation.lean` 的拆分/扩展），再 Completion；Ramification 又依赖 Completion → 三文件链 |
| `RingTheory/DedekindDomain/AdicValuation/Ramification.lean`（3） | `AdicValuation/Completion`（同上缺）、`RamificationInertia/Ramification`、`Valuation/Discrete/RankOne` | **2/3** | 串在上一行链上；暂不移植 |

## 与我们对象层的消费者映射（是否有真实消费者）

| 候选 | 潜在消费者 | 现在是否必须 | 建议 |
|---|---|---|---|
| `logSeries` | 我们/ Takkun 的 p 进 `logOnePlus`（`Padic/PadicLog`）与 archimedean log；`modelLogMap` 目前只用 valuation，不用 log 级数 | 否（Takkun 已有 padic log 实现） | 记录为 4.36 可选增强；暂不移植 |
| Padic `Measure/Monoid` + `AmiceTransform` | 未来 p 进分布/log-shell 测度层（`modelLogShell` Haar 细化、log-volume 归一化） | 否（当前 hull/log-volume 用自有 `litHaar` + Mathlib Measure） | 若对象层要 p 进分布，优先移植（依赖全可用） |
| `FiniteAdeleRing` | 全局乘积公式/log-volume 归一化（R3 literal global hull） | 否（R3 用自有 litHaar/global IQ 载体） | 候选，等 R3 需要 adele 范数时再移植 |
| `ValuativeRel/Completion` | 若把 Frobenioid/prime-strip 的 place/valuation 层提升为严谨的 valuative completion | 否 | 优先级中，与 AdicValuation 一起评估 |

## 结论

1. 可**零连带**移植的：`logSeries`、Padic `Measure/Monoid`+`AmiceTransform`、`FiniteAdeleRing`、`ValuativeRel/Completion`（依赖 4.32.2 全存在，配合 `tools/transcode_lean_432.mjs`）。
2. **成本高**：`AdicValuation/{Completion,Ramification}` 需先移植 4.36 新拆分 `Valuation.lean`，暂缓。
3. 它们都不直接覆盖 hcomp 两条 / θ-hull 比较 / PNT（与 lead 的声明级 diff 结论一致）；对对象层都是“可选增强”，当前没有阻塞性消费者 → **本轮不移植**，只在需要时按上表优先级走 `tmp/newmathlib/` + `extras_add_closure`。