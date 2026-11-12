# MATHLIB-4.36-GAP-IMPACT — 4.36.0-rc2 新数学 vs 我们的 named gaps（A507）

generated: 2026-11-11 06:05 (lattice，只读结论；源: `coord/MATHLIB-4.36-NEW-MATH.md` + `coord/NAMED-GAPS-A497.md` + `coord/DAG-BLOCKED.json`)

## 0) 结论（先写死）

**4.36.0-rc2 的新数学不改变任何 named gap 的状态。** 与 IUT 相关的新数学（logSeries、p 进 Amice/测度、FiniteAdeleRing、AdicValuation completion/ramification、ValuativeRel completion）都是**辅助基础设施**，没有新增可直接证明 hcomp 两条比较、独立 θ-pilot 读法、hull_bound/containment/(P) 或 PNT 显式常数的定理。hcomp 两条仍是唯一真实内容缺口；θ-hull/contract-provenance/hull-bound 等状态不变。

## 1) 输入与对照口径

- 4.36 新数学清单: `MATHLIB-4.36-NEW-MATH.md`（声明级 diff，基线 4.32.2 的 181,943 声明；478 新路径/334 含真新声明；搬家/拆分已忽略）。
- 我们的 named gaps: `NAMED-GAPS-A497.md`（hcomp-iut4-comparisons、independent-theta-pilot-readout、contract-provenance、literal-hull-finiteness、external-lana-reference）+ `DAG-BLOCKED.json`（takkun-containment、takkun-hull-bound、request-P-received-hull）+ PNT/Chebyshev（Section2 已有 4/3 估计，见 `NEW-MATHLIB-PNT.md`）。
- “改变状态”定义: 从 named/blocked 变为可证明（或可直接引用关闭）；仅“可作辅助引理/减少实现工作量”不算改变。

## 2) 逐项映射

| 4.36 新数学 | 内容 | 对应 named gap | 是否改变状态 | 理由 |
|---|---|---|---|---|
| ① `Analysis/Normed/Algebra/Logarithm.logSeries`（17 声明） | 一般 normed algebra 的对数级数（`logSeries`, `logSeries_apply_eq`, …），依赖 4.32.2 有 | 无直接对应；可能辅助 `independent-theta-pilot-readout` 的解析 log 侧 | **否** | 只是 normed log 级数；θ-pilot 读法缺的是 literal hull/thetaPilot 的真实 log-volume（Haar/几何对象），不是 log 级数展开。 |
| ② `NumberTheory/Padics/Measure/{Monoid,AmiceTransform}`（11+12 声明） | p 进分布卷积环 `D(G,R)`、`convolveFunRight`/`diracHom`/`monoidAlgebraHom`；Amice/Mahler 变换 `amiceTransform`/`coefficients`/`injective` | 无直接对应；可辅助 IUT 局部 p 进测度/Haar/分布记账（O7 hull/volume 周边） | **否** | hcomp 两条是高度↔区域体积、区域体积↔算术权重的 IUT IV 比较；Amice 变换提供 p 进测度工具，但不构成这两条比较。可作支持性移植候选（依赖 Basic 已有，移植性最好）。 |
| ③ `NumberTheory/NumberField/FiniteAdeleRing`（13 声明） | 有限 adele 环范数/单位 `tprod/finprod` 乘积公式（`tprod_norm_eq_finprod_of_unit` 等） | 可辅助 `hcomp-iut4-comparisons` 的全局 adele/体积记账；`named-gap:literal-hull-finiteness` 的 adele 范数侧 | **否** | 乘积公式是标准 adele 记账；hcomp 需要的是 IUT IV 的两条逐 ε 比较（高度↔normalizedRegionVolume、regionVolume↔weight+hullVolume+D），乘积公式不足以推出，且不涉及 θ-hull/PNT。 |
| ④ `RingTheory/DedekindDomain/AdicValuation/{Completion,Ramification}`（12+3 声明） | `adicCompletion`、`valuationExtension_toCompletion`、`valueGroupMulEquiv`；`intValuation_liesOver`/`valuation_liesOver`/`uniformContinuous_algebraMap_liesOver` | 可辅助 IUT IV §1 的 different/ramification 计算（hcomp 第二比较/`request-P-received-hull` 的局部输入侧） | **否** | 提供 adic 完备化与 liesOver/ramification 引理，是不同/分歧基础设施；hcomp 仍需 explicit/effective 比较与归一化；且拆分依赖新 Valuation 文件、移植成本高。 |
| ⑤ `Topology/Algebra/ValuativeRel/Completion`（35 声明） | valuative completion 的连续/闭映射引理 | 与 ④ 同域；无直接 gap | **否** | 拓扑/完备化辅助，不产生 hcomp/θ-hull/PNT 内容。 |
| ⑥ 其他（DirichletDensity、FundamentalDiscriminant、LFunction、Ramanujan、TotalVariation、VectorMeasure 等） | 数论/测度/模形式新 API | PNT/Chebyshev、hcomp、θ-hull | **否** | NEW-MATH 明确无 PNT/Height 新文件/声明；DirichletDensity 是密度工具，不是 PNT 显式常数；无 hcomp/θ-hull 直接引理。 |

## 3) 与各 named gap 的逐项结论

| named gap | 4.36 是否提供关闭引理 | 状态 |
|---|---|---|
| `named-gap:hcomp-iut4-comparisons`（两条 IUT IV 比较） | **否**；②③④只提供局部测度/adele/ramification 辅助 | **不变（唯一真内容缺口）** |
| `named-gap:independent-theta-pilot-readout`（literal θ-pilot hull log-volume） | **否**；①是抽象 log 级数，无 Haar/hull θ 读法；②是 p 进分布测度，非 θ-hull | **不变** |
| `named-gap:contract-provenance`（StepXIContract 与 paper 对象绑定） | **否**；这是定义/逻辑绑定，不涉及新数学 | **不变** |
| `named-gap:literal-hull-finiteness` | **否**；③的 adele 乘积公式可辅助记账，但不给 literal hull 有限性 | **不变** |
| `named-gap:request-P-received-hull`（(P) 接收侧体積評価） | **否**；④只给不同/ramification 基础设施，不含 (P) 的体積适用 | **不变** |
| `named-gap:takkun-containment` / `named-gap:takkun-hull-bound` | **否**；无新数学覆盖 Thm 3.11 桥/hull_bound | **不变** |
| PNT/Chebyshev（Cor 2.2 素数选择） | **否**；无 PNT 新文件/声明；我们 Section2 已有 4/3 估计 | **不变** |

## 4) 建议（cherry-pick 排序，不做整体升级）

1. **`logSeries`**（依赖 `Analytic.OfScalars` 4.32.2 有）—— 最容易移植，若后续需要 p 进/解析 log 对象可用。
2. **`Padics/Measure/{Monoid,AmiceTransform}`**（依赖 `Padics/Measure/Basic` 4.32.2 有）—— p 进测度/分布工具，移植性最好；可为局部 p 进对象/Haar 记账提供支持。
3. **`FiniteAdeleRing`**（依赖 Basic 4.32.2 有）—— 全局 adele 范数/乘积公式，支持全局体积/高度记账。
4. **`AdicValuation/{Completion,Ramification}` + `ValuativeRel/Completion`** —— 对 different/ramification 有用，但拆分依赖新 Valuation，移植成本高，暂缓。
- 移植方式: 从 `tmp/mathlib4-4.36.0-rc2` 抽取文件到 `tmp/newmathlib/`，按 4.32.2 适配（API/命名），用 `extras_add_closure` 入队；**不整体升级**（4.36 toolchain/olean 未就绪，重编 ~10k oleans）。

## 5) 诚实标注

- 本结论基于 `MATHLIB-4.36-NEW-MATH.md` 的声明级 diff 摘要（Lead 提供）+ 我们对 named gaps 的定义；**未**在 4.36 上编译/验证这些新引理的依赖链。
- 判定“不改变”是就“能否关闭 named gap”而言；不排除 ②③④ 作为辅助引理减少未来实现工作量（已在建议中列出）。
