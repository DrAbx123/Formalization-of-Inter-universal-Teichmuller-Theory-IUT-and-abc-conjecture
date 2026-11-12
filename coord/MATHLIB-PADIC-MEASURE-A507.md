# MATHLIB-PADIC-MEASURE-A507 — 4.36 p 进分布/Amice 测度移植评估

来源：`tmp/mathlib4-4.36.0-rc2/Mathlib/NumberTheory/Padics/Measure/`
目标基线：Mathlib v4.32.2（本地 `.lake/packages/mathlib`）。

## 文件与依赖核查

| 文件 | 4.36 位置 | 大小 | 4.32.2 是否有 |
|---|---|---|---|
| `Monoid.lean` | Measure/Monoid.lean | 5,891B | **无**（新增） |
| `AmiceTransform.lean` | Measure/AmiceTransform.lean | 6,449B | **无**（新增） |
| `Basic.lean` | Measure/Basic.lean | — | 有（基础：`D(X,R)` notation、`toCLMEquiv`、`dirac`、`contractSnd`、`prodMk'`） |
| `Topology.lean` | Measure/Topology.lean | — | 有 |
| `MahlerBasis.lean` | Padics/MahlerBasis.lean | — | 有（`mahler`、`mahlerTerm`、`mahlerSeries`、`mahlerEquiv`、`fwdDiff`） |

外部 import 核查（写 `import` 前逐个确认路径存在）：
`Mathlib.Algebra.MonoidAlgebra.Basic` ✓、`Mathlib.Analysis.Normed.Ring.Lemmas` ✓、
`Mathlib.NumberTheory.Padics.Measure.Basic` ✓、`Mathlib.NumberTheory.Padics.MahlerBasis` ✓、
`Mathlib.RingTheory.PowerSeries.Basic` ✓、`Mathlib.Algebra.Order.Field.Power` ✓、
`Mathlib.Topology.Algebra.InfiniteSum.Module` ✓。

## 语法差异

4.36 文件使用新 module 语法：`module`、`public import`、`public noncomputable section`、
`public section`。必须用 `tools/transcode_lean_432.mjs` 转码（去 `module`、`public import`→`import`、
`public` 前缀）后再入队；不可直接复制。

## API 缺口（评估关键）

1. **`AbstractMeasure.ext`**：4.36 `Measure/Basic.lean:67` 新增
   `@[ext] lemma ext (hμν : ∀ f, μ f = ν f) : μ = ν`；4.32.2 **无**。
   `Monoid.lean` 中 `ext` 出现 16+ 次（行 74, 99, 104, 110–112, 117–118, 125, 146, 174），
   移植需补该 ext 引理（约 4 行，`toCLMEquiv.injective` 或 `DFunLike.coe_injective` 可证），
   或把 `ext` 改写成 `ContinuousLinearMap` 外延。
2. **`PadicInt.ext_mahler`**：4.36 `MahlerBasis.lean:403–407` 新增，4.32.2 **无**；
   `AmiceTransform.lean:52` 用它。需同时回移 `dense_span_mahler`（4.36 MahlerBasis 中 `ext_mahler` 的前置，
   4.32.2 无），或重写该引理。
3. **`AbstractMeasure.arrowCongrLeft`（4.36 Basic:132–149）**：新增 4 个引理；
   `Monoid.lean` 未直接使用（无 `arrowCongrLeft` 出现），可选不合。
4. `Measure/Basic.lean` 4.36 相对 4.32.2 仅新增 `ext`/`arrowCongrLeft` 系列 5 个声明，
   旧声明无删除；其余 Monoid 用到的 `dirac/dirac_apply/map/contractSnd/prodMk/prodMk'/prodMk'_apply`
   在 4.32.2 均存在。

## 移植难度与建议

- **`Monoid.lean`：低-中风险，可先移植**。依赖 Basic 已有，只需补 `AbstractMeasure.ext`（或改 `ext` 用法），
  约 1 个文件 + 1 个小引理；转码后入队 `extras_add_closure`。
- **`AmiceTransform.lean`：中风险，暂缓**。需要回移 `dense_span_mahler` + `PadicInt.ext_mahler`
  （4.36 MahlerBasis 的新增部分），以及 `PowerSeries`/`IsBoundedSMul` 相关 API 的 v4.32.2 兼容；
  建议在 Monoid 验证通过后再做。
- **与当前 O2/3.12 路线的关系**：这两个文件属于 p 进分布/测度层（Mahler 系数、Amice 变换），
  可能支撑 log-volume 的测度层（Maass–Selberg/测度分解），但**不在 3.11⇒3.12 的对象临界路径**
  （A508：3.12 需要 BPS/multiradial/dsc/hull+det/SHE/IPL/APT，不含 Amice 变换）。因此按需移植，
  不阻塞 O2/O6。

## 结论

`Measure/Monoid` 值得移植（基础层、风险可控）；`Measure/AmiceTransform` 需先补 4.36 MahlerBasis 的
`dense_span_mahler`/`ext_mahler`，评估为中等成本、与 3.12 无直接关系，优先级低于 O2/O6。
