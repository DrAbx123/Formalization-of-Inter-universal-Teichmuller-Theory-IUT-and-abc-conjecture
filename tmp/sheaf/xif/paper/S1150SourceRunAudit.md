# S1150 第一接头：SourceRun 审计

日期：2026-10-30。范围：只读审计
- LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialIplLinkWiring.lean
  （`iplAlgorithmicProvenanceCard` :190）
- LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialPresentationWiring.lean
- LeanFormal/IUT/IUTIII/Theorem311/ParametricCarrier.lean
- 旁证：SourceFTimesMuPrimeStripPolyIsomorphism.lean（`canonicalLift` :343，
  `SourceFTimesMuPrimeStripRem3102Diagram` :805，`iplLink` :845）

## 1. actual 算法端供体

ParametricCarrier.lean 提供的是**抽象 choice/route 算法**，不是 prime-strip 算法：

- `ParametricTheorem311.Carrier Label Choice`：`core : Core Label Choice`、
  `profile`、`connector`、`ind3_level_eq`；
- `AlgorithmInput carrier`：`source : Choice`、`route : List (RouteStep Label)`、
  `source_image_nonempty`；
- `RouteStep Label` 仅 `ind1 Label | ind2 Label | ind3 Nat`；
- `runAlgorithm : AlgorithmInput → AlgorithmOutput`，
  `algorithmTarget = routeTarget route source`，
  `AlgorithmOutput` 只有 `target : Choice`、level/profile monotonicity、image-upper；
- `IndependenceBundle` 的 Ind1/Ind2/Ind3 certificates 都在 `Choice` 上；
- `SourceMultiradialPresentationWiring` 的 W.1/W.2：
  `SourceProcessionAutomorphismData.act : G →* Equiv.Perm Choice`，
  `automorphism_runAlgorithm_target` actual；
- `SourceMultiradialIplLinkWiring`：`ReducedIplLink` 与 `reducedIplLink_holds`
  是 actual，但只是**算法接口上的 reduced link**，不携带 prime-strip poly-isomorphism。

结论：算法端 actual 东西全部在 `Choice`/`List (RouteStep Label)`/`AlgorithmOutput` 上。

## 2. actual 图端供体

SourceFTimesMuPrimeStripPolyIsomorphism.lean 提供：

- `SourceFTimesMuPrimeStrip V` 载体；
- `SourceFTimesMuPrimeStripFullPolyIsomorphism`（full poly-iso，可复合、取逆）；
- `SourceFTimesMuPrimeStripEquivalence.canonicalLift`（:343）；
- `SourceFTimesMuPrimeStripRem3102Diagram`（:805）：8 个顶点、10 个箭头、3 个交换律，
  全部是 actual 数据字段；
- `iplLink`（:845）：actual 六因子复合；
- `iplLink_eq_verticalLGP_upperLGP` actual。

结论：图端 actual 东西全部在 `SourceFTimesMuPrimeStrip V` 上，但没有算法索引。

## 3. 两边接口的 exact 缺口

`iplAlgorithmicProvenanceCard`（:190）已明确记录：

- algorithm interface 没有 prime-strip object；
- 没有 functor `route operations/stages → SourceFTimesMuPrimeStrip V`；
- 没有 bridge `FPrimeStrip V → Choice/Output`；
- `ReducedIplLink` 不能被当成 source-level (IPL)。

这不是可再用一个 `compatible : Prop` 字段补上的；缺的是**对象/函子**。

## 4. reopening 路线 (a)/(b) 可行性

### (a) 直接从 route operation/stage 到 `SourceFTimesMuPrimeStrip V`

不可落 Lean。原因：
- 现有 `AlgorithmInput.source` 是 `Choice`，不是 strip；
- `RouteStep` 的 `ind1/ind2/ind3` 只作用于 `Core Label Choice`；
- tree 中不存在 `Choice → SourceFTimesMuPrimeStrip V` 或
  `List RouteStep → FullPolyIso` 的 actual functor；
- 若加入该 functor，就是新的对象层，不是补字段。

### (b) 经 F-prime-strip 层（`FPrimeStripEquiv`/`canonicalLift`）

是唯一“较接近”的 Lean 路线，但**目前也不能直接落**：
- `canonicalLift` 只在 `FPrimeStrip V` 之间工作；
- tree 中没有 `FPrimeStrip V → Choice/Output` bridge（W.3 不可表达，
  PresentationWiring header :57-64；card :225-226 重申）；
- `SourceFTimesMuPrimeStripRem3102Diagram` 需要 8 个 `SourceFTimesMuPrimeStrip V`
  顶点；现有算法不提供这些顶点。

结论：若必须选一条，选 (b)：它有 actual 图端 poly-iso donor，缺口只有
“算法索引 strip family + bridge”；(a) 连图端类型都对不上。
但 (b) 仍需新增源数据，不能声称已落。

## 5. SourceRun 所需真实数据字段

可在现有 actual 数据上立即填的字段：

```lean
structure SourceRun (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G₁)
    (ind2Data : Ind2ActionData carrier autom G₂)
    (input : ParametricTheorem311.AlgorithmInput carrier) where
  output : ParametricTheorem311.AlgorithmOutput carrier input
  output_eq : output = ParametricTheorem311.runAlgorithm carrier input
  presentation : SourceTheorem311MultiradialPresentation G₁ I n Choice
  presentation_eq : presentation = sourcePresentationOfCarrier carrier autom input
  algorithm : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Choice
  algorithm_eq : algorithm = sourceAlgorithmOfCarrier carrier autom ind2Data input
```

这些字段全部 actual，无 `compatible : Prop`。

仍需补但当前**不存在**的字段（exact minimum）：

```text
stageStrip : Int → SourceFTimesMuPrimeStrip V
stageStrip_base : stageStrip ... = ...
operationStripArrow : RouteStep Label →
  SourceFTimesMuPrimeStripFullPolyIsomorphism (stageStrip i) (stageStrip j)
diagram : SourceFTimesMuPrimeStripRem3102Diagram ...
```

其中 `stageStrip`/`operationStripArrow` 目前没有任何 actual 构造。

## 6. 首个无法构造的源 operation

不是 `runAlgorithm`（它在 `Choice` 上 actual），也不是 `ind3` level 运算。

第一个无法构造的是 **`Choice → SourceFTimesMuPrimeStrip V` 的 stage lift**：

- `carrier.core.base` 是 `Choice`，没有对应的源 prime-strip；
- 因此连 `ind1` 都无法在源 strip 层解释：
  `ind1 a : Choice → Choice` 是 actual，但
  `SourceFTimesMuPrimeStripFullPolyIsomorphism` 需要两个 strip 顶点，
  而 `ind1` 没有给出这两个顶点；
- 图端 `lowerEnv`（evaluation）等箭头也无法由 `ind1/ind2/ind3` 选出。

所以首个失败点是：**source stage / strip lift（`core.base` 的 source strip）**，
早于任何具体 operation。

## 7. 判断

- (a) 不可落；(b) 是目前唯一可讨论的 Lean 路线，但需新增算法索引 strip family
  与 bridge，仍不是 actual。
- 不应新增 `compatible : Prop` 包装；`ReducedIplLink` 已经是 reduced 事实，
  不能冒充 source-level (IPL)。
- 最小 Lean 骨架只放 actual 的 `SourceRun` 字段（见上），不把缺失的 strip lift
  写成 Prop 字段。
