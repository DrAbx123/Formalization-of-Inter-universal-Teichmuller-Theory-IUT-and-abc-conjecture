# P7 空类型影响分类（P0 迁移优先级，2026-11-13 晚）

## 判定依据
`S1429CompletionRootObstructionActual.sourcePilotRegionData_isEmpty : IsEmpty (SourcePilotRegionData I)`：
旧 C3 类型为空。**任何以 `C3 : SourcePilotRegionData ...` 为参数的“actual/构造/unconditional”结论在空类型上 vacuous**；
不得用 `IsEmpty.elim` 冒充比较，也不得把旧 C3 green 当原问题进展。

## 文件级依赖扫描（Lead 扫描；C3 计数含注释，以下按语义复核）

| 类别 | 代表文件 | 结论 |
|---|---|---|
| **C3-free（有效，可继续）** | `Mzk1IQFiniteAdeleRestrictedActual`/`Structures`（C3=0）、`Mzk1B5FractionalAbsNormFormula`/`CountNumDen`/`FinsumSummable`/`FractionalExpansionUncond`/`LocalGlobalProductFormula`/`FullProductFormula(Count)`（C3=0）、`Mzk1NormArchCKActual`（C3=0）、`Mzk1HullUBGeneralFinal`/`PaperVRawBinding`/`UBC0Absorption`（T-only）、`Mzk1ThetaVGeneralUnconditional`/`ScaleOffsetIdentity`（T-only）、`Mzk1C3S1902UnitMassCitizen`/`NativeFinitePlaceDictionary`（T-only）、`Mzk1P3TensorCore`/`DomainDecompositionMap`/`TraceDualityCoefficient`/`ExponentNet`（p/places/tuple/有限 E_i） | 数学内容有效；可作 P0/P1/P2/P3 供体 |
| **C3-typed（vacuous，需 re-type）** | #1：`Mzk1P7ComparisonConditionalFinal`、`Mzk1S1915Comparison`、`Mzk1C3S1902BallMassFormula`/`LowerBound`；#3：`Mzk1Ob33SourceIdentification`、`Mzk1Ob33DetLine`；#4：`Mzk1P7MultiradialProduction`；#6：`Mzk1C3DKeyMap`；#7 表面：`Mzk1P7ThetaDeg`/`ThetaDegC3`/`ThetaDegWeight`/`ThetaDegCancel`/`C3BlockMeasure`；#8：`Mzk1P7ContractMap`、`Mzk1P7ContractMarginConsumer`；#10 部分：`Mzk1C3S1902BlockEquivData` | 旧 C3 域为空 ⇒ 不能作为原目标证据；须迁到 P0 native core / P3 tensor core 后重述并重证消费者 |
| **边界/需逐句复核** | `Mzk1Ob33DetLineFromBadPrimeSource`、`Mzk1B5RelativeDetLogExpansion`、`Mzk1B5Assembly` 等：数学对象是 FractionalIdeal/line bundle，但接口可能带 C3 | 检查是否 C3 仅作为未用参数；若能去参数则有效，否则 re-type |

## 行动原则
1. P0（hull）产出的 native core/readout/consumer 是**新锚点**；旧 C3 green 文件只作“数学引理供体”（如 #7 的维数/域分解数学，经 P3 core 复用）。
2. #1 的路线 A/HullQDictionary 必须**整体 re-type** 到 native（或 L 侧）比较；在此之前 #1 不得宣称条件版“已收口”。
3. #3 的 B5 数学（C3-free）保留；Ob33 arithmetic-degree 部分需 native q-pilot line source 重述（qpilot source 是否 C3-typed 待查）。
4. #7 的 DONE 只作为“数学内容（域分解/维数/权重/相消）”——在旧 C3 表面 vacuous；P3 core 是有效载体。
5. #5/#9/#2/#10 的 C3-free 部分继续有效；#6/#8/#10 C3-typed 部分随 P0/P3 重述。
