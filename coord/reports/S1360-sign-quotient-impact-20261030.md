# S1360 SourceSignQuotientGeometricCore 不一致：消费者与影响审计

日期：2026-10-30 22:40（Asia/Shanghai）
工作目录：`D:\lean`
审计范围：S1360 原始发现的全签名保持不一致；当前树中的修复（genus-only）；
    `SourceDefinition31Data` / D9 / 已 actual/exact 消费者。
结论：**EXIT=0；不写新 Lean；未发现任何现有声明依赖旧的 false 定理。**

> 重要时间性说明：审计期间工作树正被并发修改。本文以 2026-10-30 22:38–22:40
> 快照为准。当前 S1360 已由 S1370/S1374 修复，且 S1360 本体的
> `s1360*_false` 三个定理已不存在。原始版本（SHA256
> `7B6BB175E731574E3BA7CF108EFBEF5E4544B08576906AF3E075D62B058A2A5E`）
> 见 AUDIT_LEDGER 旧 S1367 行与 S1360 md 的“22:15 final”段。

## 0. 一页结论

1. **原始不一致成立**：`SourceOrbicurveScalarExtension.signature_preserved`
   连同 `xK_eq_extension` 强制 `sourceTypeOneLTorsion l = sourceTypeOneOne`；
   原始 S1360 在 `S1280Arithmetic l` 上给出三个 `False` 定理。
2. **当前树已修复**：`SourceOrbicurveScalarExtension` 只保留
   `genus_preserved`；`signature_preserved`、`stackyOrders_preserved`、
   `punctures_preserved` 已删除；新增 `signature_genus_preserved`。
   S1370/S1374 证明三个记录的 signature typing 一致，S1360 改写为一致性定理。
3. **旧 false 定理没有消费者**：全仓 `LeanFormal`/`tmp/sheaf` 中没有任何
   `.lean` 文件 import S1360（只有 S1360AuditProbe）；旧
   `signature_preserved` 在 live Lean 代码中没有调用者（只有冻结的
   `tmp/sheaf/gap-exploration-20261030/snapshots/...` 快照与说明性注释）。
4. **`SourceDefinition31Data` 与 D9 不受类型级影响**：它们不包含
   `SourceSignQuotientGeometricCore`/`SourceSignQuotientData`/
   `SourceCompletionSignQuotient` 字段；D9 是五个 `(Prop, proof)` 对，
   D6 槽是抽象 `SourceOrbicurveClause`。因此 **不需要重述**。
5. **实际/精确消费者**：S1330、S1357、ClauseEToD7Actual、
   ClauseEToD7LocalGroupActual、NativeSourceTorsionGapsActualConstruction
   等在修复后均重新编译 EXIT=0；它们仍是**条件**于 S/C/T 的结果，修复不会
   自动提供这些记录的inhabitant。无需类型级重述，只需保持“conditional”
   标签并重新编译 olean。
6. **仍需重述的是文档/状态，不是 Lean 类型**：S1360.md、AUDIT_LEDGER 旧
   S1367 行、coord/STATE 的 S1360 行仍引用旧 SHA 和旧 `False` 说法；需
   更新。是否进一步把 K-side 重述为 paper-faithful
   `S1360KCoreBaseChange`/`S1360KCoreIdentification` 是**语义选择**：
   最小修复只解决逻辑一致性，仍保留 `xK = xKExtension.result` 的标识。

## 1. 原始缺陷与当前修复

### 1.1 原始缺陷（pre-fix）

三处同构字段：

| 记录 | 位置 | 关键字段 |
|---|---|---|
| `SourceSignQuotientGeometricCore` | `LeanFormal/IUT/IUTI/InitialTheta/SourceSignQuotientConstruction.lean:30` | `xF`, `xF_geometry`, `xK`, `xKExtension`, `xKType`, `xK_eq_extension` |
| `SourceCompletionSignQuotient` | `LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean:37` | 同上 |
| `SourceSignQuotientData` | `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:578` | 同上 + `V`/`V_mod_bad`/`epsilon` |

原始矛盾链：

1. `xF_geometry.signature : xF.signature = sourceTypeOneOne`；
2. `xKType : xK.signature = sourceTypeOneLTorsion l`；
3. `xK_eq_extension : xK = xKExtension.result`；
4. 旧 `SourceOrbicurveScalarExtension.signature_preserved :
   xKExtension.result.signature = xF.signature`；
5. 因此 `sourceTypeOneLTorsion l = sourceTypeOneOne`；
6. 但两者 punctures 为 0 与 1，矛盾。

原始 S1360 的三个定理只对 `A = S1280Arithmetic l` 陈述，但证明不依赖
`S1280Arithmetic` 的特殊性质；同一证明对任意
`A : InitialThetaArithmeticData l` 逐字成立。原始文件没有记录这个 generic
版本，故“任意 A 记录均无inhabitant”在原始文件里只是语义上显然、形式上未
packaged。

### 1.2 当前修复（post-fix）

`SourceDefinition31Quantifiers.lean`（当前工作树，uncommitted）：

- `SourceOrbicurveScalarExtension` 现在只有
  `result`, `stackExtension`, `target_stack`, `genus_preserved`；
- 删除 `stackyOrders_preserved` / `punctures_preserved`；
- `signature_preserved` 删除，替换为
  `signature_genus_preserved : E.result.signature.genus = X.signature.genus`；
- `SourceSignQuotientData.xK_signature` / `cK_signature` 改为直接返回
  `sourceTypeOneLTorsion l` / `sourceTypeOneLTorsionPlusMinus l`；
- 新增 `xK_genus`, `cK_genus`, `cF_genus`。

修复文件：

| 文件 | 作用 | 当前证据 |
|---|---|---|
| `tmp/sheaf/xif/paper/S1370SourceSignQuotientFix.lean` | 主修复记录；generic 三个记录的 signature typing | `lake env lean` EXIT=0；SHA256 `31A2982568C895A882FDEE20E34376CC0D31933DFA91C73BBABA1D5D156C1C18` |
| `tmp/sheaf/xif/paper/S1374SourceSignQuotientFix.lean` | 独立复核；`s1374_no_full_signature_preservation` 等 | `lake env lean` EXIT=0；当前 SHA256 `9BAC620C58F9A5F8AD4D11C6FECF193CCA21C008B75529B44945671242C725D4`（22:37 版；ledger 里的 33B9... 是更早一版） |
| `tmp/sheaf/xif/paper/S1360D9OrbicurveSlotActual.lean` | 已改写；不再有 `_false`；新增三个 signature typing 定理 | `lake env lean` probe EXIT=0；当前 SHA256 `17CA2C9A70F6CC3C9E4F8311425EB1E3FE7922F92885F2C609B81BC70F355157`，397 行，17051 字节 |

`S1360` 当前相关声明（行号为 22:38 快照）：
`S1360KCoreBaseChange` (:197), `S1360KCoreIdentification` (:214),
`s1360SignatureTyping_of_fields` (:238),
`s1360SourceSignQuotientGeometricCore_signature_typing` (:260),
`s1360SourceCompletionSignQuotient_signature_typing` (:273),
`s1360SourceSignQuotientData_signature_typing` (:286),
`S1360D9OrbicurveSlot` (:300)。

语义注意：最小修复使记录一致，但保留
`xK = xKExtension.result`（即 X_K 是 X_F 的标量扩展）。论文
Definition 3.1(d) 的 K-core 是 `C_K = C_F x_F K`，X_K 是 C_K 的
finite-etale cover；`S1360KCoreBaseChange`/`S1360KCoreIdentification`
才是 paper-faithful 的 K-side。若只求一致性，最小修复足够；若求原文语义，
仍需把 core/clause D 的 K-side 重述到 K-core identification。

## 2. 消费者清单

### 2.1 直接消费 `SourceSignQuotientGeometricCore` 的 Lean 文件

| 文件 | 关键声明 | 角色 | 修复后是否需要重述 |
|---|---|---|---|
| `SourceSignQuotientConstruction.lean` | `SourceSignQuotientGeometricCore` (:30), `toSourceCompletionSignQuotient` (:74), `toSourceSignQuotientData` (:196) | 定义与投影 | 否（类型未再改；可选 K-core 重述） |
| `SourceCompletion.lean` | `SourceCompletionSignQuotient` (:37), `toSourceSignQuotientData` (:222), `ofSourceSignQuotientData` (:332), `SourceCompletion` (:380), `toSourceNativeInitialThetaData` (:601), `ofSourceNative` (:1105), `nonempty_iff_native_nonempty` (:1333) | 容器/转换 | 否 |
| `SourceDefinition31Quantifiers.lean` | `SourceSignQuotientData` (:578), `xK_signature` (:654), `xK_genus` (:659), `cK_signature` (:667), `cK_genus` (:672), `cF_genus` (:681), `SourceClauseD` (:1106) | 数据与 clauses | 否（已随修复改 statement） |
| `SourceDefinition31SignQuotientSupplyReduction.lean` | `geometricCoreOfSignQuotientData` (:134), `nonempty_sourceSignQuotientData_iff_core_and_selection` (:190), `SourceSignQuotientSupply` (:232), `SourceSignQuotientGeometricCoreSupply` (:237), 两个 iff (:249, :262), `sourceNativeArithmeticToSourceGate_of_units` (:396) | supply 归约 | 否；supply 状态从“false”回到“open” |
| `SourceGeometricCoreFieldUnitsReduction.lean` | 六个 unit/bundle (:87–:158), 六个 block (:162–:194), `toFieldUnits` (:260), `sourceSignQuotientGeometricCoreOfFieldUnits` (:279), `nonempty...iff_fieldUnits` (:324), supply/iff (:354–:384), gate transfer (:398) | 六单元拆分 | 否；同上是 open card |
| `SourceClauseAssemblyUnitsReduction.lean` | `SourceClauseELocalFamilyUnit` (:89), `SourceClauseFBoundaryUnit` (:250), `etaleStackInstanceSupply_of_geometricCore` (:469), `geometricCoreStackUnit_of_geometricCoreSupply` (:483) | clause 单元 + stack 必要件 | 否 |
| `SourceDefinition31NativeContractBridgeReduction.lean` | `ContractRootSignQuotientSupply` (:263), `contractNativeRecordBridge_implies_signQuotientSupply` (:267) | contract/native 桥的必要卡 | 否；状态更新 |
| `SourceDefinition31A2GateReduction.lean` | `SourceNativeWitnessSupply` (:93), `witnessOfNativeData` (:98), `sourceNativeArithmeticToSourceGate_iff_witnessSupply` (:126) | A2 门的 witness 形式 | 否 |
| `SourceClauseConstructors.lean` | `SourceClauseConstructionWitness` (:1088), `sourceData` (:1106) 等 | 构造器层 | 否（仍从假设的 S 投影） |
| `Example36SourceObjectBridge.lean` | `GeometricCoreCard` (:170) | source-layer card | 否；card 从 false 回到 open |
| `SourceEtaleStackInstanceSupplyReduction.lean` | 仅注释提到 core (:56–:57) | 说明 | 否 |
| `verification/a2_source_axiom_audit.lean` | `#print axioms` (:17–:20) | 只读审计 | 否（仅需更新说明） |

### 2.2 消费 `SourceSignQuotientData` / `SourceCompletionSignQuotient` 的 broader 文件

这些文件都**以记录为显式参数**，没有构造记录；因此它们从未把不一致变成
无条件的 `False`，只是在该记录不可inhabitant时成为 vacuous。

| 文件 | 关键声明 | 依赖方式 | 当前状态 |
|---|---|---|---|
| `SourceCompletion.lean` | 见上 | 容器 | EXIT=0 |
| `SourceSignQuotientConstruction.lean` | 见上 | 核心转换 | EXIT=0 |
| `SourceTorsionCarrierReduction.lean` | :181/:241 的 `S` 变量 | clause 层参数 | 条件；无类型重述 |
| `SourcePlaceTateComparisonSynthesis.lean` | :139 `S` 变量 | clause 层参数 | 条件 |
| `SourcePlaceQParameterUniformization.lean` | :124 `S` 变量 | clause 层参数 | 条件 |
| `SourceClauseConstructors.lean` | 多个 `S` 变量与 `xK_eq_extension` cast (:618, :670, :708, :746) | 构造器 | 条件；cast 在修复后仍 typecheck |
| `SourceDefinition31D4D9Supply.lean` | `D9CompatibilitySupply` (:198), `D4D9Supply` (:246), `toSourceData` (:258) | **不消费 core** | EXIT=0；无影响 |
| `SourceDefinition31Boundary.lean` | `SourceDefinition31Data` (:619) | **不消费 core** | EXIT=0；无影响 |
| `SourceDefinition31ArithmeticCompatibilitySlots.lean` | 五个 D9 槽 (:88–:236) | **不消费 core** | 无影响 |
| `SourceDefinition31RootLemmas.lean` | D9/D10 gates (:5172–:5178) | 只用 `SourceDefinition31Data` | 无影响 |

### 2.3 tmp 中的 actual/exact 消费者

| 文件 | 关键声明 | 依赖 | 修复后编译 | 重述 |
|---|---|---|---|---|
| `S1330CuspEpsilonActual.lean` | `S1330PaperCusp` (:112), `S1330PaperEpsilon` (:117), `S1330RealCuspCoordinate` (:329), `S1330CuspClauseOfRealCuspCoordinate` (:342), `S1330RealCuspCoordinateMissing` (:362) | `S : SourceSignQuotientData (S1280Arithmetic l)` | EXIT=0 | 否；仍 conditional |
| `S1357RealCuspCoordinateActual.lean` | `S1357PaperCusp` (:18), `S1357EpsilonMap` (:24), `s1357RealCuspCoordinateOfMap` (:30), `s1357RealCuspCoordinateRequired` (:65) | 同上 | EXIT=0 | 否 |
| `ClauseEToD7Actual.lean` | `clauseEPlaceEquiv` (:59), `ClauseEToD7PlaceData` (:80), `clauseEToD7PlaceData` (:92), `ClauseEToD7LocalGroupData` (:99), `clauseEToD7Compatibility_of_localGroupData` (:118), `clauseEToD7_status` (:156) | `C : SourceCompletion` | EXIT=0 | 否 |
| `ClauseEToD7LocalGroupActual.lean` | `finitePlaceData` (:47), `infinitePlaceData` (:63), `ClauseEToD7LocalGroupBijection` (:78), `localGroupData_nonempty_iff_bijection` (:114), `clauseEToD7LocalGroup_status` (:125) | `C : SourceCompletion` | EXIT=0 | 否 |
| `NativeSourceTorsionGapsActualConstruction.lean` | `nativeSourceTorsionGapsActual` (:49), 三条 spec (:63/:70/:77) | `T : SourceNativeInitialThetaData`, `S`/`D` | EXIT=0 | 否 |
| `NativeTorsionGapsActual.lean` | `actualNativeTorsionObjects` (:81), `nativeSourceTorsionGaps` (:91), `MissingNativeTorsionGaps` (:105) | `S`/`D` | 旧 olean/未重编 | 否；deprecated |
| `NativeTorsionGapsActualField.lean` | `actualNativeTorsionCarrier` (:34), `NativeTorsionGapsMissingFields` (:43), `nativeSourceTorsionGapsOfFields` (:51) | `S`/`D` | 未重编 | 否 |
| `NativeTorsionGapsIntegration.lean` | `integratedTorsionCarrier` (:61), `NativeTorsionGapsPartial` (:83), `toNativeSourceTorsionGaps` (:91) | `S`/`D` | 未重编 | 否 |
| `NativeCuspRealActual.lean`, `NativeCuspCountActual.lean`, `NativeD7CuspActual.lean`, `NativeSourceAssembly*`, `NativeAssemblySplitIntegration.lean` | 均以 `T : SourceNativeInitialThetaData` 或 `SourceCompletion.ofSourceNative T` 为参数 | `T`/`C` | 未逐一重编 | 否；conditional |
| `n8/closure/NativeD7Proof.lean`, `NativeSourceSectionsCuspActual.lean`, `NativeSectionsCuspFieldsActual.lean`, `NativeBadFintypeDeep.lean`, `NativeSourceAssembly.lean` | 均以 `C : SourceCompletion` 或 `T` 为参数 | `C`/`T` | 未逐一重编 | 否 |
| `LocalGroupBijectionActual.lean` | `profiniteImageEquiv` (:47), `finiteLocalGroupImageEquiv` (:53), `infiniteLocalGroupImageEquiv` (:67), `localGroupImageBijections_actual` (:95) | `C`/`S` | **EXIT=1（pre-existing）**：`ProfiniteOpenEmbedding` 未导入/未知 | 不是 S1360 造成；该文件无可用 olean，不应计为 actual |
| `CuspRealizationActual.lean` | `nativeCuspObject` (:41), `CuspCoordinateMap` (:49), `cuspRealizationDataOfCoordinateMap` (:64) | `T` | **EXIT=1（pre-existing）**：`HyperbolicOrbicurve (nativeCompletion T).sourceSignQuotientData.cK` 类型误用 | 不是 S1360 造成；无 olean |

### 2.4 直接依赖旧 false 定理的声明

**没有。** 具体证据：

- `s1360SourceSignQuotientGeometricCore_false` /
  `s1360SourceCompletionSignQuotient_false` /
  `s1360SourceSignQuotientData_false`：在 `LeanFormal` 与
  `tmp/sheaf` 的 `.lean` 文件中 import/使用数为 **0**（只有旧 log/md
  引用）。当前 S1360 本身也已删除这三个声明。
- `SourceOrbicurveScalarExtension.signature_preserved`：live Lean 调用者
  只有 `SourceSignQuotientData.xK_signature` / `cK_signature`（已随修复改写）
  和旧 S1360 的 `_false`（已删除）。其余命中只在冻结快照
  `tmp/sheaf/gap-exploration-20261030/snapshots/...` 与说明性注释中。
- 旧的 `xK_signature : xK.signature = xF.signature` /
  `cK_signature : cK.signature = cF.signature` 的外部消费者为 **0**；
  `xK_eq_extension` 的其他使用（`SourceClauseConstructors`、
  `SourceGeometricCoreFieldUnitsReduction`、
  `SourceDefinition31SignQuotientSupplyReduction`）只是 cast/投影，
  不依赖全签名保持。

因此：**没有现有 Lean 定理因为“依赖 false 定理”而需要改证明**；需要改的是
文档/状态，以及可选的语义 K-core 重述。

## 3. 对 `SourceDefinition31Data` / D9 的影响

### 3.1 `SourceDefinition31Data`

`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:619`：

- 字段：`arithmetic`, `selectedPlaces`, `badPlaces`, `reduction`,
  `torsion`, `orbicurve : SourceOrbicurveClause`, `sections`, `cusp`,
  五组 `(Prop, proof)` 兼容对；
- **没有** `SourceSignQuotientGeometricCore`、`SourceSignQuotientData`、
  `SourceCompletionSignQuotient`、`HyperbolicOrbicurve`、`xK_eq_extension`
  或任何全签名保持字段；
- `orbicurve` 是抽象的 13 字段 `SourceOrbicurveClause`（`curve : Type` 等），
  不使用 `Iut.HyperbolicOrbicurve` 的 signature。

结论：**类型/字段/定理无需重述**。S1360 的不一致不会使
`SourceDefinition31Data` 的inhabitant变成不可能；D9/D10 gate 仍按原接口
保持 open，与 S1360 无关。

### 3.2 D9

`D9CompatibilitySupply`
(`SourceDefinition31D4D9Supply.lean:198`)：

- 五个任意 `(Prop, proof)` 对：`reduction`, `torsion`, `orbicurve`,
  `sections`, `cusp`；
- 不引用签名、不引用 core、不引用 `SourceSignQuotientData`。

`D4D9Supply` (:246) 的 `orbicurve` 字段是抽象
`Theorem311Source.SourceOrbicurveClause`；`toSourceData` (:258) 通过
`d11EntryData` 组装，所有字段来自显式 supply。**无影响**。

D9 的 actual/exact 文件：

- `S1339D9CompatibilityActual.lean`：只构造 `ArithmeticSectionCompatibility`
  并记录其余槽的 first field；EXIT=0。
- `S1342D9PlaceSectionActual.lean`：section 实际，reduction 条件于
  `BadPlaceQParameterCards`；EXIT=0。
- `S1355D9TorsionCuspActual.lean`：torsion 条件于 D5 clause，cusp 条件于
  `TorsionQuotientBoundaryOrigin`；EXIT=0。
  它们都不消费 `SourceSignQuotientData`/`SourceSignQuotientGeometricCore`，
  因此 **不需要重述**。

### 3.3 唯一的 contract-side 桥

`SourceDefinition31NativeContractBridgeReduction.lean`：

- `ContractRootSignQuotientSupply` (:263) :=
  `∀ S : SourceDefinition31Data, Nonempty (SourceSignQuotientData S.arithmetic)`；
- `contractNativeRecordBridge_implies_signQuotientSupply` (:267) 从
  contract-to-native bridge 推出它。

这是 `SourceDefinition31Data` 与受影响记录的唯一直接连接。它的类型不需要
重述；但：

- 原始不一致版本下，若存在任何 `S` 且 `S.arithmetic = S1280Arithmetic l`，
  该卡被 S1360 的 `s1360SourceSignQuotientData_false` 直接反驳；
- 修复后它回到 open card；
- 它仍然不是 `SourceDefinition31Data` 的字段，也不是 D9 的字段，故不影响
  D9/D10 的接口。

## 4. 是否需要重述：逐项裁决

| 对象 | 类型/陈述重述？ | 说明 |
|---|---|---|
| `SourceDefinition31Data` | **否** | 不含受影响记录 |
| `D9CompatibilitySupply` / `D4D9Supply` | **否** | 五个 Prop 对 + 抽象 clause |
| D9 actual 文件（S1339/S1342/S1355） | **否** | 不消费 core |
| `SourceSignQuotientGeometricCore` | **否（逻辑上）** | 当前 genus-only 修复已一致；可选 paper-faithful K-core 重述 |
| `SourceCompletionSignQuotient` | **否（逻辑上）** | 同上 |
| `SourceSignQuotientData` | **否（逻辑上）** | 同上；`xK_signature`/`cK_signature` 已改 |
| `SourceCompletion` / `SourceInitialThetaTuple` / `SourceNativeInitialThetaData` | **否** | 只是包含修正后的记录；类型未坏 |
| `SourceClauseConstructionWitness` | **否** | 包含修正后的记录；构造器仍条件于 S |
| `SourceGeometricCoreKSideUnit` / `SourceGeometricCoreFieldUnits` | **否（逻辑上）** | 修复后一致；可选 K-core 重述 |
| `SourceClauseD`（`k_quotientExtension` / `k_quotient_map_eq_extension`） | **否（逻辑上）** | 修复后 typecheck；若采用 K-core，则这两个字段应随 K-side 重述 |
| supply/gate 定义（`SourceSignQuotientSupply`, `SourceSignQuotientGeometricCoreSupply`, `SourceGeometricCoreFieldUnitsSupply`, `SourceNativeWitnessSupply`, `SourceNativeArithmeticToSourceGate`） | **否** | 类型不变；状态从“false/impossible”回到“open” |
| `ContractRootSignQuotientSupply` | **否** | 类型不变；状态 open |
| 实际/精确消费者（S1330 等） | **否** | 仍 conditional；重新编译即可 |
| S1360.md / AUDIT_LEDGER S1367 行 / coord/STATE S1360 行 | **是（文档）** | 旧 SHA、旧 `False` 叙述已失效 |
| 旧 `S1360Compile.log` / `S1360Build.log` | **归档/标注 stale** | 与当前 17CA 文件不一致 |
| vendor 快照中的旧 `signature_preserved` | **不重述、不消费** | 冻结快照，非 build 输入 |

## 5. 验证记录（EXIT=0）

本审计未写新 Lean；只做 `#check` 与现有文件的重编译检查。所有下列命令均
EXIT=0（除非标注 pre-existing failure）：

| 命令 | 结果 |
|---|---|
| `lake env lean tmp/sheaf/xif/paper/S1360AuditProbe.lean` | EXIT=0；确认三个 signature typing 定理与 K-core 结构；axioms = propext/Classical.choice/Quot.sound |
| `lake env lean tmp/sheaf/xif/paper/S1370SourceSignQuotientFix.lean` | EXIT=0；14 条 `#print axioms` 全部 triad |
| `lake env lean tmp/sheaf/xif/paper/S1374SourceSignQuotientFix.lean` | EXIT=0；独立复核 |
| `lake env lean LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31SignQuotientSupplyReduction.lean` | EXIT=0 |
| `lake env lean LeanFormal/IUT/IUTI/HodgeTheater/SourceGeometricCoreFieldUnitsReduction.lean` | EXIT=0 |
| `lake env lean LeanFormal/IUT/IUTI/HodgeTheater/SourceClauseAssemblyUnitsReduction.lean` | EXIT=0 |
| `lake env lean LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean` | EXIT=0 |
| `lake env lean LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31A2GateReduction.lean` | EXIT=0 |
| `lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31D4D9Supply.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/S1330CuspEpsilonActual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/S1357RealCuspCoordinateActual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/ClauseEToD7Actual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/ClauseEToD7LocalGroupActual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/NativeSourceTorsionGapsActualConstruction.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/S1339D9CompatibilityActual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/S1342D9PlaceSectionActual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/S1355D9TorsionCuspActual.lean` | EXIT=0 |
| `lake env lean tmp/sheaf/xif/paper/LocalGroupBijectionActual.lean` | **EXIT=1（pre-existing）**：`ProfiniteOpenEmbedding` 未知；与 S1360 无关 |
| `lake env lean tmp/sheaf/xif/paper/CuspRealizationActual.lean` | **EXIT=1（pre-existing）**：类型误用；与 S1360 无关 |

当前快照 SHA256：

- S1360D9OrbicurveSlotActual.lean：
  `17CA2C9A70F6CC3C9E4F8311425EB1E3FE7922F92885F2C609B81BC70F355157`
  (397 lines, 17051 bytes, 22:30:20)
- S1370SourceSignQuotientFix.lean：
  `31A2982568C895A882FDEE20E34376CC0D31933DFA91C73BBABA1D5D156C1C18`
- S1374SourceSignQuotientFix.lean：
  `9BAC620C58F9A5F8AD4D11C6FECF193CCA21C008B75529B44945671242C725D4`
  (current; ledger may cite the earlier 33B9...)
- SourceDefinition31Quantifiers.lean：
  `0E6BBBF2536A5DB72DE5A17AAF0B0E9FF5432D4465928BBD54C7C7E7AD10AA81`

未运行：全 Project `lake build`（并发有大量无关 uncommitted 修改；本次只审计
S1360 影响，不宣称全构建绿色）。

## 6. 仍待处理的项

1. **文档更正（必须）**
   - `tmp/sheaf/xif/paper/S1360D9OrbicurveSlotActual.md` 仍是 22:15 旧版：
     引用旧 SHA 7B6...、三个 `_false`、以及“records uninhabited”结论；
     应改写为 S1370/S1374 的已修复叙述和当前 SHA 17CA...。
   - `AUDIT_LEDGER.md` 旧 S1367 行（约 :9478）仍列旧 SHA 7B6...；
     现有 S1374 追加段（约 :9497）已经更正，但旧表行未更新，需明确
     superseded。
   - `coord/STATE.md:3262` 仍列旧 SHA 7B6...，需更新为 17CA... 和
     “post-fix consistency typing”。
2. **归档旧 log**：`S1360Compile.log`、`S1360Build.log` 是 pre-fix
   产物；不要作为当前证据。新的验证 log 是 S1370/S1374/S1360AuditProbe
   对应输出。
3. **重新编译消费者 olean**：S1330 (21:41)、S1357 (21:45)、
   ClauseEToD7Actual (10/28) 等 olean 早于 22:23 的基础修复；虽然源码
   `lake env lean` EXIT=0，但 gate 若要求 olean=YES，必须重新生成。
4. **可选 K-core 语义重述**：若要求 Definition 3.1(d) 的论文语义，把
   `SourceSignQuotientGeometricCore`/`SourceSignQuotientData` 的 K-side
   从“X_K = X_F 的标量扩展”改为
   `S1360KCoreBaseChange` + `S1360KCoreIdentification`（C_K = C_F x K，
   X_K -> C_K finite etale）；同时重述 `SourceClauseD` 的
   `k_quotientExtension`/`k_quotient_map_eq_extension`。若只求一致性和
   不阻断 D9，可保留最小修复并登记该语义债。
5. **不要消费**：vendor 快照、`LocalGroupBijectionActual` 与
   `CuspRealizationActual`（pre-existing 编译失败/无 olean）、S939
   （`inferInstance : Nonempty SourceNativeInitialThetaData` 无依据且文件未编译）。
