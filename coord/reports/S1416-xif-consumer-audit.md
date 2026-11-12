# S1416: SourceDefinition31Data → S605 → FinalXiF/xi-f 消费者审计

日期：2026-10-31（Asia/Shanghai）  
范围：**只读**静态消费者审计；未修改任何 Lean 文件，未运行 lake/Lean/Project/comparator/公理检查。  
基线：HEAD `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`，工作树 535 项未提交；关键文件 SHA256 见 §10。  
快照说明：审计期间有并发 agent 写入/删除 probe（例如 `_S1415Probe0.lean` 出现、`_S1395Probe.lean` 消失），模块计数是快照值；关键文件哈希在报告写入前重新核对。

方法：解析 `D:/lean/tmp/sheaf` 与 `D:/lean/LeanFormal` 下全部 Lean 模块的 import 边，计算 forward closure（目标实际依赖）与 reverse closure（谁依赖源）；再用标识符共现和声明名检索区分“import 了”与“值真的被消费”。共扫描 4,000+ 个模块（快照时 4,023；审计末尾并发新增后为 4,033）。不把 `#check` probe、注释、frozen snapshot 当作生产消费者。

---

## 0. 结论（先看）

1. **不存在字面名为 `FinalXiF` 的 Lean 声明或模块。** 全库 Lean 检索为零；coord 中只有一句“不要先写新的 FinalXiF 包装”。本报告把实际存在的 xi-f 终点分成 E1–E5 审计（§1）。
2. **`SourceDefinition31Data → S605` 不是实际边。** S605 的输入是 `SourceNativeInitialThetaData`，不是 `SourceDefinition31Data`；全库没有任何文件同时出现 `SourceDefinition31Data` 与 `qVFamilyK`。两者是两条并行分支，不是上下游。
3. **S605 仍未接通最终目标。** 活跃 import 消费者是 `S618` 与审计末尾新增的 `S1413`；但 `S1413` 只是 import 了 S605，实际使用的是 S436 的 `kSidePlace`，没有引用 S605 的任何声明，且 `S1413` 自身 0 消费者、无 olean。S605 依赖的 `KSideQVComparisonData`（place_eq / Tate uniformization / order_eq）仍无 inhabitant；S618 只把它从显式字段再条件构造一次，未被任何文件使用。
4. **S1136 没有生产消费者。** 唯一 importers 是并发 probe `_S1415Probe0`–`_S1415Probe3`。`_S1415Probe3` 做了 `glue := id`、`hullLog := thetaHullLog` 的平凡实例化，并把 `sourceXiFInclusion_of_bounded`（正是 q≤hull 目标不等式）作为 `theta_le` 字段输入，因此是循环使用，不是生产桥。S1136 本身仍只是对四个自由 Real 的单调性练习，没有证明 `hullLog = glue thetaHullLog` 的源内容。
5. **D5–D9 构造没有被 xi-f 最终目标消费。** 所有终点 E1–E5 的 import 闭包中都没有 `S1298`（D5）、`S1398`（D6）、`S1403`（D7/D8/D9 bundle）、`S1280`、`S1322`、`NativeSourceAssembly`、`D4D9Supply`。唯一完整 D5–D9 gap assembler `S1322` 的消费者为 0；canonical `D4D9Supply.toSourceData` 在 `tmp/sheaf` 中没有任何调用者；`S1403` 自身也不含 D5、D6 和五个 D9 compatibility 对。
6. **最终 E1/E2 的 `SourceDefinition31Data` 只是类型级残留。** E1 的 321 模块闭包中，唯一路径是
   `PaperXiFFinalActual → PaperLevelXiFTargetBridgeActual → PaperLevelXiFTargetActual → ProcessionNormalizationWeightsActual → SourceOriginalInput → SourceDefinition31Boundary`。
   `VbadPlaceIndexingActual`/`ProcessionNormalizationWeightsActual` 中真正提到 `SourceDefinition31Data` 的只是 `NativeBadIndexingBridge`/`VbadPlaceIndexingObstruction` 这些**未被目标定理使用**的 gap Prop；目标实际用的是 native `nativeBadLocalWeight`。
7. **因此，当前不存在“SourceDefinition31Data → S605 → FinalXiF”的链；只有三块互不相连的岛：** 抽象 contract / D5–D9 组装、native K-side q 比较（S605/S618）、native qVFam/root-hull 标量终点（E1/E2）。S1136 是第四块孤岛。

---

## 1. FinalXiF/xi-f 终点清单

全库没有 `FinalXiF` 声明。实际存在以下终点（按直接消费者数排序）：

| ID | 声明 | 输入 | 直接消费者 | 是否消费 S 值 | 是否含 D5–D9 | 是否含 S605/S1136 |
|---|---|---|---|---|---|---|
| E1 | `PaperXiFFinalActual.paperLevelXiF_actual`（`PaperXiFFinalActual.lean:54`） | `T : SourceNativeInitialThetaData` | 2（`FinalAxiomAuditActual`、`FinalUnconditionalAxiomProbe`） | 否 | 否 | 否 |
| E2 | `PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget`（`:66`） | `T : SourceNativeInitialThetaData` | 5（含 E1、`BadPlacePaperNormalizedTargetBridgeActual`、两个 probe） | 否 | 否 | 否 |
| E3 | `PaperXiFClosedActual.paperXiF_actual`（`:77`） | `T : SourceNativeInitialThetaData` | 0 | 否 | 否 | 否 |
| E4 | `PaperXiFCompileGate.paperXiF_assembly_conditional`（`:69`） | `I : OriginalInput` + `L : ThetaLinkActual` + `hlink` | 1（`XiFAxiomProbe`） | 仅类型级；无 I inhabitant | 否 | 否 |
| E5 | `PaperXiFAssemblyActual.paperXiF_assembly_conditional`（`:116`） / `PaperXiFUnconditional` 条件组装 | `PaperUnconditionalData`（含 `OriginalInput`） | 0 / 7 | 仅类型级；无 inhabitant | 否 | 否 |
| — | `PaperAssemblyActualFinal` | 无定理，仅 `#check` gate | 0 | 否 | 否 | 否 |

要点：

- **E1/E2/E3 的目标类型是 `ActualPaperXiFTarget T`，其中 `T : SourceNativeInitialThetaData`。** 定义在 `PaperLevelXiFTargetActual.lean:123-125`：
  `actualQPilotSignedLogClassical T ≤ actualThetaHullLogRoot T`。
  这里 q 侧是 `qVFamTensorP`/`qVFamNormalizedCoefficient`/native bad weights；Theta 侧是 root theta closure hull 的归一化 log。没有 `SourceDefinition31Data` 参数。
- **E4 是 DAG 节点 `xif-source-construction` 声明的目标**（`dag/nodes/xif-source-construction.json:10-12`），但它是条件定理：`I : OriginalInput`、`L : ThetaLinkActual`、`hlink : L.link_identification` 都是假设，没有任何生产 inhabitant。它不代表已经消费了 S 值。
- **E1/E2 的闭包不含 S605、S618、S1413、S1136、S1280、S1321、S1322、S1298、S1398、S1403、`NativeSourceAssembly`、`D4D9Supply`。** 这是 import 图计算结果，不是靠注释判断。审计末尾新增的 S1413 和 S1415 probes 也都不在 E1–E5 闭包中。
- 多个终点互不引用：E3 消费者 0，E5 assembly 消费者 0，`PaperXiFAssemblyActual` 消费者 0。当前没有单一“最终消费者”把它们串起来。

---

## 2. 谁消费 `SourceDefinition31Data`

### 2.1 定义与投影

- 定义：`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:619`，18 个字段：arithmetic、selectedPlaces、badPlaces、reduction、torsion、orbicurve、sections、cusp，以及 5 个不透明 `(Prop, proof)` compatibility 对。
- 到 `InitialThetaInput` 的投影：同文件 `:783` `toInitialThetaInput`；`:822-827` 给出 torsionImage = `S.torsion.imageContainsSL2`、cuspParameter = `S.cusp.epsilon` 等 rfl 投影。

### 2.2 真正的 S 值生产者（都是条件的或死的）

| 生产者 | 位置 | 从什么构造 | 直接消费者 | 到最终目标 |
|---|---|---|---|---|
| `SourceDefinition31RootLemmas.toSource` | `SourceDefinition31RootLemmas.lean:3807` | `StageConstructionTrace`（18 字段 + partition） | 仅 RootLemmas 内部/等价链 | 否 |
| `D4D9Supply.toSourceData` | `SourceDefinition31D4D9Supply.lean:258` | 完整 D4–D9 supply 接口 | 在 `tmp/sheaf` 中 **0 个调用者** | 否 |
| `S1280SourceData_of_remaining` | `S1280SourceDefinition31Actual.lean:313` | S1280 的 D3/D4 前缀 + 原始 D5–D8 clause 类型 + 任意 5 个 D9 `(Prop, proof)` | 11 个直接 importer（S1298/S1320/S1321/S1322/S1339/S1342/S1386 等） | 否 |
| `S1322SourceGap.toSourceData` / `toOriginalInput` | `S1322ConcretePaperSourceActual.lean:132/142` | D5 + D6–D8 + 5 个任意 D9 对的 gap record | **0** | 否 |
| `NativeSourceAssembly.toSourceData` | `tmp/sheaf/n8/closure/NativeSourceAssembly.lean:76` | native T + 26 个显式 source 字段（含 D5/D6/D7） | 8 个直接 importer，35 个 reverse | 否 |
| `NativeSourceAssemblyFinalPartial.finalSourceDefinition31Data` | `NativeSourceAssemblyFinalPartial.lean:46` | `NativeSourceAssembly` + 缺字段包 | 1 个直接 importer，3 个 reverse | 否 |
| `S1322SourceGap.toOriginalInput` | `S1322ConcretePaperSourceActual.lean:142` | 上述 `SourceDefinition31Data` + Haar family | **0** | 否 |

结论：**有生产者，但没有一个生产者的 S 值进入 E1–E5。** `S1280` 是最接近“实际 Gaussian D3/D4 前缀”的入口，但它的 reverse 41 个模块中没有一个在最终闭包；`S1322` 是最接近“完整 D5–D9 组装”的入口，但消费者为 0。

### 2.3 值级消费者

- `tmp/sheaf/xif/PaperQPilotObject.lean:66` `sourceBadQAbsLog (S : SourceDefinition31Data l)`，`:73` `sourceQPilotSignedLog`。这是 S 的 reduction.qParameter 的直接值级消费者，被大量 S6xx 旧值层文件使用。
- 但 E1/E2 不使用 `sourceBadQAbsLog`；E1/E2 使用 native `qVFamTensorP`/`qVFamNormalizedCoefficient`。S605 也不使用 `sourceBadQAbsLog`（S605 输入 native T）。S1136 更不涉及。
- 因此存在第三个 q 标量世界：`sourceBadQAbsLog`（contract）、`qVFamilyK`（S605 native K-side）、`qVFamTensorP`（E1/E2 native qVFam）。三者没有互相识别。

### 2.4 直接 importer 与类型级传播

- 直接 import `SourceDefinition31Boundary` 的模块：39 个；reverse closure 2,453 个（含 snapshot 副本）。
- 其中实际在声明中把 `SourceDefinition31Data` 当参数的类型/值消费者集中在：
  - LeanFormal：`SourceOriginalInput`、`SourceHodgeTheaterBridge`、`SourceDefinition31RootLemmas`、`SourceDefinition31NativeContractBridgeReduction`、`SourceDefinition31DualContractAlignment`、`SourceQlThetaObjectActual`、`SourceQlThetaPunctureIdeal`、`SourceIntegralUnitsComparison`、`InfinitePlacePsiCns*`、若干 `SourcePsi*`。
  - xif 生产/接口文件：`PaperQPilotObject`（间接 import）、`SourceCuspCountActual`、`S1384ThetaLineBundleActual`、`S1401ThetaLineBundleActual`、`CuspFromSourceClauseActual`、`NativeCuspCountActual`。
  - xif probes/mirrors：`S1271*`、`_S1206QlThetaMirror`、`_S1240Mirror`、`_S1261Mirror*`、`_S1288Probe`、`_S1296ProbeUniv`、`_S1307Probe3/4`、`S1360AuditProbe`；这些不计为生产消费者。
- 关键类型级事实：`SourceOriginalInput.lean:41-46` 的 `OriginalInput.initial : SourceDefinition31Data` 是唯一把 S 接入 `OriginalInput` 的字段。E4 只量化 `I : OriginalInput`；没有 I 的构造。E1/E2 不量化 I。

---

## 3. S605 / S618：K-side q 比较死路

### 3.1 输入与内容

- `S605KSideQVActual.lean:27`：`variable (T : SourceNativeInitialThetaData.{0} l)`，不是 `SourceDefinition31Data`。
- `:30-40` `KSideQVComparisonData` 字段：
  - `place_eq : qVFamilyKLift T b = kSidePlace T b`（两个独立 `Classical.choose`/section lift 的选择相等）；
  - `shadow_eq`；
  - `qSection : FinitePlaceQCandidate (kSidePlace T b)` 且 `qSection = place_eq.symm ▸ qVFamilyK T b`；
  - `uniformization : TateCurveComparison ...`；
  - `order_eq : qSection.order = fkDescentSectionRamificationIndex ... * (qVFamily T b).order`。
- `:45-59` `kSideQVFamilySpecOfComparison` 只在给定 G 时构造 paper spec；`:61-64` 只在给定 G 时得到 `KSideQVFamilyRequired`；`:66-67` 把缺 G 记成 `KSideQVExactGap`。**没有 G 的 inhabitant。**

### 3.2 消费者

- S605 直接 importer：活跃的有 `S618KSideQVPlaceActual.lean` 和审计末尾新增的 `S1413SourceKPlaceQComparisonActual.lean`；另有一个 frozen snapshot 副本。
- `S618` `:54-69` 从显式的 `hplace`、`qSection`、`hqSection`、`uniformization`、`order_eq` 再造一个 `KSideQVComparisonData`；没有产生 inhabitant，也没有消费者。
- S618 直接 importer：0；reverse closure：1（自身）。`S618` 在 `tmp/xif_compile_queue.txt` 中没有条目，且当前没有 olean（见 §9）。
- S605 的 `S436/S438/S467` 依赖中，`S436` 被 S605/S618/S1413 使用；`S438` 有 60+ 个 reverse（K-side q 子图），但没有一个进入 E1–E5。

### 3.2.1 新增 `S1413`：并行路线，不是 S605 的消费者

`S1413SourceKPlaceQComparisonActual.lean`（审计末尾出现，mtime 2026-10-30T16:02Z，未编译，无 olean）在原文 section 指定的 K-place 上直接构造：

- `sectionKPlace = kSidePlace T b`、`sectionFPlace = fkDescentShadow P b.1`，以及两条 comap 等式；
- `shadowQ`（F 侧 clause-B Tate 参数）、`completionMapSection`、`sectionQ = FinitePlaceQCandidate.map ... shadowQ`；
- `sectionQ_q`（rfl）、`sectionQ_order`（用源 section 的 ramification index）、`sectionQ_valuation`、`sectionQ_localLogMagnitude_vs_shadow`、`sectionQ_orderNormalized_vs_shadow`；
- `S1413ShadowEqualsNative`（F-place 身份）、`S1413SectionTateUniformization`（K-side Tate uniformization）仍作为**未证明、未假设的精确输入**；
- `kSideQVFamilySpecOfSection` / `kSideQVFamilyRequired_of_section` 只在给定这两个输入时构造 `KSideQVFamilySpec`。

关键审计事实：

- S1413 **import 了 S605，但没有引用 S605 的任何声明**；它用 S436 的 `kSidePlace` 直接构造，并用 `S1413ShadowEqualsNative`（比 S605 的 `place_eq` 更弱）替代 S605 的 `KSideQVComparisonData`。
- S1413 的直接 importer 为 **0**，不在 E1–E5 闭包中。
- 因此 S1413 是“绕过 S605 的并行条件路线”，不是把 S605 接到最终目标的桥；S605 的 `KSideQVComparisonData` 仍无人使用。

### 3.3 与最终目标的关系

- E1–E5 的闭包中都没有 S605/S618/S1413。
- 全库同时出现 `qVFamilyK` 和 `qVFamTensorP`/`qVFamNormalizedCoefficient` 的文件数：**0**。因此 S605 的 K-side q 与 E1/E2 的 native qVFam 标量之间没有现成识别定理。
- 即使二者输入类型相同（`SourceNativeInitialThetaData`），也没有桥把 `qVFamilyK` 的 q/order 运输到 `qVFamTensorP`、`qVFamNormalizedCoefficient`、`nativeBadLocalWeight` 或 root hull。

---

## 4. S1136：孤立 Real 模型

- `S1136SourceComparisonViaGluingActual.lean:17-26`：`S1136GluingData` 只有 4 个自由 Real（`thetaPilotLog`、`thetaHullLog`、`qPilotLog`、`hullLog`）和一个单调 `glue`；字段 `qPilotLog_eq`、`hullLog_eq`、`theta_le`。
- `:29-32` `s1136Comparison` 是合法的序论推导：给定 `hullLog = glue thetaHullLog` 后单调性给出结论。
- `:36-37` 明确把 `S1136HullGluingRequired` 作为缺失条件；`:49-55` 把精确残余记成 `glue thetaPilotLog ≤ hullLog`。
- 生产消费者：**0**。直接 import：4 个活跃 probe `_S1415Probe0`–`_S1415Probe3`（全部无 consumer）。
- `_S1415Probe3` 确实把 S1136 实例化到 `OriginalInput` 的 `sourceQPilotLogVolume`/`sourceThetaHullLogVolume`，但选择 `glue := id`、`hullLog := thetaHullLog`，并把 `sourceXiFInclusion_of_bounded`（正是要证的 q≤hull 不等式）放进 `theta_le` 字段。于是 `s1136Comparison` 只是把目标不等式从输入再取一次；这是循环实例化，不是独立桥。
- Probe0/1/2 只是 `#check` 声明，没有构造 gluing data；也没有把四个 Real 识别为 `globalQPilotLog`/`globalThetaHullLog` 或证明 `hullLog = glue thetaHullLog` 的源内容。
- 因此 S1136 仍只能作为“如果运输已知，则单调性成立”的模板；当前没有生产文件消费它。

---

## 5. D5–D9 构造与 xi-f 目标的关系

### 5.1 槽位对照

| 槽位 | 当前文件/关键声明 | 当前状态 | 活跃直接消费者 | 在 E1–E5 闭包 |
|---|---|---|---|---|
| D5 torsion | `S1298TorsionClauseActual.lean:327` `S1298TorsionSourceGap`，`:391` `s1298D5TorsionSupplyOfBasis` | 条件于 rank-two `l`-torsion basis + large-image；无 basis inhabitant | 3（`S1329`、`S1351Probe`、`S1351TorsionBasisFix`） | 否 |
| D6 orbicurve | `S1348D6OrbicurveActual.lean`（实际 curve/cover，`:617` 记 exact first field）；`S1398D6SupplyActual.lean:42` `S1398D6Supply` | S1348 有实际几何前缀但 exact sequence residual；S1398 条件于 `S1359FirstField` | S1398：0；S1348：多个 reverse（含新的 probe） | 否 |
| D6 audit/no-op | `S1353D6OrbicurveActual.lean` | 文件头自述“不构造 D6”，0 个声明 | 0 | 否 |
| D7 sections | `S1320SectionsCuspActual.lean:259` `S1320D7FirstField`；`S1312D7LocalGroupActual`；`S1386D7bLocalGroupActual` | D7a 实际；D7b place-indexed local group family 未构造 | S1320：1（S1330）；S1312：3；S1386：0 | 否 |
| D8 cusp | `S1320SectionsCuspActual.lean:407` `S1320CuspFirstField`；`S1330CuspEpsilonActual.lean:329` `S1330RealCuspCoordinate`，`:362` Missing | cusp point 实际；真实 cusp coordinate 未构造；且 `SourceCuspClause.epsilon : Real` 是 contract 加的 Real 卡，不是原文 cusp | S1330：3 | 否 |
| D9 compatibility（五个 `(Prop, proof)` 对） | `S1339D9CompatibilityActual.lean`（sections 槽已证，`:36`）；`S1342D9PlaceSectionActual.lean`；`S1355D9TorsionCuspActual.lean` | 只有 sections 兼容性实际；reduction 首字段在 l=5 为空（`:52`）；torsion/orbicurve/cusp 首字段仅记录 | S1339：0；S1342：0；S1355：0（文件本身无 importer） | 否 |
| “D9 orbicurve slot”（命名漂移） | `S1360D9OrbicurveSlotActual.lean:302`；`S1387D9PaperSlotActual.lean` | 是 paper `(1,l-tors)` orbicurve + K-core slot，**不是** `SourceDefinition31Data` 的五个 D9 compatibility 对；无 inhabitant | S1360：3（S1387/S1403/probe）；S1387：2（S1403/check） | 否 |

### 5.2 `S1403` 不是完整 D5–D9 bundle

`S1403D789SupplyActual.lean:47-55` 的 `S1403D789ConditionalSupply` 只有：

- `d7b : D7LocalGroupSectionSupply`
- `signData : SourceSignQuotientData`
- `d8 : S1330RealCuspCoordinate`
- `d9 : S1360D9OrbicurveSlot`

**没有 D5 torsion supply、没有 D6 orbicurve clause、没有五个 D9 compatibility 对。** 文件头 `:22-24` 也承认“D4/D5/D6 输入不在本文件发明，留给 eventual `D4D9Supply` consumer”。但它自己没有任何 consumer；直接 importer 为 0，reverse closure 为 1（自身）。所以 `S1403` 既不是完整 bundle，也没有被最终目标消费。

### 5.3 `S1322` 是唯一完整 D5–D9 gap assembler，但消费者为 0

`S1322ConcretePaperSourceActual.lean:113-115`：

```text
structure S1322SourceGap where
  torsion : SourceTorsionClause
  tail : S1322SourceGapTail   -- D6, D7, D8 + 5 arbitrary (Prop, proof) D9 pairs
```

`:132` `toSourceData` 用 `S1280SourceData_of_remaining` 组装 `SourceDefinition31Data`；`:142` `toOriginalInput` 再组装 `OriginalInput`。它确实覆盖 D5–D9 的**类型形状**，但：

- 五个 D9 对是任意 `Prop` + 任意 proof，不是 S1339/S1342/S1355 的实际兼容性实例；可以用 `True` 填充，不能视为源忠实构造。
- 它不使用 `S1298` 的 D5 supply、不使用 `S1398` 的 D6 supply、不使用 `S1403` 的 D7/D8/D9 bundle。
- 直接消费者 **0**；reverse closure **1**（自身）。因此它是 dead-end，不是桥。

### 5.4 canonical `D4D9Supply.toSourceData` 没有调用者

- 接口：`SourceDefinition31D4D9Supply.lean:246` `D4D9Supply`；`:258` `toSourceData`。
- 在 `tmp/sheaf` 中检索 `D4D9Supply`：37 处提及，全部是 import/open/类型/注释；**没有任何一个具体的 `D4D9Supply` 构造或 `toSourceData` 调用**。
- D4D9 的自身注释说 consumer 是 `SourceDefinition31Data.toInitialThetaInput → InitialThetaInput`（Theorem 3.11 items 22–31），但本审计在 xi-f 范围内没有找到 theorem 3.11 的消费点；E1–E5 都不 import 它。

### 5.5 l=5 的具体源级 obstruction

`S1280SourceDefinition31Actual.lean:427-455`：

- `S1280_badResidueCharacteristic_coprime_iff`：实际 5 上坏地方的 residue characteristic 是 5，Clause (c) 要求它与 `l` 互素，因此等价于 `l ≠ 5`；
- `S1280_clauseC_refuted_at_five : ¬ Nonempty (BadPlaceQParameterCards (S1280Selection S1280Five))`；文件注释明确：“A source-faithful Definition 3.1(b) selection for l = 5 therefore cannot use this bad moduli place.”

`S1339D9CompatibilityActual.lean:52-55` 直接复用这个事实：D9 reduction 首字段在 l=5 为空。

注意精确含义：`S1280SourceData_of_remaining` 接受任意 `redCompat : Prop` 和证明，所以可以在 l=5 用 `True` 组装一个 contract 值；但这不是源忠实的 D9 reduction slot。**l=5 的实际 D5–D9 组装被源级 Clause (c) 阻断**，不能把任意 Prop 组装当作解决。

---

## 6. 缺失桥（按优先级）

### M1. native ↔ contract 根桥（最大缺口）

- 最终 E1/E2 使用 `SourceNativeInitialThetaData`；D5–D9/S1322 使用 `SourceDefinition31Data`。
- `SourceDefinition31NativeContractBridgeReduction.lean:309-335` 的 `definition31NativeContractBridgeReduction` 状态是 `interface`，note 明确 **“No bridge is constructed”**；它只证明路线 A/B/C 的等价/阻碍，不提供构造。
- 因此即使 D5–D9 全部闭合，也不能自动进入 E1/E2；需要 native→contract 或 contract→native 的实际桥（或直接在 native T 上重做 D5–D9 组装）。

### M2. D5–D9 → `SourceDefinition31Data` 的接线

- `D4D9Supply.toSourceData` 是 canonical 接口，但 0 调用者。
- `S1322` 是唯一覆盖全部槽位的 assembler，但 0 消费者，且 D9 对是任意 Prop。
- `S1403` 不含 D5/D6/D9-compat，0 消费者。
- `S1298`（D5）、`S1398`（D6）、`S1339/S1342/S1355`（D9-compat）都没有被 `S1322` 或 `S1403` import。需要一条真实的：
  `D5 supply + D6 clause + D7 supply + D8 coordinate + D9 five pairs → D4D9Supply → SourceDefinition31Data`。

### M3. `SourceDefinition31Data`/`OriginalInput` → E1–E5

- E1/E2 目标类型不含 S；E3 同样。
- E4 只量化 `OriginalInput`，没有 inhabitant；即使提供 S1322 的 `OriginalInput`，E4 还需要 `ThetaLinkActual` 和 `hlink`。
- 需要一个“native qVFam/root hull 标量 = contract source q/hull 标量”的桥，或把 E1/E2 重新参数化到 `OriginalInput`。当前两者都没有。

### M4. S605 K-side q → E1/E2 native qVFam

- 全库 0 个文件同时出现 `qVFamilyK` 与 `qVFamTensorP`/`qVFamNormalizedCoefficient`。
- S605 自身的 `KSideQVComparisonData` 无 inhabitant；S618 只是条件再包装。
- 审计末尾新增的 S1413 已在 section 指定 K-place 上完成 q/order/valuation/norm 图，但：
  - 它绕过 S605，没有使用 S605 的 `KSideQVComparisonData`；
  - `S1413ShadowEqualsNative` 和 `S1413SectionTateUniformization` 仍未证明、未假设；
  - S1413 自身 0 消费者，未进入 E1–E5。
- 仍需：
  - 给出 `S1413ShadowEqualsNative`（或 S605 的 `place_eq`）和 `TateCurveComparison`；
  - 把 S1413/`qVFamilyK` 的 q/order 运输到 `qVFamTensorP`、`qVFamNormalizedCoefficient`、`nativeBadLocalWeight` 和 root hull。

### M5. S1136 抽象 glue → 实际 q/hull

- 需要把四个 Real 实例化为实际标量（`globalQPilotLog`、`globalThetaHullLog` 或 `sourceQPilotLogVolume`/`sourceThetaHullLogVolume`），并给出 `qPilotLog_eq`、`hullLog_eq`、`theta_le`；
- 其中 `hullLog_eq : hullLog = glue thetaHullLog` 是字段输入，不是 S1136 证明的结论；没有它，`s1136Comparison` 不适用。
- 当前没有生产消费者做这件事；`_S1415Probe3` 的实例化选择 `glue := id`、`hullLog := thetaHullLog`，并把 `sourceXiFInclusion_of_bounded` 作为 `theta_le`，只是把目标不等式循环取回，不能算源桥。

### M6. D9 五对 compatibility

- 只有 sections 槽由 `S1339D9Sections_proved` 实际证明；
- reduction 槽在 l=5 为空；
- torsion 槽依赖 D5 clause；orbicurve 槽依赖 actual K-core orbicurve；cusp 槽依赖 `TorsionQuotientBoundaryOrigin`；
- 这些都不是“再写一个 Prop 包装”能补的。

### M7. 各对象自身的 exact first field

- D5：rank-two `l`-torsion basis / Serre large image（S1298）。
- D6：`MissingD6GeometricRealization`（nondegenerate étale stack fiber + effective descent）和 orbifold `Pi` data（S1348/S1353/S1387）。
- D7b：place-indexed curve-side local group family `Pi_Xv → Pi_Cv`（S1312/S1386）。
- D8：real cusp coordinate map on the paper cusp（S1330/S1357/S1400）。
- D9：actual K-core hyperbolic orbicurve + K-core identification（S1360/S1387），以及上面四对 compatibility。

---

## 7. 死路清单

1. `S605`/`S618`/`S1413`：S605 条件 gap 无 inhabitant；S618 无消费者、无 olean；S1413 绕过 S605、自身 0 消费者、无 olean。整个 K-side q 子图未进入 E1–E5。
2. `S1136`：无生产消费者；活跃 importers 是 `_S1415Probe0`–`_S1415Probe3`，其中 Probe3 是 `glue=id`、`hullLog=thetaHullLog` 的循环实例化，其余只是 `#check`。
3. `S1321PaperOriginalInputActual`：`PaperOriginalInput` + capsule lift；消费者 0。
4. `S1322ConcretePaperSourceActual`：唯一完整 D5–D9 gap assembler → `SourceDefinition31Data`/`OriginalInput`；消费者 0。
5. `S1403D789SupplyActual`：条件 D7/D8/D9-orbicurve bundle；消费者 0，且缺 D5/D6/D9-compat。
6. `S1398D6SupplyActual`：条件 D6 supply；消费者 0。
7. `S1339D9CompatibilityActual`、`S1342D9PlaceSectionActual`：D9 compatibility 首字段/部分证明；消费者 0。
8. `S1353D6OrbicurveActual`：文件头记录“不构造 D6”，0 个声明。
9. `S1298` 的 D5 子图（`S1329`/`S1351*`/`S1361`/`S1362`/`S1365`/`S1366`/`S1379`/`S1396`）：没有进入 `S1322`/`S1403`/E1–E5。
10. `D4D9Supply` 接口：0 个具体构造/调用者。
11. `PaperXiFClosedActual`、`PaperXiFAssemblyActual`、`PaperAssemblyActualFinal`：各自消费者 0；只有 `#check`/probe。
12. `SourceDefinition31Data.toInitialThetaInput`：投影存在，但 xi-f 范围内没有 theorem 3.11 的消费点；E1–E5 不使用它。

---

## 8. 给下一步的可执行边界

如果目标是“让 D5–D9 真正进入 xi-f 最终目标”，最短的实质路径不是再写 wrapper，而是：

1. **先决定最终目标的输入类型**：E1/E2（native T）还是 E4（OriginalInput）。两者之间的 native↔contract 桥是 M1，不能绕过。
2. **在选定输入上建立一个真实 q/hull 标量桥**：S1413 已完成 section 指定 K-place 上的 q/order/valuation/norm 图；下一步是证明 `S1413ShadowEqualsNative` 与 `S1413SectionTateUniformization`（或 S605 的 `place_eq`/`uniformization`/`order_eq`），再把 q/order 运输到 `qVFamTensorP`/root-hull 标量。
3. **把 `S1403` 补成真正的 `D4D9Supply`**：加 D5 supply、D6 clause、五个 D9 compatibility 对；然后调用 `D4D9Supply.toSourceData`，而不是停在条件 bundle。
4. **在 l=5 先处理 Clause (c)**：换一个源允许的坏地方选择，或把定理范围明确限制到 `l ≠ 5`；不能把 `True` 填进 D9 reduction slot。
5. **最后才接 S1136**：只有实际 q/hull 标量和 `hull = glue thetaHull` 都有来源后，S1136 的单调性才可消费；`_S1415Probe3` 的 `glue=id`/`theta_le := 目标不等式` 是循环，不能作为该桥。

---

## 9. 验收状态（本审计未运行）

- `statement_compiles`：not_run（本审计未运行 lake/Lean）。
- `proof_body_checked`：not_run。
- `kernel_closed`：not_run。
- `target_accepted`：false。
- 未运行 Project build、comparator、独立审查、公理检查。
- 观察到的既有 olean（仅文件系统事实，不构成当前源码正确性证明）：
  - S605、S1280、S1298、S1320、S1321、S1322、S1398、S1403、E1、E2、E3、E4 均有 olean；
  - S618、S1413、`_S1415Probe0`–`_S1415Probe3` 没有 olean；
  - S1136 有 olean。
- 审计文件文本中没有真正的 `sorry`/新 `axiom`（只匹配到注释中的 “no sorry” 字样）；这不覆盖其 import 闭包中的其他文件（例如 `tmp/sheaf/n8/closure/SourceInputBinding.lean:21` 注释提到 named-sorry `sourceInputBinding_nonempty`，本审计未做 axiom 依赖检查）。

---

## 10. 版本绑定（SHA256，写入前重新计算）

| 文件 | SHA256 |
|---|---|
| `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean` | `E9C53D42EC941962A81036DF0A43916135A75D36D87E54F0D9A25F8AC703AF9A` |
| `LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean` | `D021033FF7DB772B2DBDF01D2056A8DDB31F4F1B3E1C2D94A6E309ACCD75198F` |
| `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31D4D9Supply.lean` | `F78EF1C16B1E6EAF5573100C200ABDB7FA404C8957AFDA746E4A724FEA0784BA` |
| `tmp/sheaf/xif/paper/S605KSideQVActual.lean` | `B07C194AF01137CBA64B0AB82761F33DF8508A1196BA7E85B69C4893C7E1C714` |
| `tmp/sheaf/xif/paper/S618KSideQVPlaceActual.lean` | `9834DFE1437AA5CB12FEF63F0A436582A0FBD35796309899502001346CF8382F` |
| `tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean` | `04B72AF762DDE39270D9F1BBBC038FED597EC9E20F5FC04ADE95BC5E70AFFEA6` |
| `tmp/sheaf/xif/paper/S1136SourceComparisonViaGluingActual.lean` | `EE06CE2E9389998320BF130D5E6F9AF1B5A8C90929D6712174B857B5AC3BC4AD` |
| `tmp/sheaf/xif/paper/S1280SourceDefinition31Actual.lean` | `FDFC73DAEBB8DFC339BC9334831B3FE036174C19FC05C0A1548256CFED3500A9` |
| `tmp/sheaf/xif/paper/S1298TorsionClauseActual.lean` | `C41EB27535C33269468BA09B61937078E4FEB026E4247039FE5E29DE846F2F0B` |
| `tmp/sheaf/xif/paper/S1398D6SupplyActual.lean` | `8CC60BF8D84109F2F408720783B89EDA72C249285E042BF3BA3FA359931A421C` |
| `tmp/sheaf/xif/paper/S1403D789SupplyActual.lean` | `3CF72F40730754D9D630E5E1280712BD3E6D5A807240440EFDCCD94D2413094D` |
| `tmp/sheaf/xif/paper/S1322ConcretePaperSourceActual.lean` | `A2A478ADCFFEAE5BA48417CA9E11EA5A441A59FE0BE0E838F7E94CB099DE2C0B` |
| `tmp/sheaf/xif/paper/PaperXiFFinalActual.lean` | `67DFCBC2F254869EB3D0B8663EBA7150904FD2790A1770C0B188F9C3B0873807` |
| `tmp/sheaf/xif/paper/PaperLevelXiFTargetActual.lean` | `7783BA0991E3E797C17C52F3E8F5C18446DADDEC265E1715A296741A6508CE85` |
| `tmp/sheaf/xif/paper/PaperLevelXiFTargetBridgeActual.lean` | `5E39139B54EE9964FA52D03CE6886AE66A43A3E7577F8590248A2FCD3FFDDFDB` |
| `tmp/sheaf/xif/paper/PaperXiFClosedActual.lean` | `18785FDDDC067DED8CA0DCBE6A2905ED170BC5DE13C1F2F7857875FFAAA012DF` |
| `tmp/sheaf/xif/paper/PaperXiFCompileGate.lean` | `DC35543C0D0B71DD5369A201D4FC124D67983B7C272DE7C01C9711869929AD1C` |

---

## 11. 审计边界

- 本报告只覆盖静态 Lean import/声明关系，不覆盖外部脚本、非 Lean 消费者、未来文件或未登记的动态生成。
- “0 消费者”指当前扫描范围内没有 import 边；不代表该文件没有数学价值，只表示它不在当前最终目标的依赖链上。
- 并发 agent 正在改动 probe/部分 S13xx–S14xx 文件；若关键文件哈希变化，结论需按新哈希重跑。
- 本报告不修改 Lean、不写 olean、不更新 queue/STATE；D5–D9 的证明状态仍以各文件的 `not_run`/条件声明为准。

---

EXIT=0
