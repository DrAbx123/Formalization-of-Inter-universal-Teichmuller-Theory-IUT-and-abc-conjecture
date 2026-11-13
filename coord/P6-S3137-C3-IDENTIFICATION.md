# P6-S3137-C3-IDENTIFICATION — S3137 C3 vs S2717C3 / S1487 C3 字段级对照（巡检）

日期：2026-11-13；abc。**只读审计，不改数学文件**。结论：**无可直接构造的实际识别**；下面是字段对应与精确缺口（file:line）。

## 0. 结论先行

1. **S3137 C3 与 S2717C3 同为旧 schema** `N8Closure.SourcePilotRegion.SourcePilotRegionData`（`tmp/sheaf/n8/closure/SourcePilotRegion.lean:59-100`），字段名逐一相同；识别缺的是 **index `I` 的等式**（S3137 为任意 `I`，S2717C3 为 `S2711I R …`）和 **C3 值本身的等式**（S2717C3 = `actualSignedC3 D`，需要 donor `D`）。
2. **S1487 C3 是 L-schema** `SourcePilotRegionDataL`（`S1391C3LSourcePilotActual.lean:244-279`），与旧 schema 字段**不是逐字相同**：多了 `qUnitAlgClosure_eq`、`kummerClass_eq_rootChange`，roots/Kummer 用 `ConcreteQAlgebraicClosure`/`C3LGalois` 载体；只到 `SourcePilotRegionCore` 投影（`S1391:285-300`），**没有** `SourcePilotRegionDataL → SourcePilotRegionData` 的逆构造。
3. **PaperQPilotObjectActual 无 green 构造**（`QPilotObjectActual.lean:154-162` 只有 structure；`Mzk1S3137ReadoutBridgeActual` 头注明说 C1/C2/C3/strip/oneColumn/logKummer 是 paper source obligation）；S3137 的 C3 是 `P.line.C3`，因此 C3 的 inhabitant 本身就是外部来源义务。
4. **donor 的 base-place 缺口**：`SourcePilotRegionDonors.q` 必须是在 `I.initial.arithmetic.Fmod` 的 place 的 `FinitePlaceQCandidate`（`C3Actual.lean:44-49`），而 native q 在 `F` completion；`ActualC3DonorFromNative.lean:9/26`、`C3DonorFieldsFromSource.lean:10/18` 已记录该缺口。

## 1. 三边 C3 精确定位

| 侧 | 对象 | file:line | 类型 |
|---|---|---|---|
| S3137 | `PaperQPilotObjectActual.line.C3` | `QPilotObjectActual.lean:82-86`（`C3 : SourcePilotRegionData … I`）；`PaperQPilotObjectActual.lean:154-162` | 旧 schema `SourcePilotRegionData (l:=l) (V:=V) I` |
| S2717 | `S2717C3 R … D` | `S2717Cor312FullTargetActual.lean:35-45`（`= actualSignedC3 … D`） | 旧 schema `SourcePilotRegionData (S2711I R …)` |
| S1487 | `S1487FaithfulC3` | `S1487OQPilotScalarEqualityActual.lean:548-550`（`= actualSourcePilotRegionDataL … S1487FivePlace`）；`Mzk1S3137LChainActual.lean:37-42` `S1487Input/S1487C3L` | L schema `SourcePilotRegionDataL (S1487FaithfulInput)` |

## 2. 旧 schema 字段对应（S3137 vs S2717C3）

两侧同属 `SourcePilotRegionData`（`tmp/sheaf/n8/closure/SourcePilotRegion.lean:59-100`）：

| # | 字段 | 类型/说明 | 识别条件 |
|---|---|---|---|
| 1 | `p : Nat` + `[hp : Fact p.Prime]` | 残数素数 | 需相等（同 `place` 的 p） |
| 2 | `place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p` | 实际有限位 | 需 index `I` 相等后才能比较 |
| 3 | `q : FinitePlaceQCandidate place.val` | completion 中的实际 q | 需相等（这是 q 侧读数的来源） |
| 4 | `thetaPacket : FiniteThetaPacket l` | theta packet | 需相等 |
| 5 | `qUnit` + `qUnit_eq` | `candidateUnits` 构造 | `qUnit_eq` 由 `place,q` 决定；若 `place,q` 相等则相等 |
| 6 | `roots, roots', kummerClass, rootChange, rootChange_eq` | Kummer/根系统 | 需逐字段相等 |
| 7 | `tensorIndex`, `[tensorFintype]`, `tensorPlaceIndex` | 张量索引（依赖类型） | 需类型/族相等（不是值相等） |
| 8 | `tensorPlaces, tensorTuple` | 实际张量位 | 需相等 |
| 9 | `tensorUnit`, `tensorLanding`, `tensorLanding_q` | 整数格/落点 | 需相等 |

**结论**：旧 schema 的字段级识别是可能的（同类型，字段一一对应），但需要：(a) `I = S2711I R redCompat …`；(b) `P.line.C3 = actualSignedC3 … D`（或对每个字段的等式）。**这两条都未构造**：`I` 是 `OriginalInput` 结构（含 boundary/source data），`actualSignedC3` 不是从任意 C3 反解 donor 的函数。

## 3. S1487 L-schema 与旧 schema 的不可对应项

`SourcePilotRegionDataL`（`S1391C3LSourcePilotActual.lean:244-279`）相对旧 schema 的额外/不同字段：

| 字段/差异 | file:line | 说明 |
|---|---|---|
| `qUnitAlgClosure_eq : concreteQUnitAlgebraicClosure I place = Units.map (algebraMap …).toMonoidHom qUnit` | S1391:254-258 | L 载体是实际 algebraic-closure q unit；旧 schema 的 `qUnit` 是 completion unit |
| `roots, roots' : NatRootSystem (concreteQUnitAlgebraicClosure I place)` | S1391:259-260 | 根系统载体不同（concrete closure） |
| `kummerClass, rootChange : C3LGalois I place → CyclotomicTower (ConcreteQAlgebraicClosure I place)` | S1391:261-264 | 旧 schema 的 kummerClass/rootChange 是 single tower（无 Galois 索引） |
| `kummerClass_eq_rootChange : ∀ σ, kummerClass σ = rootChange σ` | S1391:265 | 新增字段 |
| `rootChange_eq : ∀ σ, rootChange σ = rootSystemDiff roots (galoisRootsAction …)` | S1391:266-267 | L 版 root change 依赖 `galoisRootsAction` |
| core 投影 | S1391:285-300 `sourcePilotRegionLToCore` | 只到 `SourcePilotRegionCore`；**无** `SourcePilotRegionDataL → SourcePilotRegionData` 构造 |

**结论**：S1487 C3 不能通过字段等式直接识别为旧 schema C3；必须先有 **C3L ↔ 旧 C3 的 carrier 识别**（`qUnitAlgClosure_eq` 的逆、roots/Kummer 的 carrier 转换），该桥未构造。

## 4. 精确缺口清单（file:line）

```
GAP-S3137-C3-I：S3137 的 I 是任意 OriginalInput；S2717C3 的 I = S2711I R redCompat …（S1280RemainingClauses + 5 compat props）。没有 I 的等式构造。
    位置：QPilotObjectActual.lean:82-86（任意 I）；S2717Cor312FullTargetActual.lean:35-45（S2711I）。
GAP-S3137-C3-VALUE：S3137 的 C3 = P.line.C3 是任意 inhabitant；S2717C3 = actualSignedC3 … D。没有从任意 C3 反解 donor D 的函数，也没有 C3 = actualSignedC3 D 的等式。
    donor 构造：tmp/sheaf/n8/closure/C3Actual.lean:44-71（structure）、:78-100（sourcePilotRegionDataOfDonors，单向）。
GAP-S3137-C3-INHABIT：PaperQPilotObjectActual 无 green 构造（QPilotObjectActual.lean:154-162；Mzk1S3137ReadoutBridgeActual 头注）。
GAP-S3137-C3-L：S1487 C3 是 SourcePilotRegionDataL（S1391C3LSourcePilotActual.lean:244-279），与旧 schema 不同 carrier；只有 core 投影（:285-300），无旧 schema 构造/逆。
GAP-S3137-C3-DONOR-BASE：donor q 需在 Fmod base place；native q 在 F completion（ActualC3DonorFromNative.lean:9/26；C3DonorFieldsFromSource.lean:10/18）。
```

## 5. 验收口径

1. S3137 的 q/Θ 读数（`S3137QThetaPilotLogVolumeReadingsActual:77/:128`）只依赖 `P.line.C3.q` 与 `actualC3LogShellTensorHaar/Region`；**不依赖** C3 与 S2717C3/S1487C3 的等式。
2. 若要把 S3137 读数接到 S2717C3（`S2717ThetaHullLogVolume`/`S2717QPilotLogVolume`）或 S1487 C3L（`S1487FaithfulC3_q` 等），必须先补：**I 等式 + C3 值等式（旧 schema）**，或 **C3L ↔ 旧 C3 的 carrier 桥**；两项目前都没有。
3. 因此 `Mzk1S3137ReadoutBridgeActual` 的 ①–③ 只在 S3137 自己的 `P` 上成立；跨对象读数相等（本审计 §3 of `P6-S3137-READINGS-AUDIT.md`）是**条件式**，条件即上述缺口。
