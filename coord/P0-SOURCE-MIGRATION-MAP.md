# P0-SOURCE-MIGRATION-MAP — 旧 C3 空类型后的 native source 迁移

日期：2026-11-13；hull lane。**只读研究 + 新 native core 文件；未改旧 C3/L 文件。**

## 0. 结论先行

`S1429CompletionRootObstructionActual.sourcePilotRegionData_isEmpty`（file `tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean:167-173`）已证：

```lean
theorem sourcePilotRegionData_isEmpty
    {l : PrimeGeFive} {V : Type u} (I : OriginalInput l V) :
    IsEmpty (SourcePilotRegionData I)
```

因此**任何以 `SourcePilotRegionData I` 为参数的“实际构造”都是空类型上的 vacuous 定理**；不能算原问题进展。**禁止**用 `IsEmpty.elim` 从旧 C3 推出比较/读数，那是冒充。

本文件给出旧类型消费者清单与 native 迁移映射，并落地 `Mzk1P0NativeSourceCoreActual.lean`：
- roots 在代数闭包（`C3Roots.qCandidateRootSystem`），
- p/place/q/theta 来自 native `T` 与 `qVFamily`，
- tensor/readout 用 `qVFamTensorBlock`/`qVFamTensorCoefficient`（有限局部域），
- **不构造旧 C3，不用 IsEmpty 消去**。

## 1. 为什么旧 C3 空

- 旧 schema 的 `roots : NatRootSystem (candidateUnits place q)` 要求 completion 内每个自然 n 次根；
- `S1429.no_completionRootSystem`：对 q 的 valuation 指数 e>0，取 n=e+1 得 `n*log v(r) = -e`，无解；
- 故所有 `SourcePilotRegionData` 字段组合都不存在；`SourcePilotRegionData I` 是空类型。

## 2. Native 替代链（实际对象）

```text
SourceNativeInitialThetaData l (T)
  ├─ arithmetic / tuple / V / V_mod_bijection
  ├─ bad place b : Bad (nativePlaceSelection T)
  ├─ lift b : NumberField.FinitePlace T.arithmetic.F
  ├─ q_b := qVFamily T b : FinitePlaceQCandidate (lift b)
  ├─ qUnit := Units.mk0 q_b.q q_b.q_ne_zero
  ├─ roots_b := C3Roots.qCandidateRootSystem (lift b) q_b
  │     : NatRootSystem (C3Roots.unitToAlgClosed qUnit)   -- 代数闭包，不是 completion
  ├─ tensor: qVFamTensorV := Unit, qVFamTensorPlaces/Tuple, qVFamTensorBlock
  └─ readout: qVFamTensorCoefficient T b : Real = order_b
```

关键实际文件/行：
- `tmp/sheaf/n8/closure/C3Roots.lean:33-55`：`unitToAlgClosed`、`algClosedRootSystem`、`qCandidateRootSystem`、`qCandidateRootSystem_pow_self`；
- `tmp/sheaf/xif/paper/QVFamTensorCoefficientActual.lean:47-77`：`qVFamTensorPlace/P/PFact/Places/Tuple/Block/Coefficient`；
- `tmp/sheaf/xif/paper/S1391C3LSourcePilotActual.lean:98-121,308-359`：`SourcePilotRegionCore`、`actualSourcePilotRegionCore`、`actualSourcePilotRegionDataL`（L-side actual；root/Kummer 在 `ConcreteQAlgebraicClosure`）；
- `tmp/sheaf/xif/paper/Mzk1C3LogShellTensorLActual.lean:35-110`：L-carrier tensor block/region/IQ/Haar，不依赖旧 C3；
- `tmp/sheaf/xif/paper/Mzk1SourcePilotLGenericActual.lean:45-79`：任意 V 的 L-side structure copy。

## 3. 旧 C3 消费者清单（按 grep 分组）

全仓 `SourcePilotRegionData` 提及约 **900 个 .lean 文件**（含注释/adapted/probe）。按活动组：

| 组 | 文件数 | 代表文件 | 迁移目标 |
|---|---:|---|---|
| S3137 / Paper312 / hull-GAP | 43 | `S3137QThetaPilotLogVolumeReadingsActual`, `Mzk1Paper312StatementActual`, `Mzk1Paper312ActualDonorC3Actual`, `Mzk1ExactHullV*`, `Mzk1HullUB*`, `Mzk1ThetaV*`, `Mzk1C3D*` | 把 C3 参数换成 `SourcePilotRegionDataL`（S1391 `actualSourcePilotRegionDataL`）；q/θ readout 用 L 对象 + `C3LogShellTensorL` region；旧 C3 版本标 vacuous |
| C3 tensor / C3Actual / C3Norm 链 | ~100 | `C3LogShellTensorPacketActual`, `C3LogShellTensorHolomorphicHullActual`, `C3LambdaO*`, `C3Normalized*`, `S2747...`–`S2827...`, `S3137C3TensorBlockDimensionActual` | `Mzk1C3LogShellTensorLActual`（block/region/IQ/haar/log-volume）；维度用 `Module.finrank` 于 L block；旧文件保留作历史 |
| P7 / P0–P3 | 13 | `Mzk1P7ThetaDegC3Actual`, `Mzk1P7MultiradialProductionActual`, `Mzk1P2LabelBlockCoefficientActual` | P7 θ-deg 以 L tensor block 重述；#7 DONE 的 B4 已独立（`canonical_diag_volume_ratio_uncond`）；不经过旧 C3 |
| B5 / Ob33 | 5 | `Mzk1Ob33*`、`Mzk1Ob33B5AssemblyActual` | 检查是否仅传递性提及旧 C3；B5 的主要链已是 number-field/line-bundle，必要时改为不量化旧 C3 |
| 其他旧 paper/n8 closure | 余下 ~739 | `C7*`, `C9*`, `T11*`, `SourceDegree*`, `N8*` | triage：仅在需要恢复时才迁移；当前 P0 只重接 **一个** actual tensor/readout 消费者 |

注意：以上 900 是“提及”数，不等于活动消费者；真正活动 gate 名单以 `extra-targets.txt` 为准。旧 C3 的 green 定理一律**不能**当原问题进展。

## 4. 迁移映射（字段级）

| 旧 `SourcePilotRegionData` 字段 | native 替代 | 说明 |
|---|---|---|
| `p`, `hp`, `place` | `T` 的 native place / `qVFamTensorP`, `qVFamTensorPlace` | 实际有限地方 |
| `q` | `qVFamily T b` | clause-B q candidate |
| `thetaPacket` | native theta packet（`sourceTheater`/`FiniteThetaPacket`） | 尺度摘要，非局部元素来源 |
| `qUnit`, `qUnit_eq` | `Units.mk0 q.q q.q_ne_zero` | 实际 completion 单位 |
| `roots`, `roots'` | `C3Roots.qCandidateRootSystem ...`（代数闭包） | **不再要求 completion 内全阶根** |
| `kummerClass`, `rootChange`, `rootChange_eq` | `actualSourcePilotRegionDataL` 的 Galois-indexed 实际域（S1314/S1354） | L-side actual |
| `tensorIndex`, `tensorPlaceIndex`, `tensorPlaces`, `tensorTuple` | `qVFamTensorV`, `Unit`, `qVFamTensorPlaces`, `qVFamTensorTuple` | 单因子实际张量 |
| `tensorUnit`, `tensorLanding`, `tensorLanding_q` | `actualSourcePilotRegionCore` 的 `concreteActualTensorUnit`/`concreteTensorLanding`（S1219/S1267） | 实际 diagonal landing |
| readouts (`qPilotLogVolumeReading`, `thetaPilotHullLogVolumeReal`) | L-side q object + `actualC3LogShellTensorRegionL`/`HaarL` | 需重写 S3137 readout，不保留旧 C3 参数 |

## 5. 新 P0 文件

`tmp/sheaf/xif/paper/Mzk1P0NativeSourceCoreActual.lean`：
- `NativeSourceCore`（p/place/q/qUnit/roots/tensorIndex/tensorPlaces/tuple/tensorBlock/qCoeff）；
- `actualNativeSourceCore` 从 `T,b` 实际构造：`qVFamily`, `Units.mk0`, `C3Roots.qCandidateRootSystem`, `qVFamTensor*`；
- `nativeCore_roots_pow_self`（代数闭包 root 的 n 次幂等于 qUnit）；
- `nativeCore_qCoeff_nonneg` / `nativeCore_qCoeff_eq`（实际 tensor readout = order）。

这是 **P0 的 native root/Kummer core 最小落地**；下一步把 S3137 L-side q/θ readout 接到 `actualSourcePilotRegionDataL` + `C3LogShellTensorL`，再逐项迁移 #1/#3/#8 消费者。

## 6. 验收纪律（P0）

1. **禁止**以 `SourcePilotRegionData`（空）为参数宣称 actual/unconditional；只允许标 historical/vacuous。
2. **禁止**用 `IsEmpty.elim` 从旧 C3 推出任何比较/读数。
3. 新定理的 carrier 必须是 `SourceNativeInitialThetaData` / `SourcePilotRegionDataL` / `C3LogShellTensorL` / S1902 实际 product，不得新造 toy Type。
4. 每个迁移文件必须给出旧文件→native 文件/定理的显式映射；不能只改 import。
5. P7 的 #7 DONE 与 B4 与旧 C3 无关（stage4 的 canonical diag ratio 在 Qp 坐标上），保持。
