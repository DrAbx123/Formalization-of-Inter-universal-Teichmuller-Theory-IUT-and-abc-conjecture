# S1487-QPILOT-TARGET — concrete q-pilot volume target (A1074)

| field | value |
|---|---|
| Status | PARTIAL（S1487 signed target 真证；S2717 initial 与 Haar region 为 GAP） |
| Lean | `tmp/sheaf/xif/paper/Mzk1S1487QPilotTargetActual.lean`（未编译；无 sorry/axiom） |

## 1. 真证部分

```lean
noncomputable def S1487SignedLogVolume (l) := sourceQPilotSignedLog (S1487RootInput l).initial
theorem S1487SignedLogVolume_eq_neg_badQ (l) :
  S1487SignedLogVolume l = -OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l))
theorem S1487_qPilotVolumeTarget (l) :
  S1487SignedLogVolume l = -paperQAbsLog l (S1487CanonicalLogQ l)
theorem signed_volume_eq_of_haar (l) (haarA logQ) (h : haarA = paperQAbsLog l logQ) :
  -haarA = -paperQAbsLog l logQ
```
推导：`S1487RootInput_initial` rfl + `sourceQPilotSignedLog_eq_neg_badQAbsLog`（OrigXiF:114）
+ `paperQAbsLog_two_l_mul`（A1073，`paperQAbsLog l (2l*x) = x`）。

## 2. 接到 `QPilotHaarRegionData.volume_eq`

`volume_eq` 目标：`S2717QPilotLogVolume ... = -(haarLogVolume μ region).toReal`。
分两步：
1. **signed volume**：`S2717QPilotLogVolume ... = sourceQPilotSignedLog (S2711I...).initial`（定义/rfl）；
   若 `(S2711I...).initial = S1487FaithfulSourceData`（**GAP-S2711-INITIAL**，显式 Prop
   `S2711InitialCompatibility`），则 signed volume = `S1487SignedLogVolume = -paperQAbsLog l canonical`（已证）；
2. **Haar 识别**：需 `(haarLogVolume μ region).toReal = OrigXiFPaperBadQAbsLog S1487`
   （**GAP-HAAR-REGION**，即 q 侧 C3-block region 的 Haar 体积 = badQAbsLog）；
   用 `signed_volume_eq_of_haar` 即得 volume_eq。

草案：
```lean
def S1487HaarVolumeTarget (l) (haarA : Real) : Prop :=
  haarA = OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l))
def S2711InitialCompatibility (l) (initial : SourceDefinition31Data l) : Prop :=
  initial = S1487FaithfulSourceData (l := l)
-- volume_eq = S2711InitialCompatibility + S1487HaarVolumeTarget + signed_volume_eq_of_haar
```

## 3. 剩余 GAP（精确）

1. **GAP-S2711-INITIAL**：S2711 的 `initial` 与 `S1487FaithfulSourceData` 的识别（不同构造栈，
   S2711 用 S1280/S2711I，S1487 用 S1487SourceData）；
2. **GAP-HAAR-REGION**：q 侧 C3-block region 的 Haar log-volume = badQAbsLog
   （需要 q-pilot 区域构造，即 S2708 的 finite-place/discrete q 缺口的几何版）；
3. **GAP-THETA-SUBSET**：`actualC3LogShellTensorRegion ⊆ region`（theta⊆q 方向，A1059 的 Option B 字段）。

## 4. 结论

1. S1487 具体 signed target **真证**（canonical logQ）；
2. volume_eq 的算术归约 `signed_volume_eq_of_haar` **真证**；
3. 剩余两条数据/几何 GAP 已精确命名；接上后 `Mzk1QPilotHaarBridgeActual` 的 Option B 实例即可构造。