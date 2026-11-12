# CONTAIN-ATTEMPT — L/C3 载体显式 containment 尝试 (A1061)

| field | value |
|---|---|
| Status | PARTIAL (候选区域定义 + 两条真证引理；缩放元/整性两个 GAP 未构造) |
| Lean | `tmp/sheaf/xif/paper/Mzk1ContainAttemptActual.lean`（A1069 重写为抽象 X 版本；未编译；无 sorry/axiom） |
| A1069 | 首错修复：namespace 改为 `LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual`（无 Mzk1）；去掉 explicit-universe/`(I := I)`，改用抽象 `X`：`scaledRegion`/`scaledRegion_subset_of_mul_mem`/`qLog`/`qLog_le_thetaLog_of_containment`/`qLog_le_of_scaled_containment`；C3 实例化 = GAP-C3-INSTANCE。 |

## 1. 已有可用的 L/C3 构造（盘点）

- `Mzk1C3LogShellTensorLActual`（olean=True）：
  `C3LogShellTensorBlockL := ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple`；
  `actualC3LogShellL := (sourceLocalLogShellDatum).logShell`（= 积分 log-shell）；
  `actualC3LogShellTensorRegionL := tensorIntegralRegion (fun i => actualC3LogShellL i)`（compact）；
  `actualC3LogShellTensorHaarL := Measure.addHaar`；`actualC3LogShellTensorHaarL_lt_top`；
  `actualC3LogShellTensorLogVolumeL := (haarLogVolume haar region).toReal`；
  `ActualC3LogShellTensorPacketL`（region/haar/logVolume 记录）。
- `Mzk1QPilotLineLActual`（olean=True）：`QPilotLineActualL`/`qScalar`/`qScalar_neg`；
- `Mzk1SPaperQPilotIdentificationsActual`（olean=True）：`sPaperQPilotObject` + `qPilotLogVolume`=sourceQPilotSignedLog；
- `S1487FaithfulC3`/`S1487FaithfulInput`（olean=True）：具体 l 数据。

## 2. 两个区域的显式定义草案

```
qPilotHaarRegionCandidateL := actualC3LogShellTensorRegionL          -- 未缩放（较大）
thetaScaledRegionCandidateL a := (fun x => a * x) '' actualRegion      -- a 为参数（qroot^{j^2} 占位）
```
- 定义展开：`qPilotHaarRegionCandidateL` rfl；`thetaScaledRegionCandidateL` 为 image；
- 需引理：缩放元 `a` 的构造（`C3LogShellTensorBlockL` 上没有我们的 `scaleElt`；
  lana 用 `LocalTheory.incl` 构造 tensor 元素，我们 L 文件未导出该构造）；
- 需引理：`a` 整性/乘入性 `∀x∈region, a*x∈region`（qroot 收缩，一般不在 O 中）。

## 3. 包含证明所需的有限 label/place 恒等式

1. `a = qroot^{j²}` 在 label factor 的 tensor 元素（需 `LocalTheory.incl` 型构造）；
2. log-shell = 积分 log-shell（已有 `actualC3LogShellL_eq_integralLogShell`）；
3. `qroot` 收缩 ⇒ `a·O ⊆ O` 的逐 factor 包含（qroot ord >0；需 `CompletionIntegers` 闭合性）；
4. 乘积/tensor 的 `a * region ⊆ region`（由各 factor 的 `a_i * O_i ⊆ O_i` 逐点）。

## 4. Lean 尝试（真证部分）

- `thetaScaledRegion_subset_of_mul_mem`：由 `∀x∈region, a*x∈region` 直接得 image ⊆ region（真证）；
- `qPilotLogVolumeL_le_thetaLogVolumeL`：`haarLogVolume_mono` + `ENNReal.toReal_mono` + `linarith`（真证，条件于 containment）；
- GAP：`a` 的构造与 `h` 均未提供（不伪造）。

## 5. 结论

1. 候选区域与两条真证引理已落盘；
2. 真实缺口 = **scaleElt 构造（GAP-SCALE-ELEMENT）** 与 **qroot 整性/乘入性（GAP-INTEGRALITY）**；
3. 这两个缺口正好对应 lana `ThetaRegion.scaleEltAt`（`LocalTheory.incl`）与 `ordp_qrootOf` 的整性论证；
4. 下一步：把 lana 的 `LocalTheory.incl`/`scaleEltAt` 端口到我们的 `C3LogShellTensorBlockL`，再用 `ordp_qrootOf` 证 `a` 的整性。