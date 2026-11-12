# P6-WEIGHTED-DET-PACKET-PLAN — HANDOFF §8.2 P6 的一个具体实例化路径（Lead 起草；不是新路线）

> 定位说明：本文件只服务交接稿 §8.2 的 **P6（若局部机制不足，先做路线三的来源检验→全局范数/比较态射）** 与 §6.10 (C17)–(C20)。
> 它不是替代路线图；一切工作仍以 D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md 的 P0–P7 与路线一/二/三为准。

目的：给 NEXT-WAVE #14 一条可直接开写的路径。目标是把 (C17) `deg(D_Θ) − deg(D_q) = N·M` 落到仓库已有的 `WeightedDeterminantPacket` 上，而不是新造抽象。

## 1. 已有 green 工具（内容核对过）

文件：`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean`
- `WeightedDeterminantPacket (label) [Fintype label]`（:25）：字段含 adjustedLogDegree/commonTensorDegree/summandTensorExponent 等；
- `commonTensorDegree_pos`（:48）、`summandTensorExponent_pos`（:54）；
- `denominator_mul_summandTensorExponent`（:61）：清分母的精确关系；
- `normalizedLogVolume`（:68）、`weightedLogVolume`（:74）；
- `weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume`（:97）：**weighted = N · normalized**；
- `denominator_two_four_commonTensorDegree`（:107）：N = 2/4 型清分母；
- `weightedDeterminantNormalization : Obligation`（:121）：gate 记录，不是定理。

文件：`.../HullDeterminantLogVolumeReduction.lean`
- `packetDiagonalMatrix`（:220）、`packetDet_eq_packetDiagonalMatrix_det`（:226）、`packetLogVolume_eq_matrixLogDet`（:249）；
- `packetDet_tensor_via_det_kronecker`（:267）、`packetDet_rescale_via_det_smul`（:290）、`packetLogVolume_tensorPower`（:302）；
- `profileArithmeticDegree`（:312）、`profileArithmeticDegree_adjustedDetTensorPower`（:334）；
- `HolomorphicHullAdjunction`（:358）。

另有 `IQHullLogVolumeInterface` / `Cor312EpsilonArithmeticComparison`（ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:224）提供 hull log-volume 与实际比较接口。

## 2. 实际实例化步骤（建议顺序）

1) **q 侧 packet**：label = Bad (nativePlaceSelection T)（或 procession label），scale/tensor exponent 用 `qVFamTensorCoefficient`/`nativeBadLocalWeight`/`baseQLogMagnitude`；证 `commonTensorDegree` 与实际清分母常数一致（对照 `denominator_two_four_commonTensorDegree`）。
2. **Θ 侧 packet**：label = PaperNonzeroLabel（或 SignedLabel 的 procession），用 `qVFamPaperThetaTensorCoefficient`/`paperFaithfulThetaHull` 的读数。
3) **weighted/normalized 恒等式**：直接用 :97 得 weighted = N · normalized；把两侧读数接到 `arithmeticTupleNormalizedLogVolume`（QVFam block）与 `paperRootThetaHullLog`。
4) **差 = N·M**：用 `profileArithmeticDegree_adjustedDetTensorPower` + 两个 packet 的 weighted 差，目标形如
   `weightedTheta − weightedQ = N * (V + gap − (sF−1)A)` 或 `= N * M`；
   注意 (C17) 要求先证清分母 N 与 paper 权重一致。
5) 不在本包引入新假设：若 `weightedTheta − weightedQ` 与 `M` 的字典缺一条等式，写成精确 named input（GAP-P6-C17-DICT），并记录到 `coord/P6-DEGREE-FORMULA.md` / `coord/P3-TARGET-EQUIV.md`。

## 3. 交付与验收

- 新文件：`tmp/sheaf/xif/paper/Mzk1WeightedDetPacketActual.lean`（报 Lead 加 watchdog 名单）；
- 文档更新：`coord/P6-DEGREE-FORMULA.md` 增 §12（packet 实例化表、已证恒等式、GAP-P6-C17-DICT）；
- 验收：watchdog DONE EXIT=0 + `#print axioms` 只含 trio；每定理给 file:line；不把 `weightedDeterminantNormalization` 这个 Obligation 当已证。

## 4. 关联缺口

- (C18)-(C20) 的 arch/度量部分仍需 GAP-NORM-ARCH；
- `Mzk1DegreeBridgeActual`/`Mzk1DegreeSumActual` 已给 q 侧条件桥与全 bad 求和，可直接消费；
- 与 P3 的 `Mzk1TargetReductionActual`/`Mzk1DExactActual` 接口对齐后，(C17) 即可作为 M≥0 的另一条表达式。
