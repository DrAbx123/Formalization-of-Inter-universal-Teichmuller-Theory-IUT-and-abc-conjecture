# GOAL PROGRESS（目标进度记录）

更新时间：2026-11-15 10:36（Asia/Shanghai）
Goal：`goal-9baa9641-5902-46a4-87f0-1430e6005d13`（**revision 15**，phase active，rounds 14/256）

## 0. 目标锁定

从基础三公理（`propext`, `Classical.choice`, `Quot.sound`），严格按 `coord/P7-GLOBAL-Q-HULL-CONSTRUCTION-20261115.md` 路径，**无条件**构建：

1. IUT 3.12；
2. IUT IV Thm 1.10；
3. abc 猜想。

禁止 `sorry`、额外 axiom、`PUnit/True/toy carriers/value-layer surrogate`；不改 paper object；维护审计与编译 gate。**所有 Lean 编译只走 watchdog**。

## 0b. 目标 revision 14 的新增约束

- 必须查询/同步 `coord/GOAL-PROGRESS.md`；
- Lead 负责统筹，不负责具体细节；
- 所有编译用 watchdog；
- teammate 可以按需使用一次性 agent，Lead 尽量不用一次性 agent；
- 其余目标不变：三公理、无条件 3.12/IV/abc、禁 sorry/额外 axiom/toy、不改 paper object。

## 0c. Revision 15 路线变更（P7-GLOBAL-Q-HULL-CONSTRUCTION）

- 正文路线：`coord/P7-GLOBAL-Q-HULL-CONSTRUCTION-20261115.md`；
- 主线：实际 abc 三元组 → Frey 曲线/Tate q → 合格 Θ-data → 全局 q/θ-hull → reading 比较 → IV Thm 1.10 → abc；不再以 hbound/hCor312/Nonempty/free compatibility 为终点；
- 全局 q：用 `qVFamily b` 的有限乘积区域，`n_b=v_b(q_b)`，`#k_b=p_b^{f_b}`，`d_b=e_bf_b`；旧 `C3.q` 仅作局部实例/投影，不再要求单点 log 等于任意全局和；
- 权重：以重复局部因子/公共分母实现 `M_q=Σ w_b n_b f_b log p_b`；不是把希望 scalar 定义成人工 q；
- θ-hull：用 actual tensor 自身的有限域乘积分解、完整 tensor 格/整基、`integralSpan_eq_hull`、relative Haar transport；不要求 arbitrary tensor norm 或 pure-tensor box；
- A2：实际商栈 `[U/C₂]`，不用退化 point stack；
- WQuotient：Gaussian p=5 具体分支用 explicit log `Φ([u])=1/20 log(u^4)`，不把 p=5 当一般 Ind1；
- RelativeNorm：先用 `PadicField.nrm_norm` 得 contraction，再按需用 `v_norm` 精确赋值；
- stage4：用 ambient value threshold 直接证 UniformContinuous，不用 giant WithVal rfl；
- 所有编译 watchdog。

## 1. 目标状态总表

| 目标 | 当前状态 | 证据/条件 |
|---|---|---|
| IUT 3.12 | **条件形，不无条件** | `Mzk1ActualRamifiedDataActual.actual_paper312` 三公理；条件于 `actualDataCore`；R1 仍有 single-local q vs global q 缺口 |
| IUT IV Thm 1.10 | **条件形，不无条件** | `Mzk1IVThm110Actual.thm110_display_of_hCor312`；hSlack 已 derived；hCor312 仍 class-B paper input；stage4 completion 未全闭 |
| abc | **未证明** | 仅有条件 consumer `abcConjecture_of_namedInputs`；UndilatedHeight/Region、hq/hθ、SG3b、A2、WQuotient 等缺 |
| 三公理/禁 sorry | 已接受文件满足；in-progress red 文件不算 | watchdog + probe 只信当前 DONE；red 文件明确标红 |

## 2. 已 watchdog DONE 的当前成果

| 文件/声明 | DONE | 说明 |
|---|---|---|
| `Mzk1PadicFieldValuedQpActual` | 02:12:07 | `padicField_v_eq_valuation`、`padicFieldQpCoherence`、`padicValuedCoherence_qp`；三公理，无 sorryAx；abc 审计接受 |
| `Mzk1ActualRamifiedDataActual` | 02:06:23 | `mult` 已接入 actualData/actualDataCore；3.12 条件目标 |
| `S3171IUTIVSection1DisplayActual` | 01:52:21 | `thm110_slack_of_hCor312`；`Thm110DisplayInputsOfCor312`；hSlack derived |
| `Mzk1Cor312ToABCConsumerActual` | 01:59:35 | 条件 abc consumer |
| `Mzk1IVThm110Actual` | 01:59:08 | IV 条件 display |
| `Cor312ToABCBridgeInterface` | 01:58:32 | bridge interface |
| `Mzk1RamifiedPlaceDataActual` | 01:59:07 | 含 `mult : ι → ℝ` |
| `Mzk1ThetaUnitLatticeBoundActual` | 02:21:03 / olean 10:21:03 | unit-lattice 单向界，条件 hpos/hfin；**当前源 10:31:11 新于 olean，待 watchdog 重编确认** |
| `Mzk1GaloisCompletionActual` | **02:21:06 / olean 10:21:05** | `withValMovedSigma`、`withValMovedSigma_surjective`、`withValMovedSigma_val_eq`、`valueGroup_comap_eq` 全部编译（abc probe `Mzk1GaloisValOnlyProbeActual` 02:21:06 标准三公理）；**当前源 10:31:00 已改（valueGroupIso 等），START 02:31:00 待 DONE/FAIL**；下一步 UniformContinuous |
| `Mzk1ThetaFullLatticeBoundActual` | 02:04:29 | conditional；hsub 方向已确认错误，被 unit-lattice 路线替代 |
| `Mzk1TaskGDonorProbeActual` | 02:04:29 | 17 项标准三公理，sorryAx=0 |
| `Mzk1CheckSharpDonorProbeActual` | 02:03:56 | #check-only |
| S3133 四件 | 01:55–01:57 | 全局 q 除数/加权读数/q 重数 donor |
| `QPilotGlobalLogVolumeFromQActual` | 01:54:53 | qVEffectiveMultiplicity donor |
| `Mzk1QVMultiplicityBridgeActual` | **02:27:50** | `qVEffectiveMultiplicity_eq_order_mul_localResidueDegree` GREEN；保留 q 的消失阶，不是 residue degree |
| `Mzk1QVIndexMapActual` | 02:33:15 DONE，当前源 FAIL 02:35:53 | `badPlaceIndex` GREEN；新增 fiber Fintype 需求 `{b // badPlaceIndex b = i}` 未解 |
| `NormalizedNormValuationResidueActual` | 01:47:54 | residue-degree norm valuation 条件 |
| 更早的 principal/residue/card/unitLog 链 | 07:12–09:57 | 均 watchdog/probe 三公理；unitLog 为 support-only |

## 3. 当前 RED / 明确缺口

| 文件/目标 | 状态 | 精确原因/owner |
|---|---|---|
| stage4 UniformContinuous | 未完成 | valueGroup_comap_eq 已 DONE 02:21:06；仍需 ambient identity valueGroupIso、conjugate orderMonoidIso、Completion.mapRingHom；当前源 10:31:00 重编 START 02:31:00 pending |
| `Mzk1QVMultiplicityBridgeActual` | 已绿（02:27:50，见 §2） | 旧 FAIL 02:19:38 已被修复；`qVEffectiveMultiplicity_eq_order_mul_localResidueDegree` DONE，oleans 10:27:50 > src 10:26:30 |
| `Mzk1TaskECompletionFieldEquivActual` | 证据冲突 | lattice 报 olean green，但 watchdog 02:20:37 FAIL（`Field GaussianField` synth、unknown Required）；需 watchdog 当前源重跑 |
| `Mzk1ThetaUnitLatticeBoundActual` | DONE 但条件 | `hpos : 0 < μ(tensorIntegerRegion)`、`hfin : μ(...) < ⊤` 是 explicit hypothesis；donor `Mzk1TensorRegionNormalizationActual` 也把 positivity/finiteness 记为 GAP；**当前源 10:31:11 新于 olean 10:21:03，待重编** |
| `Mzk1ThetaFullLatticeBoundActual` | 方向作废 | hsub 原为 `canonicalHull ⊆ actualRegion`，实际 `actualRegion ⊆ canonicalHull`；不要再用旧 hsub |
| R1 | 结构缺口 | `C3.q` 单 local vs global q 族；缺 `ClauseBBaseQSourceIdentity` + same-q `hq` |
| hq | 接线缺口（index map 已绿） | QVMultiplicityBridge 02:27:50 + QVIndexMap 02:33:15 已 DONE；仍缺 fiber-sum `mult i` 及 `hperPlace` 等式（all places vs bad places） |
| relativeNorm field norm | **FAIL 02:30:44**（最新） | 缺 `Module.Finite (NativeBaseCompletionRaw X) (NativeFCompletion X)`（:87）与 `IsScalarTower ℚ_[pBase] (NativeBaseCompletionRaw X) (NativeFCompletion X)`（:89/:91）；:94 type mismatch；mainline 修文件级 local instances 后 watchdog 重跑 |
| hθ | 单向缺 hpos/hfin | `unitLatticeLogVolume_le_thetaHull` DONE 02:21:03 条件版；hpos `0∈interior tensorIntegerRegion` 与 hfin `IsFiniteMeasureOnCompacts addHaar` 均无 donor，显式 GAP；NormalizedTensorHaarData existence 也 GAP |
| stage4 completion | 未完成 | `UniformContinuous`/`Completion.mapRingHom`/`alignedCompletionMapMoved` 未全闭 |
| norm valuation | 部分 | Qp 的 `PadicField.v=Padic.valuation` 已证；`NormalizedCompletion` 的 ℤ-valued Valued/norm bridge 仍 exact gap |
| SG3b | 结构缺口 | tensor product/measure/region 分解 |
| A2 | blocked 3 | quotientWitness/groups/unique |
| WQuotient | 主缺口 | `completionField ≃+* ℚ_[5]` 已有 clean interface；§7.4 更短路线：unitLogTorsionQuotientEquivRange + range=5•Integers K，构造 range ≃* Multiplicative (Integers K) via Φ=5⁻¹•x/Ψ=5•a（stepxi/lattice） |
| abc | 未证 | UndilatedHeightBound、UndilatedRegionBound、regionVolume_le_normalizedWeight、hQ/hSlack 等 |

## 4. 已有 donor（不要重证）

- 全局 q：
  - `S3133RealifiedQPilotDivisorActual`；
  - `S3133RealifiedQPilotLogVolumeActual`；
  - `S3133QPilotReadoutActual`；
  - `S3133QPilotLogVolumeAgreementActual`；
  - `qVEffectiveMultiplicity` 在 `QPilotGlobalLogVolumeFromQActual.lean:50-53`。
- 局部范数：
  - `tmp/local-cft-port/PadicField/FieldNorm.lean` 的 `PadicField.v_norm`；
  - Qp bridge：`Mzk1PadicFieldValuedQpActual`（accepted）。
- hθ：
  - `LocalFieldIntegralHullSpan.integralSpan_eq_hull`；
  - `Mzk1TensorRegionNormalizationActual.tensorIntegralRegion_mono`；
  - `FinitePlaceIntegralTensorCovolume.arithmeticTupleLogTensorUnitLogVolume_le_hull`（仅单向）。
- IV stage4：
  - `withValMovedSigma_surjective`、`withValMovedSigma_val_eq` 已绿；
  - `valueGroup_comap_eq` 在 olean 10:21:05 已绿（DONE 02:21:06）；当前源 10:31:00 正在重编（START 02:31:00）。

## 5. 索引 / watchdog

- 总索引：`coord/LEAN-INDEX.md`；
- 各 Lean 根/port 的 `_INDEX/README.md`；
- 队列状态：`coord/WATCHDOG-QUEUE-STATUS.md`；
- 检查文件（诊断用）：`tmp/sheaf/xif/paper/Mzk1ContextGoalCheckActual.lean`；
- 规则：目标加入 `dag/watchdog/extra-targets.txt`，只信 `dag/watchdog/watchdog.log` DONE/FAIL；禁止 direct `lake env lean`。

## 6. 下一步队列

1. stage4：valueGroup_comap_eq 已绿，做 ambient identity valueGroupIso、conjugate orderMonoidIso、UniformContinuous/Completion；
2. qpilot：QVMultiplicityBridge/QVIndexMap 已 DONE；写 fiber-sum `mult i` 并证 A-term 等于 fiber 求和，接 `actual_A_le_Lbar_add_Dbar_mult`；
3. hull：unit-region hpos/hfin 或 normalized Haar；不要再用旧 hsub；
4. lattice：TaskE 当前源 watchdog 重跑确认；随后 (b)/(c) WQuotient；
5. mainline：RelativeNormFieldNorm 的文件级 local instances 修好后接 `PadicField.v_norm`；R1 hq 接线；
6. abc：UndilatedHeight/Region 与 hQ/hSlack 最小缺口。


## 7. 最新审计指针（abc，2026-11-15 10:35，只信 watchdog）

- **接受（watchdog DONE）**：
  - `Mzk1QVMultiplicityBridgeActual` DONE 02:27:50，olean 10:27:50 > src 10:26:30；`qVEffectiveMultiplicity_eq_order_mul_localResidueDegree`；
  - `Mzk1ThetaUnitLatticeBoundActual` DONE 02:21:03，olean 10:21:03（条件 hpos/hfin）；
  - `Mzk1GaloisCompletionActual` valueGroup DONE 02:21:06，olean 10:21:05；probe `Mzk1GaloisValOnlyProbeActual` 02:21:06 标准三公理、sorryAx=0（仅该 olean 版本；当前源 10:31:00 重编 pending）；
  - `Mzk1PadicFieldValuedQpActual` DONE 02:12:07；probe `Mzk1PadicValuedOnlyProbeActual` 02:21:00 五项标准三公理、sorryAx=0；
  - `Mzk1TaskGDonorProbeActual` DONE 02:04:30，17 项标准三公理、sorryAx=0；S3133 四件 + `QPilotGlobalLogVolumeFromQActual` DONE 01:54–01:57；
  - `Mzk1ThetaFullLatticeBoundActual` DONE 02:04:29（hsub/hunit 条件；hsub 方向已被 unit-lattice 路线替代）。
- **拒绝（当前源 red / stale）**：
  - `RelativeNormFieldNormActual` FAIL 02:30:44（缺 Module.Finite/IsScalarTower instances；无 olean）；
  - `Mzk1TaskECompletionFieldEquivActual` FAIL 02:02:47（`theorem ... : Prop :=` 应为 `def`；synthInstanceFailed）；
  - `Mzk1ThetaUnitLatticeBoundActual` 当前源 10:31:11 新于 olean 10:21:03 → 旧绿不覆盖当前源；
  - `Mzk1GaloisCompletionActual` 当前源 10:31:00 重编 pending（旧 DONE 02:21:06 仅覆盖旧版本）。
- 详细审计：`AUDIT_LEDGER.md`；Task G wiring：`coord/AUDIT-HQ-HTHETA-WIRING.md`；索引：`coord/LEAN-INDEX.md`。
