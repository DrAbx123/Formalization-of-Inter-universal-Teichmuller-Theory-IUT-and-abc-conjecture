# AUDIT: revision15 资产 → 节点 01–11 映射（abc，只读，无编译）

Date: 2026-11-15 10:45 (Asia/Shanghai). Auditor: abc (teammate).
依据：`coord/P7-GLOBAL-Q-HULL-CONSTRUCTION-20261115.md`（唯一活动路线，节点 01–11）、
`coord/GOAL-PROGRESS.md`（revision 15）、`dag/watchdog/watchdog.log`、`AUDIT_LEDGER.md`、
`coord/AUDIT-HQ-HTHETA-WIRING.md`。**本文件只读审计，未编译 Lean。**

口径：DONE/FAIL 只认 watchdog；oleans 只作辅助；标 *conditional* 者为显式假设下的证明体，可复用但**不能当终点**。

---

## 1. 节点 01–11 与现有 DONE 资产映射表

| 节点 | 现有 DONE 资产（watchdog） | 可复用内容 | 缺口 / 新增 producer | 旧目标处置 |
|---|---|---|---|---|
| **01 实际曲线与局部高度** | `FreyTateAnalyticInput`、`ABCModelHeightComparison`、`ABCInvariantHeight/LocalHeight`（既有 donor，非本轮新增）；`ABCEllipticHeightCriterion` | j/Δ/c₄/c₆ 公式、局部估值、height 字典、最终等价 | 把实际参数送入同一 Tate producer；p=2/extension/model 修正入显式 divisor | 不复算公式；不再以 arbitrary q-candidate 起实际线 |
| **02 实际 Tate q / 点比较 / 根域** | `Mzk1P2NormBridgeActual`（DONE 早期）、`Mzk1IVThm110QpDecompActual`（DONE 19:13:29Z 级）；donors：`FreyTateParameterComparison`、`TateUniformizationPointMap*` | 局部 norm bridge、q=p^k·u 分解、点映射/base change 封装、comparison packet 后半 | 实际 Tate q 的闭盘迭代、两个坐标条件（轨道分离/覆盖/下降）、root→K_v；`Mzk1P2BridgeActual` **RED** | 不把 `freyAbcTateCandidateQ=1/j` 当实际 q；不靠 j-match 推点比较 |
| **03 A2 的实际商/基本群/base change** | `Mzk1A2QuotientMorphismActual`、`Mzk1A2InvolutionCandidateActual`、`Mzk1A2SignActionActual`、`Mzk1A2ScalarStackExtensionActual`、`Mzk1A2PartialFieldsActual`（均 DONE，但**退化 point-stack/identity**）；`Mzk1GaloisRingBridgeActual`、`Mzk1ObjectLockDataActual`、`Mzk1BaseChangeQCorrespondenceActual`（place/completion 对应） | finite étale 类别/quotient gluing 的既有 donor；place/completion 对应结构；Galois 对齐 | 真实 U、[-1]、[U/G] 商栈；π₁/groups；`unique_elliptic_involution` 语义修复（排除 identity）；base change 同一张图 | **退化 A2 point-stack/identity 构造不再作为实际 producer**（仅接口参考）；`A2PartialFields.unique_elliptic_involution` 量词含 identity，须修 |
| **04 局部运输与单位商** | `Mzk1PadicFieldValuedQpActual`（DONE 02:12:07）、`Mzk1PadicFieldValuedBridgeActual`（01:49:56）、`Mzk1GaloisCompletionActual` 旧 olean（valueGroup DONE 02:21:06，当前源重编 pending）、`Mzk1IVThm110UnitLogNorm*` 链、`NormalizedNormValuationResidueActual`、`Mzk1Ind1KernelBridgeActual`/`KernelIntegersActual`/`ValuationDataActual`、`Mzk1TruncatedUnitsPrimary/SecondaryActual`、`Mzk1CongruenceUnitsEquivGeneralActual`、`Mzk1IVThm110IutIVCongruenceCardActual`、`Mzk1IVThm110PrincipalUnitsResidueActual`、`Mzk1IVThm110CardExponentActual` | Qp/PadicField v=valuation、completion 运输、unit quotient/log-shell/Haar 计数、principal/residue card | `RelativeNormFieldNormActual` **FAIL 02:30:44**（缺 Module.Finite/IsScalarTower）；`Mzk1TaskECompletionFieldEquivActual` **FAIL 02:02:47**（`theorem ...: Prop` 应为 def + synthInstance）；`WQuotientLatticeIdentification` pending；stage4 UniformContinuous/Completion.mapRingHom | 不再把 abstract W_F 与 F̄ˣ/tors 等同；不把有限秩连续性推广成任意拓扑群 |
| **05 选择 l 与合格初始数据** | donors：`S2020DicksonTransvectionActual`、`S2835ImageContainsSL2Actual`（仅搬假设）、`GenEll16BelyiExistenceActual`、`Mzk1BetaAvoidingFoldActual`、`Mzk1Consumer24AdapterUnconditionalActual`、`Mzk1Lemma22RationalGateActual`、Section2 素数供体 | prime avoidance、Chebyshev/PNT、Belyi/避让、SL₂ 矩阵部分 | 实际 l、torsion 域、坏位/section/cusp/label；S1 isogeny-height 或 S2 Frobenius 证书或 S3 X₀(l)（三选一主线 S1） | 不以 `LargeImage` 为额外输入；GenEll06 是 statement ledger 不是高度 producer |
| **06 全局 q 的几何实现与 hq** | S3133 四件（DONE 01:55–01:57：Divisor 01:55:48、Readout 01:55:52、LogVolume 01:56:41、Agreement 01:57:36）、`QPilotGlobalLogVolumeFromQActual`（DONE 01:54:53）、`Mzk1QVMultiplicityBridgeActual`（DONE 02:27:50）；donors `GlobalRealifiedFrobenioidActual`、`QPilotGlobalDivisorOnCarrier`、`QPilotZeroLocusDivisorActual`、`BaseQLogVolumeActual`、`NativeGlobalQPilotNormalizedLogVolumeActual` | 全局 q 除子/degree、`qPilotRealifiedLogVolume=-Σmult_b log(residueNormBase)`、`nativeQVPilotNormalizedSignedLogVolume`、`qVEffectiveMultiplicity=order·localResidueDegree` | 实际乘积区域+加权 reading 接回；index map `Bad→FinitePlaceAtPrime F p` 与 `actual_A_le_Lbar_add_Dbar_mult` 接线（R1 hq） | **single `C3.q` 全局和路线被替代**（见 §2.1）；`BaseQFamilyActual` arbitrary DVR candidate 不作 qVFamily 替代 |
| **07 源作用/procession/θ-hull 下界** | `Mzk1ThetaUnitLatticeBoundActual`（DONE 02:21:03，conditional hpos/hfin；当前源 10:35:52 新于 olean → 重编 pending）；`Mzk1ThetaFullLatticeBoundActual`（DONE 02:04:29，hsub 方向作废）；`Mzk1HqHthetaStructuralObstructionActual`；donors `LocalFieldIntegralHullSpan.integralSpan_eq_hull`、`FinitePadicIntegerTensorLattice`/`FinitePadicSubmoduleTensor`、`Mzk1TensorRegionNormalizationActual` | 积分 span⊆hull / compact-nondegenerate equality（product model）；compact lattice donors；`unitLatticeLogVolume_le_thetaHull` | **H1 主线**：实际 source 向量列→tensor 因子坐标→valuation 表→`Γ_t⊆H_t` 与 H1b 预算；hpos/hfin 仍是 explicit GAP（无 `0∈interior tensorIntegerRegion`；无 addHaar 的 `IsFiniteMeasureOnCompacts` 实例）；D1/D2/D3 源箭头覆盖 | **hsub 方向被替代**（`canonicalHull⊆actualRegion` 错向）；**精确 θ hull 等式降级为单向/H0 路线**（见 §2.2、§2.5） |
| **08 同源 signed reading 的 3.12 比较** | `Mzk1Paper312AssemblyActual`（DONE 18:47:32Z）、`Mzk1Paper312CorrectionConsumerActual`（18:25:59）、`Mzk1Paper312UnramifiedActual`（18:39:40）、`Mzk1FinalIndexDecompActual`（17:28:49）、`Mzk1IndexQFEConnectionActual`（17:11:06）、`Mzk1Paper312SourceExponentActual`、`Mzk1Paper312ExplicitActual`、`Mzk1Paper312FinalBoundActual`、`Mzk1TorsionSplitActual`、`Mzk1CeilDecompActual`、`Mzk1IndexDivisionActual`、`Mzk1QuotientDecompActual`、`Mzk1IndexPowIdentityActual`、`Mzk1IVThm110CardExponentActual` | 局部 index/torsion/QFE/card 链、`A_le_Lbar_add_Dbar_of_correction`、`perPlace_of_correction`、`ExplicitPaper312Inequality` | 实际 hθ 下界→Q≤Σ a_t V(H_t)+κ 的 (H)；与 06 真实 weighted reading 同一字典；conditions hcoef/hmu0/hl/hc 仍 explicit | 不把 `actual_A_le_Lbar_add_Dbar` 当无条件 3.12；不把旧 `hCor312` 终点当结果（见 §2.3） |
| **09 Prop1.4/qhat Haar/真实 IV Box/Thm1.10** | `Mzk1IVThm110Actual`（DONE 01:59:08，conditional `hCor312`）、`S3171IUTIVSection1DisplayActual`（01:52:21，hSlack derived）、`Cor312ToABCBridgeInterface`（01:58:32）、`Mzk1Cor312ToABCConsumerActual`（01:59:35，conditional）；`Mzk1IVThm110IutIVCongruenceCardActual`、`Mzk1PrincipalUnitsResidueActual`、`Mzk1IVThm110CardExponentActual`、`Mzk1IVThm110PrincipalDim*`、`Mzk1IVThm110QpDecompActual`；donors `IutIVProp14*`、`P2QNativeSourceArrowActual` | P14 计数/Haar 部分、Thm110 display 代数、hSlack derived、qhatHaar partial | actual packet/istar/ϖ/Φ/different/作用族；Step V 共同容器；P14 实际 e/f/扭元识别；qhat 乘法 Haar 模数 | **`hCor312` 作为终点被替代**（logQ 必须由 08 的 3.12 给出）；条件 display 仅作 donor（见 §2.3） |
| **10 局部→全局/统一 ε** | `Mzk1ABCMainEstimateActual`（DONE 10:39:04Z，conditional）、`Mzk1ABCHeightEstimateActual`；donors `GenEll05`、`ThetaBoundToHeightWeight`、F4/F5 frontier donors | ε 代数、Frey j-height/ABC 等价、bounded discrepancy | G1/G2/G3 全局化（Fermat cover + protected noncritical map + 紧性，或 2-adic/archimedean packet）；uniform B_ε；UndilatedHeight/Region 若只为恰好系数 1 可剪 | 不把 `hbound`/free compatibility/conditional frontier 当终点；F4/F5 保持 donor，不攻击 |
| **11 Frey j-height / ABC 终点** | `ABCEllipticHeightCriterion.abcConjecture_iff_freyJProductHeightCriterion`（donor，直接消费正向）；`ABCEllipticHeightCriterion` 末端代数 | 最终等价、ε 吸收、6/log(27/64) 常数 | 只交付实际 height/region 估计（10 的输出），不重写末端 | 不写新 wrapper；不从 `hCor312`/hbound 直接推 ABC |

---

## 2. 被替代的旧目标（superseded，不再作为路线终点/证明目标）

### 2.1 single `C3.q` 全局和路线
- 涉及：`Mzk1C3BaseQIdentificationActual`（`C3BaseQElementIdentification.log_relation`、`GlobalSumAggregation`、`ClauseBBaseQSourceIdentity`）、`Mzk1BaseChangeQCorrespondenceActual`（`QPilotC3SignedAggregation.signed_eq_global`、`qPilotLogVolumeReading_le_actualQPilotSignedLogClassical_of_structures`）。
- 为何替代：`P.signedQPilotLogVolume` 是单 local `C3.q` 的 log；全局 packet 投影才是 q_b（revision15 §9.4）。不再证明“独立 C3.q 的 log = 任意全局和”。
- 处置：保留为 **local instance / conditional donor**；接线改为 06 的真实 packet + S3133 weighted aggregation + 局部投影。

### 2.2 hsub 方向
- 涉及：`Mzk1ThetaFullLatticeBoundActual.fullLattice_le_thetaHull_of_bridges` 的 `hsub : arithmeticTupleCanonicalHull ⊆ actualC3LogShellTensorRegion`。
- 为何替代：hsub 方向与真实包含相反（GOAL-PROGRESS 已记“hsub 方向已确认错误”）；真实方向是 `tensorIntegerRegion ⊆ actualC3LogShellTensorRegion` 等（`Mzk1ThetaUnitLatticeBoundActual.tensorIntegerRegion_subset_actualRegion`）。
- 处置：旧 `hsub` 不用；走 unit-lattice 单向界 `unitLatticeLogVolume_le_thetaHull`（仍条件 hpos/hfin）。

### 2.3 `hCor312` 作为终点
- 涉及：`Mzk1IVThm110Actual`（`thm110_display_of_hCor312`）、`S3171IUTIVSection1DisplayActual`（hSlack derived）、`Mzk1Cor312ToABCConsumerActual`、`Mzk1IVThm110LogQActual`（`logQ_bound_of_hCor312`）。
- 为何替代：revision15 §12.4 明确 logQ bound 必须由 08 的 3.12 得出，不作为自由输入；最终目标 (T) 不能以 `hCor312` 为 hypothesis 的 display 终点。
- 处置：保留 display 代数/hSlack donor；终点改接 08 的 3.12 结果（`ExplicitPaper312Inequality` 链）与 07 的 hθ 下界。

### 2.4 退化 A2 point-stack/identity producer
- 涉及：`Mzk1A2PartialFieldsActual`（point stack + identity candidates）、`Mzk1A2ScalarStackExtensionActual`、`Mzk1A2SignActionActual`、`Mzk1A2InvolutionCandidateActual`（`a2EllipticInvolutionCandidate := Hom.id`）。
- 为何替代：revision15 §2 指出 producer 使用退化 point stack；§6.4 要求修正 `unique_elliptic_involution` 量词（当前含 identity）。
- 处置：仅保留接口/构造思路；实际 U、[-1]、[U/G]、π₁/groups 从 03 重做；`unique` 语义修复与消费者一起重审。

### 2.5 精确 θ-hull 等式 / hθ 精确计算
- 涉及：`Mzk1ThetaFullLatticeBoundActual` 的精确等式目标、旧“hθ 精确整 hull 体积”要求；hθ exact equality 在 `coord/LEAN-INDEX.md` §3、GOAL-PROGRESS §6 已降级。
- 为何替代：revision15 §11.1 只需 (H0) 的有限源像下界 `Γ_t⊆H_t`，不要求所有 possible images 分类；hull 体积可作单向界。
- 处置：改为 H1/H2/H3 任一给出 signed 体积下界；单向已由 unit-lattice 路线提供（条件 hpos/hfin），不再追求 integralSpan_eq_hull 在 arithmetic-tuple carrier 的等式。

### 2.6 其他不算结果的旧接口
- `BaseQFamilyActual` 的 arbitrary DVR candidate：不作 `qVFamily` 替代（revision15 §2）。
- 任何 `hbound` / 自由 compatibility 字段 / `Nonempty` Required 字段：只作接口，不作终点（revision15 §1）。
- `Mzk1IutIVTruncatedUnitsCardCorrectedActual`（tautology/spec-only）、`Mzk1Ind1CorrectedExtractionActual`（spec-only）：只能当接口，不能当证明体。
- `Mzk1ThetaFullLatticeBoundActual` 的 hsub 版本、旧 `hθ 精确等式` 相关行：见 §2.2/§2.5。

---

## 3. 当前 RED / pending（与节点直接相关）

| 资产 | 状态（watchdog） | 阻塞节点 | 明确修复点 |
|---|---|---|---|
| `RelativeNormFieldNormActual` | **FAIL 02:30:44Z**；无 olean | 04 | 缺 `Module.Finite (NativeBaseCompletionRaw X) (NativeFCompletion X)`、`IsScalarTower ℚ_[pBase] (NativeBaseCompletionRaw X) (NativeFCompletion X)`；文件级 local instances |
| `Mzk1TaskECompletionFieldEquivActual` | **FAIL 02:02:47Z**；olean 09:54:32 stale | 04 | `theorem CompletionFieldQFiveEquivRequired : Prop :=` 应为 `def ... : Prop :=`；另 synthInstanceFailed |
| `WQuotientLatticeIdentification`（`Mzk1Ind1WQuotientLatticeActual`） | 源码 pending/no olean | 04 | p=5 特化 `completionWQuotient ≃* ZpLattice 5 d` 的 inhabitant；后续 units/torsion |
| hpos/hfin（`Mzk1ThetaUnitLatticeBoundActual` 条件） | DONE 02:21:03 但 conditional；当前源 10:35:52 新于 olean | 07/09 | 缺 `0∈interior tensorIntegerRegion`（或 region=lattice 等式）；缺 addHaar 的 `IsFiniteMeasureOnCompacts` 实例 |
| `Mzk1GaloisCompletionActual` | 旧 olean 10:21:05（valueGroup DONE 02:21:06）；当前源 10:35:22 重编 START pending | 04 | UniformContinuous/Completion.mapRingHom；当前源未验收 |
| `Mzk1ThetaUnitLatticeBoundActual` | 当前源 10:35:52 新于 olean 10:21:03 | 07 | 当前源待重编；重编后重新 audit |
| `Mzk1Cor312ToABCConsumerActual` / `Mzk1IVThm110Actual` | DONE 但 conditional on hCor312 | 09/10 | 作为终点被替代；只保留 display donor |

---

## 4. 证据与指针

- watchdog：`dag/watchdog/watchdog.log`；单文件日志 `dag/watchdog/logs/`；
- 审计：`AUDIT_LEDGER.md`；Task G wiring：`coord/AUDIT-HQ-HTHETA-WIRING.md`；
- 路线：`coord/P7-GLOBAL-Q-HULL-CONSTRUCTION-20261115.md`；状态：`coord/GOAL-PROGRESS.md`；
- 索引：`coord/LEAN-INDEX.md`；本轮**未编译 Lean**，statement_compiles/proof_body_checked/kernel_closed/target_accepted 均 NOT_RUN（除已有 DONE 资产的历史证据）。

---

## 5. Route correction 2026-11-15（Lead）

- **one-way hθ/hq** 可直接用 `Mzk1HaarProductStrictMainlineActual.rp_strict_measure_resolved`：
  `rpVolume T (rpRegion T) < rpVolume T (s1902Hull T)`（file:165；watchdog DONE 2026-11-11T02:50:29；olean 10:50 > src 10:48）；
  经 `rpRequirement : XiEContainmentRequirement`（qRegion/thetaPossibleImages=rpRegion；hullRegion=s1902Hull；strict_measure 由 rpRegion_measure_lt_full）。
- `ClosedBallMassFormula`（`Mzk1ProductFiberMultBridgeGapActual`）与 `ProductHaarToFiberMult` **只用于 exact product-Haar 等式**；one-way 主线不等待它们。
- `BadPlaceBijection` generally false（已记录）；fiber 路线 = `QVBadPlaceFiber`（total map）/ injection。
- 节点 07/08 映射相应更新：可复用 donor 增加 `rp_strict_measure_resolved`；ProductFiber* 的 DONE 标为 interface/gap（非 one-way 必需）。

---

## 6. Route decision 2026-11-15（Lead）：one-way 接受 node0609_rpRegion_volume_le_hull

- **接受** `Mzk1Node0609OneWayConsumerActual.node0609_rpRegion_volume_le_hull`（DONE 03:34:30Z；olean 11:34:29 > src 11:33:20）：`rpVolume T (rpRegion T) ≤ rpVolume T (s1902Hull T)`，由 `node0609_rpRegion_volume_lt_hull`（= `rp_strict_measure_resolved`）取 `le_of_lt`；
- **exact weighted-q equality 在 inequality path 上不要求**：`ProductHaarToFiberMult`/`MqFiber` 等式、`ClosedBallMassFormula` 降级为 exact/可选强化；ProductFiber（03:27:31）、QVWeighted（03:33:17）DONE 不再是 blocker；
- 节点 07/08 可复用资产增加 `Mzk1Node0609OneWayConsumerActual`；下一步 = rpRegion/s1902Hull 与实际 packet 对象对齐 + hq fiber/index 接线。

---

## 7. CONFIRMED exact-missing inputs 2026-11-15（Lead）

- horder / hcoef / hbase 三个输入已确认 exact missing（无 donor；horder 有 order>1 反例；hbase absence of donor）→ **无无条件证明路线**；
- 最终目标只能 conditional（horder + hcoef/hmu0/hl/hc + hbase）；与 node06/09 归约（hmult→horder、hper→hcoef/hmu0/hl/hc）一致。

---

## 8. Final conditional chain 2026-11-15（Lead）

- final_abcHeightBound_of_cards（Node09FinalABCBridge DONE 05:09:05）为最终条件端点；
- exact inputs：horder/hcoef/hbase/cards family；cards 供给后经 frozen cor312ToABCBridge_heightBound 闭合，无 additional gap；
- 仅 stale probes FAIL；无产品级 real red。

---

## 9. Round18 audit status 2026-11-15（Lead）

- final conditional endpoints green（FinalConditional/ABCBridgeConditional/FinalABCBridge/CardsToFrontier/SingletonFinal/RegionMono/Gap2ToCards）；
- paper-level 仅 frozen gap2 + hweightDictionary；residual horder/hcoef/hbase；no inhabitant/fake；
- comparison (1) removed by RegionMono（singleton ⊆ normalizedComparisonRegion 定义性 + logVolume_mono）；
- 05:40 后唯一 FAIL：QVFiberWeighted 05:41:49（rerun）。

---

## 10. CRITICAL hdeg+D inconsistency 2026-11-15（Lead）

- hdeg + D 不一致（iqCarrierModel_sourceHaarData_not_nonempty_of_degreeFaithful:583-590）；
- DegreeUpper vacuous（hdeg+D 不可满足）；hweightDictionary 无 actual evidence；
- cards/final endpoints 非形式 vacuous但无 discharge path；hull obstructions sourceHullVolume_eq_top_of_degreeFaithful 等；
- 不得以 degree-faithfulness 路线作 hweightDictionary/hdegreeBound 实际供给。

---

## 11. ROUTE RE-ANCHOR 2026-11-15（Lead，Round23）

- mainline 重新锚定 N0–N11；cards/S3135 为 auxiliary（非 mainline）；
- 后续只以 N0–N11 记录 mainline 进度；cards/S3135 DONE 记录保留但降级为辅助证据。

---

## 12. ROUTE CORRECTION 2026-11-15（Lead）

- deviation：cards/S3135 + ad hoc N5 被当 mainline；
- 正确路线：**P1–P8 / D1-H1-S1-G1**；
- cards/S3135/adhoc N5 为 off-route/auxiliary；后续只按 P1–P8 / D1-H1-S1-G1 记录 mainline。
