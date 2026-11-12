# A481: 原文 IQ(S±_{j+1}; n,◦D^vdash_{vQ}) 载体相关资产清单（审计/资产，shehdd）

日期: 2026-11-11。目标: 为 abc/qpilot/hull 提供“先构造原文 IQ 载体（Hodge theater/prime-strips/local log-shell 受限乘积 + Haar），再在其上证 Cor 3.12 hull 有限性与比较不等式”的直接可复用 file:decl 清单。

## 0. 路线纠正的仓库内证据（F2）

SourceHullInterfaceDischarge.lean（tree, olean fresh）已证明 value-realization 路线在数学上不可行：
- `hull_logVolume_realRepresentation`：有限 hull log-volume 的 realRepresentation 转移（仅对有界 hull 可用）；
- `haarContractionInterface` + `haarContractionInterface_hull_logVolume_lt_top`：Haar-contraction 模型（有限维实范数空间 + 收缩 λ + 紧单位球）才能给出 finiteness 字段；
- `sourceHullVolume_not_lt_top_of_degreeFaithful`：pointwise degree-faithful 时 value-realized hull volume 不为有限（= ⊤ 方向）；
- `not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful`：同条件下不存在 paper 形状的 (λ, O, C) 紧性输入；
- `not_nonempty_valueHullCompactnessInput_of_degreeFaithful` + `ValueHullCompactnessInput`：value-level 的 paper-shaped 紧性输入不可满足；
- `iqHullInterfaceDischarge`（Audit.Obligation）：记录上述 F1/F2/F3 结论。

结论: 必须走 literal IQ 载体路线；下列资产直接可用。

## 1. literal IQ 载体（paper 层，已编译/可直接引用）

| file (olean) | 关键 decls | 提供内容 | 直接使用方 |
|---|---|---|---|
| tmp/sheaf/xif/paper/S1929LiteralIQCarrierActual.lean (fresh) | LiteralCompletionIQCarrier, completionToRootExtension, completionToRootExtension_injective, completionToRootExtensionLinear, rootExtensionProductThetaImage_oneThetaLabel, oneSignedLabel, oneThetaLabel | 字面 completion→root-extension 受限乘积 IQ 载体 + theta-pilot 单 label 像 | hull（载体骨架）, qpilot（theta 像） |
| tmp/sheaf/xif/paper/PaperIQCarrierActual.lean (fresh) | C6IQCarrierOf, actualC6_hull_eq_canonical, actualC6_iqInterface_hull_eq, actualIQInterface, actualIQInterface_imageSet, actualIQInterface_image_subset_hull, actualIQInterface_hull_logVolume_lt_top | paper 形状 IQ 接口 + hull 有限性（logVolume_lt_top） | hull（hull 有限性）, abc（接口字段） |
| tmp/sheaf/xif/paper/IQCarrierFromSource.lean (fresh) | actualB, c6CanonicalHull_compact, actualB_unitRegion_eq, actualB_logVolume_eq, actualLineBundleData(_nonempty), ActualIQCarrierDischarges, actualIQCarrierDischarges | 从 source 数据构造 actual IQ carrier（含 line-bundle 数据与 canonical hull compactness） | abc / qpilot（源头构造） |
| tmp/sheaf/xif/paper/S2723GlobalIQHullActual.lean (fresh) | GlobalIQIndex, GlobalIQPlaceIndex, globalIQPlaces, GlobalIQAmbient, globalIQUnitRegion, globalIQUnitRegion_compact, globalIQHaar, globalIQHaar_isAddHaar, globalIQLogVolume(_eq/_mono) | 全局 prime-strip 受限乘积载体 + 单位区域紧性 + Haar 测度 + logVolume | hull（紧性/测度）, abc |
| tmp/sheaf/xif/paper/S3129IQHullLogVolumeSourceActual.lean (fresh) | sourceQlPrincipalUnitLogImage(_eq_principalUnitLogShell/_subset), sourceQlHullImage, sourceHullUnitCompact, sourceHullHaar, sourceHullHaar_isAddHaar, sourceHullUnitRegion | source-side log-shell 像 + hull Haar/紧性 | hull（source log-shell 进入 hull） |
| tmp/sheaf/xif/paper/S2958HalfIQHullCertificateActual.lean (fresh) | S2958l, S2958W, S2958Pt, S2958_hpt, S2958Data, S2958_hvalue, S2958_hw, S2958_thetaHull_zero | 有限半 IQ-hull 证书（WeightedValues + hull 数据实例） | hull（证书示例/消费者） |
| tmp/sheaf/xif/paper/GlobalIQHullInterfaceActual.lean (source, 无 olean) | GlobalIQAmbient, globalIQUnitRegion, globalIQHaar(_isAddHaar), globalIQLogVolume(_eq/_mono), globalIQUnitRegion_compact | 全局 IQ hull 接口（与 S2723 互补） | hull/abc（编译后可直接引用；已加入 extra-targets） |
| tmp/sheaf/xif/paper/GlobalIQHullThetaPilotActual.lean (source, 无 olean) | GlobalThetaPilotCarrier, globalThetaPilotImageSet, globalThetaPilotHull, globalThetaPilotImageSet_subset_hull, globalThetaPilotPoint, globalThetaPilotImageSet_nonempty, globalThetaPilotHull_nonempty | 全局 theta-pilot 像 → hull 接口（literal theta-pilot image） | qpilot / hull（编译后可直接引用；已加入 extra-targets） |

## 2. tree 核心组件（已编译，按组件分组）

### 2.1 local log-shell / 积分 log-shell
- LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean: SourceLogShellDatum, pStar(_pos/_ne_zero_cast), preLogShell, logShell, unitLayer, IQSpan, logShell_eq_invScaledPreLogShell, kummerImages_mem_logShell
- LeanFormal/IUT/IUTII/Kummer/SourceLocalLogShellDatum.lean: sourceLocalLogShellDatum, _pStar, _preLogShell(_eq_range_unitLogHom), _logShell_eq_integralLogShell, _zero_mem_logShell, _unitLog_one_mem_logShell
- LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean: unitLog, unitLog_mul/_pow/_one/_eq_log1p, unitLogWithExponent(_independent); LogarithmLocalInverse.lean: exists_log1p_preimage, exists_unitLog_eq_scale_mul, integers_subset_integralLogShell; IntegralUnits.lean: Integers, unitOfNormOne, principalUnits, compactSpace_units

### 2.2 Haar 测度
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean: sourceHaarActualNonpositiveAddSubmonoid, SourceHaarActualValueMonoid, sourceHaarActualDegree(_nonpos), sourceHaarActualPositiveRealAction, sourceHaarActualTrivialAction, sourceHaarActualShearAddEquiv/_MulEquiv, SourceUnitRegionHaarData, sourceUnitRegionHaarInterface, sourceUnitRegionHaarInterface_hull_logVolume_lt_top
- tree IQCarrierHaarData.lean: image_mul_eq_scaledRegionImage, sourceSetVolume_lt_top_iff_exists_logDegree_le, sourceHullVolume_lt_top_iff_exists_hullLogDegree_le, SourceUnitRegionHaarData
- ABCBridge/Geometry/FinitePlaceIQHullInterface.lean: haarLogVolume(_of_lt_top/_eq_zero_of_null/_mono), arithmeticTupleIQHullLogVolumeInterface, exists_arithmeticTupleIQHullLogVolumeInterface
- ABCBridge/Geometry/FinitePlaceIQHullSharpUpperBound.lean: arithmeticTupleIQHullUnitRegion_measure_*（pos/lt_top/ne_zero/ne_top/toReal_pos）, arithmeticTupleIQHullUnitLogTheta_nonneg

### 2.3 受限乘积 / tensor 分解
- LeanFormal/IUT/IUTII/Kummer/SourceLogShellIQTensorPacket.lean: sourceLogShell_span_pi_eq_pi_span, sourceLogShellDirectSumPacketSet, sourceLogShellIQDirectSumPacket(_eq_span_pi/_mem_iff/_single_mem/_pStar_inv_mul_mem), sourceLogShell_piCongrRight_image_pi
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/Volume.lean: PositivePacket, tensorPacket, packetDet/_tensor/_rescale, packetLogVolume; HullDetLogVolumeReduction: matrixLogDet_* (tensor/scale/pow)
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierConcreteModel.lean: iqCarrierModelLogDegree(_add), iqCarrierModelScaling, iqCarrierModelScaleShift, iqCarrierModelUnitRegion, iqCarrierModelUnitDegreeBound, iqCarrierModelHull, iqCarrierModelImageSet

### 2.4 紧性
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean: IQHullLogVolumeInterface, imageSet_logVolume_le_hull, hull_logVolume_lt_top, lower_bound_and_finiteness, iqHullLogVolume
- IQCarrierHaarData.lean / SourceUnitRegionHaarDataActual.lean: sourceUnitRegionHaarInterface_hull_logVolume_lt_top, sourceHullVolume_lt_top_iff_exists_hullLogDegree_le
- LeanFormal/IUT/Foundations/AlgebraicGeometry/ClosedBallInstanceFromProperSpace.lean + ClosedBallProperSpaceVerification.lean + CompletionProperSpaceConsumer.lean: closed-ball compactness/proper-space 实例

### 2.5 theta-pilot 像 / possible image
- LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean: possibleImage_subset_of_generator_mem, sourceLogShellOnePlaceFamily, sourceThetaPilotProductMap(_tprod), sourceThetaPilotTensorIQPacket, sourceThetaPilotIQPacket, possibleImage_subset_sourceThetaPilotIQPacket, sourceThetaPilotProductMap_image_subset_tensorIQPacket
- LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean: core/profile, sourceMultiradialPossibleImage, sourceMultiradialMap（以及 Ind1/2/3 作用）
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction.lean: sourceScalingUnits_subset_sourceHolomorphicHull, sourceHolomorphicHull_eq_closure, sourcePointVolume_mul_le, sourceHullVolume_eq_imageVolume_iff, sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le

### 2.6 ABCBridge 有限位 IQ-hull 证书（直接给 abc）
- ABCBridge/Geometry/FinitePlaceIQHullLogShellRegion.lean: arithmeticTupleLogShellScaling(_ne_zero), arithmeticTupleCanonicalHull_subset_smul_logShellUnitReference, arithmeticTupleLogShellUnitRegion, arithmeticTupleLogShellScaleShift
- ABCBridge/Geometry/FinitePlaceIQHullSignedCertificateNonvacuous.lean: arithmeticTupleSignedFloorQ(_negative/_le_hullLog), arithmeticTupleSignedFloorCertificate(_qSigned/_thetaSigned/_q_negative)
- ABCBridge/Geometry/FinitePlaceIQHullSharpUpperBound.lean: arithmeticTupleIQHullUnitRegion(_measure_*), arithmeticTupleIQHullUnitLogTheta_nonneg
- ABCBridge/Geometry/FinitePlaceIQHullInterface.lean: 上述接口/存在性

## 3. 给 abc/qpilot/hull 的直接使用建议（一行对应）

- hull: 用 PaperIQCarrierActual.actualIQInterface(_hull_logVolume_lt_top) 做接口；用 S2723 GlobalIQAmbient/globalIQUnitRegion_compact/globalIQHaar 构造全局载体；用 S3129 sourceHullHaar/sourceHullUnitCompact 提供 source log-shell 侧 Haar/紧性；用 SourceHullCompactnessReduction.IQHullLogVolumeInterface/hull_logVolume_lt_top 做 finite 层；禁止再用 ValueHullCompactnessInput/sourceHullVolume 的 value-realization路线（F2 refuted）。
- qpilot: 用 S1929 LiteralCompletionIQCarrier/rootExtensionProductThetaImage + GlobalIQHullThetaPilotActual.globalThetaPilotImageSet(_subset_hull) 做 theta-pilot 像与 hull 包含；用 SourceThetaPilotIQContainment.possibleImage_subset_sourceThetaPilotIQPacket 做 IQ-packet 包含。
- abc: 用 IQCarrierFromSource.ActualIQCarrierDischarges/actualIQCarrierDischarges + PaperIQCarrierActual.C6IQCarrierOf 拿 actual carrier；用 ABCBridge/Geometry/FinitePlaceIQHull* 的 arithmeticTuple 证书把 hull log-volume 接到 ABC 侧；用 S2958HalfIQHullCertificateActual 做有限证书实例。

## 4. 待编译/缺口（短清单）

- GlobalIQHullInterfaceActual.lean 与 GlobalIQHullThetaPilotActual.lean：源码在，无 olean；已加入 dag/watchdog/extra-targets.txt 等编译（本文件写入时）。
- SourceThetaPilotIQContainment.lean 实际路径在 LeanFormal/IUT/IUTII/Kummer/（非 Theorem311），索引前缀见文档修正。
- 其它 literal IQ 资产: 未发现缺载体；value-realization 相关（ValueHullCompactnessInput/degreeFaithful 分支）按 F2 仅作反例/审计，不再作为推进路线。

## 5. sorry 收口审计（续）

- dag/SORRY-AUDIT.md 报 36 模块/45 处；词法级重扫（去掉注释/字符串）真实源码 sorry = 37 处，8 个文件计数不符：FiniteObservationHull/IPLFamilyData/P6ChainA/P6RelaxedGlobalReadout/P6SHEInd/IUTExternal32GateV36Actual/S2748 已无真实 sorry（部分文案字符串、部分 hull 已在 A480 修复），C5Native 2->1。
- 详见 coord/SORRY-AUDIT-CORRECTION-shehdd.md；n8 blocked 原因见 coord/N8-SORRY-TRIAGE-A480.md 与 coord/DAG-BLOCKED.json。
