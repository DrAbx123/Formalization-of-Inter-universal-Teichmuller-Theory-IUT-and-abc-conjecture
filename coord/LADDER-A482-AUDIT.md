# A482: LADDER rung 资产 vs 实际 Lean 声明核对（shehdd 审计）

日期: 2026-11-11。来源: coord/LADDER-A482.md 四个 rung 的资产清单（名称 token）+ 本仓库声明索引/文件系统核对。

规则: token 解析优先级 = 文件 basename 包含 → 声明名精确/后缀匹配；olean 状态按 .lake/build/lib/lean 对应路径检查。value-model 路线结论按 A481/F2 明确禁止作为 rung。

## Rung R1 资产核对

| LADDER token | 实际 file:decl 映射 | olean | 一致性 |
|---|---|---|---|
| SourceLogShellCarrier | SourceLogShellCarrier.lean | SourceLogShellCarrierTwistContainer.lean :: LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean:sourceLogShellStar, sourceLogShellStar_pos, SourceLogShellDatum, pStar | fresh | RENAMED/MULTI (2) |
| PrimeStripsConstruction | LeanFormal/IUT/IUTII/Frobenioid/PrimeStripsConstruction.lean:FPrimeStripLink, refl, trans, localDegree_apply | fresh | OK |
| SourceHodgeTheater | SourceHodgeTheaterFamily.lean | SourceHodgeTheaterFamilyLawsReduction.lean | SourceHodgeTheaterFamilySourceReduction.lean :: LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean:SourceHodgeTheaterFamily, theater_injective, theater_eq_iff, link_refl_at | fresh | RENAMED/MULTI (3) |
| SourceDThetaConstruction | LeanFormal/IUT/IUTIII/Theorem311/SourceDThetaConstruction.lean:DThetaShadow, dThetaShadow, dThetaShadow_index, dThetaShadow_strip | fresh | OK |
| SourceH1H2Construction | SourceH1H2Construction.lean | SourceH1H2Construction.lean :: LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction.lean:fPrimeStripAt, dThetaAt, fPrimeStripAt_eq, dPrimeStripAt_eq | fresh | RENAMED/MULTI (2) |
| MultiradialAlgorithmReduction | LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean:applyRoute_ind1_commute, applyRoute_ind2_commute, applyRoute_ind1_commute_logVolume, applyRoute_ind2_commute_logVolume | fresh | OK |
| SourceFiniteMultiradial | LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean:core, core_base, core_level, core_ind1 | fresh | OK |

## Rung R2 资产核对

| LADDER token | 实际 file:decl 映射 | olean | 一致性 |
|---|---|---|---|
| Ind1Reduction | LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean:generatedQuotientMap_eq_of_ind1Step, Ind1Setoid, ind1QuotientMap, ind1QuotientMap_ind1 | fresh | OK |
| Ind2Reduction | LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean:Ind2AlienLink, linkMap_ind1Step, linkMap_ind2Step, linkMap_respects_indeterminacy | fresh | OK |
| K1K2BoundaryReduction | LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean:nonarchimedeanImageInclusion, ind3ImageWellDefined, archimedeanTargetLift, identityLabelledKummerIso | fresh | OK |
| SourceColumnCarrierIdentification | LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceColumnCarrierIdentification.lean:core_ind1_rotate_of_comm, core_ind2_rotate_of_comm, coreColumnRealization, coreColumnRealization_ind1 | fresh | OK |
| SourceProcessionStepXI | SourceProcessionStepXI.lean | SourceProcessionStepXIInclusionResidual.lean | SourceProcessionStepXIMinimalForm.lean :: LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceProcessionStepXI.lean:ProcessionTheorem311Target, Wall, ProcessionTheorem311Target_eq, routeWall | fresh | RENAMED/MULTI (3) |
| SourceAdjacentColumnProcessionIsomorphism | LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:SourceProcessionIsomorphism, intEquiv_trans_apply, intEquiv_refl_apply, refl | fresh | OK |

## Rung R3 资产核对

| LADDER token | 实际 file:decl 映射 | olean | 一致性 |
|---|---|---|---|
| HullDeterminantLogVolumeReduction | LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean:HullDeterminantLogVolumeFrozenSpec, hullDeterminantLogVolumeFrozenSpec_holds, matrixLogDet, matrixLogDet_mul_posDef | fresh | OK |
| PaperIQCarrierActual | tmp/sheaf/xif/paper/PaperIQCarrierActual.lean:C6IQCarrierOf, actualC6_hull_eq_canonical, actualC6_iqInterface_hull_eq, actualIQInterface | fresh | OK |
| S2723GlobalIQHullActual | tmp/sheaf/xif/paper/S2723GlobalIQHullActual.lean:GlobalIQIndex, GlobalIQPlaceIndex, globalIQPlaces, GlobalIQAmbient | fresh | OK |
| S3129IQHullLogVolumeSourceActual | tmp/sheaf/xif/paper/S3129IQHullLogVolumeSourceActual.lean:sourceQlPrincipalUnitLogImage, sourceQlPrincipalUnitLogImage_eq_principalUnitLogShell, sourceQlPrincipalUnitLogImage_subset, sourceQlHullImage | fresh | OK |

## Rung R4 资产核对

| LADDER token | 实际 file:decl 映射 | olean | 一致性 |
|---|---|---|---|
| ArithmeticQPilot | ArithmeticQPilotBaseChange.lean | ArithmeticQPilotGlobalNormalization.lean | ArithmeticQPilotLogVolume.lean :: LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotBaseChange.lean:residueNormBase, residueNormBase_gt_one, log_residueNormBase_pos, qNorm_eq_residueNormBase_zpow | fresh | RENAMED/MULTI (3) |
| CardHullRealGeometryGapCards | LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryGapCards.lean:possibleThetaPilotImageSet_eq_iUnion_singleton, possibleThetaPilotImageSet_eq_biUnion_finset, possibleThetaPilotImageSet_subset_iff_forall_mem, sourceOneCircUCompactness_image_subset_iff_forall | fresh | OK |
| S1929LiteralIQCarrierActual | tmp/sheaf/xif/paper/S1929LiteralIQCarrierActual.lean:bad_nonempty, oneSignedLabel, oneThetaLabel, rootExtensionProductThetaImage_oneThetaLabel | fresh | OK |
| SourceSHETransportObligations | LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportObligations.lean:that, toLink, toLink_index, toLink_mapPi_apply | fresh | OK |
| Obligations | SourceObligations.lean | ConcreteInitialThetaCObligations.lean | SourceObligations.lean :: LeanFormal/IUT/IUTI/HodgeTheater/SourceObligations.lean:hodgeTheaterSource, hodgeTheaterSourceExistence | fresh | RENAMED/MULTI (3) |
| APT | UnitPerfectionMapTopology.lean | Example36ValueMapTransport.lean | Example36ValueMapTransportCorrection.lean :: LeanFormal/IUT/Foundations/LocalFields/UnitPerfectionMapTopology.lean:continuous_integralUnitMap, unitPerfectionMap_comp, continuous_unitPerfectionMap | fresh | RENAMED/MULTI (3) |
| CertificateHullWiring | CertificateHullWiring.lean | CertificateHullWiringRealization.lean | CertificateHullWiringSigned.lean :: LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean:ofReal_le_toReal_of_ne_top, toReal_le_of_le_ofReal, iqHullRealVolume, iqHullRealVolume_nonneg | fresh | RENAMED/MULTI (3) |
| ConcreteFiniteRouteColumns | LeanFormal/IUT/IUTIII/Corollary312/StepXI/ConcreteFiniteRouteColumns.lean:finiteSup, le_finiteSup, finiteSup_le, finiteHullOfValues | fresh | OK |
| StepXIContract | Mzk1HullStepXIContractConsumerTreeActual.lean | Mzk1HullStepXIContractConsumerTreeActualAdapted.lean | Mzk1StepXIContractActual.lean :: tmp/sheaf/xif/paper/Mzk1HullStepXIContractConsumerTreeActual.lean:(decl index empty) | stale | RENAMED/MULTI (3) |

## Rung 缺口报告

- R1 (BPS -> multiradial representation): 对象资产齐全（SourceLogShellCarrier, PrimeStripsConstruction, SourceHodgeTheater*, SourceDThetaConstruction, SourceH1H2Construction, MultiradialAlgorithmReduction, SourceFiniteMultiradial 均是 tree/paper 已存在模块）。**缺口**: LADDER 要求的“算法打包”（BPS 输入 -> multiradial 输出）尚无单一定理/结构 rung 文件；需以 MultiradialAlgorithmReduction.carrierAlgorithmContract + SourceFiniteMultiradial 为组件新增真实 rung 定理。
- R2 (dsc: Ind1/2/3): Ind1Reduction/Ind2Reduction/K1K2BoundaryReduction(Ind3) 均存在；SourceColumnCarrierIdentification/SourceProcessionStepXI/SourceAdjacentColumnProcessionIsomorphism 存在（名称一致）。**缺口**: 四三角合成（Ind1/2/3 联合下降 + 0-column quotient 组装）未有单一 rung 定理。
- R3 (hull+det): HullDeterminantLogVolumeReduction(FrozenSpec)、PaperIQCarrierActual、S2723GlobalIQHullActual、S3129IQHullLogVolumeSourceActual 均存在（paper 层资产在 tmp，需 watchdog 编译进 DAG）。**缺口**: literal 载体上的 hull 有限性（Cor 3.12 内容层）尚待 abc/hull 以 product Haar 证明；value-model 的 hull 有限性禁止作为证据（F2）。
- R4 (HDD∘SHE): ArithmeticQPilot*（3 文件）、CardHullRealGeometryGapCards、S1929LiteralIQCarrierActual、SourceSHETransportObligations、Obligations.lean(ipl/she -> LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean)、StepXI/APT.lean、CertificateHullWiring、ConcreteFiniteRouteColumns、StepXIContract（声明在 StepXI/Contract.lean:30）均存在。**缺口**: 目标 rung “literal 载体上 3.11.5⇒3.12 的组装” 尚缺；需要把 (hull+det)∘(dsc) 与 SHE/IPL 组装成单一真实定理（当前只有组件）。

## 映射修正（LADDER 名称 -> 实际声明名/文件）

- StepXIContract 是声明名（LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:30），不是文件名；
- Obligations.lean(ipl/she) 对应 LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean（另有多处 Obligations 文件，注意消歧）；
- APT 对应 LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean；
- ArithmeticQPilot* 是 3 个文件的族（BaseChange/GlobalNormalization/LogVolume）；
- S1929LiteralIQCarrierActual / PaperIQCarrierActual / S2723GlobalIQHullActual / S3129IQHullLogVolumeSourceActual 在 tmp/sheaf/xif/paper（paper 层，需 olean 才入正式 DAG）。

## value-model 禁用声明（A481/F2 复核）

- 任何以 value-realized/model-carrier hull 有限性（ValueHullCompactnessInput / sourceHullVolume<⊤ 的 value 版本）为基础的结论不得登记为 rung；证据: SourceHullInterfaceDischarge.lean 的 sourceHullVolume_not_lt_top_of_degreeFaithful / not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful / not_nonempty_valueHullCompactnessInput_of_degreeFaithful。


## A482 映射修正与消歧（人工核对，覆盖上面表内误解析行）

- SourceLogShellCarrier -> LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean: SourceLogShellDatum, pStar, preLogShell, logShell, unitLayer, IQSpan, logShell_eq_invScaledPreLogShell (olean fresh)。TwistContainer 是补充模块，不是该 token 所指；
- SourceHodgeTheater -> LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean: SourceHodgeTheaterFamily, theater_injective, theater_eq_iff, link_refl_at；配套 SourceHodgeTheaterFamilyLawsReduction.lean: thetaPacket_eq/theater_ne_of_ne (fresh)；
- SourceH1H2Construction -> LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction.lean: fPrimeStripAt, dThetaAt, fPrimeStripAt_eq, dPrimeStripAt_eq (fresh)；
- SourceProcessionStepXI -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceProcessionStepXI.lean: ProcessionTheorem311Target, Wall, routeWall (fresh)；InclusionResidual/MinimalForm 为补充文件；
- K1K2BoundaryReduction (Ind3) -> LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean: nonarchimedeanImageInclusion, ind3ImageWellDefined, archimedeanTargetLift, identityLabelledKummerIso (fresh)；注意它与 Theorem311/SourceK1K2CardReduction.lean 是两个不同资产；
- Obligations(ipl/she) -> LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean（ipl/she 记录）；Corollary312/Obligations.lean 是另一文件；
- APT -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean（不是 Foundations/UnitPerfectionMapTopology 等同名片段）；
- CertificateHullWiring -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean（另有 Signed/Realization 变体）；
- StepXIContract -> 声明 LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:30（文件不叫 StepXIContract；tmp 下同名 paper 文件不是 LADDER 所指 tree 资产）；
- ArithmeticQPilot -> 3 文件族：ArithmeticQPilotBaseChange.lean: residueNormBase/qNorm_eq_residueNormBase_zpow, ArithmeticQPilotGlobalNormalization.lean, ArithmeticQPilotLogVolume.lean: qNorm_pos/qNorm_lt_one/localSignedLog (fresh)；

## sorry 审计续（A482 重扫）

- dag/SORRY-AUDIT.md 报 36 模块 / 45 处；词法重扫（去嵌套注释/行注释/字符串）真实源码 sorry = **37** 处。
- 与审计计数不符的文件: C5Native.lean(2->1), FiniteObservationHull.lean(1->0), IPLFamilyData.lean(1->0), P6ChainA.lean(1->0), P6RelaxedGlobalReadout.lean(1->0), P6SHEInd.lean(1->0), IUTExternal32GateV36Actual.lean(1->0), S2748AbsNormGeRationalPrimeActual.lean(1->0)。
- 结论: 部分审计条目为文案字符串/已被 hull 等修复；真实剩余集中在 n8 closure/paper 缺口，已登记 blocked。详见 coord/SORRY-AUDIT-CORRECTION-shehdd.md。
