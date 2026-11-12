# GAP-CONSTRUCTIBILITY-A483 — 9 个 gap 关键词组三分类（①可拼装 / ②需补构造 / ③已证不可行）

generated: 2026-11-11 (A483 合并; lattice + shehdd)

输入: `dag/GAP-CLOSURE-CANDIDATES.json`（9 组全仓搜索）、`coord/GAP-CLOSURE-A483.md`、`tmp/a483-sections-lattice.md`（lattice 五组）、`tmp/a483-sections-shehdd.md`（shehdd 四组）。

审计规则:
- ① 可从现有已编译资产构造: 给出 file:decl 拼装路径；允许缺“单一 assembly consumer”定理（真实证明目标），但不得缺对象/公理。
- ② 需补缺失构造: 指明缺哪个对象/定理，仓库无替代（附搜索证据/编译失败点）。
- ③ 已知不可行: 引已证 obstruction / DAG-BLOCKED 登记，不重开 rung。
- 禁止把 value-realized/model-carrier 的 hull 有限性当 rung（F2: `SourceHullInterfaceDischarge.lean:170/183/232`；见 `coord/DAG-AUDIT-lattice-A480.md` §5）。
- 本审计只读（src+olean+DAG）；未编译、未碰 watchdog。

## 汇总表（每 gap 一行）

| gap | 三分类 | 一行结论 | 关键证据 / 拼装路径 | 缺失对象 / obstruction |
|---|---|---|---|---|
| R1_multiradial | ① 可拼装 | 9 个编译资产可接成 BPS→multiradial consumer | `PrimeStripsConstruction.FPrimeStrip/FPrimeStripLink`; `MultiradialAlgorithm.multiradialAlgorithm`; `MultiradialAlgorithmReduction.{finiteMultiradialAlgorithmDischarge,sourceMultiradialOutputDischarge}`; `SourceFiniteMultiradial.{core,profile,profile_ind1/2/3_*}`; `SourceDThetaConstruction.theorem311DThetaShadow`; `SourceH1H2Construction.{fPrimeStripAt,dThetaAt,bridge}`; `SourceH1H2OriginalArrows.theorem311H1H2OriginalArrows`; `SourceMultiradialTwoActionEquivalence.sourceMultiradialTwoActionEquivalence`; `SourceHodgeTheaterBridge.SourceHodgeTheaterSystem`; `FiniteSourceColumnTrunkBridge.sourceColumnCarrierIdentification` | 缺唯一 assembly consumer（真实证明目标；无缺失对象） |
| R2_descent | ① 可拼装 | Ind1/2/3 + 0-column carrier 识别可复用 | `Ind1Reduction.*`; `Ind2Reduction.*`; `K1K2BoundaryReduction.{nonarchimedeanImageInclusion,archimedeanTargetLift}`; `FiniteSourceColumnTrunkBridge.sourceColumnCarrierIdentification`; `SourceMultiradialTwoActionEquivalence.sourceMultiradialTwoActionEquivalence` | `SourceProcessionStepXI`/`SourceAdjacentColumnProcessionIsomorphism` 待编译（非缺数学）；四三角合成归 R4 |
| R3_literal_IQ | **② 需补缺失构造** | literal 载体已写出但未编译；缺 literal hull 有限性/归一化定理 | 已编译 near-assets: `PaperIQCarrierActual`(actualIQInterface), `S2723GlobalIQHullActual`, `S3129IQHullLogVolumeSourceActual`, `S1929LiteralIQCarrierActual.{LiteralCompletionIQCarrier,rootExtensionProductThetaImage_oneThetaLabel}`。缺失: literal product-Haar 归一化 + `literalHull` 紧性/有限性；`MeasurableSpace (GlobalIQAmbient)`/Set 类型桥 | 非 ③（F2 仅排除 value-model）；`A481LiteralIQCarrierActual`/`Mzk1LiteralIQHullFinitenessActual` 编译 FAIL 详情见下 |
| R4_four_triangles | ① 可拼装 | APT/IPL/SHE 方图→hull real volume→QCMP→StepXIContract 可组装 | `APT.lean.{SourceAPTStatement,SourceAPTSlotAssembly,sourceAPTTransportSupply}`; `ConcreteFiniteRouteColumns.{finiteAPTData,finiteIPLSquare,finiteSHESquare}`; `CertificateHullWiring.iqHullRealVolume`; `CardQCMPComparison.{QCMPComparisonSupply.toStepXIContract,cor312Conclusion_of_toStepXIContract}`; `Contract.{StepXIContract,Cor312Conclusion}`; `Comparison.cor312Conclusion_of_contract` | 缺 SHE/HDD→comparison 单一组装定理；无新 obstruction（F2 仅边界） |
| fixed_beta | ① 可复用 | finite-β 修正版已证；β=∞ 旧版已反例否定 | `Mzk1BetaAvoidingFoldActual.betaAvoiding_all`; `Mzk1BetaAvoidingBaseActual.{BetaAvoidingBelyiBaseInputCorrected,betaAvoidingBelyiBaseInputCorrected_proved,restatedInductionConclusionFinite_proved}`; 反例: `not_betaAvoidingBelyiBaseInput`, `not_mzk1Lemma24Target_infty` | 无缺失（β=∞ 版按 ③ 记录为已证不可行） |
| scheme_side | ① 可拼装 | Definition3.1 scheme-side 组件齐全 | `SourceDefinition31Boundary.{sectionMap_injective,sectionMap_surjective}`; `SourceDefinition31*` 家族; `SourceInitialThetaData`; `SourceHodgeTheaterBridge.SourceHodgeTheaterSystem`; `tmp/sheaf/l03-g2/S2Transport.SchemeSideHasFiniteGroupQuotients` | `Mzk1SchemeSideMapsActual` 待编译（PENDING）；缺 assembly consumer |
| fiber_functor | **③ 已登记不可行（BLOCKED）** | S1794 五字段 + S2432 slice-push 为真实阻塞 | S1794 五个 sorry 字段；S2432 `test_slicePushNaturality` sorry | `coord/DAG-BLOCKED.json` xif-sorry:*（PRAGMATIC-DEAD-END）；`coord/AUDIT-MANIFEST-2026-11-03.md:19`；Mathlib 缺 slice-push/pseudofunctor pullback API |
| qpilot | ① 可拼装 | θ-pilot scaled region/IQ containment/finite hull 有 olean；缺全局双像+SHE 组装 | `FinitePlaceThetaPilotScaledRegion.{arithmeticTupleThetaPilotGenerator,arithmeticTupleThetaPilotRegion,arithmeticTupleThetaPilotExactRadius}`; `SourceThetaPilotIQContainment.{possibleImage_subset_sourceThetaPilotIQPacket,sourceThetaPilotProductMap_image_subset_tensorIQPacket}`; `CertificateHullWiring.{thetaPilotCarrierFintype,sourceThetaPilotFiniteHull}`; `CardHullRealGeometryGapCards.possibleThetaPilotImageSet_*`; `S1929LiteralIQCarrierActual.LiteralCompletionIQCarrier` | `GlobalIQHullThetaPilotActual` 待编译（PENDING）；缺 q/Θ 双像+SHE 组装定理；无 obstruction（禁 value-model 替代） |
| iut4_compare | ① 可拼装 | rooted QC/HC、undilated height/region、endgame 条件均可用 | `S3131CanonicalRootedQC/HC/_le_HC`; `S3131PaperRouteHeightReductionActual.{UndilatedHeightBound,heightComparisonFamily_of_undilated}`; `S3131PaperRouteRegionReductionActual.{UndilatedRegionBound,regionVolumeFamily_of_undilated}`; `S3131EndgameDependencyLedgerActual.endgame_conditional`; `Iut/Foundations/GaloisImage.imageComparison*` | Section2 undilated 输入为 class-B named（[IUTchIV] Thm1.10/Cor2.2 内容）；无 obstruction |

## 详细证据（lattice：R1/R2/R3/fixed_beta/scheme_side）

## 详细证据（lattice：R1/R2/R3/fixed_beta/scheme_side）

### R1_multiradial — ① 可拼装

- 可拼装路径（全部 src+olean 已核实）:
  1. `LeanFormal/IUT/IUTII/Frobenioid/PrimeStripsConstruction.lean`: `FPrimeStrip`, `FPrimeStripLink`, `refl`, `trans`, `localDegree_apply`, `toAlgebraicClosureUnits_galoisAction`（BPS prime-strip 对象与 link 律）；
  2. `LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean`: `SourceLogShellDatum`, `preLogShell`, `logShell`, `unitLayer`, `pStar`（local log-shell 载体）；
  3. `LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction.lean`: `fPrimeStripAt`, `dThetaAt`, `dThetaAt_identity`, `DThetaBridge`, `bridge`；`SourceH1H2OriginalArrows.lean`: `theorem311H1H2OriginalArrows`；
  4. `LeanFormal/IUT/IUTIII/Theorem311/SourceDThetaConstruction.lean`: `DThetaShadow`, `theorem311DThetaShadow`；
  5. `LeanFormal/IUT/IUTIII/Theorem311/Output/MultiradialAlgorithm.lean`: `multiradialAlgorithm : Obligation`；`Output/MultiradialAlgorithmReduction.lean`: `finiteMultiradialAlgorithmDischarge`, `sourceMultiradialOutputDischarge`, `multiradialAlgorithmReductionRecord`；
  6. `LeanFormal/IUT/IUTIII/Theorem311/SourceFiniteMultiradial.lean`: `core`, `profile`, `profile_logVolume_formula`, `profile_ind1_invariant`, `profile_ind2_invariant`, `profile_ind3_upper`, `profile_possible_nonempty`；
  7. `LeanFormal/IUT/IUTIII/Theorem311/SourceMultiradialTwoActionEquivalence.lean`: `SourceTheorem311MultiradialPresentation`, `SourceTheorem311MultiradialAlgorithm`, `sourceMultiradialTwoActionEquivalence`；
  8. `LeanFormal/IUT/IUTIII/Theorem311/SourceHodgeTheaterBridge.lean`: `SourceHodgeTheaterSystem`, `link_q_naturality`, `link_scale_naturality`, `permutation_q_at`, `permutation_scale_at`；
  9. `LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteSourceColumnTrunkBridge.lean`: `sourceColumnCarrierIdentification`。
- 结论: ①——BPS→multiradial 的对象/算法/不变性/投影全部有编译资产，缺的只是把上述 9 项接成单一 consumer 的组约定理（真实证明目标，无新数学对象）；不属 ②/③。

### R2_descent — ① 可拼装（含 2 个待编译文件）

- 路径（src+olean 已核实）: `LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean`（`Ind1Setoid`, `ind1QuotientMap`, `generatedQuotientMap_eq_of_ind1Step`）、`Ind2Reduction.lean`（`Ind2AlienLink`, `linkMap_ind1Step`, `linkMap_ind2Step`）、`LeanFormal/IUT/IUTII/Kummer/K1K2BoundaryReduction.lean`（`nonarchimedeanImageInclusion`, `archimedeanTargetLift`，Ind3 边界）、`FiniteSourceColumnTrunkBridge.sourceColumnCarrierIdentification`、`SourceMultiradialTwoActionEquivalence.sourceMultiradialTwoActionEquivalence`。
- 待编译（src 存在、olean 缺失，非缺数学）: `LeanFormal/IUT/IUTIII/Theorem311/SourceProcessionStepXI.lean`、`SourceAdjacentColumnProcessionIsomorphism.lean` → 等 watchdog；不影响 ① 判定（无新对象）。
- 结论: ①——Ind1/2/3 下降组件与 0-column carrier 识别均可编译复用；缺四三角合成（R4 另计）。

### R3_literal_IQ — ② 需补缺失构造

- 已编译 near-assets（olean=true）: `tmp/sheaf/xif/paper/PaperIQCarrierActual.lean`（actualIQInterface）、`S2723GlobalIQHullActual.lean`（`globalIQUnitRegion_compact`/`globalIQHaar` 类）、`S3129IQHullLogVolumeSourceActual.lean`（IQ hull log-volume source）、`S1929LiteralIQCarrierActual.lean`（`LiteralCompletionIQCarrier`, `rootExtensionProductThetaImage_oneThetaLabel`）。
- 缺对象/定理（仓库无替代）: (a) literal carrier（受限乘积 + product Haar）上的**归一化 Haar 测度与 `literalHull` 紧性/有限性定理**；(b) literal carrier 与 `GlobalIQAmbient` 的 `MeasurableSpace`/`Set` 类型桥（hull 文件当前编译失败点）。
- 证据: `tmp/sheaf/xif/paper/A481LiteralIQCarrierActual.lean` 源已写出 literal carrier（`ι → ℚ_[p]`, `unitRegion`, `scale`）但 olean 未生成（首轮 FAIL: `def scale` 需 `noncomputable`；`mem_scaledUnitRegion_iff` 的 `Iff.rfl` 与 `Set.image` 成员顺序不符）；`Mzk1LiteralIQHullFinitenessActual.lean` FAIL: `failed to synthesize MeasurableSpace (GlobalIQAmbient C3 j)` 与 `sourceHullHaar` Set 类型不匹配；`GlobalIQHullInterfaceActual`/`GlobalIQHullThetaPilotActual` src 有、olean 无（PENDING）。
- 结论: ②——literal 载体刚写出（未编译），literal hull 有限性/归一化定理尚缺；**不是 ③**：F2 只排除 value-realized/model carrier，不排除 literal carrier。

### fixed_beta — ① 可直接复用（含 β=∞ 修正反例）

- 路径（src+olean 已核实）: `tmp/sheaf/xif/paper/Mzk1BetaAvoidingFoldActual.lean`: `betaAvoiding_all`（Problem A fold PROVED）；`Mzk1BetaAvoidingBaseActual.lean`: `BetaAvoidingBelyiBaseInputCorrected`, `betaAvoidingBelyiBaseInputCorrected_proved`, `restatedInductionConclusionFinite_proved`, `not_betaAvoidingBelyiBaseInput`, `not_mzk1Lemma24Target_infty`（原 β=∞ 版已被反例否定，finite-β 修正版已证）。
- 结论: ①——fixed-β 选择可直接由 corrected base + fold 归纳构造，无需新对象；β=∞ 旧版按 ③（已证不可行/反例）记录，不重开。

### scheme_side — ① 可拼装

- 路径（src+olean 已核实）: `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean`: `sectionMap_injective`, `sectionMap_surjective`；同目录 `SourceDefinition31D3D4Root/D4D9Supply/D5D8Root/LocalValuationSections/RootLemmas.lean`（Definition 3.1 scheme-side 组件）；`SourceInitialThetaData.lean`；`LeanFormal/IUT/IUTIII/Theorem311/SourceHodgeTheaterBridge.lean`: `SourceHodgeTheaterSystem`, `link_q_naturality`；`tmp/sheaf/l03-g2/S2Transport.lean`: `SchemeSideHasFiniteGroupQuotients`。
- 待编译: `tmp/sheaf/xif/paper/Mzk1SchemeSideMapsActual.lean` src 有、olean 无（PENDING）→ 组装 consumer 用它时需先编译；不改变 ① 判定。
- 结论: ①——scheme-side Section/sectionMap/有限群商与 Hodge theater 桥均有编译资产，缺 assembly consumer；无缺失数学。


## 详细证据（shehdd：R4/fiber_functor/qpilot/iut4_compare）

## R4_four_triangles — (HDD)∘(SHE) 第四三角（组件可拼装；缺组装定理）

**一行结论**: 组件齐全且全部 olean+PROVED，可沿“APT/IPL/SHE 方图 -> hull real volume -> QCMPComparisonSupply -> StepXIContract -> Cor312Conclusion”拼装；唯一缺口是从 SHE/HDD 到 comparison supply 的单一组装定理（不新造 value-model 结论，F2 边界仅记录）。

**拼装路径 (file:decl, 状态)**
1. LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean: SourceAPTStatement, SourceAPTSlotAssembly, sourceAPTTransportSupply (OK)
2. LeanFormal/IUT/IUTIII/Corollary312/StepXI/ConcreteFiniteRouteColumns.lean: finiteAPTData(+_bijective/_shift/_level/_comp/_inverse/_zero), finiteIPLSquare(+_commute/_volume_horizontal/_volume_vertical/_comp_horizontal), finiteSHESquare(+_commute) (OK)
3. LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean: iqHullRealVolume, iqHullRealVolume_nonneg, ofReal_le_toReal_of_ne_top (OK; 该文件另含 F2/unsat 边界记录，不作 rung 结论)
4. LeanFormal/IUT/IUTIII/Corollary312/StepXI/CardQCMPComparison.lean: QCMPComparisonSupply.toStepXIContract, _toStepXIContract_qSigned, _q_le_target, _target_le_theta, cor312Conclusion_of_toStepXIContract (OK)
5. LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean: StepXIContract, Cor312Conclusion (OK)
6. LeanFormal/IUT/IUTIII/Corollary312/Comparison.lean: cor312Conclusion_of_contract (OK)

**缺失对象**: ① SHE 方向（simultaneous holomorphic expressibility）与 (hull+det) 的合成到 QCMPComparisonSupply/StepXIContract 的组装箱；② HDD 三角与 APT/IPL 方图的交换（finiteIPLSquare/finiteSHESquare 已有方图，但缺与 hull real volume 的联合消费者定理）。
**obstruction**: 无新 obstruction；注意 CertificateHullWiring/CertificateHullWiringRealization 的 F2/unsat 记录只是边界说明，不得作为 rung 结论（lattice DAG-AUDIT A480 §5 规则）。

## fiber_functor — PreGalois/fiber functor（部分可拼装；5 字段 + slice-push 为真实缺口，BLOCKED）

**一行结论**: 已有 geometric fiber functor 与 remaining-fields 接口可拼装到“PreGaloisCategory 五字段待证”的边界；S1794 五字段与 S2432 slice-push naturality 是仓库内已登记的真实 sorry/缺 API 缺口，BLOCKED，不作为 rung。

**拼装路径 (file:decl, 状态)**
1. LeanFormal/IUT/Foundations/AlgebraicGeometry/FiniteEtaleCoverFiber.lean: geometricFiberFunctor, geometricFiberFunctor_map_id, geometricFiberFunctor_map_comp (OK)
2. LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean: geometricFiberFunctor; CurveEtaleFundamentalGroupExt.lean: puncturedEllipticOriginFiberFunctor (OK)
3. LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.lean: CurvePreGaloisCategoryRemainingFields (OK; 记录剩余字段)
4. tmp/sheaf/xif/paper/S1794FiberFunctorProductActual.lean: preservesTerminalObjectsField_holds (PROVED), preservesPullbacksField_holds / preservesFiniteCoproductsField_holds / preservesEpisField_holds / preservesQuotientsByFiniteGroupsField_holds / reflectsIsosField_holds (5 sorries, BLOCKED)
5. tmp/sheaf/xif/paper/S2432PrestackCloseActual.lean: test_slicePushNaturality (sorry at line 34, BLOCKED; 缺 Mathlib slice-push naturality / pseudofunctor pullback API)

**缺失对象**: ① 五字段的 categorical half（fiber functor 保持 pullbacks/finite coproducts/epis/quotients/reflects isos 的 cocone 比较）；② slice-push naturality API（Mathlib 无）。
**obstruction**: S1794（5 real sorries）与 S2432（1 real sorry，AUDIT-MANIFEST-2026-11-03.md:19 记录，dirty）均已登记 coord/DAG-BLOCKED.json（PRAGMATIC-DEAD-END，xif-sorry:*）→ fiber_functor 组标 BLOCKED，不派新 rung。

## qpilot — q-pilot/Theta-pilot（组件可拼装；缺双像+SHE 组装）

**一行结论**: finite-place Theta-pilot scaled region、IQ containment、finite hull 与 possible-image 分解均有 olean+PROVED，可拼装到“全局 theta-pilot 像 -> hull”边界；缺 global image/hull 组装与 SHE 箭头（GlobalIQHullThetaPilotActual 待编译）。

**拼装路径 (file:decl, 状态)**
1. LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceThetaPilotScaledRegion.lean: arithmeticTupleThetaPilotGenerator, arithmeticTupleThetaPilotRegion, arithmeticTupleThetaPilotExponent_nonneg, arithmeticTupleThetaPilotGenerator_mem_singleFractionalLattice, arithmeticTupleThetaPilotRegion_le_singleCoordinateFractional, arithmeticTupleThetaPilotExactRadius (OK)
2. LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean: SourceThetaPilotOnePlacePacket, sourceThetaPilotProductMap, sourceThetaPilotProductMap_tprod, sourceThetaPilotTensorIQPacket, sourceThetaPilotIQPacket, possibleImage_subset_sourceThetaPilotIQPacket, sourceThetaPilotProductMap_image_subset_tensorIQPacket (OK)
3. LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean: thetaPilotCarrierFintype, sourceThetaPilotFiniteHull (OK)
4. LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryGapCards.lean: possibleThetaPilotImageSet_eq_iUnion_singleton, possibleThetaPilotImageSet_eq_biUnion_finset, possibleThetaPilotImageSet_subset_iff_forall_mem (OK)
5. tmp/sheaf/xif/paper/S1929LiteralIQCarrierActual.lean: LiteralCompletionIQCarrier, rootExtensionProductThetaImage_oneThetaLabel, oneThetaLabel (OK)
6. tmp/sheaf/xif/paper/GlobalIQHullThetaPilotActual.lean: GlobalThetaPilotCarrier, globalThetaPilotImageSet, globalThetaPilotHull, globalThetaPilotImageSet_subset_hull, globalThetaPilotImageSet_nonempty, globalThetaPilotHull_nonempty (PENDING: src 存在、olean 缺失，已在 extra-targets)

**缺失对象**: ① GlobalIQHullThetaPilotActual 编译（等 watchdog）；② q-pilot/Θ-pilot 双像比较与 SHE 箭头（simultaneous holomorphic expressibility）的组装定理；③ q-pilot 与 literal IQ carrier 的产物 Haar 归一化连接（与 R3 literal 载体联动，由 abc/hull rung 提供）。
**obstruction**: 无登记 obstruction；注意不得用 value-realized hull 有限性替代 literal 载体结论（F2）。

## iut4_compare — IUT IV Section2/estimate comparison（比较组件可拼装；class-B named 输入）

**一行结论**: canonical rooted QC/HC 比较、undilated height/region 的 reduction 与 endgame 条件定理均 olean+PROVED，可拼装比较链；Section2 的 undilated 输入（UndilatedHeightBound/UndilatedRegionBound）为 class-B named，非 obstruction。

**拼装路径 (file:decl, 状态)**
1. tmp/sheaf/xif/paper/S3131CanonicalRootedQCActual.lean: S3131CanonicalRootedQC, S3131CanonicalRootedHC, S3131CanonicalRootedQC_le_HC (OK)
2. tmp/sheaf/xif/paper/S3131PaperRouteHeightReductionActual.lean: UndilatedHeightBound, heightComparisonFamily_of_undilated (OK; 修正 LADDER 名称: 不是 heightUndilated 而是 UndilatedHeightBound 定义)
3. tmp/sheaf/xif/paper/S3131PaperRouteRegionReductionActual.lean: UndilatedRegionBound, regionVolumeFamily_of_undilated (OK; 同上修正)
4. tmp/sheaf/xif/paper/S3131EndgameDependencyLedgerActual.lean: S3131EndgameConditionalTheorem, endgame_conditional (OK)
5. Iut/Foundations/GaloisImage.lean: imageComparison, imageComparison_inclusion, imageComparison_projection, imageComparisonPreimage(_spec), imageComparisonFlip (OK)

**缺失对象**: Section2 uniform comparison 的 class-B 输入（undilated height/region 界的证明本身；[IUTchIV] Thm 1.10 / Cor 2.2 的 paper 内容），以及 endgame 条件定理到 literal 载体比较形式的实例化。
**obstruction**: 无登记 obstruction；class-B named 输入按 LADDER/qpilot/stepxi 分工处理，不得以 value-model 结论替代。

## 合并备注

- shehdd 更正: LADDER 表 `heightUndilated`/`regionUndilated` 的实际声明名是 `UndilatedHeightBound`/`UndilatedRegionBound`（已按其分段采用）。
- fiber_functor 的 ③ 是“已登记 BLOCKED（PRAGMATIC-DEAD-END + Mathlib 缺 API）”，不是形式化反例；若后续 Mathlib 增加 slice-push/pseudofunctor pullback API，可重开。
- 下一可执行: (a) R3 优先让 abc 修 `A481LiteralIQCarrierActual` 两处编译错误、hull 补 `MeasurableSpace (GlobalIQAmbient)` 实例并修 `sourceHullHaar` 类型桥，watchdog 出 olean 后更新本表；(b) qpilot 等 `GlobalIQHullThetaPilotActual` 编译；(c) 各 ① 组按给出的拼装路径写真实 assembly consumer（写入 extra-targets，不碰 watchdog）。

## 拼装执行（A483 续，lattice 写真实 Lean + extra-targets）

| gap | 拼装文件 | 内容 | 状态 |
|---|---|---|---|
| R1_multiradial | `tmp/sheaf/xif/paper/Mzk1MultiradialOutputAssemblyActual.lean` | `multiradial_output_base_invariants`（Output.target=base / level=0 / logVolume=thetaLogVolume）、`multiradial_profile_ind_invariants`（Ind1/Ind2 不变 + Ind3 upper）、`multiradial_possible_image_invariants`（非空 + Ind1/Ind2 不变）；全部由 `SourceFiniteMultiradial` 已编译定理组装 | 已入 extra-targets，等 watchdog |
| fixed_beta | `tmp/sheaf/xif/paper/Mzk1FixedBetaAssemblyActual.lean` | `FixedBetaChoice` structure（corrected base + finite induction） + `fixedBetaChoice_nonempty` + `fixedBeta_corrected_base_and_pointwise` + `fixedBeta_old_false_corrected_true`；复用 `betaAvoidingBelyiBaseInputCorrected_proved` / `restatedInductionConclusionFinite_proved` / `not_betaAvoidingBelyiBaseInput` | 已入 extra-targets，等 watchdog |
| （旁证修正） | `tmp/sheaf/xif/paper/Mzk1AbsTriangleActual.lean` | 该 Mathlib 版本无 `∑ x in s` binder，已改为 `∑ x ∈ s`（`Finset.abs_sum_le_sum_abs s f`），LOG/ABS 修复；`Mzk1LogVolumeRealActual` 已 EXIT=0 | 已重新入队 |

说明: R2/scheme_side 的组件本身已编译（见汇总表）；`SourceDefinition31Boundary.section_map_bijective` 已提供 scheme-side 双射，暂不重复写 consumer；R2 是否再加 Ind1/Ind2 组合 consumer 依 watchdog 日志与 mainline 需求再定。


| R2_descent | `tmp/sheaf/xif/paper/Mzk1DescentAssemblyActual.lean` | `descent_ind1_quotient_package`（ind1 作用被形式商吸收 + descended lift 在代表元上算 quotientMap）、`descent_ind1_functorial_package`（Ind1 商函子性）；组合 `Ind1Reduction` 已编译定理 | 已入 extra-targets，等 watchdog |
| scheme_side | `tmp/sheaf/xif/paper/Mzk1SchemeSideAssemblyActual.lean` | `sourceDefinition31_scheme_side_assembly`（sectionMap 双射 + finite/infinite place data + cusp ε>0）、`sourceSectionClause_package`（左右逆 + ε≠0）；组合 `SourceDefinition31Boundary` 已编译定理 | 已入 extra-targets，等 watchdog |

已编译结果（首轮）: `Mzk1MultiradialOutputAssemblyActual` EXIT=0（57s）、`Mzk1FixedBetaAssemblyActual` EXIT=0（92s）；`Mzk1LogVolumeRealActual` EXIT=0、`Mzk1ThetaHullTransportConsumerActual` EXIT=0；`Mzk1AbsTriangleActual` 已按 ∈ 记号修复重入队。


## A484 状态更新（literal / R3 / R4）

- R3 literal 载体: `Mzk1LiteralIQCarrierActual` EXIT=0、`GlobalIQHullInterfaceActual` EXIT=0、`Mzk1LiteralIQHullFinitenessActual` EXIT=0、`Mzk1LiteralIQThirdTriangleActual` 有 olean → literal hull 有限性核心已落地；R3 由 ② 转「②→① 进行中」。
- 待修链: `A483LiteralCarrierProductHaarActual` 源语法/实例错误（invalid explicit universe params / invalid arg name `l` / invalid parametric local instance），导致 `A482LiteralCarrierAxiomsActual` → `A482LiteralIQHullInterfaceActual` 依赖缺失；修好后按 extras_add 重编。
- R4: `Mzk1FourTriangleSynthesisActual` 的唯一缺失依赖 `Mzk1LiteralIQCarrierActual.olean` 已 EXIT=0，四三角组装可重编（文件已在队列）。
- 新规: 以后只经 `tools/extras_add.mjs` 加入关键路径文件；非关键 consumer/assembly（含 lattice 先前写的）保留磁盘但不入队。

