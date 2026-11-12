# AUDIT-02-XIF-S1-1000 — tmp/sheaf/xif/paper S1–S1000 全量审计 (审计 02-xif)

| field | value |
|---|---|
| 快照时间 | **2026-11-13 02:30 Asia/Shanghai** |
| 范围 | `tmp/sheaf/xif/paper/` 下文件名 `S<num>*`，num ∈ [1,1000]；按 num 分组，每组取 **LastWriteTime 最新** 的文件 |
| 方法 | **只读**：枚举 + 文件大小 + olean 存在性 (` .lake/build/lib/lean/<mod>.olean`) + 正文首 2 条声明行 + 文本扫描 `sorry`/`axiom`；**未编译、未改仓内文件** |
| 判定口径 | `PROVED`=olean 存在且文本无 sorry/axiom；`GAP`=文本含 sorry/axiom；`AUDIT`=文件名含 Audit/Probe/Status/Check/Inventory/Rows；`INVALID`=无 olean 且非 audit/gap；`STATEMENT`=无可识别声明 |
| 重要 caveat | olean 存在 ≠ 当前源码已 kernel 验证（可能是旧 olean）；判定为**启发式登记**，非编译验证。不确定性以 `UNKNOWN`/注释标注 |

## 统计摘要

```
组数（S 编号）= 578；命中的 .lean 文件总数 = 755
PROVED = 424；GAP = 35；AUDIT = 54；INVALID = 63；STATEMENT = 2
无 olean（red）= 67
```

## 组清单（每组最新文件）

| S# | 组内文件数 | 最新文件 | size | olean | 声明1 | 声明2 | 判定 |
|---|---|---|---|---|---|---|---|
| S2 | 1 | `S2lNormalizationActual.lean` | 1807 | False | `noncomputable def paperThetaValueFromQParameter` | `theorem paperThetaValueFromQParameter_pos` | **INVALID** |
| S12 | 1 | `S12CompletionGeometryBridgeActual.lean` | 4731 | True | `noncomputable def fixedToDependent [Fintype V]` | `def commonPrimeIndex (D : DependentCompletionValuedGeometry K) (p : Nat) : Type :=` | **PROVED** |
| S21 | 6 | `S21fSourceTheaterFieldComparisonActual.lean` | 3816 | True | `abbrev fieldI : OriginalInput l (NativePlaces X.S) :=` | `theorem fieldI_fmod_eq :` | **GAP** |
| S22 | 1 | `S22DependentProductActual.lean` | 12598 | True | `abbrev DependentCompletion (b : Bad (nativePlaceSelection T)) : Type :=` | `abbrev DependentCompletionProduct : Type :=` | **PROVED** |
| S40 | 1 | `S40SourceTheaterFieldMapDirectActual.lean` | 4941 | True | `noncomputable def sourceFieldMap :` | `noncomputable def sourcePlaceMap` | **GAP** |
| S44 | 1 | `S44ThetaMuSymbolAuditActual.lean` | 3430 | True | `abbrev ThetaPilotObjectCarrier : Type := ThetaPilotCarrier l` | `abbrev ThetaPacketValueCarrier : Type := FiniteThetaPacket l` | **AUDIT** |
| S51 | 1 | `S51DecorationWrapperActual.lean` | 3459 | True | `inductive Decoration where` | `structure DecoratedDPrimeStrip (δ : Decoration) (V : Type u) where` | **GAP** |
| S54 | 1 | `S54DecorationAssignmentActual.lean` | 3657 | True | `inductive SourceConsumer where` | `def consumerDecoration : SourceConsumer → Decoration` | **GAP** |
| S56 | 1 | `S56OTriangularCarrierActual.lean` | 3161 | True | `noncomputable def oTriangularMonoid :` | `abbrev oTimesUnits : Type u := (CompletionIntegers place.val)ˣ` | **GAP** |
| S60 | 1 | `S60OTriangleBoundaryActual.lean` | 3251 | True | `noncomputable def oBoundaryMonoid :` | `def oBoundaryToTriangular :` | **GAP** |
| S63 | 1 | `S63OBoundaryLogShellActual.lean` | 3434 | True | `theorem sourceLogShellUnits_eq_integralUnits :` | `noncomputable def sourceOBoundaryMonoid :` | **GAP** |
| S64 | 1 | `S64DependentThetaHullActual.lean` | 10342 | True | `noncomputable def dependentThetaHull :` | `noncomputable def dependentThetaHullProductHaar` | **PROVED** |
| S68 | 5 | `S68Probe2Adapted.lean` | 467 | False | `` | `` | **AUDIT** |
| S77 | 1 | `S77CompletionIntegersEquivActual.lean` | 2479 | True | `def completionIntegersCarrierEq : Prop :=` | `noncomputable def completionIntegersRingEquivOfCarrierEq` | **GAP** |
| S79 | 1 | `S79IntegralRingEquivActual.lean` | 2405 | True | `theorem completionIntegersCarrierEq_holds :` | `noncomputable def completionIntegersEquivIntegers :` | **GAP** |
| S82 | 3 | `S82ProbeAdapted.lean` | 161 | False | `` | `` | **AUDIT** |
| S87 | 1 | `S87OBoundaryDecompositionActual.lean` | 5156 | True | `noncomputable def dvrUniformizer : Integers (CommonPrimeCompletion place) := by` | `theorem dvrUniformizer_irreducible :` | **GAP** |
| S92 | 1 | `S92NormRatioUnifiedActual.lean` | 4561 | True | `theorem qVFamNormRatio_eq_normalized_div_default` | `theorem qVFamDefaultNorm_pos (b : Bad (nativePlaceSelection T)) :` | **PROVED** |
| S93 | 1 | `S93BoundaryLogCompatibilityActual.lean` | 4072 | True | `theorem boundaryLogWith_unit` | `structure UniformizerChangeData` | **GAP** |
| S100 | 1 | `S100QVFamNormInstanceGapActual.lean` | 4867 | True | `theorem qVFamNormInstanceGap_iff_paperCoefficient_eq_cNorm` | `theorem qVFamNormRatio_ne_one_of_coefficient_ne` | **PROVED** |
| S101 | 1 | `S101UniformizerChangeActual.lean` | 5237 | True | `structure OBoundaryUnitDecompFor` | `noncomputable def boundaryUnitDecompositionFor` | **GAP** |
| S104 | 1 | `S104CanonicalLogPiActual.lean` | 2743 | True | `theorem boundaryLogWithFor_logPi_difference` | `def candidateLog1pPi : CommonPrimeCompletion place :=` | **GAP** |
| S109 | 1 | `S109QVFamNormValueActual.lean` | 5672 | True | `theorem qVFamDefaultNorm_eq_residueNormBase_zpow` | `theorem qVFamNormalizedNorm_eq_p_zpow_neg_coefficient` | **PROVED** |
| S111 | 1 | `S111FormalBoundaryLogActual.lean` | 9838 | True | `theorem boundaryUnitDecomposition_unique` | `noncomputable def boundaryLogFormal` | **GAP** |
| S118 | 1 | `S118QVFamNormRatioValueActual.lean` | 4584 | True | `theorem qVFamTensorPlace_residueNormBase_eq_lower_pow` | `theorem qVFamNormRatio_eq_p_div_rationalBase` | **PROVED** |
| S120 | 1 | `S120QVFamWeightedValuationConditionActual.lean` | 5704 | True | `theorem qVFamNormalizedCoefficient_eq_neg_logb_norm` | `theorem weightedValuationCondition_iff_coefficient_eq_exponent_mul_degree` | **PROVED** |
| S121 | 1 | `S121QVFamSpectralValuationActual.lean` | 6452 | True | `theorem qVFamNormalizedCoefficient_eq_exponent_mul_degree_sub_logRatio` | `theorem qVFamNormalizedCoefficient_eq_exponent_mul_degree_iff` | **PROVED** |
| S126 | 1 | `S126FormalBoundaryLogUseActual.lean` | 3685 | True | `noncomputable def logShellLogFormal` | `theorem boundaryLogFormal_agrees_logShellLog` | **GAP** |
| S132 | 1 | `S132FormalLogVolumeActual.lean` | 5239 | True | `noncomputable def boundaryLogNormalized` | `noncomputable def boundaryLogInteger` | **GAP** |
| S134 | 1 | `S134ActualPaperTargetCorrectionActual.lean` | 7659 | True | `theorem log_normRatio_eq_spectralGap` | `theorem normRatioCorrectionSum_eq_spectralGapSum` | **PROVED** |
| S137 | 1 | `S137PaperTargetCorrectionStatusActual.lean` | 7390 | True | `def IntermediateActualPaperTargetUpToNormRatioCorrection : Prop :=` | `theorem intermediateTarget_iff_paperComparison :` | **AUDIT** |
| S142 | 1 | `S142NormalizedBoundaryLogVolumeActual.lean` | 5602 | True | `noncomputable def boundaryLogVolumeNormalized` | `noncomputable def sourceLogShellLog` | **GAP** |
| S143 | 1 | `S143dQuotientLogVolumeActual.lean` | 3576 | True | `noncomputable def unitLogRange :` | `theorem unitLog_mem_range` | **GAP** |
| S145 | 1 | `S145NormRatioCorrectionZeroActual.lean` | 7378 | True | `noncomputable def normRatioSpectralGap` | `theorem normRatioCorrectionSum_eq_weighted_spectralGap` | **PROVED** |
| S148 | 1 | `S148QuotientLogVolumeSourceActual.lean` | 5294 | True | `theorem boundaryLogFormalFor_dvr_eq` | `noncomputable def sourceLogShellNormalizedQuot` | **GAP** |
| S150 | 1 | `S150SourceLogVolumeNormalizationActual.lean` | 5373 | True | `noncomputable def sourceLogVolumeScale :` | `noncomputable def sourceLogShellNormalizedMap` | **GAP** |
| S151 | 2 | `S151PaperNormalizationChoiceActualAdapted.lean` | 7526 | False | `theorem paperNormalizedCoefficient_eq_order_mul_rationalDegree` | `theorem paperNormalizedCoefficient_eq_exponent_mul_rationalDegree` | **INVALID** |
| S154 | 1 | `S154PaperNormalizedQUnitActual.lean` | 4389 | True | `noncomputable def qVFamNormalizedQPilotLog : Real :=` | `theorem perBQPilotLog_eq_neg_cNorm_mul_logp` | **PROVED** |
| S155 | 2 | `S155FrozenTargetStatusActualAdapted.lean` | 5922 | False | `noncomputable def classicalPaperQPilotMagnitude : Real :=` | `theorem classicalPaperQPilotMagnitude_eq :` | **AUDIT** |
| S156 | 1 | `S156QPilotSideObjectActual.lean` | 5332 | True | `noncomputable def QPilotQParameter` | `noncomputable def QPilotImagePoint : DependentCompletionProduct T :=` | **PROVED** |
| S157 | 1 | `S157ThetaRootCorrectionActual.lean` | 2092 | True | `noncomputable def paperRootThetaPower` | `theorem paperRootThetaPower_pow_twoL` | **GAP** |
| S172 | 1 | `S172QPilotMultiradialImageActual.lean` | 7902 | True | `abbrev QPilotMultiradialFiber` | `abbrev QPilotMultiradialCarrier : Type :=` | **PROVED** |
| S176 | 2 | `S176QPilotObjectImageActualAdapted.lean` | 6410 | False | `noncomputable def qPilotMultiradialActualHaarFamily :` | `noncomputable def qPilotMultiradialAmbientHaarActual :` | **INVALID** |
| S178 | 1 | `S178QPilotObjectFullActual.lean` | 4405 | True | `noncomputable def qPilotImageHaarFamily :` | `noncomputable def qPilotImageObject :` | **PROVED** |
| S185 | 1 | `S185HaarRootThetaActual.lean` | 5415 | True | `noncomputable def completionAddHaar :` | `noncomputable def nonunitHaarMeasure :` | **GAP** |
| S186 | 1 | `S186QPilotIndBaseChangeActual.lean` | 4557 | True | `abbrev QPilotMultiradialSourceQTensorCarrier : Type :=` | `noncomputable def QPilotMultiradialToSourceQTensor :` | **PROVED** |
| S191 | 1 | `S191QPilotCarrierTransportActual.lean` | 6165 | True | `abbrev s191TensorFamily (b : Bad (nativePlaceSelection T)) : PUnit.{1} → Type :=` | `noncomputable def s191BlockEquiv (b : Bad (nativePlaceSelection T)) :` | **PROVED** |
| S194 | 1 | `S194RootThetaNormActual.lean` | 3802 | True | `noncomputable def rootThetaNorm` | `theorem rootThetaNorm_pos` | **GAP** |
| S201 | 1 | `S201RootThetaNormLActual.lean` | 4273 | True | `noncomputable def rootNormedElementNorm : Real :=` | `theorem rootNormedElementNorm_pow_twoL :` | **GAP** |
| S214 | 3 | `S214ProbeAdapted.lean` | 173 | False | `` | `` | **AUDIT** |
| S227 | 3 | `S227ProbeAdapted.lean` | 145 | False | `` | `` | **AUDIT** |
| S232 | 1 | `S232QPilotHaarTransportActual.lean` | 5132 | True | `theorem QPilotImagePoint_eq_dependentQVFamProductPoint :` | `theorem s156ProductToBlock_QPilotImagePoint :` | **PROVED** |
| S234 | 1 | `S234QPilotHaarNormalizationActual.lean` | 2753 | True | `noncomputable def haarNormalizationFactor : ℝ≥0 :=` | `theorem haarNormalizationFactor_spec : μ' = (haarNormalizationFactor μ' μ) • μ :=` | **PROVED** |
| S237 | 1 | `S237SourceHullProperActual.lean` | 4084 | True | `theorem sourceQTensorLambdaOHull_compact :` | `noncomputable def sourceQTensorHullHaar : Measure (SourceQTensorBlock T b) :=` | **PROVED** |
| S238 | 1 | `S238ProductTensorHullHaarActual.lean` | 3652 | True | `noncomputable def productBlockHaar :` | `noncomputable def productRootNormedHaar :` | **PROVED** |
| S239 | 1 | `S239ProductHaarScalarActual.lean` | 1701 | True | `structure ProductHaarScalarGap where` | `def ProductHaarScalarGapRequired : Prop :=` | **PROVED** |
| S241 | 1 | `S241SourceHullNoncompactActual.lean` | 2248 | True | `theorem sourceQTensorBlock_noncompactSpace :` | `theorem sourceQTensorLambdaOHull_ne_univ_unconditional :` | **PROVED** |
| S245 | 1 | `S245SourceHullMeasureActual.lean` | 6237 | True | `theorem sourceQTensorLambdaOHull_eq_unit_smul :` | `theorem sourceQTensorLambdaOHull_isOpen :` | **PROVED** |
| S247 | 1 | `S247QPilotHaarInstancesActual.lean` | 3758 | True | `` | `` | **PROVED** |
| S255 | 6 | `S255ProbeAdapted.lean` | 236 | False | `` | `` | **AUDIT** |
| S264 | 3 | `S264ProbeAdapted.lean` | 108 | False | `` | `` | **AUDIT** |
| S273 | 1 | `S273QPilotTransportedHaarActual.lean` | 6411 | False | `noncomputable def s191BlockCLE (b : Bad (nativePlaceSelection T)) :` | `noncomputable def s191ProductContinuousAddEquiv :` | **INVALID** |
| S275 | 1 | `S275HaarFactorIsometryActual.lean` | 2089 | True | `structure BlockRootHaarFactorComparison (lam : (rootNormedExtension T b)ˣ) where` | `def BlockRootHaarFactorComparisonRequired` | **GAP** |
| S278 | 1 | `S278HaarFactorConjugacyActual.lean` | 3542 | True | `theorem image_blockScaling_unitBall` | `structure BlockRootHaarFactorEqualityGap` | **GAP** |
| S280 | 1 | `S280QPilotBlockCLEActual.lean` | 3019 | True | `noncomputable def s191BlockCLE (b : Bad (nativePlaceSelection T)) :` | `` | **PROVED** |
| S281 | 2 | `S281QPilotTransportedHaarActualAdapted.lean` | 5991 | False | `noncomputable def s191ProductContinuousAddEquiv :` | `noncomputable def qPilotHaarNormalizationFactorConcrete : ℝ≥0 :=` | **INVALID** |
| S284 | 1 | `S284RootUniformizerFactorActual.lean` | 3466 | True | `theorem rootHaarFactor_uniformizer_eq_norm_pow :` | `` | **PROVED** |
| S285 | 2 | `S285QPilotProductCAEActualAdapted.lean` | 3060 | False | `noncomputable def s191ProductContinuousAddEquiv :` | `` | **INVALID** |
| S288 | 1 | `S288ThetaScalingHaarFactorActual.lean` | 5220 | True | `theorem rootNormedUnitBall_eq_rootExtensionUnitBall :` | `theorem blockHaar_map_eq_rootNormedHaar :` | **GAP** |
| S289 | 1 | `S289SourceHullConcreteHaarActual.lean` | 4149 | True | `noncomputable def concreteSourceQTensorHullMuLog : ENNReal :=` | `theorem concreteSourceQTensorHullMuLog_eq_ofReal_log :` | **PROVED** |
| S290 | 1 | `S290BlockHaarFactorActual.lean` | 2838 | True | `theorem thetaScalingHaarFactor_uniformizer_eq_norm_pow :` | `theorem thetaScalingHaarFactor_prime_eq_norm_pow :` | **GAP** |
| S294 | 1 | `S294SourceHullNormalizedLogActual.lean` | 8422 | True | `noncomputable def sourceQTensorUnitReferenceMass : ENNReal :=` | `noncomputable def sourceQTensorHullMass : ENNReal :=` | **PROVED** |
| S295 | 5 | `S295Probe2Adapted.lean` | 94 | False | `` | `` | **AUDIT** |
| S296 | 1 | `S296BlockScaledHullLogActual.lean` | 7105 | True | `theorem blockScaledRegion_eq_scaling_image` | `theorem blockScaledRegionMeasure_eq_thetaScalingHaarFactor` | **PROVED** |
| S297 | 2 | `S297QPilotProductHaarActualAdapted.lean` | 4134 | False | `theorem s191FiberType_eq (b : Bad (nativePlaceSelection T)) :` | `noncomputable def s191DepCastCLE (b : Bad (nativePlaceSelection T)) :` | **INVALID** |
| S300 | 1 | `S300GeneralFactorNormActual.lean` | 3666 | True | `theorem exists_unit_uniformizer_zpow` | `structure RootHaarFactorNormPowGap where` | **GAP** |
| S301 | 1 | `S301GlobalThetaHullLogActual.lean` | 6340 | True | `noncomputable def globalSourceHullNormalizedLog : Real :=` | `theorem globalSourceHullNormalizedLog_eq :` | **PROVED** |
| S302 | 1 | `S302ComparisonReadySourcePairActual.lean` | 6219 | True | `noncomputable def thetaSideOfPair : GlobalSourceThetaHullLogObject T :=` | `noncomputable def qPilotSideOfPair : QPilotHaarTransportActual T :=` | **PROVED** |
| S304 | 7 | `S304Probe2Adapted.lean` | 126 | False | `` | `` | **AUDIT** |
| S305 | 1 | `S305SingleLambdaNormActual.lean` | 2422 | True | `theorem rootNormedElementNorm_pow_twoL_eq_qVFamNormalizedNorm :` | `theorem singleLambda_norm_eq_rootNorm_pow :` | **PROVED** |
| S307 | 1 | `S307QPilotThetaCarrierActual.lean` | 3180 | True | `noncomputable def qPilotBlockPoint : qVFamTensorBlock T b :=` | `noncomputable def qPilotRootLImagePoint : RootLValuedCarrier T b :=` | **PROVED** |
| S308 | 1 | `S308SameCarrierPairActual.lean` | 5757 | True | `abbrev RootLProductCarrier : Type :=` | `noncomputable def qPilotToRootLCarrier :` | **PROVED** |
| S309 | 1 | `S309RootTensorSameCarrierAuditActual.lean` | 7765 | True | `abbrev ThetaRootTensorProductCarrier : Type :=` | `noncomputable def thetaRootTensorProductHull :` | **AUDIT** |
| S310 | 1 | `S310CompletionSameCarrierPairActual.lean` | 6046 | True | `abbrev CompletionRootDataFamily : Type :=` | `def CompletionRootSystemExistenceGap : Prop :=` | **PROVED** |
| S311 | 1 | `S311RootLValuedK0CarrierActual.lean` | 2516 | False | `abbrev RootLValuedCarrierK0 : Type :=` | `noncomputable def carrierK0EquivRootL :` | **INVALID** |
| S312 | 1 | `S312QPilotRootTensorBaseChangeActual.lean` | 4107 | True | `noncomputable def qVFamBlockLinearEquiv :` | `noncomputable def qPilotBlockToRootTensor :` | **PROVED** |
| S313 | 1 | `S313CompletionThetaSideObjectActual.lean` | 5347 | True | `abbrev CompletionThetaCarrier : Type := qVFamTensorBlock T b` | `noncomputable def completionThetaRoot` | **PROVED** |
| S317 | 1 | `S317QPilotThetaSameCompletionBlockActual.lean` | 3732 | True | `noncomputable def qPilotCompletionImagePoint : qVFamTensorBlock T b :=` | `noncomputable def coefficientSurrogateCoefficient : qVFamTensorV → Real :=` | **PROVED** |
| S319 | 1 | `S319CompletionRootFromTorsion23Actual.lean` | 3740 | True | `theorem sourceTorsion23Rational :` | `def completionQVUnit :` | **PROVED** |
| S325 | 1 | `S325CompletionThetaMuOrbitActual.lean` | 4590 | True | `abbrev CompletionPlace : Type := Completion ((nativeBadLift T).lift b)` | `noncomputable def muCompletionFactor` | **PROVED** |
| S327 | 1 | `S327C3IndActionsActual.lean` | 4330 | True | `structure C3IndTransport where` | `noncomputable def ind1Action (S : C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))` | **PROVED** |
| S328 | 1 | `S328C3LiteralLambdaOHullActual.lean` | 6124 | True | `theorem literalScaledRegion_subset_hull (lam : HullBlock C3) :` | `theorem literalScaledHull_eq_scaledRegion` | **PROVED** |
| S330 | 1 | `S330QVFamilyRootCardActual.lean` | 4727 | True | `abbrev qVFamilyPlace : NumberField.FinitePlace T.arithmetic.F :=` | `abbrev QVFamilyTwoLRootCard : Type :=` | **PROVED** |
| S342 | 1 | `S342QVFamilyRootImpossibleActual.lean` | 3913 | True | `noncomputable def qVFamilyTateWitness :` | `theorem qVFamily_order_coprime :` | **PROVED** |
| S343 | 1 | `S343CompletionThetaC3TensorActual.lean` | 4927 | True | `abbrev C3Block (T : SourceNativeInitialThetaData.{0} l)` | `noncomputable def c3ThetaTensorImagePoint` | **PROVED** |
| S346 | 1 | `S346OrbifoldStructuralSheafActual.lean` | 3603 | True | `structure OrbifoldStructuralSheafCarrierSpec` | `def OrbifoldStructuralSheafRootSectionRequired : Prop :=` | **PROVED** |
| S348 | 2 | `S348OrbifoldMu2lInterfaceActual.lean` | 3461 | True | `structure OrbifoldMu2lInterface` | `noncomputable def mu2lAction` | **PROVED** |
| S349 | 1 | `S349C3TensorLatticeRegionActual.lean` | 6173 | True | `noncomputable def actualC3LogShellTensorLattice :` | `noncomputable def actualC3LogShellTensorLatticeRegion :` | **PROVED** |
| S353 | 1 | `S353C3LatticeScaledHullActual.lean` | 8909 | True | `noncomputable def literalScaledRegion (a : ℚ_[C3.p]) :` | `noncomputable def literalCandidateHulls` | **PROVED** |
| S355 | 1 | `S355OrbifoldRootStackCandidateActual.lean` | 5702 | True | `abbrev K (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=` | `abbrev AC (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=` | **PROVED** |
| S356 | 1 | `S356RootStackActionGroupoidActual.lean` | 3380 | True | `abbrev RootObj : Type := CandidateRoots T b` | `noncomputable def rootObj : RootObj T b := candidateRootSubtype T b` | **PROVED** |
| S357 | 1 | `S357OtrianglerightStructuralSheafActual.lean` | 3149 | True | `structure OtrianglerightOnSplitFrobenioid` | `def OtrianglerightStructuralSheafRequired` | **PROVED** |
| S366 | 2 | `S366OneColumnActualAdapted.lean` | 2103 | False | `noncomputable def oneColumnLocalField : NativePlaces P.X.S -> Type :=` | `noncomputable def oneColumnLocalRing : NativePlaces P.X.S -> Type :=` | **INVALID** |
| S369 | 1 | `S369OtriSplitFrobenioidActual.lean` | 4415 | True | `abbrev nativeStagePlace : NumberField.FinitePlace T.arithmetic.F :=` | `noncomputable def nativeStageFrobenioidPresentation :` | **PROVED** |
| S370 | 1 | `S370ThetaSectionLogVolumeInterfaceActual.lean` | 2592 | True | `structure ThetaSectionLogVolumeInterface` | `noncomputable def thetaSectionLogVolumePlaceholder` | **PROVED** |
| S371 | 1 | `S371C3ScaledHullScalingClosedActual.lean` | 3284 | True | `theorem literalScaledRegion_scalingClosed` | `theorem literalHull_scalingClosed` | **PROVED** |
| S372 | 1 | `S372APacketC3TransportGapActual.lean` | 2793 | True | `structure APacketC3SpecialCaseTransport where` | `def APacketC3SpecialCaseTransportRequired : Prop :=` | **PROVED** |
| S373 | 1 | `S373NativeStageSplittingActual.lean` | 5091 | True | `abbrev stagePresentation : Iut.FrobenioidPresentation :=` | `abbrev stageTransport :` | **PROVED** |
| S376 | 1 | `S376StageTauConstructionActual.lean` | 2238 | True | `noncomputable def stageTauDataOfSplitting` | `def NativeStageCharacteristicSplittingMissing` | **PROVED** |
| S379 | 1 | `S379NativeStageTauExactMissingActual.lean` | 3230 | True | `abbrev StagePresentation : Iut.FrobenioidPresentation :=` | `abbrev StageTransport :` | **PROVED** |
| S384 | 1 | `S384C3LatticeHullNormalizedLogActual.lean` | 7835 | True | `noncomputable def c3LatticeUnitMass : ENNReal :=` | `noncomputable def c3LatticeHullMass (a : ℚ_[C3.p]) : ENNReal :=` | **PROVED** |
| S389 | 1 | `S389SingleStageSplitActual.lean` | 1510 | True | `abbrev SingleStageBase : Type u :=` | `theorem singleStageBase_single_object :` | **PROVED** |
| S392 | 1 | `S392RootStackSectionMonoidActual.lean` | 3353 | True | `abbrev SectionCarrier : Type := RootObj T b → Multiplicative ℤ` | `noncomputable def rootDelta (r : RootObj T b) : SectionCarrier T b := by` | **PROVED** |
| S397 | 1 | `S397SingleStageTauCharacteristicActual.lean` | 5787 | True | `abbrev StageUnitMonoid : Type u := U × Multiplicative ℤ` | `abbrev StageOneObjectD : Type :=` | **PROVED** |
| S402 | 1 | `S402EquivariantSectionCarrierActual.lean` | 4773 | True | `noncomputable def equivariantSections : Submonoid (SectionCarrier T b) where` | `abbrev EquivariantSectionCarrier : Type :=` | **PROVED** |
| S405 | 1 | `S405OrbicurveCoverCategoryActual.lean` | 1803 | True | `noncomputable def idMap (A : OrbicurveFiniteEtaleCover X) :` | `structure OrbicurveCoverCategoryGap where` | **PROVED** |
| S407 | 1 | `S407OrbicurveStructuralSheafMissingActual.lean` | 2270 | True | `structure OrbicurveStructuralSheafCarrierSpec where` | `def OrbicurveStructuralSheafCarrierRequired : Prop :=` | **PROVED** |
| S409 | 1 | `S409Example32FrobenioidActual.lean` | 2892 | True | `abbrev Example32AlgebraBase : Type (u + 1) :=` | `abbrev Example32Base : Type (u + 1) :=` | **PROVED** |
| S412 | 1 | `S412DvTriangleTauActual.lean` | 5566 | True | `structure DvCoverNormalizedValuationData (K : Type u) [Field K]` | `noncomputable def dvPi : Lˣ :=` | **PROVED** |
| S421 | 1 | `S421ConstantNatDivisorialMonoidActual.lean` | 2266 | True | `noncomputable def constantNatDivisorialMonoidOn` | `abbrev DvBase (K : Type u) [Field K] : Type (u + 1) :=` | **PROVED** |
| S423 | 1 | `S423NatDivisorialAddMonoidActual.lean` | 2245 | True | `noncomputable def natDivisorialAddMonoid : Iut.DivisorialAddMonoid where` | `` | **PROVED** |
| S424 | 2 | `S424QVFamilyPaperQAuditActualAdapted.lean` | 2643 | False | `theorem qVFamily_repo_place_base :` | `theorem qVFamily_repo_order_coprime :` | **AUDIT** |
| S432 | 1 | `S432SmallModelActual.lean` | 3092 | True | `abbrev Example32Base : Type (u + 1) :=` | `abbrev Example32SmallBase : Type (u + 1) :=` | **PROVED** |
| S433 | 1 | `S433Example32RationalDivisorActual.lean` | 3921 | True | `abbrev example32RationalFunctions : Type u := L.obj.objˣ` | `def example32DivisorCoefficient (x : example32RationalFunctions L) : ℤ :=` | **PROVED** |
| S436 | 1 | `S436KSideQVActual.lean` | 2619 | True | `abbrev kSidePlace : NumberField.FinitePlace T.arithmetic.K :=` | `abbrev kSideCurve : PuncturedEllipticCurve T.arithmetic.K :=` | **PROVED** |
| S438 | 1 | `S438QVFamilyKSideCandidateActual.lean` | 4384 | True | `noncomputable def qVFamilyKLift (b : Bad (nativePlaceSelection T)) :` | `theorem qVFamilyKLift_comap :` | **PROVED** |
| S442 | 1 | `S442DvCoverNormPullbackActual.lean` | 3575 | True | `noncomputable def normPullback (f : L →ₐ[K] L') : L'ˣ →* Lˣ :=` | `theorem normPullback_apply (f : L →ₐ[K] L') (x : L'ˣ) :` | **PROVED** |
| S445 | 1 | `S445Example32SmallInputActual.lean` | 2774 | True | `structure Example32SmallInputData where` | `noncomputable def example32SmallInputOfData` | **PROVED** |
| S446 | 1 | `S446Example32DivisorNaturalityActual.lean` | 5269 | True | `def divisorCoefficientOfValuation (x : Lˣ) : ℤ :=` | `theorem example32DivisorCoefficient_normPullback` | **PROVED** |
| S448 | 1 | `S448Example32SmallInputActual.lean` | 2121 | True | `abbrev Example32SmallRationalObject (X : Example32SmallBase K) : Type u :=` | `structure Example32SmallNormBridge where` | **PROVED** |
| S449 | 1 | `S449NormPullbackGroupActual.lean` | 958 | True | `structure NormPullbackGroupLaws (K : Type u) [Field K]` | `def NormPullbackGroupLawsRequired : Prop :=` | **PROVED** |
| S451 | 1 | `S451GroupLikePullbackAuditActual.lean` | 1995 | True | `theorem unitsMap_injective {M N : Type u} [Monoid M] [Monoid N]` | `structure InclusionPullbackBijectiveData` | **AUDIT** |
| S453 | 1 | `S453DvTriangleMorphismAlgHomActual.lean` | 1978 | True | `noncomputable def arrowAlgebraMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :` | `theorem arrowAlgebraMap_id (X : Example32SmallBase K) :` | **PROVED** |
| S456 | 1 | `S456RationalInclusionActual.lean` | 1536 | True | `noncomputable def arrowAlgebraMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :` | `noncomputable def unitInclusionPullback {X Y : Example32SmallBase K} (f : X ⟶ Y) :` | **PROVED** |
| S457 | 1 | `S457DivisorMapActual.lean` | 1952 | True | `noncomputable def valuationExponentHom :` | `noncomputable def divisorMap :` | **PROVED** |
| S459 | 1 | `S459KrootCandidateActual.lean` | 3962 | True | `abbrev Kq : Type := Completion (qVFamilyKLift T b)` | `abbrev ACq : Type := AlgebraicClosure (Kq T b)` | **PROVED** |
| S460 | 1 | `S460RationalFunctionsFieldCoverActual.lean` | 4688 | True | `theorem pull_injective {X Y : D} (f : X ⟶ Y) :` | `noncomputable def rationalFunctions :` | **PROVED** |
| S462 | 1 | `S462Example32PhiIsoGroupLikeActual.lean` | 3881 | True | `def Example32FSMIso : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop :=` | `noncomputable def example32PhiIso :` | **PROVED** |
| S464 | 1 | `S464RationalFunctionsLiftedActual.lean` | 1369 | True | `noncomputable def uliftUnitMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :` | `structure Example32LiftedGroupLaws where` | **PROVED** |
| S465 | 1 | `S465LiftedDivisorMapActual.lean` | 2046 | True | `noncomputable def uliftAdditiveDown :` | `noncomputable def liftedDivisorMap :` | **PROVED** |
| S467 | 1 | `S467KrootOrderControlAuditActual.lean` | 3310 | True | `noncomputable def qVFamilyKRamificationIdx : Nat :=` | `theorem qVFamilyK_order_factorization :` | **AUDIT** |
| S468 | 1 | `S468DivisorNaturalityActual.lean` | 2445 | True | `abbrev DvSmallValuationFamily : Type (u + 1) :=` | `def DvSmallValuationCompatibility` | **PROVED** |
| S469 | 1 | `S469RationalFunctionsLiftedActual.lean` | 2518 | True | `theorem arrowAlgebraMap_id_local (X : Example32SmallBase K) :` | `theorem arrowAlgebraMap_comp_local {X Y Z : Example32SmallBase K}` | **PROVED** |
| S472 | 1 | `S472TorsionKInputAuditActual.lean` | 3034 | True | `theorem torsion23_actual :` | `theorem qVFamilyK_order_factorization_actual :` | **AUDIT** |
| S474 | 1 | `S474Example32GroupLikeIsoActual.lean` | 4692 | True | `theorem arrowAlgebraMap_id' (X : Example32SmallBase K) :` | `theorem arrowAlgebraMap_comp' {X Y Z : Example32SmallBase K}` | **PROVED** |
| S476 | 1 | `S476GenericGroupLikeGapActual.lean` | 1533 | True | `structure S476GenericInstantiationData (K : Type u) [Field K] where` | `def S476GenericInstantiationDataRequired (K : Type u) [Field K] : Prop :=` | **PROVED** |
| S477 | 3 | `S477ProbeAdapted.lean` | 289 | False | `` | `` | **AUDIT** |
| S479 | 1 | `S479TwoTorsionParityGapActual.lean` | 2452 | True | `theorem torsion23_input_actual :` | `structure TwoTorsionToQSqrtGap where` | **PROVED** |
| S480 | 1 | `S480Example32InputActual.lean` | 3381 | True | `noncomputable def example32PhiIsFSM :` | `structure Example32InputData where` | **PROVED** |
| S481 | 1 | `S481AlignedDivisorMapActual.lean` | 3912 | True | `noncomputable def stageDivisorULiftEquiv :` | `noncomputable def grothendieckStageDivisorULift :` | **PROVED** |
| S483 | 1 | `S483Example32InputActualConstruction.lean` | 4784 | True | `noncomputable def stageDivisorULiftUp :` | `noncomputable def grothendieckStageULiftUp :` | **PROVED** |
| S485 | 1 | `S485TateTwoTorsionQSqrtActual.lean` | 4797 | True | `abbrev FPlace : NumberField.FinitePlace T.arithmetic.F :=` | `abbrev KF : Type := Completion (FPlace T b)` | **PROVED** |
| S486 | 1 | `S486Example32ULiftGroupLikeActual.lean` | 1498 | True | `abbrev Example32ULiftUnits (X : Example32SmallBase K) : Type (u + 1) :=` | `noncomputable def example32ULiftPullback` | **PROVED** |
| S491 | 1 | `S491AlignedDivisorMapActual.lean` | 4866 | True | `noncomputable def stageDivisorULiftEquiv' :` | `noncomputable def grothendieckStageDivisorULift' :` | **PROVED** |
| S492 | 1 | `S492Example32InputActual.lean` | 3179 | True | `structure Example32InputDataActual where` | `noncomputable def example32InputActual` | **PROVED** |
| S493 | 1 | `S493Example32InputIsoActual.lean` | 3868 | True | `abbrev PhiIso : DivisorialMonoidOn (Example32SmallBase K)` | `abbrev PhiFSM : DivisorialMonoidOn (Example32SmallBase K)` | **PROVED** |
| S494 | 1 | `S494TateTwoTorsionConverseGapActual.lean` | 2771 | True | `abbrev ConversePoint : Type :=` | `structure TwoTorsionQuotientLiftData where` | **PROVED** |
| S495 | 1 | `S495DvSmallValuationActual.lean` | 2437 | True | `def DvSmallValuationExtensionExists : Prop :=` | `def DvSmallValuationExtensionUnique : Prop :=` | **PROVED** |
| S496 | 1 | `S496Example32AlignedDivisorNaturalityActual.lean` | 3174 | True | `theorem phi_gpPullback_id {X Y : Example32SmallBase K} (f : X ⟶ Y) :` | `theorem liftedPullback_ofMul_up {X Y : Example32SmallBase K} (f : X ⟶ Y)` | **PROVED** |
| S499 | 1 | `S499DvSmallValuationFamilyActual.lean` | 3184 | True | `abbrev S499DvSmallValuationFamily : Type (u + 1) :=` | `noncomputable def s499DvSmallValuationFamily` | **PROVED** |
| S501 | 1 | `S501ValuationExtensionActual.lean` | 4434 | True | `structure DvNormalizedBaseValuation where` | `structure DvNormalizedValuationExtension` | **PROVED** |
| S502 | 1 | `S502OddLiftObstructionActual.lean` | 3312 | True | `noncomputable def minusOneUnit : (ACF T b)ˣ := -1` | `noncomputable def minusOneDeck : FDeck T b :=` | **PROVED** |
| S503 | 2 | `S503QvPhiModelActualAdapted.lean` | 2071 | False | `structure QvGeneratedPhiPaperData where` | `def QvGeneratedPhiPaperDataRequired : Prop :=` | **INVALID** |
| S505 | 2 | `S505QvPhiGeneratorActualAdapted.lean` | 2873 | False | `abbrev QvK : Type := NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b)` | `noncomputable def qOrder : ℕ := (qVFamily T b).order` | **INVALID** |
| S506 | 1 | `S506QvPhiRamificationActual.lean` | 2416 | True | `structure DvRamificationIndexData where` | `structure DvNatDivisorialMonoidAtU where` | **PROVED** |
| S507 | 1 | `S507PhiCvCandidateActual.lean` | 2515 | True | `noncomputable def phiCvCandidate :` | `abbrev PhiCarrier : Type u := StageDivisor.{u}` | **PROVED** |
| S508 | 1 | `S508PaperPhiCvCandidateActual.lean` | 2455 | True | `structure DvSmallRamificationIndexData where` | `structure DvSmallQOrderSection where` | **PROVED** |
| S509 | 1 | `S509OddLiftChoiceActual.lean` | 2694 | True | `theorem qHalfRootClass_sq_one :` | `noncomputable def qSqrtOddLiftCondition : OddLiftCondition T b where` | **PROVED** |
| S510 | 1 | `S510Example32ULiftGroupLikeCompleteActual.lean` | 1623 | True | `noncomputable def s510GroupLike :` | `theorem s510GroupLike_obj (X : Example32SmallBase K) :` | **PROVED** |
| S511 | 1 | `S511PhiCvCandidateActual.lean` | 3305 | True | `structure RamificationIndexData where` | `abbrev PhiCvCarrier (_X : Example32SmallBase K) : Type := ℕ` | **PROVED** |
| S513 | 2 | `S513DvPhiCvCandidateActualAdapted.lean` | 3029 | False | `abbrev DvPhiBase : Type := Example32SmallBase T.arithmetic.K` | `noncomputable def dvQOrderSection (N : ℕ) (hN : 0 < N) :` | **INVALID** |
| S515 | 1 | `S515NatDivisorialMonoidULiftActual.lean` | 1950 | True | `def ULiftNatSaturated : Prop :=` | `noncomputable def dvNatDivisorialAddMonoidAtU` | **PROVED** |
| S516 | 1 | `S516ULiftNatPhiActual.lean` | 4358 | True | `noncomputable def uliftNatDivisorialAddMonoid :` | `noncomputable def uliftNatMulLeft (e : ℕ) :` | **PROVED** |
| S517 | 1 | `S517EtThSpecialTwoTorsionGapActual.lean` | 1609 | True | `structure EtThSpecialTwoTorsionGap where` | `` | **PROVED** |
| S518 | 1 | `S518ULiftNatDivisorialAddMonoidActual.lean` | 2426 | True | `noncomputable def uliftNatDivisorialAddMonoid :` | `` | **PROVED** |
| S519 | 1 | `S519QvPhiRamificationModelActual.lean` | 3943 | True | `noncomputable def uliftNatDivisorialAddMonoid :` | `noncomputable def uliftNatMulLeft (e : ℕ) :` | **PROVED** |
| S522 | 1 | `S522QvPhiRamificationModelActual.lean` | 2761 | True | `noncomputable def uliftNatMulLeft (e : ℕ) :` | `theorem uliftNatMulLeft_injective {e : ℕ} (he : 0 < e) :` | **PROVED** |
| S523 | 1 | `S523EtThReductionSelectorActual.lean` | 1829 | True | `structure EtThReductionSelectorData where` | `def EtThReductionSelectorDataRequired : Prop :=` | **PROVED** |
| S524 | 1 | `S524QvPhiRamificationModelS518Actual.lean` | 3141 | True | `noncomputable def uliftNatMulLeft (e : ℕ) :` | `theorem uliftNatMulLeft_injective {e : ℕ} (he : 0 < e) :` | **PROVED** |
| S526 | 1 | `S526Example32AlignedNaturalityActual.lean` | 2029 | True | `theorem example32AlignedDivisor_ofMul_up` | `def example32AlignedDivisorNaturalityGap : Prop :=` | **PROVED** |
| S528 | 2 | `S528QvPhiTriSubmonoidActual.lean` | 3223 | True | `theorem uliftNatMulLeft_apply_nsmul (e : ℕ) (n : ULift.{u+1} ℕ) :` | `noncomputable def qvTriQOrder` | **PROVED** |
| S530 | 1 | `S530EtThQSqrtRecipeSpecActual.lean` | 2137 | True | `structure EtThThetaSplittingRecipe (T : SourceNativeInitialThetaData.{0} l)` | `` | **PROVED** |
| S531 | 1 | `S531EtThThetaUnitRecipeActual.lean` | 3321 | True | `noncomputable def thetaUnitElement : ACF T b :=` | `theorem thetaUnitElement_pow :` | **PROVED** |
| S532 | 1 | `S532QHalfUnitActual.lean` | 3828 | True | `noncomputable def thetaRootElement : ACF T b :=` | `theorem thetaRootElement_pow :` | **PROVED** |
| S533 | 1 | `S533QvPhiSubmonoidActual.lean` | 2536 | True | `noncomputable def qvOrder : ℕ := (qVFamilyK T b).order` | `theorem qvOrder_pos : 0 < qvOrder T b :=` | **PROVED** |
| S534 | 1 | `S534QvPhiCvSharpSubmonoidActual.lean` | 2749 | True | `noncomputable def qvKOrder : ℕ := (qVFamilyK T b).order` | `noncomputable def sharpSubmonoid (g : ℕ) : AddSubmonoid (ULift.{u+1} ℕ) where` | **PROVED** |
| S536 | 2 | `S536Example32AlignedNaturalityFinalActualAdapted.lean` | 1975 | False | `theorem example32AlignedDivisor_naturality` | `` | **INVALID** |
| S539 | 1 | `S539PhiCvSubmonoidActual.lean` | 3064 | True | `noncomputable def s539PhiSubmonoid (qOrder : ℕ)` | `def s539QOrder (_X : Example32SmallBase K) : ℕ := 0` | **PROVED** |
| S540 | 1 | `S540QvPhiTauExactGapActual.lean` | 3418 | True | `structure QvPhiTauData where` | `noncomputable def characteristicSplittingOfQvPhiTauData` | **PROVED** |
| S542 | 1 | `S542ThetaQHalfActual.lean` | 1580 | True | `def qHalfUnitOfTheta (thetaUnit : (ACF T b)ˣ) : (ACF T b)ˣ :=` | `theorem qHalfUnitOfTheta_sq (thetaUnit : (ACF T b)ˣ)` | **PROVED** |
| S543 | 1 | `S543ConditionalEtThRecipeActual.lean` | 4137 | True | `noncomputable def conditionalEtThThetaSplittingRecipe` | `theorem conditionalRecipe_qHalf_sq` | **PROVED** |
| S544 | 1 | `S544Example32AlignedTypeLemmaActual.lean` | 3252 | True | `theorem example32AlignedDivisor_as_S469_obj` | `theorem example32AlignedDivisor_naturality` | **PROVED** |
| S545 | 1 | `S545RealThetaUnitAnalyticModelActual.lean` | 2963 | True | `noncomputable def realThetaLabelUnit (t : AnalyticThetaCarrier) (j : ℤ) : ℝˣ :=` | `theorem realThetaLabelUnit_eq_qUnit_pow (j : ℤ) :` | **PROVED** |
| S546 | 1 | `S546QHalfCandidateActual.lean` | 2702 | True | `noncomputable def qHalfRoot :` | `theorem qHalfRoot_pow :` | **PROVED** |
| S547 | 1 | `S547PhiCvPackageActual.lean` | 2875 | True | `abbrev BaseField : Type := T.arithmetic.K` | `structure PhiCvPackage where` | **PROVED** |
| S548 | 1 | `S548SplitFrobenioidActual.lean` | 3491 | True | `structure S548InputData (K : Type u) [Field K] where` | `noncomputable def s548InputOfData` | **PROVED** |
| S549 | 1 | `S549QvPhiTriSubmonoidActual.lean` | 1703 | True | `structure QvPhiTriSubmonoidData` | `noncomputable def qvPhiTriSubmonoidData` | **PROVED** |
| S550 | 1 | `S550QvPhiPreFrobenioidActual.lean` | 4319 | True | `abbrev qvPhi := qvPhiRamificationModel (K := K) R` | `abbrev qvIsFSM : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop := fun {X Y} f => IsIso f` | **PROVED** |
| S551 | 1 | `S551QHalfComparisonActual.lean` | 2818 | True | `noncomputable def qHalfRootActual : (ACF T b)ˣ :=` | `structure QHalfComparisonData where` | **PROVED** |
| S552 | 1 | `S552Example32ConditionalPresentationActual.lean` | 3550 | True | `structure Example32PresentationConditions where` | `noncomputable def example32InputOfValuation` | **PROVED** |
| S553 | 1 | `S553QvPhiTriDataActual.lean` | 3056 | True | `structure QvPhiTriData (K : Type u) [Field K] where` | `noncomputable def qvPhiTriDataOf` | **PROVED** |
| S554 | 1 | `S554QHalfPaperActual.lean` | 2536 | True | `structure QHalfPaperData where` | `noncomputable def qHalfPaperDataOfComparison` | **PROVED** |
| S555 | 1 | `S555QvPhiTauConstructionGapActual.lean` | 3618 | True | `abbrev QvP := qvPreFrobenioid (K := K) R data` | `abbrev QvR := qvRationalMonoidTransport (K := K) R data` | **PROVED** |
| S556 | 1 | `S556QvPhiInputActual.lean` | 3332 | True | `structure S556InputDataActual where` | `noncomputable def s556InputActual` | **PROVED** |
| S557 | 1 | `S557QvPhiSplitFrobenioidConditional.lean` | 2157 | True | `noncomputable def qvCharacteristicSplitting :` | `noncomputable def qvFrobenioidPresentation` | **PROVED** |
| S558 | 1 | `S558QvPhiTauFromPiActual.lean` | 3532 | True | `structure QvPhiPiTauInput where` | `noncomputable def tauDataOfPiInput` | **PROVED** |
| S559 | 1 | `S559S556NaturalityAlignmentActual.lean` | 2134 | True | `theorem qvPhiPullback_eq_mul` | `def S556NaturalityAlignmentRequired (K : Type u) [Field K]` | **PROVED** |
| S560 | 1 | `S560QvPhiTauPiActual.lean` | 1897 | True | `structure QvPhiTauPiData where` | `def QvPhiTauPiDataRequired : Prop :=` | **PROVED** |
| S561 | 1 | `S561QvPhiMinimalPackageActual.lean` | 2473 | True | `structure S561MinimalPackage where` | `noncomputable def s561InputData` | **PROVED** |
| S562 | 1 | `S562QvPhiInputPackageActual.lean` | 1506 | True | `structure QvPhiInputPackage (K : Type u) [Field K]` | `noncomputable def qvPhiInputPackage (K : Type u) [Field K]` | **PROVED** |
| S563 | 1 | `S563QvOrderElementConstructionActual.lean` | 3039 | True | `structure QvPhiQOrderFields (A : Object (qvPhi (K := K) R)) where` | `noncomputable def qOrderEndomorphismOfFields` | **PROVED** |
| S564 | 1 | `S564QvPiOtriangleCandidateActual.lean` | 3999 | True | `noncomputable def qvPiOrder (T : SourceNativeInitialThetaData.{0} l)` | `theorem qvPiOrder_pos (T : SourceNativeInitialThetaData.{0} l)` | **PROVED** |
| S565 | 1 | `S565QvOrderFromS556InputActual.lean` | 2828 | True | `abbrev Dat (D : S556InputDataActual (K := K)) := s556InputActual D` | `structure S556QOrderWitness where` | **PROVED** |
| S566 | 1 | `S566QvPhiQOrderFieldsActual.lean` | 3150 | True | `abbrev s566Input : Input (qvPhi (K := K) P.ramification) :=` | `noncomputable def zeroQvPhiQOrderFields :` | **PROVED** |
| S567 | 1 | `S567QvPhiQOrderFieldsFromTriDataActual.lean` | 3343 | True | `abbrev s567Input : Input (qvPhi (K := K) D.ramification) :=` | `noncomputable def s567ZeroQvPhiQOrderFields :` | **PROVED** |
| S568 | 1 | `S568QvPhiQOrderTauActual.lean` | 4166 | True | `structure QvPhiQOrderTauInput where` | `noncomputable def tauDataOfQOrderInput` | **PROVED** |
| S569 | 1 | `S569QvOrderPiActual.lean` | 2566 | True | `noncomputable def qOrderAtArrow {X Y : Example32SmallBase K} (f : X ⟶ Y) : ℕ :=` | `theorem qOrderAtArrow_pos {X Y : Example32SmallBase K} (f : X ⟶ Y) :` | **PROVED** |
| S571 | 1 | `S571QvPhiUnitDecompositionActual.lean` | 2922 | True | `noncomputable def qvPi :` | `def QvPhiDivisorDivisibility` | **PROVED** |
| S573 | 1 | `S573QOrderPreimageActual.lean` | 2321 | True | `noncomputable def s567QOrderPreimageOfUnit` | `structure S573QOrderPreimageUnitData where` | **PROVED** |
| S574 | 1 | `S574QvPhiUnitDecompositionConditionalActual.lean` | 4368 | True | `abbrev F574 : QvPhiQOrderFields (K := K) D.ramification (s567Input (K := K) D) A :=` | `noncomputable def pi574 :` | **PROVED** |
| S575 | 1 | `S575QvPhiPositivePreimageActual.lean` | 4595 | True | `noncomputable def positiveUnit (qOrder : ℕ) : (coverField A.base)ˣ :=` | `theorem positiveUnit_valuation (qOrder : ℕ) :` | **PROVED** |
| S576 | 1 | `S576PositiveQvPhiQOrderFieldsActual.lean` | 3538 | True | `structure S576PositiveQvPhiQOrderFields where` | `noncomputable def s576PositiveQvPhiQOrderFieldsOfPreimage` | **PROVED** |
| S577 | 1 | `S577QvPiRealizationFromS556Actual.lean` | 3129 | True | `structure S556QvPiData (D : S556InputDataActual (K := K)) where` | `noncomputable def qvPiRealizationOfS556` | **PROVED** |
| S580 | 1 | `S580PositivePreimageConstructionActual.lean` | 2411 | True | `noncomputable def positiveQvPhiPreimage (qOrder : ℕ) (hpos : 0 < qOrder) :` | `noncomputable def s556QOrderWitnessOfPositive :` | **PROVED** |
| S581 | 1 | `S581QvPhiPositivePreimageFromS575Actual.lean` | 4484 | True | `noncomputable def s581PositiveUnit (qOrder : ℕ) : (coverField A.base)ˣ :=` | `theorem s581PositiveUnit_valuation (qOrder : ℕ) :` | **PROVED** |
| S582 | 1 | `S582AlignedDivisorEvalActual.lean` | 1374 | True | `theorem grothendieckStageDivisorULift'_of (x : StageDivisor.{u}) :` | `` | **PROVED** |
| S583 | 1 | `S583AlignedDivisorEvalS491Actual.lean` | 2128 | True | `theorem example32DivisorAlignedS491_eval` | `theorem grothendieckStageDivisorULift'_of` | **PROVED** |
| S584 | 1 | `S584QOrderWitnessActual.lean` | 3105 | True | `theorem positiveUnit_divisor_evalS584 (qOrder : ℕ) :` | `noncomputable def s556QOrderWitnessActual :` | **PROVED** |
| S586 | 1 | `S586PositiveQvPhiPreimageActual.lean` | 3093 | True | `structure PositiveQvPhiPreimageEvalData (qOrder : ℕ) where` | `noncomputable def positiveQvPhiPreimageS586` | **PROVED** |
| S590 | 2 | `S590EvalActualAdapted.lean` | 2147 | False | `` | `` | **STATEMENT** |
| S591 | 1 | `S591PositiveUnitDivisorEvalActual.lean` | 3341 | True | `theorem positiveUnit_divisor_toLift (qOrder : ℕ) :` | `theorem positiveUnit_divisor_eval (qOrder : ℕ) :` | **PROVED** |
| S593 | 1 | `S593PositivePreimageQvOrderActual.lean` | 1593 | True | `noncomputable def positiveQvPhiPreimageAtQvOrder :` | `` | **PROVED** |
| S595 | 1 | `S595PositiveEvalIndependentActual.lean` | 3004 | True | `theorem positiveUnit_divisor_eval` | `noncomputable def positivePreimage` | **PROVED** |
| S596 | 1 | `S596PositivePreimageActual.lean` | 1561 | True | `noncomputable def positivePreimage (qOrder : ℕ) (hpos : 0 < qOrder) :` | `` | **PROVED** |
| S597 | 1 | `S597QvPhiQOrderFieldsActual.lean` | 3962 | True | `noncomputable def qOrderFields` | `noncomputable def qOrderEndomorphism` | **PROVED** |
| S598 | 1 | `S598QvPhiQOrderTauFromQvOrderActual.lean` | 2862 | True | `noncomputable def positivePreimageAtQvOrder :` | `noncomputable def qOrderFieldsAtQvOrder :` | **PROVED** |
| S599 | 1 | `S599QvPhiTauFieldsActual.lean` | 5225 | True | `noncomputable def s599QOrderFields` | `structure S599TauCompatibility where` | **PROVED** |
| S600 | 1 | `S600PositiveFieldsFromS593Actual.lean` | 3910 | True | `noncomputable def s600QvPhiQOrderFields :` | `noncomputable def s600Tau :` | **PROVED** |
| S601 | 1 | `S601QvPhiQOrderFieldsFromPreimageActual.lean` | 2337 | True | `noncomputable def qvPhiQOrderFieldsOfPreimage` | `noncomputable def qOrderEndomorphismOfPreimage` | **PROVED** |
| S602 | 1 | `S602CharacteristicSplittingFromPreimagesActual.lean` | 7154 | True | `noncomputable def preimageFields (qOrder : ℕ) (hpos : 0 < qOrder)` | `noncomputable def qvPhiQOrderTauInputOfPreimages` | **PROVED** |
| S603 | 1 | `S603QvPhiDivisibilityGoalActual.lean` | 4258 | True | `abbrev threeInput : Input (qvPhi (K := K) P.ramification) :=` | `abbrev threePi :` | **PROVED** |
| S604 | 1 | `S604QvPhiQOrderTauInputActual.lean` | 4933 | True | `noncomputable def fieldsOfPreimageFamily` | `noncomputable def qvPhiQOrderTauInputOfPreimageFamily` | **PROVED** |
| S605 | 1 | `S605KSideQVActual.lean` | 3133 | True | `structure KSideQVComparisonData where` | `def KSideQVComparisonRequired : Prop :=` | **PROVED** |
| S606 | 1 | `S606PositiveUnitQvImageActual.lean` | 3008 | True | `theorem positiveUnit_valuation_qvOrder :` | `theorem positiveUnit_divisor_qvOrder :` | **PROVED** |
| S607 | 3 | `S607ProbeAdapted.lean` | 298 | False | `` | `` | **AUDIT** |
| S608 | 2 | `S608QOrderDivisibilityLawsActualAdapted.lean` | 4356 | False | `abbrev qvPi := qOrderEndomorphism (K := K) T b P A` | `abbrev qvFields := qOrderFields (K := K) T b P A` | **INVALID** |
| S609 | 1 | `S609QHalfRigidityActual.lean` | 1954 | True | `theorem qHalf_ratio_sq_one` | `theorem qHalf_constant_multiple_rigidity` | **PROVED** |
| S610 | 1 | `S610PositiveUnitQvImageActual.lean` | 2733 | True | `noncomputable def positiveUnitAtQvOrder :` | `theorem positiveUnitAtQvOrder_valuation :` | **PROVED** |
| S611 | 1 | `S611SpecialTwoTorsionEvaluationActual.lean` | 4105 | True | `noncomputable def qHalfRootS546 : (ACF T b)ˣ :=` | `theorem qHalfRootS546_pow :` | **PROVED** |
| S612 | 1 | `S612QvPositiveUnitImageMapActual.lean` | 2891 | True | `noncomputable def qUnitAtQvFamilyK : (Completion (qVFamilyKLift T b))ˣ :=` | `theorem qUnitAtQvFamilyK_val :` | **PROVED** |
| S613 | 1 | `S613QvPhiDivisibilityAttemptActual.lean` | 2099 | True | `abbrev divMon : Type _ :=` | `theorem identity_divisorDivisibility :` | **PROVED** |
| S614 | 1 | `S614PhiCvModelComparisonActual.lean` | 2039 | True | `structure PhiCvModelComparison (place : NumberField.FinitePlace K)` | `noncomputable def phiCvModelComparisonOf` | **PROVED** |
| S615 | 1 | `S615UnitsCommuteActual.lean` | 3774 | True | `noncomputable def s615Tau (X : (qvPreFrobenioid (K := K) P.ramification` | `def S615UnitsCommuteStatement : Prop :=` | **PROVED** |
| S616 | 4 | `S616ModelPaperAlignmentActualAdapted.lean` | 1917 | False | `def s616ModelBaseEquiv : Example32SmallBase K ≌ Example32SmallBase K :=` | `structure S616PaperPhiObjEquivData where` | **INVALID** |
| S617 | 1 | `S617SpecialFiberOriginActual.lean` | 1862 | False | `noncomputable def specialFiberOrigin (W : WeierstrassCurve R) :` | `theorem specialFiberOrigin_eq_zero (W : WeierstrassCurve R) :` | **INVALID** |
| S618 | 2 | `S618KSideQVPlaceActualAdapted.lean` | 2792 | False | `theorem place_eq_imp_shadow_eq` | `structure KSideQVPlaceGap where` | **INVALID** |
| S619 | 2 | `S619IdentityTauUnitsCommuteActualAdapted.lean` | 4419 | False | `noncomputable def s619IdentityTau` | `theorem s619IdentityTau_units_commute` | **INVALID** |
| S620 | 5 | `S620FinalContractActualAdapted.lean` | 4733 | False | `noncomputable def sourceQSigned : Real :=` | `noncomputable def sourceTargetSigned : Real :=` | **INVALID** |
| S621 | 5 | `S621ConcreteComparisonMinimalGapActualAdapted.lean` | 2431 | False | `theorem obstacle_iff_badQAbsLog :` | `def ConcreteSourceComparisonMinimalGap : Prop :=` | **INVALID** |
| S622 | 3 | `S622FinalNumericInequalityActualAdapted.lean` | 2410 | False | `def FinalNumericInequality : Prop :=` | `theorem not_finalNumericInequality_of_badQAbsLog_eq_log5` | **INVALID** |
| S623 | 2 | `S623SourceBadQAuditActualAdapted.lean` | 2533 | False | `theorem sourceBadQAbsLog_eq_sum_abs_log` | `theorem obstacle_of_badQAbsLog_lower_bound` | **AUDIT** |
| S624 | 3 | `S624FinalConcreteSourceComparisonGapActualAdapted.lean` | 3370 | False | `theorem concreteSourceComparisonObstacle_iff_gaussSum_le_badQAbsLog` | `def FinalConcreteSourceComparisonGap : Prop :=` | **INVALID** |
| S625 | 2 | `S625FinalConditionalPackageActualAdapted.lean` | 3387 | False | `structure FinalConcreteComparisonPackage where` | `noncomputable def finalConcreteComparisonPackage` | **INVALID** |
| S627 | 1 | `S627ThetaSourceComparisonActual.lean` | 2601 | True | `def paperComparisonGap` | `theorem thetaSourceComparison_iff_gap` | **PROVED** |
| S628 | 2 | `S628PaperXiFSourceLinkConstructionActualAdapted.lean` | 6166 | False | `def ConcreteSourceQIdentification` | `theorem qPilotLogVolume_eq_paper` | **INVALID** |
| S629 | 1 | `S629SourceIdentificationAuditActual.lean` | 2332 | True | `theorem concrete_strip_identification_eq :` | `theorem concrete_lineBundle_identification_eq :` | **AUDIT** |
| S630 | 1 | `S630ActualQPilotXiFLinkAudit.lean` | 2480 | True | `theorem actual_signedQPilotLogVolume_eq_paper :` | `theorem actual_qPilotLogVolume_eq_paper_withTop :` | **AUDIT** |
| S631 | 1 | `S631SourceQIdentificationActual.lean` | 3289 | True | `theorem sourceQPilotSignedLog_unfold` | `theorem paperQPilotLogVolume_C3_unfold` | **PROVED** |
| S633 | 2 | `S633ThetaPacketQMagnitudeActualAdapted.lean` | 3156 | False | `theorem paperQPilotLogMagnitude_eq_qPilotLogMagnitude` | `theorem missingPaperXiFComparison_of_thetaPacket` | **INVALID** |
| S634 | 2 | `S634PaperXiFConditionalCor312Actual.lean` | 4964 | True | `def ConcreteSourceQIdentification` | `theorem qPilotLogVolume_eq_paper` | **PROVED** |
| S636 | 1 | `S636ThetaNormalizationAuditActual.lean` | 2647 | True | `def paperThetaScale (qTwoU : Real) (j : SignedLabel l.value) : Real :=` | `theorem paperThetaScale_eq_realThetaValue (qTwoU : Real)` | **AUDIT** |
| S637 | 2 | `S637ActualPaperXiFBridgeActualAdapted.lean` | 3466 | False | `noncomputable def actualThetaLinkOfBridge :` | `Theorem actualThetaLinkOfBridge_identification :` | **INVALID** |
| S638 | 3 | `S638ActualToPaperXiFSourceLinkActualAdapted.lean` | 1998 | False | `noncomputable def paperXiFSourceLinkOfActual :` | `` | **INVALID** |
| S640 | 5 | `S640PaperRootThetaProcessionActualAdapted.lean` | 4158 | False | `noncomputable def processionSignedLabel (x : ProcessionLabel l) : SignedLabel l.value :=` | `noncomputable def paperRootThetaProcession :` | **INVALID** |
| S641 | 1 | `S641CorrectedPaperThetaComparisonActual.lean` | 2127 | True | `theorem s641GlobalQPilot_le_thetaHull :` | `def S641PaperRootHullFormulaGapRequired : Prop :=` | **PROVED** |
| S642 | 2 | `S642PaperRootThetaProcessionActualAdapted.lean` | 3573 | False | `noncomputable def paperRootThetaWeight : Real :=` | `noncomputable def paperRootThetaValue (j : SignedLabel l.value) : Real :=` | **INVALID** |
| S644 | 2 | `S644PaperRootThetaProcessionActualAdapted.lean` | 4511 | False | `noncomputable def paperThetaLogMagnitude` | `noncomputable def paperThetaSignedLogValue` | **INVALID** |
| S645 | 2 | `S645RootNormalizedPaperSignedHullActualAdapted.lean` | 3882 | False | `noncomputable def rootThetaSignedProcession :` | `theorem rootThetaSignedProcession_value (j : SignedLabel l.value) :` | **INVALID** |
| S646 | 1 | `S646PaperRootHullComparisonActual.lean` | 3808 | True | `def PaperRootCoefficientLeRootNorm : Prop :=` | `theorem qPilotClassicalLog_le_paperRootHullLog` | **PROVED** |
| S647 | 1 | `S647RootThetaExtensionHullMeasureActual.lean` | 3027 | True | `structure RootThetaExtensionHullMeasureData where` | `def RootThetaExtensionHullMeasureRequired : Prop :=` | **PROVED** |
| S649 | 1 | `S649RootThetaExtensionComparisonActual.lean` | 2910 | True | `noncomputable def s649CarrierData :` | `theorem s649RootThetaPowerPoint_eq_embedded` | **PROVED** |
| S650 | 3 | `S650ActualSignedCor312ContractAdapted.lean` | 2763 | False | `noncomputable def s650ActualSignedContract : StepXIContract :=` | `theorem s650ActualSignedCor312Conclusion :` | **INVALID** |
| S652 | 1 | `S652ExtensionImageLogActual.lean` | 2411 | True | `noncomputable def extensionImageLog` | `theorem extensionImageLog_eq_log_card` | **PROVED** |
| S653 | 1 | `S653RootThetaTensorHullCarrierGapActual.lean` | 3767 | True | `noncomputable def rootThetaProductImageMap` | `theorem rootThetaProductImageMap_imagePoint` | **PROVED** |
| S654 | 1 | `S654RootSignedHullSignCorrectionActual.lean` | 2590 | True | `theorem rootThetaMagnitudeValue_nonneg (j : SignedLabel l.value) :` | `theorem rootThetaMagnitudeProcession_average_nonneg :` | **PROVED** |
| S656 | 2 | `S656RootThetaSignAuditActualAdapted.lean` | 1739 | False | `theorem s642_value_eq_s644_signedLog (j : SignedLabel l.value) :` | `theorem s642_value_eq_neg_magnitude (j : SignedLabel l.value) :` | **AUDIT** |
| S657 | 1 | `S657RootSignedHullIndependentActual.lean` | 4982 | True | `noncomputable def rootThetaMagnitudeValue (j : SignedLabel l.value) : Real :=` | `theorem rootThetaMagnitudeValue_nonneg (j : SignedLabel l.value) :` | **PROVED** |
| S658 | 1 | `S658RootNormalizedPaperSignedHullActual.lean` | 2194 | True | `noncomputable def rootNormalizedPaperSignedHullCorrected` | `theorem rootNormalizedPaperSignedHullCorrected_signed_eq` | **PROVED** |
| S660 | 3 | `S660ConcreteSourceComparisonObstacleActualAdapted.lean` | 4032 | False | `def ConcreteSourceComparisonScalarGap : Prop :=` | `theorem concreteSourceComparisonObstacle_iff_scalarGap :` | **INVALID** |
| S662 | 1 | `S662NormalizedHaarArbitraryAverageActual.lean` | 5384 | True | `noncomputable def normalizedHaarScaleFor (A : Real) : Real :=` | `theorem normalizedHaarScaleFor_pos (A : Real) :` | **PROVED** |
| S663 | 2 | `S663ActualAverageNormalizedHaarActual.lean` | 6109 | True | `noncomputable def s663Scale (a : Real) : Real :=` | `theorem s663Scale_pos (a : Real) :` | **PROVED** |
| S664 | 1 | `S664RootQUnitNormLeOneActual.lean` | 2023 | True | `theorem rootQUnitNormLeOne : RootQUnitNormLeOne (T := T) := by` | `` | **PROVED** |
| S665 | 1 | `S665PaperSignedHullXiFInterfaceActual.lean` | 4058 | True | `noncomputable def s665PaperSignedHull : PaperSignedHull X (SignedLabel l.value) :=` | `theorem s665_signedHullLogVolume_eq_neg_average :` | **PROVED** |
| S666 | 1 | `S666QPilotRootExtensionInterfaceActual.lean` | 4521 | True | `noncomputable def qPilotRegion :` | `noncomputable def qPilotLog : Real :=` | **PROVED** |
| S668 | 1 | `S668QPilotRootExtensionPerBActual.lean` | 4578 | True | `noncomputable def qPilotToRootExtension :` | `theorem qPilotToRootExtension_eq (x : qVFamTensorBlock T b) :` | **PROVED** |
| S669 | 1 | `S669S663PaperXiFSourceLinkActual.lean` | 5593 | True | `def S669QPilotLogVolumeEqPaper` | `noncomputable def s669PaperXiFSourceLink` | **PROVED** |
| S670 | 1 | `S670QPilotRootExtensionContainmentActual.lean` | 3795 | True | `def QPilotPerBPointwiseNormBound : Prop :=` | `theorem qPilotPerBContainmentObstacle_iff_pointwise :` | **PROVED** |
| S671 | 1 | `S671QPilotRadiusAuditActual.lean` | 4383 | True | `theorem rootImageCoordinate_eq_closedBall :` | `def QPilotRadiusBoundObstacle : Prop :=` | **AUDIT** |
| S672 | 1 | `S672OtrianglerightConstructionActual.lean` | 2669 | True | `noncomputable def otrianglerightOfSections` | `structure OtrianglerightCandidate` | **PROVED** |
| S673 | 2 | `S673QPilotRootImageContainmentActualAdapted.lean` | 2297 | False | `noncomputable def qPilotImageInRootExtension : Set (rootNormedExtension T b) :=` | `noncomputable def rootImageCoordinate : Set (rootNormedExtension T b) :=` | **INVALID** |
| S674 | 1 | `S674SourceQIdentificationPackageActual.lean` | 2863 | True | `def ConcreteSourceQIdentification` | `theorem qPilotLogVolume_eq_paper_iff_sourceQ :` | **PROVED** |
| S676 | 1 | `S676FinalConditionalCor312Actual.lean` | 5221 | True | `noncomputable def s676SourceLink` | `theorem s676_finalCor312` | **PROVED** |
| S677 | 1 | `S677OtriFromTauGapActual.lean` | 2904 | True | `noncomputable def splitOfStageSplitting` | `structure OtriCandidateFromTauData` | **PROVED** |
| S678 | 1 | `S678QPilotRootExtensionOperatorBoundActual.lean` | 5086 | True | `noncomputable def qPilotBlockLinearMap :` | `theorem qPilotBlockLinearMap_apply (x : qVFamTensorBlock T b) :` | **PROVED** |
| S679 | 1 | `S679DirectScalarComparisonActual.lean` | 5165 | True | `noncomputable def rootThetaAverageCoefficient : Real :=` | `noncomputable def qVFamLocalQPilotMagnitude : Real :=` | **PROVED** |
| S680 | 1 | `S680OtriUnitsFromLogShellSectionsActual.lean` | 4410 | True | `noncomputable def otriSubmonoidOfSections` | `theorem q_mem_otriSubmonoidOfSections` | **PROVED** |
| S681 | 1 | `S681OtriQSectionReflectionNoGoActual.lean` | 3565 | True | `theorem completionMap_root_pow` | `theorem no_completion_reflection_with_root` | **PROVED** |
| S682 | 1 | `S682LogGeometryToolInventory.lean` | 946 | True | `` | `` | **AUDIT** |
| S683 | 1 | `S683QPilotRadiusOperatorAuditActual.lean` | 2359 | True | `theorem qPilotRadiusBound_of_operatorConstant` | `` | **AUDIT** |
| S684 | 1 | `S684QuadraticGaussFiniteActual.lean` | 1231 | True | `noncomputable def quadraticGaussSum (psi : AddChar (ZMod N) ℂ) (a : ZMod N) : ℂ :=` | `theorem quadraticGaussSum_zero (psi : AddChar (ZMod N) ℂ) :` | **PROVED** |
| S685 | 1 | `S685NewtonOkounkovToolAuditActual.lean` | 2047 | False | `structure NewtonOkounkovSkeletonBridge where` | `def NewtonOkounkovSkeletonBridgeRequired : Prop :=` | **AUDIT** |
| S687 | 1 | `S687QPilotSourceNormBoundActual.lean` | 3424 | True | `def QPilotRegionNormLe (R : Real) : Prop :=` | `def QPilotSourceNormBound (C : Real) : Prop :=` | **PROVED** |
| S688 | 1 | `S688OtriFromRootStackSectionMapActual.lean` | 3417 | True | `abbrev RootStackSectionUnitsMap : Type u :=` | `noncomputable def otriUnitsSectionsOfRootStackMap` | **PROVED** |
| S690 | 1 | `S690RootThetaCoefficientExpansionActual.lean` | 3374 | True | `noncomputable def qPilotLocalMagnitude : Real :=` | `theorem rootThetaMagnitudeValue_eq_ratio_mul_qPilot` | **PROVED** |
| S691 | 1 | `S691RootStackUnitsFieldsActual.lean` | 3099 | True | `structure OTriangleUnitCoordinates where` | `structure RootStackUnitsFieldsData where` | **PROVED** |
| S692 | 1 | `S692QPilotRegionNormExactActual.lean` | 2405 | True | `def ThetaScaledRegionNormLe (c : qVFamTensorV → Real) (R : Real) : Prop :=` | `theorem qPilotRegionNormLe_iff_scaled :` | **PROVED** |
| S693 | 1 | `S693DirectComparisonCounterexampleActual.lean` | 2170 | True | `def l29 : PrimeGeFive where` | `theorem l29_value : l29.value = 29 := rfl` | **PROVED** |
| S694 | 1 | `S694ThetaAverageNormalizationActual.lean` | 2880 | True | `abbrev PaperThetaLabel (l : PrimeGeFive) : Type := Fin (lStar l.value)` | `noncomputable def paperThetaLabelWeight (l : PrimeGeFive) : Real :=` | **PROVED** |
| S695 | 1 | `S695QPilotNormalizationAuditActual.lean` | 2974 | True | `theorem qVFamTensorCoefficient_eq_order :` | `theorem qPilotCoefficient_eq_classical_div_twoL :` | **AUDIT** |
| S697 | 1 | `S697QPilotRegionCoefficientReductionActual.lean` | 3446 | True | `noncomputable def qPilotClassicalNormGoal : Prop :=` | `def RootLabelRegionNormLeRootRadius : Prop :=` | **PROVED** |
| S699 | 1 | `S699QPilotRootExtensionNormActual.lean` | 3141 | True | `theorem norm_algebraMap_rootBase_rootNormedExtension` | `theorem qPilotToRootExtension_norm_eq (x : qVFamTensorBlock T b) :` | **PROVED** |
| S700 | 1 | `S700ThetaQParameterNormalizationActual.lean` | 2831 | True | `noncomputable def qParameterThetaValue` | `theorem qParameterThetaValue_eq_rpow` | **PROVED** |
| S701 | 1 | `S701QPilotRegionNormExactGoalActual.lean` | 2969 | True | `noncomputable def qPilotRegionNormRadius : Real :=` | `theorem qPilotRegion_eq_scaledRegion :` | **PROVED** |
| S702 | 1 | `S702QPilotRegionNormCandidateActual.lean` | 2463 | True | `noncomputable def qPilotRegionRadiusCandidate : Real :=` | `noncomputable def qPilotRootImageRadiusCandidate : Real :=` | **PROVED** |
| S703 | 2 | `S703GlobalPaperThetaComparisonActualAdapted.lean` | 4776 | False | `noncomputable def paperThetaPositiveLabel (i : Fin (lStar l.value)) :` | `noncomputable def paperThetaAverageValue (b : Bad (nativePlaceSelection T)) : Real :=` | **INVALID** |
| S704 | 1 | `S704PaperThetaLogVolumeFormulaActual.lean` | 4456 | True | `noncomputable def paperThetaExponent (j : PaperThetaLabel l) : Real :=` | `noncomputable def paperThetaLinearCoefficient (l : PrimeGeFive) : Real :=` | **PROVED** |
| S705 | 1 | `S705QPilotThetaFormulaAuditActual.lean` | 3160 | True | `def qPilotLocalCoefficient : Real :=` | `def thetaLocalCoefficient (j : SignedLabel l.value) : Real :=` | **AUDIT** |
| S706 | 1 | `S706ThetaPilotHullLogActual.lean` | 2891 | True | `noncomputable def thetaPilotHullLog (b : Bad (nativePlaceSelection T)) : Real :=` | `noncomputable def qPilotLog (b : Bad (nativePlaceSelection T)) : Real :=` | **PROVED** |
| S707 | 1 | `S707ThetaHullVsThetaValueActual.lean` | 2859 | True | `noncomputable def thetaPilotMagnitude : Real :=` | `theorem thetaPilotMagnitude_eq_neg_signedHullLogVolume :` | **PROVED** |
| S708 | 1 | `S708QPilotRootLabelRegionNormActual.lean` | 4013 | True | `def S708FirstIdentification : Prop :=` | `theorem qPilotRootLabelRegion_eq_thetaTensorScaledRegion :` | **PROVED** |
| S709 | 1 | `S709RootImageRadiusFormulaActual.lean` | 6857 | True | `noncomputable def oneThetaLabel : ThetaLabel (l := l) :=` | `theorem rootNormedThetaValueInL_one_norm :` | **PROVED** |
| S712 | 1 | `S712RootLabelRegionNormActual.lean` | 2233 | True | `noncomputable def rootLabelRegionRadiusCandidate : Real :=` | `def RootLabelRegionLatticeNormBound : Prop :=` | **PROVED** |
| S714 | 1 | `S714HullComparisonActual.lean` | 4723 | True | `noncomputable def paperQPilotMagnitude : Real :=` | `def paperThetaIndexToSigned (i : PaperThetaLabel l) : SignedLabel l.value :=` | **PROVED** |
| S715 | 1 | `S715S663SurrogateAuditActual.lean` | 5372 | True | `theorem s663Interface_target_builtin (a : Real) :` | `theorem s663PaperSignedHull_hnormal_is_builtin :` | **AUDIT** |
| S716 | 1 | `S716PaperThetaHullLogSourceAuditActual.lean` | 3444 | True | `noncomputable def paperPerBThetaHullLog : Real :=` | `theorem paperPerBThetaHullLog_eq_rootNormHullLog :` | **AUDIT** |
| S717 | 1 | `S717TensorLatticeNormExactActual.lean` | 2913 | True | `noncomputable def rootLabelCoefficientAtOne : qVFamTensorV → Real :=` | `def S717CorrectedRootLabelRegionNormBound : Prop :=` | **PROVED** |
| S718 | 1 | `S718RootImageRadiusLowerActual.lean` | 3028 | True | `noncomputable def rootThetaLabelOne : ThetaLabel (l := l) :=` | `def RootThetaOneNormFormula : Prop :=` | **PROVED** |
| S719 | 2 | `S719PaperRootHullGapDecompositionActualAdapted.lean` | 2850 | False | `structure PaperRootHullScalingDataGap (b : Bad (nativePlaceSelection T)) where` | `def PaperRootHullSetGap (b : Bad (nativePlaceSelection T)) : Prop :=` | **INVALID** |
| S720 | 1 | `S720OneFactorTensorNormReductionActual.lean` | 4027 | True | `def QVFamBlockMapsFractionalLattice : Prop :=` | `def QVFamBlockNormPreserving : Prop :=` | **PROVED** |
| S721 | 1 | `S721ActualHullToPaperSignedHullActual.lean` | 2958 | True | `noncomputable def paperSignedHullOfActualHullLog` | `theorem paperSignedHullOfActualHullLog_signed_eq` | **PROVED** |
| S722 | 1 | `S722CorrectHullComparisonActual.lean` | 2243 | True | `theorem correct_thetaPilotMagnitude_le_qPilotMagnitude` | `theorem correct_globalComparison` | **PROVED** |
| S723 | 1 | `S723OneFactorNormPreservingActual.lean` | 1583 | True | `def S723ExactGoal : Prop :=` | `` | **PROVED** |
| S724 | 3 | `S724ProbeAdapted.lean` | 97 | False | `` | `` | **AUDIT** |
| S725 | 1 | `S725PaperHullCorrectedSourceLinkActual.lean` | 4962 | True | `def PaperSignedHullCorrected (P : PaperSignedHull X label) : Prop :=` | `noncomputable def s725PaperXiFSourceLink` | **PROVED** |
| S726 | 2 | `S726PaperHullVsS663GapActualAdapted.lean` | 4600 | False | `theorem paperPerBThetaHullLog_nonpos :` | `theorem rootThetaMagnitudeValue_one_pos :` | **INVALID** |
| S727 | 1 | `S727RootThetaOneNormFormulaActual.lean` | 2926 | True | `theorem rootImageRadius_eq_cNorm_rpow :` | `def NormalizedOrderCorrectionZero : Prop :=` | **PROVED** |
| S729 | 2 | `S729PaperSignedHullActualHullLogActualAdapted.lean` | 5353 | False | `noncomputable def paperThetaProcession (A : Real) :` | `theorem paperThetaProcession_average (A : Real) :` | **INVALID** |
| S730 | 3 | `S730PaperRootCarrierActualAdapted.lean` | 6375 | False | `theorem root_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}` | `theorem paper_twoLRoot_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}` | **GAP** |
| S732 | 1 | `S732NCGLogVolumeNoGo.lean` | 10922 | True | `structure PaperLogVolume (Region : Type*) where` | `theorem logVol_hull (t : Real) (ht : 0 < t) :` | **GAP** |
| S733 | 1 | `S733CorrectedPaperFinalCor312Actual.lean` | 5419 | True | `def S733CorrectedHullLog : Prop :=` | `noncomputable def s733SourceLink` | **PROVED** |
| S734 | 1 | `S734PaperCoefficientBridgeActual.lean` | 3296 | True | `def PaperRootThetaLogBridgeCondition (b : Bad (nativePlaceSelection T)) : Prop :=` | `theorem paperRootThetaLogBridgeCondition_iff_correction_zero` | **PROVED** |
| S735 | 5 | `S735CoefficientNamespaceAuditActualAdapted.lean` | 2343 | False | `theorem actual_coefficient_is_order_rfl :` | `theorem s734_condition_iff_namespace_equality :` | **AUDIT** |
| S736 | 2 | `S736RootNormCoefficientAuditActualAdapted.lean` | 2922 | False | `theorem rootNormCoefficient_eq_generatorSupply :` | `theorem paperOrderCoefficient_eq :` | **AUDIT** |
| S737 | 2 | `S737PaperCoefficientBridgeCorrectionActualAdapted.lean` | 2031 | False | `def UnconditionalCoefficientBridgeCorrection : Prop :=` | `theorem unconditionalBridge_iff_correction :` | **INVALID** |
| S738 | 2 | `S738QVFamBlockAlignmentActualAdapted.lean` | 2810 | False | `def CommonPrimeNormalizedLatticeAlignment : Prop :=` | `theorem commonPrimeCompletionRingEquiv_norm` | **INVALID** |
| S739 | 2 | `S739PaperOrderThetaHullActualAdapted.lean` | 3646 | False | `noncomputable def paperPerBThetaHullLogPaperOrder : Real :=` | `theorem paperRootCoefficientFamily_eq_order_div` | **INVALID** |
| S740 | 2 | `S740SpectralCoefficientAuditActualAdapted.lean` | 2703 | False | `noncomputable def paperOrderCoefficient : Real :=` | `noncomputable def spectralCoefficient : Real :=` | **AUDIT** |
| S741 | 1 | `S741QVFamBlockSMulActual.lean` | 1789 | True | `theorem qVFamBlockSMulCompatibility_actual :` | `` | **PROVED** |
| S742 | 2 | `S742SpectralOrderFactorActualAdapted.lean` | 3926 | False | `noncomputable def paperOrderCoefficient : Real :=` | `noncomputable def spectralCoefficient : Real :=` | **INVALID** |
| S743 | 2 | `S743PaperSignedHullPaperOrderActualAdapted.lean` | 7868 | False | `noncomputable def paperOrderThetaHullLog : Real :=` | `noncomputable def paperOrderThetaHullMagnitude : Real :=` | **INVALID** |
| S744 | 2 | `S744PaperOrderReplacementActualAdapted.lean` | 3439 | False | `noncomputable def paperPerBThetaHullLogPaperOrder : Real :=` | `def S744CorrectedHullLog : Prop :=` | **INVALID** |
| S745 | 2 | `S745PaperRootHullNonzeroCorrectionActualAdapted.lean` | 5469 | False | `theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :` | `noncomputable def paperRootThetaHullNonzero : Set (qVFamTensorBlock T b) :=` | **INVALID** |
| S746 | 1 | `S746OrdinaryOTriActual.lean` | 3329 | True | `structure OrdinaryOTri (K : Type u) [Monoid K] where` | `def ofExponent (u : Kˣ) (n : Nat) : OrdinaryOTri K :=` | **PROVED** |
| S747 | 1 | `S747ZeroLabelHullAuditActual.lean` | 4230 | True | `def zeroSignedLabel : SignedLabel l.value :=` | `theorem rootThetaRegion_zero :` | **AUDIT** |
| S750 | 3 | `S750ProbeAdapted.lean` | 106 | False | `` | `` | **AUDIT** |
| S751 | 1 | `S751HullAdjunctionActual.lean` | 2998 | True | `structure HullAdjunction (X : Type uX) where` | `theorem hull_fixed (H : HullAdjunction X) (P : Set X) :` | **PROVED** |
| S753 | 1 | `S753StructuralContainmentActual.lean` | 4848 | True | `structure QPilotThetaStructuralData where` | `noncomputable def qPilotThetaStructuralData :` | **PROVED** |
| S754 | 1 | `S754CandidateRootsTorsorActual.lean` | 2953 | False | `theorem candidateRoots_ne_zero (r : CandidateRoots T b) : r.1 ≠ 0 := by` | `noncomputable def candidateRootsSDiv (r s : CandidateRoots T b) :` | **INVALID** |
| S757 | 1 | `S757QVFamBlockIsometryActual.lean` | 2013 | True | `noncomputable def qVFamBlockLinearIsometryEquiv` | `theorem qVFamBlockLinearIsometryEquiv_norm_map` | **PROVED** |
| S759 | 1 | `S759LSectionCarrierCorrectionActual.lean` | 2495 | True | `abbrev LSectionCarrier : Type :=` | `noncomputable def lDivisorSection (u : LSectionCarrier T b) : Multiplicative Real := u.2` | **PROVED** |
| S761 | 2 | `S761S733SurrogateAuditActualAdapted.lean` | 3250 | False | `noncomputable def paperPerBThetaHullLogPaperOrder : Real :=` | `def S761PaperOrderHullLog : Prop :=` | **AUDIT** |
| S763 | 1 | `S763QPilotRootStackKummerActual.lean` | 3516 | False | `def qPilotScalingLog : Real :=` | `def thetaRootScalingLog : Real :=` | **INVALID** |
| S764 | 1 | `S764ThetaHullMinVsAverageActual.lean` | 5910 | True | `noncomputable def paperThetaHullMinCoefficient : Real :=` | `noncomputable def paperThetaAverageCoefficient : Real :=` | **PROVED** |
| S765 | 1 | `S765CompletionValueGroupObstructionActual.lean` | 2056 | False | `theorem twoL_mul_valuation_eq_order_implies_dvd` | `theorem no_completion_twoL_root_of_not_dvd` | **INVALID** |
| S766 | 1 | `S766QPilot2LNormalizationActual.lean` | 2031 | True | `noncomputable def paperQPilotScalar : Real :=` | `noncomputable def paperQPilotMagnitude : Real :=` | **PROVED** |
| S767 | 1 | `S767ThetaHull2lNormalizationActual.lean` | 2469 | True | `def thetaHullMagnitude (qMag : Real) (l : Nat) : Real :=` | `def qPilotSignedLog (qMag : Real) : Real := -qMag` | **PROVED** |
| S769 | 1 | `S769StackyLogVolumeNormalizationActual.lean` | 3714 | False | `theorem stackyMuCard :` | `theorem stackyRootLog_eq_inv_card_mul` | **INVALID** |
| S770 | 1 | `S770QVFamBlockNormFactorActual.lean` | 2771 | True | `noncomputable def qVFamBlockCoordinateNorm` | `theorem qVFamBlock_tensor_norm_eq_coordinate` | **PROVED** |
| S771 | 2 | `S771RootNormCarrierActual.lean` | 3218 | True | `structure RootNormQVBlock where` | `noncomputable def rootNormEquiv :` | **PROVED** |
| S772 | 1 | `S772QVFamBlockMapsLatticeActual.lean` | 4408 | False | `def PureTensorFractionalLatticeImage : Prop :=` | `theorem qVFamBlockMapsFractionalLattice_of_pure` | **INVALID** |
| S773 | 1 | `S773RootCorrectedPaperTargetActual.lean` | 3234 | True | `noncomputable def rootCorrectedQPilotMagnitude : Real :=` | `def RootCorrectedThetaQpilotComparison : Prop :=` | **PROVED** |
| S775 | 1 | `S775PaperOrderQPilotCorrectionActual.lean` | 3734 | True | `noncomputable def paperQPilotCoefficientPaperOrder : qVFamTensorV → Real :=` | `noncomputable def paperQPilotLogPaperOrder : Real :=` | **PROVED** |
| S777 | 1 | `S777PaperTargetRootStackAlignmentActual.lean` | 3653 | True | `theorem s777_paperQLog_eq :` | `theorem s777_structuralContainment :` | **PROVED** |
| S778 | 1 | `S778PaperQPilotHalfRegionActual.lean` | 5119 | True | `noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=` | `theorem qPilotPaperRegion_eq_rootThetaRegion_one :` | **PROVED** |
| S779 | 1 | `S779RootHullNonzeroFixActual.lean` | 10542 | True | `abbrev NonzeroLabel := {j : SignedLabel l.value // j.1 ≠ 0}` | `theorem one_le_exp_of_ne_zero {j : SignedLabel l.value} (hj : j.1 ≠ 0) :` | **PROVED** |
| S781 | 1 | `S781TwoLTargetGapActual.lean` | 2819 | True | `def TwoLTarget (T : SourceNativeInitialThetaData.{0} l)` | `theorem actualQPilotLeTheta :` | **PROVED** |
| S782 | 1 | `S782FiniteRootStackExtensionActual.lean` | 6740 | True | `noncomputable def stackMuRoot : (rootNormedAmbient T b)ˣ :=` | `theorem stackMuRoot_pow :` | **PROVED** |
| S783 | 1 | `S783Mu2lRootExtensionAuditActual.lean` | 2581 | True | `def Mu2lInRootBase : Prop :=` | `def Mu2lInRootExtension : Prop :=` | **AUDIT** |
| S784 | 1 | `S784RootNormRegionsActual.lean` | 5571 | True | `def rootNormSet (S : Set (qVFamTensorBlock T b)) : Set (RootNormQVBlock (T := T) b) :=` | `abbrev rootNormQPilotRegion : Set (RootNormQVBlock (T := T) b) :=` | **PROVED** |
| S785 | 1 | `S785PaperOrderThetaHullBypassActual.lean` | 3126 | True | `theorem paperThetaHullLogPaperOrder_eq_paperRoot :` | `theorem paperRootCoefficientFamily_eq_order_div :` | **PROVED** |
| S788 | 1 | `S788PaperQpilotRegionActual.lean` | 4910 | True | `def oneSignedLabel : SignedLabel l.value :=` | `theorem oneSignedLabel_gauss :` | **PROVED** |
| S789 | 1 | `S789StackMuActionActual.lean` | 1803 | True | `theorem leftMul_not_mulAut` | `` | **PROVED** |
| S790 | 1 | `S790StackToPaperQPilotThetaActual.lean` | 5693 | True | `theorem stackRootSection_divisor_order :` | `theorem stackQSection_divisor_order :` | **PROVED** |
| S792 | 2 | `S792RootStackPaperHullRebaseActualAdapted.lean` | 3246 | False | `noncomputable def paperRootHullLogRebased : Real :=` | `theorem paperRootHullLogRebased_eq :` | **INVALID** |
| S793 | 1 | `S793PaperLeastLambdaOHullActual.lean` | 7570 | True | `abbrev PaperLabel := SignedLabel l.value` | `abbrev PaperNonzeroLabel := {j : PaperLabel (l := l) // j.1 ≠ 0}` | **PROVED** |
| S794 | 1 | `S794LStarProcessionAverageActual.lean` | 4746 | True | `def paperThetaLabelToSigned (i : PaperThetaLabel l) : SignedLabel l.value :=` | `noncomputable def paperThetaProcession : WeightedValues (PaperThetaLabel l) where` | **PROVED** |
| S795 | 1 | `S795OrderSemanticsActual.lean` | 2527 | True | `theorem qVFamily_order_eq_valuation :` | `theorem qVFamily_order_coprime_actual :` | **PROVED** |
| S797 | 2 | `S797PaperHullFirstAuditActual.lean` | 4039 | True | `noncomputable def paperHullFirstCarrier : Set (qVFamTensorBlock T b) :=` | `theorem paperHullFirstCarrier_eq_paperRootThetaHull :` | **AUDIT** |
| S798 | 1 | `S798OtRootStackSectionActual.lean` | 4883 | True | `theorem stackQSection_divisor_order :` | `theorem stackRootSection_divisor_order :` | **PROVED** |
| S799 | 1 | `S799LeastLambdaOPaperTargetActual.lean` | 4089 | True | `noncomputable def paperQPilotRegionLeast : Set (qVFamTensorBlock T b) :=` | `theorem paperQPilotRegionLeast_eq_least :` | **PROVED** |
| S800 | 1 | `S800LeastLambdaOHullActual.lean` | 5590 | True | `noncomputable def lambdaORegion (c : qVFamTensorV → Real) :` | `def candidateHulls (P : Set (qVFamTensorBlock T b)) :` | **PROVED** |
| S801 | 1 | `S801PaperHullLogActual.lean` | 4439 | True | `theorem paperLeastLambdaOHull_eq_paperQPilotRegion :` | `noncomputable def paperHullLog` | **PROVED** |
| S802 | 2 | `S802QVFamBlockMapsLatticeActualAdapted.lean` | 3597 | False | `theorem pureTensor_mem_fractionalLattice` | `theorem qVFamBlockMapsFractionalLattice_actual :` | **INVALID** |
| S803 | 1 | `S803RootNormCarrierDecisionActual.lean` | 3404 | True | `theorem rootNormCarrier_norm_eq_actual` | `def RootNormTensorFractionalLattice : Set (RootNormQVBlock (T := T) b) :=` | **PROVED** |
| S804 | 1 | `S804FinalCor312NonzeroActual.lean` | 3495 | True | `def S804CorrectedHullLog (P : PaperSignedHull X label) : Prop :=` | `noncomputable def s804SourceLink` | **PROVED** |
| S805 | 1 | `S805NonzeroHullReplacementActual.lean` | 4137 | True | `noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=` | `theorem qPilotPaperRegion_eq_rootThetaRegion_one :` | **PROVED** |
| S806 | 1 | `S806PaperRootHullNonzeroGapsActual.lean` | 4700 | True | `theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :` | `noncomputable def paperRootMinimalRegion : Set (qVFamTensorBlock T b) :=` | **PROVED** |
| S807 | 3 | `S807CancellationNoGoActual.lean` | 6663 | False | `theorem norm_add_eq_left_of_norm_lt {x y : K} (h : ‖y‖ < ‖x‖) :` | `theorem norm_sum_eq_of_unique_max {ι : Type*} (s : Finset ι) (f : ι → K) (i0 : ι)` | **GAP** |
| S809 | 1 | `S809PaperLeastHullRootStackBridgeActual.lean` | 4324 | True | `def PaperLeastHullLogFormulaTarget : Prop :=` | `structure PaperLeastHullCompletionData where` | **PROVED** |
| S810 | 1 | `S810LeastHullPaperCarrierActual.lean` | 3444 | True | `noncomputable def paperHullFirstCarrierCorrected : Set (qVFamTensorBlock T b) :=` | `theorem paperHullFirstCarrierCorrected_eq_lambdaORegion :` | **PROVED** |
| S811 | 1 | `S811StackMuPermActionActual.lean` | 2583 | True | `abbrev StackMuGroup : Type := rootsOfUnity (2 * l.value) (rootStackExtension T b)` | `noncomputable def stackMuPerm (ζ : StackMuGroup T b) :` | **PROVED** |
| S812 | 1 | `S812LeastLambdaOFiniteLStackActual.lean` | 4073 | True | `theorem paperLeastLambdaOHullLog_formula` | `theorem paperQPilotLogLeast_le_paperLeastHullLog` | **PROVED** |
| S813 | 1 | `S813PaperInterfaceHub.lean` | 4311 | True | `structure PaperHullLogInterface (X : Type*) where` | `structure StackyHullLogInterface (X : Type*) extends PaperHullLogInterface X where` | **PROVED** |
| S814 | 2 | `S814SkeletonQuantizedLeastHullActual.lean` | 18533 | True | `noncomputable def valueGroupSkeletonLength (c : Real) : Real :=` | `noncomputable def paperQPilotExponentFamily : qVFamTensorV -> Real :=` | **GAP** |
| S815 | 1 | `S815PaperScalingDataFiniteLActual.lean` | 3732 | True | `theorem paperScalingData_nonempty_iff_localGenerator :` | `structure FiniteLScalingGenerator where` | **PROVED** |
| S816 | 1 | `S816StackyHullInterfaceActual.lean` | 5508 | True | `noncomputable def hull : Set (qVFamTensorBlock T b) :=` | `noncomputable def qPilotRegion : Set (qVFamTensorBlock T b) :=` | **PROVED** |
| S817 | 1 | `S817StackRootUnitNormActual.lean` | 5048 | True | `theorem stackRootUnit_norm_eq_rootNormedElementNorm :` | `theorem stackRootUnit_norm_eq_p_rpow :` | **PROVED** |
| S818 | 1 | `S818StackHaarNormalizationAuditActual.lean` | 3154 | True | `noncomputable def stackHaarBallLog : Real :=` | `theorem stackHaarNormalizationBridge_iff :` | **AUDIT** |
| S819 | 1 | `S819PaperRootCompletionGeneratorActual.lean` | 4174 | True | `noncomputable def paperCRoot : Real :=` | `theorem paperCRoot_eq_order_div :` | **PROVED** |
| S820 | 1 | `S820FiniteLScalingGeneratorActual.lean` | 5216 | True | `noncomputable def stackRootUnit : (rootStackExtension T b)ˣ :=` | `theorem stackRootUnit_ne_zero :` | **PROVED** |
| S821 | 1 | `S821StackHaarScalingAuditActual.lean` | 3226 | True | `noncomputable def stackHaarUnitBallLog : Real :=` | `noncomputable def stackHaarBallScalingFactor : Real :=` | **AUDIT** |
| S822 | 3 | `S822StackyCardActualAdapted.lean` | 3093 | False | `theorem stackMuUnit_isPrimitiveRoot :` | `theorem stackMuGroup_card :` | **INVALID** |
| S823 | 1 | `S823StackHaarNormalizedActual.lean` | 3816 | True | `noncomputable def normalizedRootStackHaar : Measure (rootStackExtension (l := l) T b) :=` | `noncomputable def normalizedRootStackUnitBallLog : Real :=` | **PROVED** |
| S824 | 1 | `S824RootStackyHaarVolumeActual.lean` | 20475 | True | `noncomputable def stackMuElem : rootStackExtension T b :=` | `theorem stackMuElem_pow :` | **GAP** |
| S825 | 1 | `S825StackFactorCNormEquivActual.lean` | 4684 | True | `theorem stackRootUnitFactor_eq_one_iff_norm_eq_paperNorm (i : qVFamTensorV) :` | `theorem stackRootUnitFactorOne_iff_norm_eq_paperNorm :` | **PROVED** |
| S826 | 1 | `S826CNormOrderRamificationActual.lean` | 5514 | True | `def QVFamNormalizedNormCompatibility : Prop :=` | `theorem qVFamNormalizedCoefficient_eq_order_div_e` | **PROVED** |
| S827 | 1 | `S827PaperValueGroupNormCardActual.lean` | 3129 | True | `abbrev paperValueGroupPlace : NumberField.FinitePlace T.arithmetic.F :=` | `def PaperNormValuationCard : Prop :=` | **GAP** |
| S828 | 2 | `S828PaperRootValueGroupActualAdapted.lean` | 3210 | False | `def PaperRootValueGroupDivisibility : Prop :=` | `theorem paperRootInValueGroup_iff_divisibility :` | **INVALID** |
| S829 | 1 | `S829PaperNormValuationSpectralActual.lean` | 3482 | False | `theorem paperGeneralNormalizedNormFormula` | `theorem paperGeneralNormalizedLogFormula` | **INVALID** |
| S830 | 1 | `S830ValueGroupNormChainActual.lean` | 2432 | True | `structure PaperValueGroupNormChain where` | `theorem valueGroupNormCharacterization_of_chain` | **PROVED** |
| S831 | 1 | `S831StackHaarDimensionActual.lean` | 3844 | True | `noncomputable def d : Nat :=` | `noncomputable def dK : Nat :=` | **PROVED** |
| S832 | 1 | `S832DFactorAbsorptionAuditActual.lean` | 1767 | True | `theorem dFactor_eq_iff (d L : Real) :` | `theorem weighted_dFactor_iff (w d L : Real) (hw : w ≠ 0) :` | **AUDIT** |
| S833 | 1 | `S833PaperNormalizedStackHaarActual.lean` | 4964 | True | `noncomputable def paperNormalizedRootStackHaar (d : Nat) :` | `noncomputable def paperNormalizedRootStackRootBallLog (d : Nat) : Real :=` | **PROVED** |
| S835 | 1 | `S835PaperRootValueGroupIffActual.lean` | 3381 | True | `def PaperRootValueGroupDivisibility : Prop :=` | `theorem paperRootInValueGroup_iff_divisibility :` | **PROVED** |
| S836 | 1 | `S836NormFormulaFixAuditActual.lean` | 1668 | True | `structure NormFormulaFixSpec where` | `def AnalyticFormulaSource : String :=` | **AUDIT** |
| S837 | 1 | `S837PaperRootMinimalCompactActual.lean` | 3140 | True | `def S837MinimalCompactRequired : Prop :=` | `def S837MinimalOpenRequired : Prop :=` | **PROVED** |
| S838 | 1 | `S838QVFamilyDivisibilityActual.lean` | 2925 | True | `theorem l_not_dvd_order :` | `theorem not_twoL_dvd_of_e_one` | **PROVED** |
| S839 | 1 | `S839PaperRootMinimalProductCompactActual.lean` | 5079 | True | `noncomputable def s839FractionalLattice : Submodule ℤ_[(qVFamTensorP T b)]` | `noncomputable def s839HolomorphicLattice : Submodule ℤ_[(qVFamTensorP T b)]` | **PROVED** |
| S840 | 1 | `S840QVFamRamificationAuditActual.lean` | 2936 | True | `def QVFamRamificationExponentOne : Prop :=` | `theorem qVFamRamificationExponent_pos :` | **AUDIT** |
| S841 | 1 | `S841FractionalCompactAbsorptionActual.lean` | 4088 | True | `theorem s841FractionalCompact :` | `def S841PointwiseAbsorption : Prop :=` | **PROVED** |
| S850 | 1 | `S850LocalQParameterNormalizationActual.lean` | 1734 | True | `noncomputable def paperRamificationIndex : Nat :=` | `noncomputable def paperOrderPi (q : FinitePlaceQCandidate place) : Int :=` | **PROVED** |
| S851 | 1 | `S851PointwiseAbsorptionAuditActual.lean` | 3603 | True | `def S851FractionalMulLe : Prop :=` | `theorem s851Pointwise_iff_mulLe :` | **AUDIT** |
| S853 | 2 | `S853PaperOrderNoEActual.lean` | 3657 | True | `theorem paperRootCoefficientFamily_eq_order_div :` | `theorem paperRootCoefficientFamily_no_e (i : qVFamTensorV) :` | **PROVED** |
| S854 | 1 | `S854ProductCompactRouteActual.lean` | 4145 | True | `theorem s854HolomorphicCompact :` | `def S854ProductCompact : Prop :=` | **PROVED** |
| S855 | 1 | `S855OtriLogVolumeInterfaceActual.lean` | 3089 | True | `noncomputable def stackQDivisorOrder : Real :=` | `noncomputable def stackRootDivisorOrder : Real :=` | **PROVED** |
| S856 | 1 | `S856LogShellIntrinsicVolumeAuditActual.lean` | 5437 | True | `structure SourceLogShellIntrinsicVolume` | `def SourceLogShellIntrinsicVolumeSpec (D : SourceLogShellDatum.{u}) : Prop :=` | **AUDIT** |
| S857 | 1 | `S857OtriLogVolumeInterfaceActual.lean` | 4055 | True | `structure OtriLogVolumeInterface (X : Type*) where` | `noncomputable def otriLogVolumeInterface` | **PROVED** |
| S858 | 1 | `S858PaperGapConditionalCor312Actual.lean` | 7604 | True | `structure PaperGapIntrinsicVolume where` | `structure PaperGap (P : PaperSignedHull X label) where` | **PROVED** |
| S859 | 1 | `S859PaperIntrinsicLogVolumeActual.lean` | 2417 | True | `noncomputable def paperIntrinsicLogVolume (u : StackSectionCarrier (l := l) T b) : Real :=` | `theorem paperIntrinsicLogVolume_root :` | **PROVED** |
| S860 | 1 | `S860GlobalCor312AuditActual.lean` | 3856 | True | `noncomputable def weightedQPilot : Real :=` | `noncomputable def thetaHullScalar : Real :=` | **AUDIT** |
| S861 | 1 | `S861RootCharacterNormComparisonActual.lean` | 2892 | True | `def RootNormedCharacterNormComparison (n : Nat) : Prop :=` | `def RootHaarFactorNormPow (n : Nat) : Prop :=` | **PROVED** |
| S862 | 1 | `S862OtriLogVolumeInterfacePaperActual.lean` | 5528 | True | `noncomputable def paperOtriPlace : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=` | `noncomputable def otriQDivisorOrder : Real :=` | **PROVED** |
| S863 | 1 | `S863ProductImageCompactActual.lean` | 4366 | True | `def s863MulImage : Set (qVFamTensorBlock T b) :=` | `theorem s863MulImageCompact : IsCompact (s863MulImage (l := l) T b) := by` | **PROVED** |
| S864 | 1 | `S864PaperLambdaOLogVolumeActual.lean` | 3317 | True | `noncomputable def paperLambdaOLogVolume (lam : qVFamTensorV → Real) : Real :=` | `theorem paperLambdaOLogVolume_cRoot :` | **PROVED** |
| S865 | 1 | `S865RootHaarFactorNormPowActual.lean` | 4192 | True | `noncomputable def rootHaarFactorNormPowExactGoal : Prop :=` | `theorem rootHaarFactor_normPow_actual :` | **PROVED** |
| S866 | 1 | `S866RootStackCharacterNormLiftActual.lean` | 3804 | True | `noncomputable def rootStackAlgebraMapUnits :` | `def RootStackHaarCharRestrictionBridge (n : Nat) : Prop :=` | **PROVED** |
| S867 | 1 | `S867OtriPaperIntegrationActual.lean` | 4581 | True | `theorem s867_intrinsicRoot_eq_neg_lambdaO :` | `noncomputable def s867OtriInterface` | **PROVED** |
| S868 | 1 | `S868GlobalPaperTargetInterfaceActual.lean` | 3929 | True | `theorem leastHullPaperRegion_actual (b : Bad (nativePlaceSelection T)) :` | `def PaperHullLogFormulaGap (b : Bad (nativePlaceSelection T)) : Prop :=` | **PROVED** |
| S869 | 1 | `S869OtriGapsFilledActual.lean` | 4206 | True | `noncomputable def otriNonunitLogMeasure : StackSectionCarrier (l := l) T b → Real :=` | `theorem otriNonunitLogMeasure_root :` | **PROVED** |
| S870 | 1 | `S870RootStackRestrictionBridgeActual.lean` | 3179 | True | `theorem rootStack_scalar_det (u : rootNormedExtension T b) :` | `def RootStackGeneralNormFormula : Prop :=` | **PROVED** |
| S872 | 1 | `S872OtriLogVolumeInterfaceActual.lean` | 3144 | True | `structure OtriLogVolumeInterface (X : Type) where` | `noncomputable def paperLogVolumeOnHull :` | **PROVED** |
| S873 | 1 | `S873PaperGapIntrinsicVolumeActual.lean` | 5251 | True | `noncomputable def stackDivisorLogMap :` | `noncomputable def gapLogShellDatum : SourceLogShellDatum where` | **PROVED** |
| S874 | 1 | `S874GlobalInterfaceFillActual.lean` | 4467 | True | `def leastHullPaperRegionGlobal : Prop :=` | `theorem leastHullPaperRegionGlobal_actual :` | **PROVED** |
| S875 | 1 | `S875PaperGapHullLogActual.lean` | 3379 | True | `def S875HullLogDatum : Prop :=` | `theorem paperLeastLambdaOHullLog_eq_neg_order_div` | **PROVED** |
| S876 | 1 | `S876CorrectedGlobalTargetActual.lean` | 3378 | True | `abbrev PaperLeastHullData (b : Bad (nativePlaceSelection T)) : Type :=` | `noncomputable def paperQPilotWeightedLeast : Real :=` | **PROVED** |
| S877 | 1 | `S877WeightedIdentificationActual.lean` | 4694 | True | `def HqCorrected : Prop :=` | `def HthetaCorrected : Prop :=` | **PROVED** |
| S878 | 1 | `S878RootStackCharacterNormDirectActual.lean` | 3298 | True | `noncomputable def rootStackHaarFactor (u : (rootStackExtension T b)ˣ) : ENNReal :=` | `def RootStackHaarFactorNormPow (n : Nat) : Prop :=` | **PROVED** |
| S879 | 1 | `S879RootStackNormFormulaInputsActual.lean` | 3692 | True | `theorem rootStack_scalar_det_actual (u : rootNormedExtension T b) :` | `def ENormExtensionFormula : Prop :=` | **PROVED** |
| S880 | 1 | `S880S867ExactFillActual.lean` | 3101 | True | `theorem s880PaperLeastHullLogDatumQVFam :` | `noncomputable def s880CarrierVolume :` | **PROVED** |
| S881 | 1 | `S881PaperGapIntrinsicVolumeS869Actual.lean` | 3618 | True | `def S881HullLogExactGap : Prop :=` | `theorem S881HullLogExactGap_eq_S873 :` | **PROVED** |
| S882 | 1 | `S882PerBCorrectedActual.lean` | 3911 | True | `theorem rootThetaHull_eq_canonicalUnitReference :` | `theorem perBThetaHullLog_eq_zero :` | **PROVED** |
| S883 | 1 | `S883HullLogSingleFieldActual.lean` | 4783 | True | `theorem lambdaOLogVolume_eq_gapVolumeLog :` | `theorem s883HullLogExactGap_iff_lambdaO :` | **PROVED** |
| S884 | 1 | `S884PaperGapIntrinsicVolumeRebuildActual.lean` | 4410 | True | `noncomputable def stackDivisorLogMap :` | `noncomputable def gapLogShellDatum : SourceLogShellDatum where` | **PROVED** |
| S885 | 1 | `S885RootStackUniformizerNormActual.lean` | 3962 | True | `def S885UnitFactorOne : Prop :=` | `def S885UnitDecomposition (pi : (rootStackExtension T b)ˣ) : Prop :=` | **PROVED** |
| S886 | 1 | `S886ENormExtensionFormulaActual.lean` | 1443 | True | `theorem eNormExtensionFormula_actual :` | `theorem rootStackNormFormulaInputs_actual :` | **PROVED** |
| S887 | 1 | `S887RootStackHaarDetViaS861EActual.lean` | 3440 | True | `def RootStackCharacterNormComparisonAt (n : Nat) : Prop :=` | `def RootStackCharacterNormComparisonAtDQp : Prop :=` | **PROVED** |
| S888 | 1 | `S888HqHthetaActual.lean` | 2926 | True | `def HthetaNoTwoL : Prop :=` | `theorem s877_htheta_iff_extra (hno : HthetaNoTwoL T) :` | **PROVED** |
| S889 | 1 | `S889CompatibilityScalingGroupoid.lean` | 2681 | True | `structure ScalingGraph where` | `inductive Path : G.Obj → G.Obj → Type` | **PROVED** |
| S890 | 1 | `S890CompatibilityScalingInstanceActual.lean` | 4756 | True | `noncomputable def qClassicalLog : Real :=` | `noncomputable def qRootLog : Real :=` | **PROVED** |
| S891 | 1 | `S891IndScaleOneEdgesActual.lean` | 3143 | True | `structure IndInvarianceData (α : Type) where` | `inductive IndEdge (D : IndInvarianceData α) (a b : α) : Type` | **PROVED** |
| S892 | 2 | `S892RootStackGeneralNormFormulaActualAdapted.lean` | 3060 | False | `theorem rootStackNormExtensionFormula_actual :` | `theorem finrankL_eq_dK_mul_dLK :` | **INVALID** |
| S893 | 1 | `S893RootStackDVRInstanceActual.lean` | 3071 | True | `def S893AmbientUltrametricRequired : Prop :=` | `def S893NormedAlgebraQpLRequired : Prop :=` | **PROVED** |
| S894 | 1 | `S894HqPositiveActual.lean` | 3303 | True | `theorem hqWeightedCNormOrder_of_cNorm_eq_order` | `theorem hq_weighted_term_eq_zero_of_cNorm_eq_order` | **PROVED** |
| S895 | 1 | `S895HthetaPositiveActual.lean` | 4155 | True | `theorem perBThetaHullLog_eq_leastHullLog_of_bridges` | `theorem thetaHullScalar_eq_leastHullWeighted_of_bridges` | **PROVED** |
| S896 | 2 | `S896NonzeroPerBCorrectedActualAdapted.lean` | 5094 | False | `def ClosedInput (b : Bad (nativePlaceSelection T)) : Prop :=` | `theorem paperRootThetaHullNonzero_eq_qPilotPaperRegion` | **INVALID** |
| S897 | 1 | `S897ECharacterNormViaUniformizerActual.lean` | 3222 | True | `theorem rootStackCharacterNormComparisonAtDQp_of_factorNormPow` | `theorem rootStackCharacterNormComparisonAtDQp_of_uniformizerData` | **PROVED** |
| S898 | 1 | `S898PaperGapFromScalingActual.lean` | 3593 | True | `theorem thetaHullLog_eq_neg_paperRoot :` | `theorem thetaHullLog_eq_gapVolumeLog :` | **PROVED** |
| S899 | 1 | `S899CNormOrderRamificationActual.lean` | 4122 | True | `def S899NormCompatibility : Prop :=` | `def S899RamificationOne : Prop :=` | **PROVED** |
| S900 | 2 | `S900PerBThetaHullLogNonzeroActualAdapted.lean` | 4642 | False | `theorem rootMinimalRegion_closed :` | `theorem paperRootThetaHullNonzero_eq_qPilotPaperRegion :` | **INVALID** |
| S901 | 19 | `S901ProbeAdapted.lean` | 173 | False | `` | `` | **AUDIT** |
| S902 | 1 | `S902RootStackDVRInstancesActual.lean` | 3075 | True | `def S902NormedAlgebraLERequired : Prop :=` | `def S902NormedAlgebraQpERequired : Prop :=` | **PROVED** |
| S903 | 1 | `S903ECharacterNormLightActual.lean` | 2545 | True | `def S903ECharacterNormExactInput : Prop :=` | `theorem s903_hchar_of_exactInput` | **PROVED** |
| S904 | 2 | `S904PaperCor312ScalingActualAdapted.lean` | 4239 | False | `noncomputable def s904PaperGap` | `theorem paperCor312_of_scaling` | **INVALID** |
| S907 | 1 | `S907LVExToyActual.lean` | 5050 | True | `abbrev V : Type := ℝ × ℝ` | `def sigma (v : V) : V := (-v.1, v.2)` | **PROVED** |
| S908 | 1 | `S908ORExpansionContainmentActual.lean` | 4718 | True | `structure ORExpansionData (X : Type u) (ι : Type v) where` | `theorem orExpansion_comparison` | **PROVED** |
| S909 | 1 | `S909PaperSVsLeastHullActual.lean` | 2481 | True | `noncomputable def modelHull : Set (qVFamTensorBlock T b) :=` | `theorem modelHull_eq_qPilotPaperRegion :` | **PROVED** |
| S910 | 2 | `S910ProbeAdapted.lean` | 157 | False | `` | `` | **AUDIT** |
| S911 | 1 | `S911PaperQPilotHullCorollaryActual.lean` | 6829 | True | `theorem paperRootCoefficientFamily_sum_eq :` | `theorem paperSkeletonQPilotLog_le_hull :` | **PROVED** |
| S912 | 2 | `S912RootStackNormedAlgebraActualAdapted.lean` | 1668 | False | `` | `` | **STATEMENT** |
| S913 | 1 | `S913PaperMonodromyActual.lean` | 4331 | True | `noncomputable def paperQPilotScalar : Real :=` | `noncomputable def paperThetaScalar : Real :=` | **PROVED** |
| S914 | 1 | `S914PaperLVExInstantiationActual.lean` | 3182 | True | `noncomputable def s914R : Set (qVFamTensorBlock T b) :=` | `noncomputable def s914S : Set (qVFamTensorBlock T b) :=` | **PROVED** |
| S915 | 2 | `S915MultiradialHullCompareActualAdapted.lean` | 3863 | False | `noncomputable def paperMultiradialPossibleImageUnion : Set (qVFamTensorBlock T b) :=` | `noncomputable def paperMultiradialHull : Set (qVFamTensorBlock T b) :=` | **INVALID** |
| S916 | 1 | `S916PaperMultiradialSActual.lean` | 4001 | True | `structure PaperIndImageData where` | `noncomputable def paperSImageUnion (D : PaperIndImageData (l := l) T b) :` | **PROVED** |
| S917 | 1 | `S917IndImageUnionActual.lean` | 4122 | True | `theorem currentMultiradialImageUnion_eq_theta :` | `theorem qPilotPaperRegion_subset_thetaImageNZ :` | **PROVED** |
| S918 | 3 | `S918InequalityMeasureActual.lean` | 3165 | True | `theorem s914S_measure_lt_top : mu (s914S (l := l) T b) < ⊤ :=` | `theorem s918RPos_actual : S918RMeasurePosRequired (l := l) T b mu := by` | **PROVED** |
| S919 | 1 | `S919GlobalWeightedInequalityActual.lean` | 3432 | True | `noncomputable def weightedPaperV` | `theorem weightedPaperV_mono` | **PROVED** |
| S920 | 1 | `S920SHullFinitenessActual.lean` | 4651 | True | `abbrev s920O : Set (qVFamTensorBlock T b) :=` | `theorem s920PaperRegion_subset_O (j : SignedLabel l.value) :` | **PROVED** |
| S921 | 1 | `S921RQpilotPaperRegionPositivityActual.lean` | 3747 | True | `theorem s921R_zero_mem : (0 : qVFamTensorBlock T b) ∈ s914R (l := l) T b := by` | `theorem s921R_nonempty : (s914R (l := l) T b).Nonempty :=` | **PROVED** |
| S922 | 1 | `S922ModelHullPaperSHullInequalityActual.lean` | 5312 | True | `abbrev S922O : Set (qVFamTensorBlock T b) :=` | `theorem S922O_closed : IsClosed (S922O (l := l) T b) :=` | **PROVED** |
| S923 | 4 | `S923CheckAdapted.lean` | 223 | False | `` | `` | **AUDIT** |
| S924 | 1 | `S924S918InequalityFixedActual.lean` | 3174 | True | `theorem s924R_measure_pos_of_interior` | `def S924SHullFinite : Prop :=` | **PROVED** |
| S925 | 1 | `S925HullFinitenessActual.lean` | 2774 | True | `theorem s914S_measure_lt_top_actual :` | `theorem paperRootThetaHullNonzero_measure_lt_top :` | **PROVED** |
| S926 | 1 | `S926GlobalIntegrationActual.lean` | 4104 | True | `noncomputable def perBModelLog (b : Bad (nativePlaceSelection T)) : Real :=` | `noncomputable def perBPaperSLog (b : Bad (nativePlaceSelection T)) : Real :=` | **PROVED** |
| S927 | 1 | `S927FinalWeightedInequalityActual.lean` | 3231 | True | `noncomputable def perBVRGlobal (b : Bad (nativePlaceSelection T)) : Real :=` | `noncomputable def perBVSGlobal (b : Bad (nativePlaceSelection T)) : Real :=` | **PROVED** |
| S928 | 2 | `S928ActualIndImageGapActual.lean` | 3204 | True | `structure ActualIndImageData where` | `noncomputable def actualIndImage (D : ActualIndImageData (l := l) T b) :` | **PROVED** |
| S929 | 1 | `S929RQpilotPaperSHullFinalActual.lean` | 3354 | True | `theorem s914R_eq_modelHull :` | `theorem S918RMeasurePosRequired_actual :` | **PROVED** |
| S930 | 2 | `S930GlobalWeightedPaperInequalityActualAdapted.lean` | 2963 | False | `def S930IndImageBounded` | `noncomputable def s930VR (b : Bad (nativePlaceSelection T)) : Real :=` | **INVALID** |
| S931 | 1 | `S931IndImageBoundedActual.lean` | 3008 | True | `theorem indImageBounded_iff :` | `def S931IndImageBoundGap : Prop :=` | **PROVED** |
| S932 | 1 | `S932S918ActualPositivityActual.lean` | 3005 | True | `theorem s914R_measure_pos_actual :` | `theorem s932V_R_le_V_S :` | **PROVED** |
| S934 | 3 | `S934PaperIndImageExactGapActualAdapted.lean` | 2157 | False | `structure PaperIndImageExactGap where` | `def PaperIndImageExactGapRequired : Prop :=` | **INVALID** |
| S936 | 1 | `S936IndImageTransferActual.lean` | 2986 | True | `structure S936IndImageTransferData where` | `def S936IndImageTransferRequired : Prop :=` | **PROVED** |
| S937 | 1 | `S937IndImageActual.lean` | 2481 | True | `theorem s937Ind1Image_nonempty` | `theorem s937Ind2Image_nonempty` | **PROVED** |
| S939 | 2 | `S939PaperSCarrierAuditActualAdapted.lean` | 3943 | False | `abbrev PaperSCarrier (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type uR :=` | `abbrev ModelSCarrier (T : SourceNativeInitialThetaData.{0} l)` | **AUDIT** |
| S940 | 1 | `S940Ind3ImageActual.lean` | 4819 | True | `noncomputable def ind1ImageOfSet` | `theorem ind1ImageOfSet_nonempty` | **PROVED** |
| S941 | 1 | `S941PaperCor312FaithfulContractActual.lean` | 4643 | True | `def PaperCor312FaithfulObject : Prop :=` | `theorem paperCor312_object_actual : PaperCor312FaithfulObject (l := l) T D :=` | **PROVED** |
| S942 | 1 | `S942ActualPaperSInterfaceActual.lean` | 4180 | True | `structure ActualPaperIndImage (D : PaperIndImageData (l := l) T b) where` | `structure ActualPaperSInterface where` | **PROVED** |
| S943 | 1 | `S943ActualIndImageTransferActual.lean` | 3316 | True | `structure ActualIndImageTransfer where` | `def ActualIndImageTransferRequired : Prop :=` | **PROVED** |
| S944 | 1 | `S944PaperSHullFiniteActual.lean` | 3434 | True | `theorem paperSHull_measure_lt_top_perB` | `theorem s934PaperSHullFinite_of_bounded` | **PROVED** |
| S945 | 4 | `S945CheckAdapted.lean` | 451 | False | `` | `` | **AUDIT** |
| S946 | 2 | `S946TensorPaperSContainmentActual.lean` | 3082 | True | `def S946TensorPointwiseImageCondition : Prop :=` | `theorem s946QPilotContainment_iff_pointwise :` | **PROVED** |
| S949 | 1 | `S949PaperQPilotCarrierBridgeActual.lean` | 3674 | True | `structure PaperCarrierAssembly where` | `noncomputable def bridgeOfAssembly (A : PaperCarrierAssembly (T := T) b) :` | **PROVED** |
| S950 | 1 | `S950PaperFaithfulFinalInequalityActual.lean` | 3406 | True | `structure PaperFaithfulFinalData where` | `def PaperFaithfulFinalInequality` | **PROVED** |
| S951 | 1 | `S951ActualIndImageTransferActual.lean` | 5201 | True | `abbrev S951Ind1Carrier (j : Fin (capsuleLevels l)) (vQ : C.VQ)` | `abbrev S951Ind2Carrier (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type :=` | **PROVED** |
| S952 | 1 | `S952IndImageSubsetOActual.lean` | 2638 | True | `def S952IndImageSubsetO : Prop :=` | `theorem s952IndImageSubsetO_iff_bounded :` | **PROVED** |
| S956 | 3 | `S956ClosureContainmentActual.lean` | 2696 | True | `noncomputable def paperTensorSClosure : Set (FinalLValuedCarrier T b) :=` | `def S956ClosureContainment : Prop :=` | **PROVED** |
| S957 | 1 | `S957TensorClosureContainmentActual.lean` | 3075 | True | `noncomputable def paperTensorHull : Set (FinalLValuedCarrier T b) := by` | `def S957ThetaImageDenseInQPilot : Prop :=` | **PROVED** |
| S958 | 1 | `S958ThetaDensityExactActual.lean` | 3484 | True | `theorem s958_density_iff_approximation :` | `def S958DensityExactInput : Prop :=` | **PROVED** |
| S959 | 1 | `S959FinalLValuedTopologyExactActual.lean` | 3462 | True | `def S959FiniteProductTopologyModel : Prop :=` | `def S959FinalLLocallyCompactRequired : Prop :=` | **PROVED** |
| S960 | 1 | `S960PointwiseApproxActual.lean` | 3669 | True | `theorem qPilotPaperRegion_eq_rootThetaRegion_one :` | `theorem qPilotImage_eq_thetaJ1Image :` | **PROVED** |
| S961 | 1 | `S961FinalLTensorLogVolumeFromCarrierTopologyActual.lean` | 3698 | True | `noncomputable def finalLTensorLogVolumeDataOfCarrierTopology` | `noncomputable def carrierTopologyDataOfFinalLTensor` | **PROVED** |
| S962 | 1 | `S962TensorPacketPaperInequalityActual.lean` | 4658 | True | `noncomputable def tensorNormalizedLogVolume` | `theorem tensorNormalizedLogVolume_mono` | **PROVED** |
| S963 | 1 | `S963ActualToBlockProjectionActual.lean` | 4772 | True | `structure S963IndProjectionTriple` | `noncomputable def s963TransferOfProjections` | **PROVED** |
| S964 | 1 | `S964TensorPacketIndBoundedExactActual.lean` | 2246 | True | `structure S964TensorIndBoundedData where` | `def S964TensorIndBoundedRequired : Prop :=` | **PROVED** |
| S965 | 1 | `S965FinalLCarrierTopologyActual.lean` | 3265 | True | `structure S965CarrierLinearization where` | `def S965CarrierLinearizationRequired : Prop :=` | **PROVED** |
| S966 | 1 | `S966ActualToBlockActual.lean` | 4691 | True | `structure S966ToQVFamActual` | `def S966ToQVFamRequired : Prop :=` | **PROVED** |
| S967 | 1 | `S967FinalLIndBoundedActual.lean` | 3266 | True | `noncomputable def finalLUnitRegion : Set (FinalLValuedCarrier T b) :=` | `noncomputable def finalLImageOfQVam (E : Set (qVFamTensorBlock T b)) :` | **PROVED** |
| S968 | 1 | `S968FinalTensorInequalityCor312Actual.lean` | 4606 | True | `noncomputable def s968Inclusion` | `theorem paperCor312_of_tensorInequality` | **PROVED** |
| S969 | 1 | `S969IndCarrierEmbeddingActual.lean` | 4948 | True | `structure S969IndCarrierEmbeddingData` | `noncomputable def s969ProjectionTriple_of_embeddings` | **PROVED** |
| S970 | 1 | `S970FiniteLogShellCarrierActual.lean` | 2481 | True | `abbrev FiniteLogShellCarrier (p : Nat) [Fact p.Prime] (d : Nat) : Type :=` | `structure FiniteLogShellHaarData (d : Nat) where` | **PROVED** |
| S971 | 1 | `S971TensorRegionImageActual.lean` | 3711 | True | `noncomputable def tensorThetaRegionImage : Set (FinalLValuedCarrier T b) :=` | `noncomputable def tensorThetaRegionIndUnion : Set (FinalLValuedCarrier T b) :=` | **PROVED** |
| S972 | 1 | `S972IndAdditiveEmbeddingConditionsActual.lean` | 5216 | True | `structure S972IndAdditiveEmbeddingConditions` | `noncomputable def s972EmbeddingData_of_conditions` | **PROVED** |
| S973 | 1 | `S973QPilotTensorImagePositivityActual.lean` | 4936 | True | `def S973QPilotImageInteriorNonempty : Prop :=` | `theorem s973QPilotImage_measure_pos_of_interior` | **PROVED** |
| S974 | 1 | `S974TensorHullFiniteActual.lean` | 2351 | True | `def S974HullSubsetUnitRegion : Prop :=` | `theorem paperTensorHull_measure_lt_top_of_subset` | **PROVED** |
| S975 | 1 | `S975DensityRegionImageActual.lean` | 3416 | True | `noncomputable def rootThetaRegionImageInLValued` | `noncomputable def paperPossibleRegionImageUnion` | **PROVED** |
| S976 | 1 | `S976FiniteLogShellHaarActual.lean` | 3166 | True | `noncomputable def finiteLogShellHaarData (d : Nat) :` | `theorem finiteLogShellHaarRequired (d : Nat) :` | **PROVED** |
| S977 | 1 | `S977ActualIndImageDataFromEmbeddingsActual.lean` | 2793 | True | `theorem s928ActualIndImageData_nonempty_of_embeddings` | `def S977ExactRequirement : Prop :=` | **PROVED** |
| S978 | 1 | `S978FiniteCarrierHullActual.lean` | 3743 | True | `noncomputable def finitePossibleRegionImageUnion :` | `noncomputable def finitePaperTensorHull :` | **PROVED** |
| S979 | 1 | `S979TensorRegionHullInequalityActual.lean` | 6263 | True | `noncomputable def tensorRegionHullLog` | `theorem qPilotTensorLog_le_tensorRegionHullLog` | **PROVED** |
| S980 | 1 | `S980QPilotImagePositivityActual.lean` | 3673 | True | `theorem s980QPilotRegion_measure_pos_of_open` | `theorem s980FiniteLogShell_unit_pos (p d : Nat) [Fact p.Prime] :` | **PROVED** |
| S981 | 1 | `S981TensorRegionHullFiniteActual.lean` | 3889 | True | `def S981TensorRegionHullSubsetUnitRegion : Prop :=` | `theorem tensorRegionHull_measure_lt_top_of_subset` | **PROVED** |
| S982 | 1 | `S982FinalLTensorFromFiniteQuotientActual.lean` | 3240 | True | `structure S982FiniteQuotientBridge where` | `def S982FiniteQuotientBridgeRequired : Prop :=` | **PROVED** |
| S983 | 1 | `S983PaperXiFSourceLinkConstructionActual.lean` | 4249 | True | `noncomputable def paperXiFSourceLinkOfActualTheta` | `theorem paperXiFSourceLinkOfActualTheta_link_identification` | **PROVED** |
| S984 | 1 | `S984FiniteQuotientBridgeActual.lean` | 2781 | True | `def S984FiniteFreeCondition : Prop :=` | `abbrev S984FiniteQuotientBridge : Type :=` | **PROVED** |
| S985 | 1 | `S985FinalExactAssemblyActual.lean` | 3329 | True | `structure S985FinalExactInputs where` | `theorem s979Hypotheses_of_finalInputs` | **PROVED** |
| S986 | 1 | `S986FiniteQuotientTransportActual.lean` | 3125 | True | `structure S986TransportObligations where` | `def S986TransportObligationsRequired : Prop :=` | **PROVED** |
| S987 | 1 | `S987FiniteQuotientTransportActual.lean` | 5238 | False | `noncomputable def carrierTopologyDataOfLinearization` | `noncomputable def finalLTensorLogVolumeDataOfLinearization` | **INVALID** |
| S988 | 11 | `S988ExactProbeAdapted.lean` | 1539 | False | `structure Data where` | `` | **AUDIT** |
| S989 | 1 | `S989FiniteCarrierDirectActual.lean` | 4659 | True | `noncomputable def finitePaperTensorData (d : Nat) :` | `noncomputable def finiteQPilotImage` | **PROVED** |
| S990 | 1 | `S990FiniteCarrierPositivityFinitenessActual.lean` | 4974 | True | `noncomputable def finiteCarrierUnitRegion (d : Nat) :` | `theorem finiteCarrierUnitRegion_pos (d : Nat) :` | **PROVED** |
| S991 | 1 | `S991S983LinkInputsActual.lean` | 4110 | True | `theorem s991SourceIdentifications :` | `theorem s991SignedQIdentification` | **PROVED** |
| S992 | 1 | `S992FinalIntegrationActual.lean` | 6199 | True | `theorem s992S979Hypotheses` | `noncomputable def s992ConcreteLink` | **PROVED** |
| S994 | 1 | `S994FiniteCarrierCor312Actual.lean` | 5606 | True | `structure S994FiniteLinearization where` | `noncomputable def s994ActualLinearization : S994FiniteLinearization T b where` | **PROVED** |
| S995 | 1 | `S995FiniteCarrierCor312ConclusionActual.lean` | 5318 | True | `theorem s995FiniteCarrierCor312Conclusion` | `theorem s995Cor312Conclusion` | **PROVED** |
| S996 | 1 | `S996FiniteQuotientLinearizationActual.lean` | 3410 | True | `noncomputable def s996QVFamLinearization :` | `def S996FinalLValuedFiniteModuleRequired : Prop :=` | **PROVED** |
| S997 | 1 | `S997FiniteQPilotPositivityActual.lean` | 3768 | True | `def S997UnitRegionSubsetQPilot` | `theorem s997QPilotImage_measure_pos_of_unitRegion_subset` | **PROVED** |
| S998 | 1 | `S998FinitePaperHullFinitenessActual.lean` | 4077 | True | `def S998FiniteHullSubsetUnitRegion : Prop :=` | `theorem finitePaperHull_measure_lt_top_of_subset` | **PROVED** |
| S999 | 1 | `S999HQHC3Actual.lean` | 3152 | True | `def S999LineC3Identification : Prop :=` | `def S999QPilotLogVolumeIdentification : Prop :=` | **PROVED** |
| S1000 | 1 | `S1000FinalCor312AssemblyActual.lean` | 5113 | True | `structure S1000FinalInputs where` | `theorem s1000FinalCor312` | **PROVED** |

## 红/GAP 明细（无 olean 或含 sorry/axiom）

```
S2  S2lNormalizationActual.lean  size=1807  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperThetaValueFromQParameter
S151  S151PaperNormalizationChoiceActualAdapted.lean  size=7526  olean=False  sorry=False  verdict=INVALID  decl1=theorem paperNormalizedCoefficient_eq_order_mul_rationalDegree
S176  S176QPilotObjectImageActualAdapted.lean  size=6410  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def qPilotMultiradialActualHaarFamily :
S273  S273QPilotTransportedHaarActual.lean  size=6411  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def s191BlockCLE (b : Bad (nativePlaceSelection T)) :
S281  S281QPilotTransportedHaarActualAdapted.lean  size=5991  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def s191ProductContinuousAddEquiv :
S285  S285QPilotProductCAEActualAdapted.lean  size=3060  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def s191ProductContinuousAddEquiv :
S297  S297QPilotProductHaarActualAdapted.lean  size=4134  olean=False  sorry=False  verdict=INVALID  decl1=theorem s191FiberType_eq (b : Bad (nativePlaceSelection T)) :
S311  S311RootLValuedK0CarrierActual.lean  size=2516  olean=False  sorry=False  verdict=INVALID  decl1=abbrev RootLValuedCarrierK0 : Type :=
S366  S366OneColumnActualAdapted.lean  size=2103  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def oneColumnLocalField : NativePlaces P.X.S -> Type :=
S503  S503QvPhiModelActualAdapted.lean  size=2071  olean=False  sorry=False  verdict=INVALID  decl1=structure QvGeneratedPhiPaperData where
S505  S505QvPhiGeneratorActualAdapted.lean  size=2873  olean=False  sorry=False  verdict=INVALID  decl1=abbrev QvK : Type := NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b)
S513  S513DvPhiCvCandidateActualAdapted.lean  size=3029  olean=False  sorry=False  verdict=INVALID  decl1=abbrev DvPhiBase : Type := Example32SmallBase T.arithmetic.K
S536  S536Example32AlignedNaturalityFinalActualAdapted.lean  size=1975  olean=False  sorry=False  verdict=INVALID  decl1=theorem example32AlignedDivisor_naturality
S590  S590EvalActualAdapted.lean  size=2147  olean=False  sorry=False  verdict=STATEMENT  decl1=
S608  S608QOrderDivisibilityLawsActualAdapted.lean  size=4356  olean=False  sorry=False  verdict=INVALID  decl1=abbrev qvPi := qOrderEndomorphism (K := K) T b P A
S616  S616ModelPaperAlignmentActualAdapted.lean  size=1917  olean=False  sorry=False  verdict=INVALID  decl1=def s616ModelBaseEquiv : Example32SmallBase K ≌ Example32SmallBase K :=
S617  S617SpecialFiberOriginActual.lean  size=1862  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def specialFiberOrigin (W : WeierstrassCurve R) :
S618  S618KSideQVPlaceActualAdapted.lean  size=2792  olean=False  sorry=False  verdict=INVALID  decl1=theorem place_eq_imp_shadow_eq
S619  S619IdentityTauUnitsCommuteActualAdapted.lean  size=4419  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def s619IdentityTau
S620  S620FinalContractActualAdapted.lean  size=4733  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def sourceQSigned : Real :=
S621  S621ConcreteComparisonMinimalGapActualAdapted.lean  size=2431  olean=False  sorry=False  verdict=INVALID  decl1=theorem obstacle_iff_badQAbsLog :
S622  S622FinalNumericInequalityActualAdapted.lean  size=2410  olean=False  sorry=False  verdict=INVALID  decl1=def FinalNumericInequality : Prop :=
S624  S624FinalConcreteSourceComparisonGapActualAdapted.lean  size=3370  olean=False  sorry=False  verdict=INVALID  decl1=theorem concreteSourceComparisonObstacle_iff_gaussSum_le_badQAbsLog
S625  S625FinalConditionalPackageActualAdapted.lean  size=3387  olean=False  sorry=False  verdict=INVALID  decl1=structure FinalConcreteComparisonPackage where
S628  S628PaperXiFSourceLinkConstructionActualAdapted.lean  size=6166  olean=False  sorry=False  verdict=INVALID  decl1=def ConcreteSourceQIdentification
S633  S633ThetaPacketQMagnitudeActualAdapted.lean  size=3156  olean=False  sorry=False  verdict=INVALID  decl1=theorem paperQPilotLogMagnitude_eq_qPilotLogMagnitude
S637  S637ActualPaperXiFBridgeActualAdapted.lean  size=3466  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def actualThetaLinkOfBridge :
S638  S638ActualToPaperXiFSourceLinkActualAdapted.lean  size=1998  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperXiFSourceLinkOfActual :
S640  S640PaperRootThetaProcessionActualAdapted.lean  size=4158  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def processionSignedLabel (x : ProcessionLabel l) : SignedLabel l.value :=
S642  S642PaperRootThetaProcessionActualAdapted.lean  size=3573  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperRootThetaWeight : Real :=
S644  S644PaperRootThetaProcessionActualAdapted.lean  size=4511  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperThetaLogMagnitude
S645  S645RootNormalizedPaperSignedHullActualAdapted.lean  size=3882  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def rootThetaSignedProcession :
S650  S650ActualSignedCor312ContractAdapted.lean  size=2763  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def s650ActualSignedContract : StepXIContract :=
S660  S660ConcreteSourceComparisonObstacleActualAdapted.lean  size=4032  olean=False  sorry=False  verdict=INVALID  decl1=def ConcreteSourceComparisonScalarGap : Prop :=
S673  S673QPilotRootImageContainmentActualAdapted.lean  size=2297  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def qPilotImageInRootExtension : Set (rootNormedExtension T b) :=
S703  S703GlobalPaperThetaComparisonActualAdapted.lean  size=4776  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperThetaPositiveLabel (i : Fin (lStar l.value)) :
S719  S719PaperRootHullGapDecompositionActualAdapted.lean  size=2850  olean=False  sorry=False  verdict=INVALID  decl1=structure PaperRootHullScalingDataGap (b : Bad (nativePlaceSelection T)) where
S726  S726PaperHullVsS663GapActualAdapted.lean  size=4600  olean=False  sorry=False  verdict=INVALID  decl1=theorem paperPerBThetaHullLog_nonpos :
S729  S729PaperSignedHullActualHullLogActualAdapted.lean  size=5353  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperThetaProcession (A : Real) :
S730  S730PaperRootCarrierActualAdapted.lean  size=6375  olean=False  sorry=False  verdict=GAP  decl1=theorem root_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}
S737  S737PaperCoefficientBridgeCorrectionActualAdapted.lean  size=2031  olean=False  sorry=False  verdict=INVALID  decl1=def UnconditionalCoefficientBridgeCorrection : Prop :=
S738  S738QVFamBlockAlignmentActualAdapted.lean  size=2810  olean=False  sorry=False  verdict=INVALID  decl1=def CommonPrimeNormalizedLatticeAlignment : Prop :=
S739  S739PaperOrderThetaHullActualAdapted.lean  size=3646  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperPerBThetaHullLogPaperOrder : Real :=
S742  S742SpectralOrderFactorActualAdapted.lean  size=3926  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperOrderCoefficient : Real :=
S743  S743PaperSignedHullPaperOrderActualAdapted.lean  size=7868  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperOrderThetaHullLog : Real :=
S744  S744PaperOrderReplacementActualAdapted.lean  size=3439  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperPerBThetaHullLogPaperOrder : Real :=
S745  S745PaperRootHullNonzeroCorrectionActualAdapted.lean  size=5469  olean=False  sorry=False  verdict=INVALID  decl1=theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :
S754  S754CandidateRootsTorsorActual.lean  size=2953  olean=False  sorry=False  verdict=INVALID  decl1=theorem candidateRoots_ne_zero (r : CandidateRoots T b) : r.1 ≠ 0 := by
S763  S763QPilotRootStackKummerActual.lean  size=3516  olean=False  sorry=False  verdict=INVALID  decl1=def qPilotScalingLog : Real :=
S765  S765CompletionValueGroupObstructionActual.lean  size=2056  olean=False  sorry=False  verdict=INVALID  decl1=theorem twoL_mul_valuation_eq_order_implies_dvd
S769  S769StackyLogVolumeNormalizationActual.lean  size=3714  olean=False  sorry=False  verdict=INVALID  decl1=theorem stackyMuCard :
S772  S772QVFamBlockMapsLatticeActual.lean  size=4408  olean=False  sorry=False  verdict=INVALID  decl1=def PureTensorFractionalLatticeImage : Prop :=
S792  S792RootStackPaperHullRebaseActualAdapted.lean  size=3246  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperRootHullLogRebased : Real :=
S802  S802QVFamBlockMapsLatticeActualAdapted.lean  size=3597  olean=False  sorry=False  verdict=INVALID  decl1=theorem pureTensor_mem_fractionalLattice
S807  S807CancellationNoGoActual.lean  size=6663  olean=False  sorry=True  verdict=GAP  decl1=theorem norm_add_eq_left_of_norm_lt {x y : K} (h : ‖y‖ < ‖x‖) :
S822  S822StackyCardActualAdapted.lean  size=3093  olean=False  sorry=False  verdict=INVALID  decl1=theorem stackMuUnit_isPrimitiveRoot :
S828  S828PaperRootValueGroupActualAdapted.lean  size=3210  olean=False  sorry=False  verdict=INVALID  decl1=def PaperRootValueGroupDivisibility : Prop :=
S829  S829PaperNormValuationSpectralActual.lean  size=3482  olean=False  sorry=False  verdict=INVALID  decl1=theorem paperGeneralNormalizedNormFormula
S892  S892RootStackGeneralNormFormulaActualAdapted.lean  size=3060  olean=False  sorry=False  verdict=INVALID  decl1=theorem rootStackNormExtensionFormula_actual :
S896  S896NonzeroPerBCorrectedActualAdapted.lean  size=5094  olean=False  sorry=False  verdict=INVALID  decl1=def ClosedInput (b : Bad (nativePlaceSelection T)) : Prop :=
S900  S900PerBThetaHullLogNonzeroActualAdapted.lean  size=4642  olean=False  sorry=False  verdict=INVALID  decl1=theorem rootMinimalRegion_closed :
S904  S904PaperCor312ScalingActualAdapted.lean  size=4239  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def s904PaperGap
S912  S912RootStackNormedAlgebraActualAdapted.lean  size=1668  olean=False  sorry=False  verdict=STATEMENT  decl1=
S915  S915MultiradialHullCompareActualAdapted.lean  size=3863  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def paperMultiradialPossibleImageUnion : Set (qVFamTensorBlock T b) :=
S930  S930GlobalWeightedPaperInequalityActualAdapted.lean  size=2963  olean=False  sorry=False  verdict=INVALID  decl1=def S930IndImageBounded
S934  S934PaperIndImageExactGapActualAdapted.lean  size=2157  olean=False  sorry=False  verdict=INVALID  decl1=structure PaperIndImageExactGap where
S987  S987FiniteQuotientTransportActual.lean  size=5238  olean=False  sorry=False  verdict=INVALID  decl1=noncomputable def carrierTopologyDataOfLinearization
S21  S21fSourceTheaterFieldComparisonActual.lean  size=3816  olean=True  sorry=True  verdict=GAP  decl1=abbrev fieldI : OriginalInput l (NativePlaces X.S) :=
S40  S40SourceTheaterFieldMapDirectActual.lean  size=4941  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def sourceFieldMap :
S51  S51DecorationWrapperActual.lean  size=3459  olean=True  sorry=True  verdict=GAP  decl1=inductive Decoration where
S54  S54DecorationAssignmentActual.lean  size=3657  olean=True  sorry=True  verdict=GAP  decl1=inductive SourceConsumer where
S56  S56OTriangularCarrierActual.lean  size=3161  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def oTriangularMonoid :
S60  S60OTriangleBoundaryActual.lean  size=3251  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def oBoundaryMonoid :
S63  S63OBoundaryLogShellActual.lean  size=3434  olean=True  sorry=True  verdict=GAP  decl1=theorem sourceLogShellUnits_eq_integralUnits :
S77  S77CompletionIntegersEquivActual.lean  size=2479  olean=True  sorry=True  verdict=GAP  decl1=def completionIntegersCarrierEq : Prop :=
S79  S79IntegralRingEquivActual.lean  size=2405  olean=True  sorry=True  verdict=GAP  decl1=theorem completionIntegersCarrierEq_holds :
S87  S87OBoundaryDecompositionActual.lean  size=5156  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def dvrUniformizer : Integers (CommonPrimeCompletion place) := by
S93  S93BoundaryLogCompatibilityActual.lean  size=4072  olean=True  sorry=True  verdict=GAP  decl1=theorem boundaryLogWith_unit
S101  S101UniformizerChangeActual.lean  size=5237  olean=True  sorry=True  verdict=GAP  decl1=structure OBoundaryUnitDecompFor
S104  S104CanonicalLogPiActual.lean  size=2743  olean=True  sorry=True  verdict=GAP  decl1=theorem boundaryLogWithFor_logPi_difference
S111  S111FormalBoundaryLogActual.lean  size=9838  olean=True  sorry=True  verdict=GAP  decl1=theorem boundaryUnitDecomposition_unique
S126  S126FormalBoundaryLogUseActual.lean  size=3685  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def logShellLogFormal
S132  S132FormalLogVolumeActual.lean  size=5239  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def boundaryLogNormalized
S142  S142NormalizedBoundaryLogVolumeActual.lean  size=5602  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def boundaryLogVolumeNormalized
S143  S143dQuotientLogVolumeActual.lean  size=3576  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def unitLogRange :
S148  S148QuotientLogVolumeSourceActual.lean  size=5294  olean=True  sorry=True  verdict=GAP  decl1=theorem boundaryLogFormalFor_dvr_eq
S150  S150SourceLogVolumeNormalizationActual.lean  size=5373  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def sourceLogVolumeScale :
S157  S157ThetaRootCorrectionActual.lean  size=2092  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def paperRootThetaPower
S185  S185HaarRootThetaActual.lean  size=5415  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def completionAddHaar :
S194  S194RootThetaNormActual.lean  size=3802  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def rootThetaNorm
S201  S201RootThetaNormLActual.lean  size=4273  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def rootNormedElementNorm : Real :=
S275  S275HaarFactorIsometryActual.lean  size=2089  olean=True  sorry=True  verdict=GAP  decl1=structure BlockRootHaarFactorComparison (lam : (rootNormedExtension T b)ˣ) where
S278  S278HaarFactorConjugacyActual.lean  size=3542  olean=True  sorry=True  verdict=GAP  decl1=theorem image_blockScaling_unitBall
S288  S288ThetaScalingHaarFactorActual.lean  size=5220  olean=True  sorry=True  verdict=GAP  decl1=theorem rootNormedUnitBall_eq_rootExtensionUnitBall :
S290  S290BlockHaarFactorActual.lean  size=2838  olean=True  sorry=True  verdict=GAP  decl1=theorem thetaScalingHaarFactor_uniformizer_eq_norm_pow :
S300  S300GeneralFactorNormActual.lean  size=3666  olean=True  sorry=True  verdict=GAP  decl1=theorem exists_unit_uniformizer_zpow
S730  S730PaperRootCarrierActualAdapted.lean  size=6375  olean=False  sorry=False  verdict=GAP  decl1=theorem root_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}
S732  S732NCGLogVolumeNoGo.lean  size=10922  olean=True  sorry=False  verdict=GAP  decl1=structure PaperLogVolume (Region : Type*) where
S807  S807CancellationNoGoActual.lean  size=6663  olean=False  sorry=True  verdict=GAP  decl1=theorem norm_add_eq_left_of_norm_lt {x y : K} (h : ‖y‖ < ‖x‖) :
S814  S814SkeletonQuantizedLeastHullActual.lean  size=18533  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def valueGroupSkeletonLength (c : Real) : Real :=
S824  S824RootStackyHaarVolumeActual.lean  size=20475  olean=True  sorry=True  verdict=GAP  decl1=noncomputable def stackMuElem : rootStackExtension T b :=
S827  S827PaperValueGroupNormCardActual.lean  size=3129  olean=True  sorry=False  verdict=GAP  decl1=abbrev paperValueGroupPlace : NumberField.FinitePlace T.arithmetic.F :=
```

## 关键定理名（每组 decl1/decl2 摘要）

见上表 `声明1`/`声明2` 列；这是每组最新文件的**前两条声明**（不保证是该组最重要定理）。

## 关键残余（审计结论）

1. 本审计是**无遗漏登记**（578 组/755 文件），不是质量验证；olean 存在性来自仓内文件，未重新编译。
2. 红/GAP 组见上节；这些是当前首查对象，需 mainline/watchdog 以真实编译确认。
3. 组内多文件时只登记最新文件；同组旧文件（如 Adapted/_DRAFT）未逐条列出，如需全文件级审计需另跑清单。
4. 判定为启发式：`PROVED` 仅表示 olean 存在且文本无 sorry/axiom，不能替代 kernel 检查。
5. UNKNOWN：个别文件可能 import 失败但 olean 残留；需以 watchdog 重编结果为准。

## 全量 TSV（机器可读）

```tsv
num	count	name	size	olean	decl1	decl2	verdict	sorry	red
100	1	S100QVFamNormInstanceGapActual.lean	4867	True	theorem qVFamNormInstanceGap_iff_paperCoefficient_eq_cNorm	theorem qVFamNormRatio_ne_one_of_coefficient_ne	PROVED	False	no
1000	1	S1000FinalCor312AssemblyActual.lean	5113	True	structure S1000FinalInputs where	theorem s1000FinalCor312	PROVED	False	no
101	1	S101UniformizerChangeActual.lean	5237	True	structure OBoundaryUnitDecompFor	noncomputable def boundaryUnitDecompositionFor	GAP	True	no
104	1	S104CanonicalLogPiActual.lean	2743	True	theorem boundaryLogWithFor_logPi_difference	def candidateLog1pPi : CommonPrimeCompletion place :=	GAP	True	no
109	1	S109QVFamNormValueActual.lean	5672	True	theorem qVFamDefaultNorm_eq_residueNormBase_zpow	theorem qVFamNormalizedNorm_eq_p_zpow_neg_coefficient	PROVED	False	no
111	1	S111FormalBoundaryLogActual.lean	9838	True	theorem boundaryUnitDecomposition_unique	noncomputable def boundaryLogFormal	GAP	True	no
118	1	S118QVFamNormRatioValueActual.lean	4584	True	theorem qVFamTensorPlace_residueNormBase_eq_lower_pow	theorem qVFamNormRatio_eq_p_div_rationalBase	PROVED	False	no
12	1	S12CompletionGeometryBridgeActual.lean	4731	True	noncomputable def fixedToDependent [Fintype V]	def commonPrimeIndex (D : DependentCompletionValuedGeometry K) (p : Nat) : Type :=	PROVED	False	no
120	1	S120QVFamWeightedValuationConditionActual.lean	5704	True	theorem qVFamNormalizedCoefficient_eq_neg_logb_norm	theorem weightedValuationCondition_iff_coefficient_eq_exponent_mul_degree	PROVED	False	no
121	1	S121QVFamSpectralValuationActual.lean	6452	True	theorem qVFamNormalizedCoefficient_eq_exponent_mul_degree_sub_logRatio	theorem qVFamNormalizedCoefficient_eq_exponent_mul_degree_iff	PROVED	False	no
126	1	S126FormalBoundaryLogUseActual.lean	3685	True	noncomputable def logShellLogFormal	theorem boundaryLogFormal_agrees_logShellLog	GAP	True	no
132	1	S132FormalLogVolumeActual.lean	5239	True	noncomputable def boundaryLogNormalized	noncomputable def boundaryLogInteger	GAP	True	no
134	1	S134ActualPaperTargetCorrectionActual.lean	7659	True	theorem log_normRatio_eq_spectralGap	theorem normRatioCorrectionSum_eq_spectralGapSum	PROVED	False	no
137	1	S137PaperTargetCorrectionStatusActual.lean	7390	True	def IntermediateActualPaperTargetUpToNormRatioCorrection : Prop :=	theorem intermediateTarget_iff_paperComparison :	AUDIT	False	no
142	1	S142NormalizedBoundaryLogVolumeActual.lean	5602	True	noncomputable def boundaryLogVolumeNormalized	noncomputable def sourceLogShellLog	GAP	True	no
143	1	S143dQuotientLogVolumeActual.lean	3576	True	noncomputable def unitLogRange :	theorem unitLog_mem_range	GAP	True	no
145	1	S145NormRatioCorrectionZeroActual.lean	7378	True	noncomputable def normRatioSpectralGap	theorem normRatioCorrectionSum_eq_weighted_spectralGap	PROVED	False	no
148	1	S148QuotientLogVolumeSourceActual.lean	5294	True	theorem boundaryLogFormalFor_dvr_eq	noncomputable def sourceLogShellNormalizedQuot	GAP	True	no
150	1	S150SourceLogVolumeNormalizationActual.lean	5373	True	noncomputable def sourceLogVolumeScale :	noncomputable def sourceLogShellNormalizedMap	GAP	True	no
151	2	S151PaperNormalizationChoiceActualAdapted.lean	7526	False	theorem paperNormalizedCoefficient_eq_order_mul_rationalDegree	theorem paperNormalizedCoefficient_eq_exponent_mul_rationalDegree	INVALID	False	yes
154	1	S154PaperNormalizedQUnitActual.lean	4389	True	noncomputable def qVFamNormalizedQPilotLog : Real :=	theorem perBQPilotLog_eq_neg_cNorm_mul_logp	PROVED	False	no
155	2	S155FrozenTargetStatusActualAdapted.lean	5922	False	noncomputable def classicalPaperQPilotMagnitude : Real :=	theorem classicalPaperQPilotMagnitude_eq :	AUDIT	False	no
156	1	S156QPilotSideObjectActual.lean	5332	True	noncomputable def QPilotQParameter	noncomputable def QPilotImagePoint : DependentCompletionProduct T :=	PROVED	False	no
157	1	S157ThetaRootCorrectionActual.lean	2092	True	noncomputable def paperRootThetaPower	theorem paperRootThetaPower_pow_twoL	GAP	True	no
172	1	S172QPilotMultiradialImageActual.lean	7902	True	abbrev QPilotMultiradialFiber	abbrev QPilotMultiradialCarrier : Type :=	PROVED	False	no
176	2	S176QPilotObjectImageActualAdapted.lean	6410	False	noncomputable def qPilotMultiradialActualHaarFamily :	noncomputable def qPilotMultiradialAmbientHaarActual :	INVALID	False	yes
178	1	S178QPilotObjectFullActual.lean	4405	True	noncomputable def qPilotImageHaarFamily :	noncomputable def qPilotImageObject :	PROVED	False	no
185	1	S185HaarRootThetaActual.lean	5415	True	noncomputable def completionAddHaar :	noncomputable def nonunitHaarMeasure :	GAP	True	no
186	1	S186QPilotIndBaseChangeActual.lean	4557	True	abbrev QPilotMultiradialSourceQTensorCarrier : Type :=	noncomputable def QPilotMultiradialToSourceQTensor :	PROVED	False	no
191	1	S191QPilotCarrierTransportActual.lean	6165	True	abbrev s191TensorFamily (b : Bad (nativePlaceSelection T)) : PUnit.{1} → Type :=	noncomputable def s191BlockEquiv (b : Bad (nativePlaceSelection T)) :	PROVED	False	no
194	1	S194RootThetaNormActual.lean	3802	True	noncomputable def rootThetaNorm	theorem rootThetaNorm_pos	GAP	True	no
2	1	S2lNormalizationActual.lean	1807	False	noncomputable def paperThetaValueFromQParameter	theorem paperThetaValueFromQParameter_pos	INVALID	False	yes
201	1	S201RootThetaNormLActual.lean	4273	True	noncomputable def rootNormedElementNorm : Real :=	theorem rootNormedElementNorm_pow_twoL :	GAP	True	no
21	6	S21fSourceTheaterFieldComparisonActual.lean	3816	True	abbrev fieldI : OriginalInput l (NativePlaces X.S) :=	theorem fieldI_fmod_eq :	GAP	True	no
214	3	S214ProbeAdapted.lean	173	False			AUDIT	False	no
22	1	S22DependentProductActual.lean	12598	True	abbrev DependentCompletion (b : Bad (nativePlaceSelection T)) : Type :=	abbrev DependentCompletionProduct : Type :=	PROVED	False	no
227	3	S227ProbeAdapted.lean	145	False			AUDIT	False	no
232	1	S232QPilotHaarTransportActual.lean	5132	True	theorem QPilotImagePoint_eq_dependentQVFamProductPoint :	theorem s156ProductToBlock_QPilotImagePoint :	PROVED	False	no
234	1	S234QPilotHaarNormalizationActual.lean	2753	True	noncomputable def haarNormalizationFactor : ℝ≥0 :=	theorem haarNormalizationFactor_spec : μ' = (haarNormalizationFactor μ' μ) • μ :=	PROVED	False	no
237	1	S237SourceHullProperActual.lean	4084	True	theorem sourceQTensorLambdaOHull_compact :	noncomputable def sourceQTensorHullHaar : Measure (SourceQTensorBlock T b) :=	PROVED	False	no
238	1	S238ProductTensorHullHaarActual.lean	3652	True	noncomputable def productBlockHaar :	noncomputable def productRootNormedHaar :	PROVED	False	no
239	1	S239ProductHaarScalarActual.lean	1701	True	structure ProductHaarScalarGap where	def ProductHaarScalarGapRequired : Prop :=	PROVED	False	no
241	1	S241SourceHullNoncompactActual.lean	2248	True	theorem sourceQTensorBlock_noncompactSpace :	theorem sourceQTensorLambdaOHull_ne_univ_unconditional :	PROVED	False	no
245	1	S245SourceHullMeasureActual.lean	6237	True	theorem sourceQTensorLambdaOHull_eq_unit_smul :	theorem sourceQTensorLambdaOHull_isOpen :	PROVED	False	no
247	1	S247QPilotHaarInstancesActual.lean	3758	True			PROVED	False	no
255	6	S255ProbeAdapted.lean	236	False			AUDIT	False	no
264	3	S264ProbeAdapted.lean	108	False			AUDIT	False	no
273	1	S273QPilotTransportedHaarActual.lean	6411	False	noncomputable def s191BlockCLE (b : Bad (nativePlaceSelection T)) :	noncomputable def s191ProductContinuousAddEquiv :	INVALID	False	yes
275	1	S275HaarFactorIsometryActual.lean	2089	True	structure BlockRootHaarFactorComparison (lam : (rootNormedExtension T b)ˣ) where	def BlockRootHaarFactorComparisonRequired	GAP	True	no
278	1	S278HaarFactorConjugacyActual.lean	3542	True	theorem image_blockScaling_unitBall	structure BlockRootHaarFactorEqualityGap	GAP	True	no
280	1	S280QPilotBlockCLEActual.lean	3019	True	noncomputable def s191BlockCLE (b : Bad (nativePlaceSelection T)) :		PROVED	False	no
281	2	S281QPilotTransportedHaarActualAdapted.lean	5991	False	noncomputable def s191ProductContinuousAddEquiv :	noncomputable def qPilotHaarNormalizationFactorConcrete : ℝ≥0 :=	INVALID	False	yes
284	1	S284RootUniformizerFactorActual.lean	3466	True	theorem rootHaarFactor_uniformizer_eq_norm_pow :		PROVED	False	no
285	2	S285QPilotProductCAEActualAdapted.lean	3060	False	noncomputable def s191ProductContinuousAddEquiv :		INVALID	False	yes
288	1	S288ThetaScalingHaarFactorActual.lean	5220	True	theorem rootNormedUnitBall_eq_rootExtensionUnitBall :	theorem blockHaar_map_eq_rootNormedHaar :	GAP	True	no
289	1	S289SourceHullConcreteHaarActual.lean	4149	True	noncomputable def concreteSourceQTensorHullMuLog : ENNReal :=	theorem concreteSourceQTensorHullMuLog_eq_ofReal_log :	PROVED	False	no
290	1	S290BlockHaarFactorActual.lean	2838	True	theorem thetaScalingHaarFactor_uniformizer_eq_norm_pow :	theorem thetaScalingHaarFactor_prime_eq_norm_pow :	GAP	True	no
294	1	S294SourceHullNormalizedLogActual.lean	8422	True	noncomputable def sourceQTensorUnitReferenceMass : ENNReal :=	noncomputable def sourceQTensorHullMass : ENNReal :=	PROVED	False	no
295	5	S295Probe2Adapted.lean	94	False			AUDIT	False	no
296	1	S296BlockScaledHullLogActual.lean	7105	True	theorem blockScaledRegion_eq_scaling_image	theorem blockScaledRegionMeasure_eq_thetaScalingHaarFactor	PROVED	False	no
297	2	S297QPilotProductHaarActualAdapted.lean	4134	False	theorem s191FiberType_eq (b : Bad (nativePlaceSelection T)) :	noncomputable def s191DepCastCLE (b : Bad (nativePlaceSelection T)) :	INVALID	False	yes
300	1	S300GeneralFactorNormActual.lean	3666	True	theorem exists_unit_uniformizer_zpow	structure RootHaarFactorNormPowGap where	GAP	True	no
301	1	S301GlobalThetaHullLogActual.lean	6340	True	noncomputable def globalSourceHullNormalizedLog : Real :=	theorem globalSourceHullNormalizedLog_eq :	PROVED	False	no
302	1	S302ComparisonReadySourcePairActual.lean	6219	True	noncomputable def thetaSideOfPair : GlobalSourceThetaHullLogObject T :=	noncomputable def qPilotSideOfPair : QPilotHaarTransportActual T :=	PROVED	False	no
304	7	S304Probe2Adapted.lean	126	False			AUDIT	False	no
305	1	S305SingleLambdaNormActual.lean	2422	True	theorem rootNormedElementNorm_pow_twoL_eq_qVFamNormalizedNorm :	theorem singleLambda_norm_eq_rootNorm_pow :	PROVED	False	no
307	1	S307QPilotThetaCarrierActual.lean	3180	True	noncomputable def qPilotBlockPoint : qVFamTensorBlock T b :=	noncomputable def qPilotRootLImagePoint : RootLValuedCarrier T b :=	PROVED	False	no
308	1	S308SameCarrierPairActual.lean	5757	True	abbrev RootLProductCarrier : Type :=	noncomputable def qPilotToRootLCarrier :	PROVED	False	no
309	1	S309RootTensorSameCarrierAuditActual.lean	7765	True	abbrev ThetaRootTensorProductCarrier : Type :=	noncomputable def thetaRootTensorProductHull :	AUDIT	False	no
310	1	S310CompletionSameCarrierPairActual.lean	6046	True	abbrev CompletionRootDataFamily : Type :=	def CompletionRootSystemExistenceGap : Prop :=	PROVED	False	no
311	1	S311RootLValuedK0CarrierActual.lean	2516	False	abbrev RootLValuedCarrierK0 : Type :=	noncomputable def carrierK0EquivRootL :	INVALID	False	yes
312	1	S312QPilotRootTensorBaseChangeActual.lean	4107	True	noncomputable def qVFamBlockLinearEquiv :	noncomputable def qPilotBlockToRootTensor :	PROVED	False	no
313	1	S313CompletionThetaSideObjectActual.lean	5347	True	abbrev CompletionThetaCarrier : Type := qVFamTensorBlock T b	noncomputable def completionThetaRoot	PROVED	False	no
317	1	S317QPilotThetaSameCompletionBlockActual.lean	3732	True	noncomputable def qPilotCompletionImagePoint : qVFamTensorBlock T b :=	noncomputable def coefficientSurrogateCoefficient : qVFamTensorV → Real :=	PROVED	False	no
319	1	S319CompletionRootFromTorsion23Actual.lean	3740	True	theorem sourceTorsion23Rational :	def completionQVUnit :	PROVED	False	no
325	1	S325CompletionThetaMuOrbitActual.lean	4590	True	abbrev CompletionPlace : Type := Completion ((nativeBadLift T).lift b)	noncomputable def muCompletionFactor	PROVED	False	no
327	1	S327C3IndActionsActual.lean	4330	True	structure C3IndTransport where	noncomputable def ind1Action (S : C3IndTransport (A := A) (C := C) (C3 := C3) (j := j) (vQ := vQ) (v := v))	PROVED	False	no
328	1	S328C3LiteralLambdaOHullActual.lean	6124	True	theorem literalScaledRegion_subset_hull (lam : HullBlock C3) :	theorem literalScaledHull_eq_scaledRegion	PROVED	False	no
330	1	S330QVFamilyRootCardActual.lean	4727	True	abbrev qVFamilyPlace : NumberField.FinitePlace T.arithmetic.F :=	abbrev QVFamilyTwoLRootCard : Type :=	PROVED	False	no
342	1	S342QVFamilyRootImpossibleActual.lean	3913	True	noncomputable def qVFamilyTateWitness :	theorem qVFamily_order_coprime :	PROVED	False	no
343	1	S343CompletionThetaC3TensorActual.lean	4927	True	abbrev C3Block (T : SourceNativeInitialThetaData.{0} l)	noncomputable def c3ThetaTensorImagePoint	PROVED	False	no
346	1	S346OrbifoldStructuralSheafActual.lean	3603	True	structure OrbifoldStructuralSheafCarrierSpec	def OrbifoldStructuralSheafRootSectionRequired : Prop :=	PROVED	False	no
348	2	S348OrbifoldMu2lInterfaceActual.lean	3461	True	structure OrbifoldMu2lInterface	noncomputable def mu2lAction	PROVED	False	no
349	1	S349C3TensorLatticeRegionActual.lean	6173	True	noncomputable def actualC3LogShellTensorLattice :	noncomputable def actualC3LogShellTensorLatticeRegion :	PROVED	False	no
353	1	S353C3LatticeScaledHullActual.lean	8909	True	noncomputable def literalScaledRegion (a : ℚ_[C3.p]) :	noncomputable def literalCandidateHulls	PROVED	False	no
355	1	S355OrbifoldRootStackCandidateActual.lean	5702	True	abbrev K (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=	abbrev AC (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Type :=	PROVED	False	no
356	1	S356RootStackActionGroupoidActual.lean	3380	True	abbrev RootObj : Type := CandidateRoots T b	noncomputable def rootObj : RootObj T b := candidateRootSubtype T b	PROVED	False	no
357	1	S357OtrianglerightStructuralSheafActual.lean	3149	True	structure OtrianglerightOnSplitFrobenioid	def OtrianglerightStructuralSheafRequired	PROVED	False	no
366	2	S366OneColumnActualAdapted.lean	2103	False	noncomputable def oneColumnLocalField : NativePlaces P.X.S -> Type :=	noncomputable def oneColumnLocalRing : NativePlaces P.X.S -> Type :=	INVALID	False	yes
369	1	S369OtriSplitFrobenioidActual.lean	4415	True	abbrev nativeStagePlace : NumberField.FinitePlace T.arithmetic.F :=	noncomputable def nativeStageFrobenioidPresentation :	PROVED	False	no
370	1	S370ThetaSectionLogVolumeInterfaceActual.lean	2592	True	structure ThetaSectionLogVolumeInterface	noncomputable def thetaSectionLogVolumePlaceholder	PROVED	False	no
371	1	S371C3ScaledHullScalingClosedActual.lean	3284	True	theorem literalScaledRegion_scalingClosed	theorem literalHull_scalingClosed	PROVED	False	no
372	1	S372APacketC3TransportGapActual.lean	2793	True	structure APacketC3SpecialCaseTransport where	def APacketC3SpecialCaseTransportRequired : Prop :=	PROVED	False	no
373	1	S373NativeStageSplittingActual.lean	5091	True	abbrev stagePresentation : Iut.FrobenioidPresentation :=	abbrev stageTransport :	PROVED	False	no
376	1	S376StageTauConstructionActual.lean	2238	True	noncomputable def stageTauDataOfSplitting	def NativeStageCharacteristicSplittingMissing	PROVED	False	no
379	1	S379NativeStageTauExactMissingActual.lean	3230	True	abbrev StagePresentation : Iut.FrobenioidPresentation :=	abbrev StageTransport :	PROVED	False	no
384	1	S384C3LatticeHullNormalizedLogActual.lean	7835	True	noncomputable def c3LatticeUnitMass : ENNReal :=	noncomputable def c3LatticeHullMass (a : ℚ_[C3.p]) : ENNReal :=	PROVED	False	no
389	1	S389SingleStageSplitActual.lean	1510	True	abbrev SingleStageBase : Type u :=	theorem singleStageBase_single_object :	PROVED	False	no
392	1	S392RootStackSectionMonoidActual.lean	3353	True	abbrev SectionCarrier : Type := RootObj T b → Multiplicative ℤ	noncomputable def rootDelta (r : RootObj T b) : SectionCarrier T b := by	PROVED	False	no
397	1	S397SingleStageTauCharacteristicActual.lean	5787	True	abbrev StageUnitMonoid : Type u := U × Multiplicative ℤ	abbrev StageOneObjectD : Type :=	PROVED	False	no
40	1	S40SourceTheaterFieldMapDirectActual.lean	4941	True	noncomputable def sourceFieldMap :	noncomputable def sourcePlaceMap	GAP	True	no
402	1	S402EquivariantSectionCarrierActual.lean	4773	True	noncomputable def equivariantSections : Submonoid (SectionCarrier T b) where	abbrev EquivariantSectionCarrier : Type :=	PROVED	False	no
405	1	S405OrbicurveCoverCategoryActual.lean	1803	True	noncomputable def idMap (A : OrbicurveFiniteEtaleCover X) :	structure OrbicurveCoverCategoryGap where	PROVED	False	no
407	1	S407OrbicurveStructuralSheafMissingActual.lean	2270	True	structure OrbicurveStructuralSheafCarrierSpec where	def OrbicurveStructuralSheafCarrierRequired : Prop :=	PROVED	False	no
409	1	S409Example32FrobenioidActual.lean	2892	True	abbrev Example32AlgebraBase : Type (u + 1) :=	abbrev Example32Base : Type (u + 1) :=	PROVED	False	no
412	1	S412DvTriangleTauActual.lean	5566	True	structure DvCoverNormalizedValuationData (K : Type u) [Field K]	noncomputable def dvPi : Lˣ :=	PROVED	False	no
421	1	S421ConstantNatDivisorialMonoidActual.lean	2266	True	noncomputable def constantNatDivisorialMonoidOn	abbrev DvBase (K : Type u) [Field K] : Type (u + 1) :=	PROVED	False	no
423	1	S423NatDivisorialAddMonoidActual.lean	2245	True	noncomputable def natDivisorialAddMonoid : Iut.DivisorialAddMonoid where		PROVED	False	no
424	2	S424QVFamilyPaperQAuditActualAdapted.lean	2643	False	theorem qVFamily_repo_place_base :	theorem qVFamily_repo_order_coprime :	AUDIT	False	no
432	1	S432SmallModelActual.lean	3092	True	abbrev Example32Base : Type (u + 1) :=	abbrev Example32SmallBase : Type (u + 1) :=	PROVED	False	no
433	1	S433Example32RationalDivisorActual.lean	3921	True	abbrev example32RationalFunctions : Type u := L.obj.objˣ	def example32DivisorCoefficient (x : example32RationalFunctions L) : ℤ :=	PROVED	False	no
436	1	S436KSideQVActual.lean	2619	True	abbrev kSidePlace : NumberField.FinitePlace T.arithmetic.K :=	abbrev kSideCurve : PuncturedEllipticCurve T.arithmetic.K :=	PROVED	False	no
438	1	S438QVFamilyKSideCandidateActual.lean	4384	True	noncomputable def qVFamilyKLift (b : Bad (nativePlaceSelection T)) :	theorem qVFamilyKLift_comap :	PROVED	False	no
44	1	S44ThetaMuSymbolAuditActual.lean	3430	True	abbrev ThetaPilotObjectCarrier : Type := ThetaPilotCarrier l	abbrev ThetaPacketValueCarrier : Type := FiniteThetaPacket l	AUDIT	True	no
442	1	S442DvCoverNormPullbackActual.lean	3575	True	noncomputable def normPullback (f : L →ₐ[K] L') : L'ˣ →* Lˣ :=	theorem normPullback_apply (f : L →ₐ[K] L') (x : L'ˣ) :	PROVED	False	no
445	1	S445Example32SmallInputActual.lean	2774	True	structure Example32SmallInputData where	noncomputable def example32SmallInputOfData	PROVED	False	no
446	1	S446Example32DivisorNaturalityActual.lean	5269	True	def divisorCoefficientOfValuation (x : Lˣ) : ℤ :=	theorem example32DivisorCoefficient_normPullback	PROVED	False	no
448	1	S448Example32SmallInputActual.lean	2121	True	abbrev Example32SmallRationalObject (X : Example32SmallBase K) : Type u :=	structure Example32SmallNormBridge where	PROVED	False	no
449	1	S449NormPullbackGroupActual.lean	958	True	structure NormPullbackGroupLaws (K : Type u) [Field K]	def NormPullbackGroupLawsRequired : Prop :=	PROVED	False	no
451	1	S451GroupLikePullbackAuditActual.lean	1995	True	theorem unitsMap_injective {M N : Type u} [Monoid M] [Monoid N]	structure InclusionPullbackBijectiveData	AUDIT	False	no
453	1	S453DvTriangleMorphismAlgHomActual.lean	1978	True	noncomputable def arrowAlgebraMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :	theorem arrowAlgebraMap_id (X : Example32SmallBase K) :	PROVED	False	no
456	1	S456RationalInclusionActual.lean	1536	True	noncomputable def arrowAlgebraMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :	noncomputable def unitInclusionPullback {X Y : Example32SmallBase K} (f : X ⟶ Y) :	PROVED	False	no
457	1	S457DivisorMapActual.lean	1952	True	noncomputable def valuationExponentHom :	noncomputable def divisorMap :	PROVED	False	no
459	1	S459KrootCandidateActual.lean	3962	True	abbrev Kq : Type := Completion (qVFamilyKLift T b)	abbrev ACq : Type := AlgebraicClosure (Kq T b)	PROVED	False	no
460	1	S460RationalFunctionsFieldCoverActual.lean	4688	True	theorem pull_injective {X Y : D} (f : X ⟶ Y) :	noncomputable def rationalFunctions :	PROVED	False	no
462	1	S462Example32PhiIsoGroupLikeActual.lean	3881	True	def Example32FSMIso : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop :=	noncomputable def example32PhiIso :	PROVED	False	no
464	1	S464RationalFunctionsLiftedActual.lean	1369	True	noncomputable def uliftUnitMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :	structure Example32LiftedGroupLaws where	PROVED	False	no
465	1	S465LiftedDivisorMapActual.lean	2046	True	noncomputable def uliftAdditiveDown :	noncomputable def liftedDivisorMap :	PROVED	False	no
467	1	S467KrootOrderControlAuditActual.lean	3310	True	noncomputable def qVFamilyKRamificationIdx : Nat :=	theorem qVFamilyK_order_factorization :	AUDIT	False	no
468	1	S468DivisorNaturalityActual.lean	2445	True	abbrev DvSmallValuationFamily : Type (u + 1) :=	def DvSmallValuationCompatibility	PROVED	False	no
469	1	S469RationalFunctionsLiftedActual.lean	2518	True	theorem arrowAlgebraMap_id_local (X : Example32SmallBase K) :	theorem arrowAlgebraMap_comp_local {X Y Z : Example32SmallBase K}	PROVED	False	no
472	1	S472TorsionKInputAuditActual.lean	3034	True	theorem torsion23_actual :	theorem qVFamilyK_order_factorization_actual :	AUDIT	False	no
474	1	S474Example32GroupLikeIsoActual.lean	4692	True	theorem arrowAlgebraMap_id' (X : Example32SmallBase K) :	theorem arrowAlgebraMap_comp' {X Y Z : Example32SmallBase K}	PROVED	False	no
476	1	S476GenericGroupLikeGapActual.lean	1533	True	structure S476GenericInstantiationData (K : Type u) [Field K] where	def S476GenericInstantiationDataRequired (K : Type u) [Field K] : Prop :=	PROVED	False	no
477	3	S477ProbeAdapted.lean	289	False			AUDIT	False	no
479	1	S479TwoTorsionParityGapActual.lean	2452	True	theorem torsion23_input_actual :	structure TwoTorsionToQSqrtGap where	PROVED	False	no
480	1	S480Example32InputActual.lean	3381	True	noncomputable def example32PhiIsFSM :	structure Example32InputData where	PROVED	False	no
481	1	S481AlignedDivisorMapActual.lean	3912	True	noncomputable def stageDivisorULiftEquiv :	noncomputable def grothendieckStageDivisorULift :	PROVED	False	no
483	1	S483Example32InputActualConstruction.lean	4784	True	noncomputable def stageDivisorULiftUp :	noncomputable def grothendieckStageULiftUp :	PROVED	False	no
485	1	S485TateTwoTorsionQSqrtActual.lean	4797	True	abbrev FPlace : NumberField.FinitePlace T.arithmetic.F :=	abbrev KF : Type := Completion (FPlace T b)	PROVED	False	no
486	1	S486Example32ULiftGroupLikeActual.lean	1498	True	abbrev Example32ULiftUnits (X : Example32SmallBase K) : Type (u + 1) :=	noncomputable def example32ULiftPullback	PROVED	False	no
491	1	S491AlignedDivisorMapActual.lean	4866	True	noncomputable def stageDivisorULiftEquiv' :	noncomputable def grothendieckStageDivisorULift' :	PROVED	False	no
492	1	S492Example32InputActual.lean	3179	True	structure Example32InputDataActual where	noncomputable def example32InputActual	PROVED	False	no
493	1	S493Example32InputIsoActual.lean	3868	True	abbrev PhiIso : DivisorialMonoidOn (Example32SmallBase K)	abbrev PhiFSM : DivisorialMonoidOn (Example32SmallBase K)	PROVED	False	no
494	1	S494TateTwoTorsionConverseGapActual.lean	2771	True	abbrev ConversePoint : Type :=	structure TwoTorsionQuotientLiftData where	PROVED	False	no
495	1	S495DvSmallValuationActual.lean	2437	True	def DvSmallValuationExtensionExists : Prop :=	def DvSmallValuationExtensionUnique : Prop :=	PROVED	False	no
496	1	S496Example32AlignedDivisorNaturalityActual.lean	3174	True	theorem phi_gpPullback_id {X Y : Example32SmallBase K} (f : X ⟶ Y) :	theorem liftedPullback_ofMul_up {X Y : Example32SmallBase K} (f : X ⟶ Y)	PROVED	False	no
499	1	S499DvSmallValuationFamilyActual.lean	3184	True	abbrev S499DvSmallValuationFamily : Type (u + 1) :=	noncomputable def s499DvSmallValuationFamily	PROVED	False	no
501	1	S501ValuationExtensionActual.lean	4434	True	structure DvNormalizedBaseValuation where	structure DvNormalizedValuationExtension	PROVED	False	no
502	1	S502OddLiftObstructionActual.lean	3312	True	noncomputable def minusOneUnit : (ACF T b)ˣ := -1	noncomputable def minusOneDeck : FDeck T b :=	PROVED	False	no
503	2	S503QvPhiModelActualAdapted.lean	2071	False	structure QvGeneratedPhiPaperData where	def QvGeneratedPhiPaperDataRequired : Prop :=	INVALID	False	yes
505	2	S505QvPhiGeneratorActualAdapted.lean	2873	False	abbrev QvK : Type := NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b)	noncomputable def qOrder : ℕ := (qVFamily T b).order	INVALID	False	yes
506	1	S506QvPhiRamificationActual.lean	2416	True	structure DvRamificationIndexData where	structure DvNatDivisorialMonoidAtU where	PROVED	False	no
507	1	S507PhiCvCandidateActual.lean	2515	True	noncomputable def phiCvCandidate :	abbrev PhiCarrier : Type u := StageDivisor.{u}	PROVED	False	no
508	1	S508PaperPhiCvCandidateActual.lean	2455	True	structure DvSmallRamificationIndexData where	structure DvSmallQOrderSection where	PROVED	False	no
509	1	S509OddLiftChoiceActual.lean	2694	True	theorem qHalfRootClass_sq_one :	noncomputable def qSqrtOddLiftCondition : OddLiftCondition T b where	PROVED	False	no
51	1	S51DecorationWrapperActual.lean	3459	True	inductive Decoration where	structure DecoratedDPrimeStrip (δ : Decoration) (V : Type u) where	GAP	True	no
510	1	S510Example32ULiftGroupLikeCompleteActual.lean	1623	True	noncomputable def s510GroupLike :	theorem s510GroupLike_obj (X : Example32SmallBase K) :	PROVED	False	no
511	1	S511PhiCvCandidateActual.lean	3305	True	structure RamificationIndexData where	abbrev PhiCvCarrier (_X : Example32SmallBase K) : Type := ℕ	PROVED	False	no
513	2	S513DvPhiCvCandidateActualAdapted.lean	3029	False	abbrev DvPhiBase : Type := Example32SmallBase T.arithmetic.K	noncomputable def dvQOrderSection (N : ℕ) (hN : 0 < N) :	INVALID	False	yes
515	1	S515NatDivisorialMonoidULiftActual.lean	1950	True	def ULiftNatSaturated : Prop :=	noncomputable def dvNatDivisorialAddMonoidAtU	PROVED	False	no
516	1	S516ULiftNatPhiActual.lean	4358	True	noncomputable def uliftNatDivisorialAddMonoid :	noncomputable def uliftNatMulLeft (e : ℕ) :	PROVED	False	no
517	1	S517EtThSpecialTwoTorsionGapActual.lean	1609	True	structure EtThSpecialTwoTorsionGap where		PROVED	False	no
518	1	S518ULiftNatDivisorialAddMonoidActual.lean	2426	True	noncomputable def uliftNatDivisorialAddMonoid :		PROVED	False	no
519	1	S519QvPhiRamificationModelActual.lean	3943	True	noncomputable def uliftNatDivisorialAddMonoid :	noncomputable def uliftNatMulLeft (e : ℕ) :	PROVED	False	no
522	1	S522QvPhiRamificationModelActual.lean	2761	True	noncomputable def uliftNatMulLeft (e : ℕ) :	theorem uliftNatMulLeft_injective {e : ℕ} (he : 0 < e) :	PROVED	False	no
523	1	S523EtThReductionSelectorActual.lean	1829	True	structure EtThReductionSelectorData where	def EtThReductionSelectorDataRequired : Prop :=	PROVED	False	no
524	1	S524QvPhiRamificationModelS518Actual.lean	3141	True	noncomputable def uliftNatMulLeft (e : ℕ) :	theorem uliftNatMulLeft_injective {e : ℕ} (he : 0 < e) :	PROVED	False	no
526	1	S526Example32AlignedNaturalityActual.lean	2029	True	theorem example32AlignedDivisor_ofMul_up	def example32AlignedDivisorNaturalityGap : Prop :=	PROVED	False	no
528	2	S528QvPhiTriSubmonoidActual.lean	3223	True	theorem uliftNatMulLeft_apply_nsmul (e : ℕ) (n : ULift.{u+1} ℕ) :	noncomputable def qvTriQOrder	PROVED	False	no
530	1	S530EtThQSqrtRecipeSpecActual.lean	2137	True	structure EtThThetaSplittingRecipe (T : SourceNativeInitialThetaData.{0} l)		PROVED	False	no
531	1	S531EtThThetaUnitRecipeActual.lean	3321	True	noncomputable def thetaUnitElement : ACF T b :=	theorem thetaUnitElement_pow :	PROVED	False	no
532	1	S532QHalfUnitActual.lean	3828	True	noncomputable def thetaRootElement : ACF T b :=	theorem thetaRootElement_pow :	PROVED	False	no
533	1	S533QvPhiSubmonoidActual.lean	2536	True	noncomputable def qvOrder : ℕ := (qVFamilyK T b).order	theorem qvOrder_pos : 0 < qvOrder T b :=	PROVED	False	no
534	1	S534QvPhiCvSharpSubmonoidActual.lean	2749	True	noncomputable def qvKOrder : ℕ := (qVFamilyK T b).order	noncomputable def sharpSubmonoid (g : ℕ) : AddSubmonoid (ULift.{u+1} ℕ) where	PROVED	False	no
536	2	S536Example32AlignedNaturalityFinalActualAdapted.lean	1975	False	theorem example32AlignedDivisor_naturality		INVALID	False	yes
539	1	S539PhiCvSubmonoidActual.lean	3064	True	noncomputable def s539PhiSubmonoid (qOrder : ℕ)	def s539QOrder (_X : Example32SmallBase K) : ℕ := 0	PROVED	False	no
54	1	S54DecorationAssignmentActual.lean	3657	True	inductive SourceConsumer where	def consumerDecoration : SourceConsumer → Decoration	GAP	True	no
540	1	S540QvPhiTauExactGapActual.lean	3418	True	structure QvPhiTauData where	noncomputable def characteristicSplittingOfQvPhiTauData	PROVED	False	no
542	1	S542ThetaQHalfActual.lean	1580	True	def qHalfUnitOfTheta (thetaUnit : (ACF T b)ˣ) : (ACF T b)ˣ :=	theorem qHalfUnitOfTheta_sq (thetaUnit : (ACF T b)ˣ)	PROVED	False	no
543	1	S543ConditionalEtThRecipeActual.lean	4137	True	noncomputable def conditionalEtThThetaSplittingRecipe	theorem conditionalRecipe_qHalf_sq	PROVED	False	no
544	1	S544Example32AlignedTypeLemmaActual.lean	3252	True	theorem example32AlignedDivisor_as_S469_obj	theorem example32AlignedDivisor_naturality	PROVED	False	no
545	1	S545RealThetaUnitAnalyticModelActual.lean	2963	True	noncomputable def realThetaLabelUnit (t : AnalyticThetaCarrier) (j : ℤ) : ℝˣ :=	theorem realThetaLabelUnit_eq_qUnit_pow (j : ℤ) :	PROVED	False	no
546	1	S546QHalfCandidateActual.lean	2702	True	noncomputable def qHalfRoot :	theorem qHalfRoot_pow :	PROVED	False	no
547	1	S547PhiCvPackageActual.lean	2875	True	abbrev BaseField : Type := T.arithmetic.K	structure PhiCvPackage where	PROVED	False	no
548	1	S548SplitFrobenioidActual.lean	3491	True	structure S548InputData (K : Type u) [Field K] where	noncomputable def s548InputOfData	PROVED	False	no
549	1	S549QvPhiTriSubmonoidActual.lean	1703	True	structure QvPhiTriSubmonoidData	noncomputable def qvPhiTriSubmonoidData	PROVED	False	no
550	1	S550QvPhiPreFrobenioidActual.lean	4319	True	abbrev qvPhi := qvPhiRamificationModel (K := K) R	abbrev qvIsFSM : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → Prop := fun {X Y} f => IsIso f	PROVED	False	no
551	1	S551QHalfComparisonActual.lean	2818	True	noncomputable def qHalfRootActual : (ACF T b)ˣ :=	structure QHalfComparisonData where	PROVED	False	no
552	1	S552Example32ConditionalPresentationActual.lean	3550	True	structure Example32PresentationConditions where	noncomputable def example32InputOfValuation	PROVED	False	no
553	1	S553QvPhiTriDataActual.lean	3056	True	structure QvPhiTriData (K : Type u) [Field K] where	noncomputable def qvPhiTriDataOf	PROVED	False	no
554	1	S554QHalfPaperActual.lean	2536	True	structure QHalfPaperData where	noncomputable def qHalfPaperDataOfComparison	PROVED	False	no
555	1	S555QvPhiTauConstructionGapActual.lean	3618	True	abbrev QvP := qvPreFrobenioid (K := K) R data	abbrev QvR := qvRationalMonoidTransport (K := K) R data	PROVED	False	no
556	1	S556QvPhiInputActual.lean	3332	True	structure S556InputDataActual where	noncomputable def s556InputActual	PROVED	False	no
557	1	S557QvPhiSplitFrobenioidConditional.lean	2157	True	noncomputable def qvCharacteristicSplitting :	noncomputable def qvFrobenioidPresentation	PROVED	False	no
558	1	S558QvPhiTauFromPiActual.lean	3532	True	structure QvPhiPiTauInput where	noncomputable def tauDataOfPiInput	PROVED	False	no
559	1	S559S556NaturalityAlignmentActual.lean	2134	True	theorem qvPhiPullback_eq_mul	def S556NaturalityAlignmentRequired (K : Type u) [Field K]	PROVED	False	no
56	1	S56OTriangularCarrierActual.lean	3161	True	noncomputable def oTriangularMonoid :	abbrev oTimesUnits : Type u := (CompletionIntegers place.val)ˣ	GAP	True	no
560	1	S560QvPhiTauPiActual.lean	1897	True	structure QvPhiTauPiData where	def QvPhiTauPiDataRequired : Prop :=	PROVED	False	no
561	1	S561QvPhiMinimalPackageActual.lean	2473	True	structure S561MinimalPackage where	noncomputable def s561InputData	PROVED	False	no
562	1	S562QvPhiInputPackageActual.lean	1506	True	structure QvPhiInputPackage (K : Type u) [Field K]	noncomputable def qvPhiInputPackage (K : Type u) [Field K]	PROVED	False	no
563	1	S563QvOrderElementConstructionActual.lean	3039	True	structure QvPhiQOrderFields (A : Object (qvPhi (K := K) R)) where	noncomputable def qOrderEndomorphismOfFields	PROVED	False	no
564	1	S564QvPiOtriangleCandidateActual.lean	3999	True	noncomputable def qvPiOrder (T : SourceNativeInitialThetaData.{0} l)	theorem qvPiOrder_pos (T : SourceNativeInitialThetaData.{0} l)	PROVED	False	no
565	1	S565QvOrderFromS556InputActual.lean	2828	True	abbrev Dat (D : S556InputDataActual (K := K)) := s556InputActual D	structure S556QOrderWitness where	PROVED	False	no
566	1	S566QvPhiQOrderFieldsActual.lean	3150	True	abbrev s566Input : Input (qvPhi (K := K) P.ramification) :=	noncomputable def zeroQvPhiQOrderFields :	PROVED	False	no
567	1	S567QvPhiQOrderFieldsFromTriDataActual.lean	3343	True	abbrev s567Input : Input (qvPhi (K := K) D.ramification) :=	noncomputable def s567ZeroQvPhiQOrderFields :	PROVED	False	no
568	1	S568QvPhiQOrderTauActual.lean	4166	True	structure QvPhiQOrderTauInput where	noncomputable def tauDataOfQOrderInput	PROVED	False	no
569	1	S569QvOrderPiActual.lean	2566	True	noncomputable def qOrderAtArrow {X Y : Example32SmallBase K} (f : X ⟶ Y) : ℕ :=	theorem qOrderAtArrow_pos {X Y : Example32SmallBase K} (f : X ⟶ Y) :	PROVED	False	no
571	1	S571QvPhiUnitDecompositionActual.lean	2922	True	noncomputable def qvPi :	def QvPhiDivisorDivisibility	PROVED	False	no
573	1	S573QOrderPreimageActual.lean	2321	True	noncomputable def s567QOrderPreimageOfUnit	structure S573QOrderPreimageUnitData where	PROVED	False	no
574	1	S574QvPhiUnitDecompositionConditionalActual.lean	4368	True	abbrev F574 : QvPhiQOrderFields (K := K) D.ramification (s567Input (K := K) D) A :=	noncomputable def pi574 :	PROVED	False	no
575	1	S575QvPhiPositivePreimageActual.lean	4595	True	noncomputable def positiveUnit (qOrder : ℕ) : (coverField A.base)ˣ :=	theorem positiveUnit_valuation (qOrder : ℕ) :	PROVED	False	no
576	1	S576PositiveQvPhiQOrderFieldsActual.lean	3538	True	structure S576PositiveQvPhiQOrderFields where	noncomputable def s576PositiveQvPhiQOrderFieldsOfPreimage	PROVED	False	no
577	1	S577QvPiRealizationFromS556Actual.lean	3129	True	structure S556QvPiData (D : S556InputDataActual (K := K)) where	noncomputable def qvPiRealizationOfS556	PROVED	False	no
580	1	S580PositivePreimageConstructionActual.lean	2411	True	noncomputable def positiveQvPhiPreimage (qOrder : ℕ) (hpos : 0 < qOrder) :	noncomputable def s556QOrderWitnessOfPositive :	PROVED	False	no
581	1	S581QvPhiPositivePreimageFromS575Actual.lean	4484	True	noncomputable def s581PositiveUnit (qOrder : ℕ) : (coverField A.base)ˣ :=	theorem s581PositiveUnit_valuation (qOrder : ℕ) :	PROVED	False	no
582	1	S582AlignedDivisorEvalActual.lean	1374	True	theorem grothendieckStageDivisorULift'_of (x : StageDivisor.{u}) :		PROVED	False	no
583	1	S583AlignedDivisorEvalS491Actual.lean	2128	True	theorem example32DivisorAlignedS491_eval	theorem grothendieckStageDivisorULift'_of	PROVED	False	no
584	1	S584QOrderWitnessActual.lean	3105	True	theorem positiveUnit_divisor_evalS584 (qOrder : ℕ) :	noncomputable def s556QOrderWitnessActual :	PROVED	False	no
586	1	S586PositiveQvPhiPreimageActual.lean	3093	True	structure PositiveQvPhiPreimageEvalData (qOrder : ℕ) where	noncomputable def positiveQvPhiPreimageS586	PROVED	False	no
590	2	S590EvalActualAdapted.lean	2147	False			STATEMENT	False	yes
591	1	S591PositiveUnitDivisorEvalActual.lean	3341	True	theorem positiveUnit_divisor_toLift (qOrder : ℕ) :	theorem positiveUnit_divisor_eval (qOrder : ℕ) :	PROVED	False	no
593	1	S593PositivePreimageQvOrderActual.lean	1593	True	noncomputable def positiveQvPhiPreimageAtQvOrder :		PROVED	False	no
595	1	S595PositiveEvalIndependentActual.lean	3004	True	theorem positiveUnit_divisor_eval	noncomputable def positivePreimage	PROVED	False	no
596	1	S596PositivePreimageActual.lean	1561	True	noncomputable def positivePreimage (qOrder : ℕ) (hpos : 0 < qOrder) :		PROVED	False	no
597	1	S597QvPhiQOrderFieldsActual.lean	3962	True	noncomputable def qOrderFields	noncomputable def qOrderEndomorphism	PROVED	False	no
598	1	S598QvPhiQOrderTauFromQvOrderActual.lean	2862	True	noncomputable def positivePreimageAtQvOrder :	noncomputable def qOrderFieldsAtQvOrder :	PROVED	False	no
599	1	S599QvPhiTauFieldsActual.lean	5225	True	noncomputable def s599QOrderFields	structure S599TauCompatibility where	PROVED	False	no
60	1	S60OTriangleBoundaryActual.lean	3251	True	noncomputable def oBoundaryMonoid :	def oBoundaryToTriangular :	GAP	True	no
600	1	S600PositiveFieldsFromS593Actual.lean	3910	True	noncomputable def s600QvPhiQOrderFields :	noncomputable def s600Tau :	PROVED	False	no
601	1	S601QvPhiQOrderFieldsFromPreimageActual.lean	2337	True	noncomputable def qvPhiQOrderFieldsOfPreimage	noncomputable def qOrderEndomorphismOfPreimage	PROVED	False	no
602	1	S602CharacteristicSplittingFromPreimagesActual.lean	7154	True	noncomputable def preimageFields (qOrder : ℕ) (hpos : 0 < qOrder)	noncomputable def qvPhiQOrderTauInputOfPreimages	PROVED	False	no
603	1	S603QvPhiDivisibilityGoalActual.lean	4258	True	abbrev threeInput : Input (qvPhi (K := K) P.ramification) :=	abbrev threePi :	PROVED	False	no
604	1	S604QvPhiQOrderTauInputActual.lean	4933	True	noncomputable def fieldsOfPreimageFamily	noncomputable def qvPhiQOrderTauInputOfPreimageFamily	PROVED	False	no
605	1	S605KSideQVActual.lean	3133	True	structure KSideQVComparisonData where	def KSideQVComparisonRequired : Prop :=	PROVED	False	no
606	1	S606PositiveUnitQvImageActual.lean	3008	True	theorem positiveUnit_valuation_qvOrder :	theorem positiveUnit_divisor_qvOrder :	PROVED	False	no
607	3	S607ProbeAdapted.lean	298	False			AUDIT	False	no
608	2	S608QOrderDivisibilityLawsActualAdapted.lean	4356	False	abbrev qvPi := qOrderEndomorphism (K := K) T b P A	abbrev qvFields := qOrderFields (K := K) T b P A	INVALID	False	yes
609	1	S609QHalfRigidityActual.lean	1954	True	theorem qHalf_ratio_sq_one	theorem qHalf_constant_multiple_rigidity	PROVED	False	no
610	1	S610PositiveUnitQvImageActual.lean	2733	True	noncomputable def positiveUnitAtQvOrder :	theorem positiveUnitAtQvOrder_valuation :	PROVED	False	no
611	1	S611SpecialTwoTorsionEvaluationActual.lean	4105	True	noncomputable def qHalfRootS546 : (ACF T b)ˣ :=	theorem qHalfRootS546_pow :	PROVED	False	no
612	1	S612QvPositiveUnitImageMapActual.lean	2891	True	noncomputable def qUnitAtQvFamilyK : (Completion (qVFamilyKLift T b))ˣ :=	theorem qUnitAtQvFamilyK_val :	PROVED	False	no
613	1	S613QvPhiDivisibilityAttemptActual.lean	2099	True	abbrev divMon : Type _ :=	theorem identity_divisorDivisibility :	PROVED	False	no
614	1	S614PhiCvModelComparisonActual.lean	2039	True	structure PhiCvModelComparison (place : NumberField.FinitePlace K)	noncomputable def phiCvModelComparisonOf	PROVED	False	no
615	1	S615UnitsCommuteActual.lean	3774	True	noncomputable def s615Tau (X : (qvPreFrobenioid (K := K) P.ramification	def S615UnitsCommuteStatement : Prop :=	PROVED	False	no
616	4	S616ModelPaperAlignmentActualAdapted.lean	1917	False	def s616ModelBaseEquiv : Example32SmallBase K ≌ Example32SmallBase K :=	structure S616PaperPhiObjEquivData where	INVALID	False	yes
617	1	S617SpecialFiberOriginActual.lean	1862	False	noncomputable def specialFiberOrigin (W : WeierstrassCurve R) :	theorem specialFiberOrigin_eq_zero (W : WeierstrassCurve R) :	INVALID	False	yes
618	2	S618KSideQVPlaceActualAdapted.lean	2792	False	theorem place_eq_imp_shadow_eq	structure KSideQVPlaceGap where	INVALID	False	yes
619	2	S619IdentityTauUnitsCommuteActualAdapted.lean	4419	False	noncomputable def s619IdentityTau	theorem s619IdentityTau_units_commute	INVALID	False	yes
620	5	S620FinalContractActualAdapted.lean	4733	False	noncomputable def sourceQSigned : Real :=	noncomputable def sourceTargetSigned : Real :=	INVALID	False	yes
621	5	S621ConcreteComparisonMinimalGapActualAdapted.lean	2431	False	theorem obstacle_iff_badQAbsLog :	def ConcreteSourceComparisonMinimalGap : Prop :=	INVALID	False	yes
622	3	S622FinalNumericInequalityActualAdapted.lean	2410	False	def FinalNumericInequality : Prop :=	theorem not_finalNumericInequality_of_badQAbsLog_eq_log5	INVALID	False	yes
623	2	S623SourceBadQAuditActualAdapted.lean	2533	False	theorem sourceBadQAbsLog_eq_sum_abs_log	theorem obstacle_of_badQAbsLog_lower_bound	AUDIT	False	no
624	3	S624FinalConcreteSourceComparisonGapActualAdapted.lean	3370	False	theorem concreteSourceComparisonObstacle_iff_gaussSum_le_badQAbsLog	def FinalConcreteSourceComparisonGap : Prop :=	INVALID	False	yes
625	2	S625FinalConditionalPackageActualAdapted.lean	3387	False	structure FinalConcreteComparisonPackage where	noncomputable def finalConcreteComparisonPackage	INVALID	False	yes
627	1	S627ThetaSourceComparisonActual.lean	2601	True	def paperComparisonGap	theorem thetaSourceComparison_iff_gap	PROVED	False	no
628	2	S628PaperXiFSourceLinkConstructionActualAdapted.lean	6166	False	def ConcreteSourceQIdentification	theorem qPilotLogVolume_eq_paper	INVALID	False	yes
629	1	S629SourceIdentificationAuditActual.lean	2332	True	theorem concrete_strip_identification_eq :	theorem concrete_lineBundle_identification_eq :	AUDIT	False	no
63	1	S63OBoundaryLogShellActual.lean	3434	True	theorem sourceLogShellUnits_eq_integralUnits :	noncomputable def sourceOBoundaryMonoid :	GAP	True	no
630	1	S630ActualQPilotXiFLinkAudit.lean	2480	True	theorem actual_signedQPilotLogVolume_eq_paper :	theorem actual_qPilotLogVolume_eq_paper_withTop :	AUDIT	False	no
631	1	S631SourceQIdentificationActual.lean	3289	True	theorem sourceQPilotSignedLog_unfold	theorem paperQPilotLogVolume_C3_unfold	PROVED	False	no
633	2	S633ThetaPacketQMagnitudeActualAdapted.lean	3156	False	theorem paperQPilotLogMagnitude_eq_qPilotLogMagnitude	theorem missingPaperXiFComparison_of_thetaPacket	INVALID	False	yes
634	2	S634PaperXiFConditionalCor312Actual.lean	4964	True	def ConcreteSourceQIdentification	theorem qPilotLogVolume_eq_paper	PROVED	False	no
636	1	S636ThetaNormalizationAuditActual.lean	2647	True	def paperThetaScale (qTwoU : Real) (j : SignedLabel l.value) : Real :=	theorem paperThetaScale_eq_realThetaValue (qTwoU : Real)	AUDIT	False	no
637	2	S637ActualPaperXiFBridgeActualAdapted.lean	3466	False	noncomputable def actualThetaLinkOfBridge :	Theorem actualThetaLinkOfBridge_identification :	INVALID	False	yes
638	3	S638ActualToPaperXiFSourceLinkActualAdapted.lean	1998	False	noncomputable def paperXiFSourceLinkOfActual :		INVALID	False	yes
64	1	S64DependentThetaHullActual.lean	10342	True	noncomputable def dependentThetaHull :	noncomputable def dependentThetaHullProductHaar	PROVED	False	no
640	5	S640PaperRootThetaProcessionActualAdapted.lean	4158	False	noncomputable def processionSignedLabel (x : ProcessionLabel l) : SignedLabel l.value :=	noncomputable def paperRootThetaProcession :	INVALID	False	yes
641	1	S641CorrectedPaperThetaComparisonActual.lean	2127	True	theorem s641GlobalQPilot_le_thetaHull :	def S641PaperRootHullFormulaGapRequired : Prop :=	PROVED	False	no
642	2	S642PaperRootThetaProcessionActualAdapted.lean	3573	False	noncomputable def paperRootThetaWeight : Real :=	noncomputable def paperRootThetaValue (j : SignedLabel l.value) : Real :=	INVALID	False	yes
644	2	S644PaperRootThetaProcessionActualAdapted.lean	4511	False	noncomputable def paperThetaLogMagnitude	noncomputable def paperThetaSignedLogValue	INVALID	False	yes
645	2	S645RootNormalizedPaperSignedHullActualAdapted.lean	3882	False	noncomputable def rootThetaSignedProcession :	theorem rootThetaSignedProcession_value (j : SignedLabel l.value) :	INVALID	False	yes
646	1	S646PaperRootHullComparisonActual.lean	3808	True	def PaperRootCoefficientLeRootNorm : Prop :=	theorem qPilotClassicalLog_le_paperRootHullLog	PROVED	False	no
647	1	S647RootThetaExtensionHullMeasureActual.lean	3027	True	structure RootThetaExtensionHullMeasureData where	def RootThetaExtensionHullMeasureRequired : Prop :=	PROVED	False	no
649	1	S649RootThetaExtensionComparisonActual.lean	2910	True	noncomputable def s649CarrierData :	theorem s649RootThetaPowerPoint_eq_embedded	PROVED	False	no
650	3	S650ActualSignedCor312ContractAdapted.lean	2763	False	noncomputable def s650ActualSignedContract : StepXIContract :=	theorem s650ActualSignedCor312Conclusion :	INVALID	False	yes
652	1	S652ExtensionImageLogActual.lean	2411	True	noncomputable def extensionImageLog	theorem extensionImageLog_eq_log_card	PROVED	False	no
653	1	S653RootThetaTensorHullCarrierGapActual.lean	3767	True	noncomputable def rootThetaProductImageMap	theorem rootThetaProductImageMap_imagePoint	PROVED	False	no
654	1	S654RootSignedHullSignCorrectionActual.lean	2590	True	theorem rootThetaMagnitudeValue_nonneg (j : SignedLabel l.value) :	theorem rootThetaMagnitudeProcession_average_nonneg :	PROVED	False	no
656	2	S656RootThetaSignAuditActualAdapted.lean	1739	False	theorem s642_value_eq_s644_signedLog (j : SignedLabel l.value) :	theorem s642_value_eq_neg_magnitude (j : SignedLabel l.value) :	AUDIT	False	no
657	1	S657RootSignedHullIndependentActual.lean	4982	True	noncomputable def rootThetaMagnitudeValue (j : SignedLabel l.value) : Real :=	theorem rootThetaMagnitudeValue_nonneg (j : SignedLabel l.value) :	PROVED	False	no
658	1	S658RootNormalizedPaperSignedHullActual.lean	2194	True	noncomputable def rootNormalizedPaperSignedHullCorrected	theorem rootNormalizedPaperSignedHullCorrected_signed_eq	PROVED	False	no
660	3	S660ConcreteSourceComparisonObstacleActualAdapted.lean	4032	False	def ConcreteSourceComparisonScalarGap : Prop :=	theorem concreteSourceComparisonObstacle_iff_scalarGap :	INVALID	False	yes
662	1	S662NormalizedHaarArbitraryAverageActual.lean	5384	True	noncomputable def normalizedHaarScaleFor (A : Real) : Real :=	theorem normalizedHaarScaleFor_pos (A : Real) :	PROVED	False	no
663	2	S663ActualAverageNormalizedHaarActual.lean	6109	True	noncomputable def s663Scale (a : Real) : Real :=	theorem s663Scale_pos (a : Real) :	PROVED	False	no
664	1	S664RootQUnitNormLeOneActual.lean	2023	True	theorem rootQUnitNormLeOne : RootQUnitNormLeOne (T := T) := by		PROVED	False	no
665	1	S665PaperSignedHullXiFInterfaceActual.lean	4058	True	noncomputable def s665PaperSignedHull : PaperSignedHull X (SignedLabel l.value) :=	theorem s665_signedHullLogVolume_eq_neg_average :	PROVED	False	no
666	1	S666QPilotRootExtensionInterfaceActual.lean	4521	True	noncomputable def qPilotRegion :	noncomputable def qPilotLog : Real :=	PROVED	False	no
668	1	S668QPilotRootExtensionPerBActual.lean	4578	True	noncomputable def qPilotToRootExtension :	theorem qPilotToRootExtension_eq (x : qVFamTensorBlock T b) :	PROVED	False	no
669	1	S669S663PaperXiFSourceLinkActual.lean	5593	True	def S669QPilotLogVolumeEqPaper	noncomputable def s669PaperXiFSourceLink	PROVED	False	no
670	1	S670QPilotRootExtensionContainmentActual.lean	3795	True	def QPilotPerBPointwiseNormBound : Prop :=	theorem qPilotPerBContainmentObstacle_iff_pointwise :	PROVED	False	no
671	1	S671QPilotRadiusAuditActual.lean	4383	True	theorem rootImageCoordinate_eq_closedBall :	def QPilotRadiusBoundObstacle : Prop :=	AUDIT	False	no
672	1	S672OtrianglerightConstructionActual.lean	2669	True	noncomputable def otrianglerightOfSections	structure OtrianglerightCandidate	PROVED	False	no
673	2	S673QPilotRootImageContainmentActualAdapted.lean	2297	False	noncomputable def qPilotImageInRootExtension : Set (rootNormedExtension T b) :=	noncomputable def rootImageCoordinate : Set (rootNormedExtension T b) :=	INVALID	False	yes
674	1	S674SourceQIdentificationPackageActual.lean	2863	True	def ConcreteSourceQIdentification	theorem qPilotLogVolume_eq_paper_iff_sourceQ :	PROVED	False	no
676	1	S676FinalConditionalCor312Actual.lean	5221	True	noncomputable def s676SourceLink	theorem s676_finalCor312	PROVED	False	no
677	1	S677OtriFromTauGapActual.lean	2904	True	noncomputable def splitOfStageSplitting	structure OtriCandidateFromTauData	PROVED	False	no
678	1	S678QPilotRootExtensionOperatorBoundActual.lean	5086	True	noncomputable def qPilotBlockLinearMap :	theorem qPilotBlockLinearMap_apply (x : qVFamTensorBlock T b) :	PROVED	False	no
679	1	S679DirectScalarComparisonActual.lean	5165	True	noncomputable def rootThetaAverageCoefficient : Real :=	noncomputable def qVFamLocalQPilotMagnitude : Real :=	PROVED	False	no
68	5	S68Probe2Adapted.lean	467	False			AUDIT	False	no
680	1	S680OtriUnitsFromLogShellSectionsActual.lean	4410	True	noncomputable def otriSubmonoidOfSections	theorem q_mem_otriSubmonoidOfSections	PROVED	False	no
681	1	S681OtriQSectionReflectionNoGoActual.lean	3565	True	theorem completionMap_root_pow	theorem no_completion_reflection_with_root	PROVED	False	no
682	1	S682LogGeometryToolInventory.lean	946	True			AUDIT	False	no
683	1	S683QPilotRadiusOperatorAuditActual.lean	2359	True	theorem qPilotRadiusBound_of_operatorConstant		AUDIT	False	no
684	1	S684QuadraticGaussFiniteActual.lean	1231	True	noncomputable def quadraticGaussSum (psi : AddChar (ZMod N) ℂ) (a : ZMod N) : ℂ :=	theorem quadraticGaussSum_zero (psi : AddChar (ZMod N) ℂ) :	PROVED	False	no
685	1	S685NewtonOkounkovToolAuditActual.lean	2047	False	structure NewtonOkounkovSkeletonBridge where	def NewtonOkounkovSkeletonBridgeRequired : Prop :=	AUDIT	False	no
687	1	S687QPilotSourceNormBoundActual.lean	3424	True	def QPilotRegionNormLe (R : Real) : Prop :=	def QPilotSourceNormBound (C : Real) : Prop :=	PROVED	False	no
688	1	S688OtriFromRootStackSectionMapActual.lean	3417	True	abbrev RootStackSectionUnitsMap : Type u :=	noncomputable def otriUnitsSectionsOfRootStackMap	PROVED	False	no
690	1	S690RootThetaCoefficientExpansionActual.lean	3374	True	noncomputable def qPilotLocalMagnitude : Real :=	theorem rootThetaMagnitudeValue_eq_ratio_mul_qPilot	PROVED	False	no
691	1	S691RootStackUnitsFieldsActual.lean	3099	True	structure OTriangleUnitCoordinates where	structure RootStackUnitsFieldsData where	PROVED	False	no
692	1	S692QPilotRegionNormExactActual.lean	2405	True	def ThetaScaledRegionNormLe (c : qVFamTensorV → Real) (R : Real) : Prop :=	theorem qPilotRegionNormLe_iff_scaled :	PROVED	False	no
693	1	S693DirectComparisonCounterexampleActual.lean	2170	True	def l29 : PrimeGeFive where	theorem l29_value : l29.value = 29 := rfl	PROVED	False	no
694	1	S694ThetaAverageNormalizationActual.lean	2880	True	abbrev PaperThetaLabel (l : PrimeGeFive) : Type := Fin (lStar l.value)	noncomputable def paperThetaLabelWeight (l : PrimeGeFive) : Real :=	PROVED	False	no
695	1	S695QPilotNormalizationAuditActual.lean	2974	True	theorem qVFamTensorCoefficient_eq_order :	theorem qPilotCoefficient_eq_classical_div_twoL :	AUDIT	False	no
697	1	S697QPilotRegionCoefficientReductionActual.lean	3446	True	noncomputable def qPilotClassicalNormGoal : Prop :=	def RootLabelRegionNormLeRootRadius : Prop :=	PROVED	False	no
699	1	S699QPilotRootExtensionNormActual.lean	3141	True	theorem norm_algebraMap_rootBase_rootNormedExtension	theorem qPilotToRootExtension_norm_eq (x : qVFamTensorBlock T b) :	PROVED	False	no
700	1	S700ThetaQParameterNormalizationActual.lean	2831	True	noncomputable def qParameterThetaValue	theorem qParameterThetaValue_eq_rpow	PROVED	False	no
701	1	S701QPilotRegionNormExactGoalActual.lean	2969	True	noncomputable def qPilotRegionNormRadius : Real :=	theorem qPilotRegion_eq_scaledRegion :	PROVED	False	no
702	1	S702QPilotRegionNormCandidateActual.lean	2463	True	noncomputable def qPilotRegionRadiusCandidate : Real :=	noncomputable def qPilotRootImageRadiusCandidate : Real :=	PROVED	False	no
703	2	S703GlobalPaperThetaComparisonActualAdapted.lean	4776	False	noncomputable def paperThetaPositiveLabel (i : Fin (lStar l.value)) :	noncomputable def paperThetaAverageValue (b : Bad (nativePlaceSelection T)) : Real :=	INVALID	False	yes
704	1	S704PaperThetaLogVolumeFormulaActual.lean	4456	True	noncomputable def paperThetaExponent (j : PaperThetaLabel l) : Real :=	noncomputable def paperThetaLinearCoefficient (l : PrimeGeFive) : Real :=	PROVED	False	no
705	1	S705QPilotThetaFormulaAuditActual.lean	3160	True	def qPilotLocalCoefficient : Real :=	def thetaLocalCoefficient (j : SignedLabel l.value) : Real :=	AUDIT	False	no
706	1	S706ThetaPilotHullLogActual.lean	2891	True	noncomputable def thetaPilotHullLog (b : Bad (nativePlaceSelection T)) : Real :=	noncomputable def qPilotLog (b : Bad (nativePlaceSelection T)) : Real :=	PROVED	False	no
707	1	S707ThetaHullVsThetaValueActual.lean	2859	True	noncomputable def thetaPilotMagnitude : Real :=	theorem thetaPilotMagnitude_eq_neg_signedHullLogVolume :	PROVED	False	no
708	1	S708QPilotRootLabelRegionNormActual.lean	4013	True	def S708FirstIdentification : Prop :=	theorem qPilotRootLabelRegion_eq_thetaTensorScaledRegion :	PROVED	False	no
709	1	S709RootImageRadiusFormulaActual.lean	6857	True	noncomputable def oneThetaLabel : ThetaLabel (l := l) :=	theorem rootNormedThetaValueInL_one_norm :	PROVED	False	no
712	1	S712RootLabelRegionNormActual.lean	2233	True	noncomputable def rootLabelRegionRadiusCandidate : Real :=	def RootLabelRegionLatticeNormBound : Prop :=	PROVED	False	no
714	1	S714HullComparisonActual.lean	4723	True	noncomputable def paperQPilotMagnitude : Real :=	def paperThetaIndexToSigned (i : PaperThetaLabel l) : SignedLabel l.value :=	PROVED	False	no
715	1	S715S663SurrogateAuditActual.lean	5372	True	theorem s663Interface_target_builtin (a : Real) :	theorem s663PaperSignedHull_hnormal_is_builtin :	AUDIT	False	no
716	1	S716PaperThetaHullLogSourceAuditActual.lean	3444	True	noncomputable def paperPerBThetaHullLog : Real :=	theorem paperPerBThetaHullLog_eq_rootNormHullLog :	AUDIT	False	no
717	1	S717TensorLatticeNormExactActual.lean	2913	True	noncomputable def rootLabelCoefficientAtOne : qVFamTensorV → Real :=	def S717CorrectedRootLabelRegionNormBound : Prop :=	PROVED	False	no
718	1	S718RootImageRadiusLowerActual.lean	3028	True	noncomputable def rootThetaLabelOne : ThetaLabel (l := l) :=	def RootThetaOneNormFormula : Prop :=	PROVED	False	no
719	2	S719PaperRootHullGapDecompositionActualAdapted.lean	2850	False	structure PaperRootHullScalingDataGap (b : Bad (nativePlaceSelection T)) where	def PaperRootHullSetGap (b : Bad (nativePlaceSelection T)) : Prop :=	INVALID	False	yes
720	1	S720OneFactorTensorNormReductionActual.lean	4027	True	def QVFamBlockMapsFractionalLattice : Prop :=	def QVFamBlockNormPreserving : Prop :=	PROVED	False	no
721	1	S721ActualHullToPaperSignedHullActual.lean	2958	True	noncomputable def paperSignedHullOfActualHullLog	theorem paperSignedHullOfActualHullLog_signed_eq	PROVED	False	no
722	1	S722CorrectHullComparisonActual.lean	2243	True	theorem correct_thetaPilotMagnitude_le_qPilotMagnitude	theorem correct_globalComparison	PROVED	False	no
723	1	S723OneFactorNormPreservingActual.lean	1583	True	def S723ExactGoal : Prop :=		PROVED	False	no
724	3	S724ProbeAdapted.lean	97	False			AUDIT	False	no
725	1	S725PaperHullCorrectedSourceLinkActual.lean	4962	True	def PaperSignedHullCorrected (P : PaperSignedHull X label) : Prop :=	noncomputable def s725PaperXiFSourceLink	PROVED	False	no
726	2	S726PaperHullVsS663GapActualAdapted.lean	4600	False	theorem paperPerBThetaHullLog_nonpos :	theorem rootThetaMagnitudeValue_one_pos :	INVALID	False	yes
727	1	S727RootThetaOneNormFormulaActual.lean	2926	True	theorem rootImageRadius_eq_cNorm_rpow :	def NormalizedOrderCorrectionZero : Prop :=	PROVED	False	no
729	2	S729PaperSignedHullActualHullLogActualAdapted.lean	5353	False	noncomputable def paperThetaProcession (A : Real) :	theorem paperThetaProcession_average (A : Real) :	INVALID	False	yes
730	3	S730PaperRootCarrierActualAdapted.lean	6375	False	theorem root_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}	theorem paper_twoLRoot_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}	GAP	False	yes
732	1	S732NCGLogVolumeNoGo.lean	10922	True	structure PaperLogVolume (Region : Type*) where	theorem logVol_hull (t : Real) (ht : 0 < t) :	GAP	False	no
733	1	S733CorrectedPaperFinalCor312Actual.lean	5419	True	def S733CorrectedHullLog : Prop :=	noncomputable def s733SourceLink	PROVED	False	no
734	1	S734PaperCoefficientBridgeActual.lean	3296	True	def PaperRootThetaLogBridgeCondition (b : Bad (nativePlaceSelection T)) : Prop :=	theorem paperRootThetaLogBridgeCondition_iff_correction_zero	PROVED	False	no
735	5	S735CoefficientNamespaceAuditActualAdapted.lean	2343	False	theorem actual_coefficient_is_order_rfl :	theorem s734_condition_iff_namespace_equality :	AUDIT	False	no
736	2	S736RootNormCoefficientAuditActualAdapted.lean	2922	False	theorem rootNormCoefficient_eq_generatorSupply :	theorem paperOrderCoefficient_eq :	AUDIT	False	no
737	2	S737PaperCoefficientBridgeCorrectionActualAdapted.lean	2031	False	def UnconditionalCoefficientBridgeCorrection : Prop :=	theorem unconditionalBridge_iff_correction :	INVALID	False	yes
738	2	S738QVFamBlockAlignmentActualAdapted.lean	2810	False	def CommonPrimeNormalizedLatticeAlignment : Prop :=	theorem commonPrimeCompletionRingEquiv_norm	INVALID	False	yes
739	2	S739PaperOrderThetaHullActualAdapted.lean	3646	False	noncomputable def paperPerBThetaHullLogPaperOrder : Real :=	theorem paperRootCoefficientFamily_eq_order_div	INVALID	False	yes
740	2	S740SpectralCoefficientAuditActualAdapted.lean	2703	False	noncomputable def paperOrderCoefficient : Real :=	noncomputable def spectralCoefficient : Real :=	AUDIT	False	no
741	1	S741QVFamBlockSMulActual.lean	1789	True	theorem qVFamBlockSMulCompatibility_actual :		PROVED	False	no
742	2	S742SpectralOrderFactorActualAdapted.lean	3926	False	noncomputable def paperOrderCoefficient : Real :=	noncomputable def spectralCoefficient : Real :=	INVALID	False	yes
743	2	S743PaperSignedHullPaperOrderActualAdapted.lean	7868	False	noncomputable def paperOrderThetaHullLog : Real :=	noncomputable def paperOrderThetaHullMagnitude : Real :=	INVALID	False	yes
744	2	S744PaperOrderReplacementActualAdapted.lean	3439	False	noncomputable def paperPerBThetaHullLogPaperOrder : Real :=	def S744CorrectedHullLog : Prop :=	INVALID	False	yes
745	2	S745PaperRootHullNonzeroCorrectionActualAdapted.lean	5469	False	theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :	noncomputable def paperRootThetaHullNonzero : Set (qVFamTensorBlock T b) :=	INVALID	False	yes
746	1	S746OrdinaryOTriActual.lean	3329	True	structure OrdinaryOTri (K : Type u) [Monoid K] where	def ofExponent (u : Kˣ) (n : Nat) : OrdinaryOTri K :=	PROVED	False	no
747	1	S747ZeroLabelHullAuditActual.lean	4230	True	def zeroSignedLabel : SignedLabel l.value :=	theorem rootThetaRegion_zero :	AUDIT	False	no
750	3	S750ProbeAdapted.lean	106	False			AUDIT	False	no
751	1	S751HullAdjunctionActual.lean	2998	True	structure HullAdjunction (X : Type uX) where	theorem hull_fixed (H : HullAdjunction X) (P : Set X) :	PROVED	False	no
753	1	S753StructuralContainmentActual.lean	4848	True	structure QPilotThetaStructuralData where	noncomputable def qPilotThetaStructuralData :	PROVED	False	no
754	1	S754CandidateRootsTorsorActual.lean	2953	False	theorem candidateRoots_ne_zero (r : CandidateRoots T b) : r.1 ≠ 0 := by	noncomputable def candidateRootsSDiv (r s : CandidateRoots T b) :	INVALID	False	yes
757	1	S757QVFamBlockIsometryActual.lean	2013	True	noncomputable def qVFamBlockLinearIsometryEquiv	theorem qVFamBlockLinearIsometryEquiv_norm_map	PROVED	False	no
759	1	S759LSectionCarrierCorrectionActual.lean	2495	True	abbrev LSectionCarrier : Type :=	noncomputable def lDivisorSection (u : LSectionCarrier T b) : Multiplicative Real := u.2	PROVED	False	no
761	2	S761S733SurrogateAuditActualAdapted.lean	3250	False	noncomputable def paperPerBThetaHullLogPaperOrder : Real :=	def S761PaperOrderHullLog : Prop :=	AUDIT	False	no
763	1	S763QPilotRootStackKummerActual.lean	3516	False	def qPilotScalingLog : Real :=	def thetaRootScalingLog : Real :=	INVALID	False	yes
764	1	S764ThetaHullMinVsAverageActual.lean	5910	True	noncomputable def paperThetaHullMinCoefficient : Real :=	noncomputable def paperThetaAverageCoefficient : Real :=	PROVED	False	no
765	1	S765CompletionValueGroupObstructionActual.lean	2056	False	theorem twoL_mul_valuation_eq_order_implies_dvd	theorem no_completion_twoL_root_of_not_dvd	INVALID	False	yes
766	1	S766QPilot2LNormalizationActual.lean	2031	True	noncomputable def paperQPilotScalar : Real :=	noncomputable def paperQPilotMagnitude : Real :=	PROVED	False	no
767	1	S767ThetaHull2lNormalizationActual.lean	2469	True	def thetaHullMagnitude (qMag : Real) (l : Nat) : Real :=	def qPilotSignedLog (qMag : Real) : Real := -qMag	PROVED	False	no
769	1	S769StackyLogVolumeNormalizationActual.lean	3714	False	theorem stackyMuCard :	theorem stackyRootLog_eq_inv_card_mul	INVALID	False	yes
77	1	S77CompletionIntegersEquivActual.lean	2479	True	def completionIntegersCarrierEq : Prop :=	noncomputable def completionIntegersRingEquivOfCarrierEq	GAP	True	no
770	1	S770QVFamBlockNormFactorActual.lean	2771	True	noncomputable def qVFamBlockCoordinateNorm	theorem qVFamBlock_tensor_norm_eq_coordinate	PROVED	False	no
771	2	S771RootNormCarrierActual.lean	3218	True	structure RootNormQVBlock where	noncomputable def rootNormEquiv :	PROVED	False	no
772	1	S772QVFamBlockMapsLatticeActual.lean	4408	False	def PureTensorFractionalLatticeImage : Prop :=	theorem qVFamBlockMapsFractionalLattice_of_pure	INVALID	False	yes
773	1	S773RootCorrectedPaperTargetActual.lean	3234	True	noncomputable def rootCorrectedQPilotMagnitude : Real :=	def RootCorrectedThetaQpilotComparison : Prop :=	PROVED	False	no
775	1	S775PaperOrderQPilotCorrectionActual.lean	3734	True	noncomputable def paperQPilotCoefficientPaperOrder : qVFamTensorV → Real :=	noncomputable def paperQPilotLogPaperOrder : Real :=	PROVED	False	no
777	1	S777PaperTargetRootStackAlignmentActual.lean	3653	True	theorem s777_paperQLog_eq :	theorem s777_structuralContainment :	PROVED	False	no
778	1	S778PaperQPilotHalfRegionActual.lean	5119	True	noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=	theorem qPilotPaperRegion_eq_rootThetaRegion_one :	PROVED	False	no
779	1	S779RootHullNonzeroFixActual.lean	10542	True	abbrev NonzeroLabel := {j : SignedLabel l.value // j.1 ≠ 0}	theorem one_le_exp_of_ne_zero {j : SignedLabel l.value} (hj : j.1 ≠ 0) :	PROVED	False	no
781	1	S781TwoLTargetGapActual.lean	2819	True	def TwoLTarget (T : SourceNativeInitialThetaData.{0} l)	theorem actualQPilotLeTheta :	PROVED	False	no
782	1	S782FiniteRootStackExtensionActual.lean	6740	True	noncomputable def stackMuRoot : (rootNormedAmbient T b)ˣ :=	theorem stackMuRoot_pow :	PROVED	False	no
783	1	S783Mu2lRootExtensionAuditActual.lean	2581	True	def Mu2lInRootBase : Prop :=	def Mu2lInRootExtension : Prop :=	AUDIT	False	no
784	1	S784RootNormRegionsActual.lean	5571	True	def rootNormSet (S : Set (qVFamTensorBlock T b)) : Set (RootNormQVBlock (T := T) b) :=	abbrev rootNormQPilotRegion : Set (RootNormQVBlock (T := T) b) :=	PROVED	False	no
785	1	S785PaperOrderThetaHullBypassActual.lean	3126	True	theorem paperThetaHullLogPaperOrder_eq_paperRoot :	theorem paperRootCoefficientFamily_eq_order_div :	PROVED	False	no
788	1	S788PaperQpilotRegionActual.lean	4910	True	def oneSignedLabel : SignedLabel l.value :=	theorem oneSignedLabel_gauss :	PROVED	False	no
789	1	S789StackMuActionActual.lean	1803	True	theorem leftMul_not_mulAut		PROVED	False	no
79	1	S79IntegralRingEquivActual.lean	2405	True	theorem completionIntegersCarrierEq_holds :	noncomputable def completionIntegersEquivIntegers :	GAP	True	no
790	1	S790StackToPaperQPilotThetaActual.lean	5693	True	theorem stackRootSection_divisor_order :	theorem stackQSection_divisor_order :	PROVED	False	no
792	2	S792RootStackPaperHullRebaseActualAdapted.lean	3246	False	noncomputable def paperRootHullLogRebased : Real :=	theorem paperRootHullLogRebased_eq :	INVALID	False	yes
793	1	S793PaperLeastLambdaOHullActual.lean	7570	True	abbrev PaperLabel := SignedLabel l.value	abbrev PaperNonzeroLabel := {j : PaperLabel (l := l) // j.1 ≠ 0}	PROVED	False	no
794	1	S794LStarProcessionAverageActual.lean	4746	True	def paperThetaLabelToSigned (i : PaperThetaLabel l) : SignedLabel l.value :=	noncomputable def paperThetaProcession : WeightedValues (PaperThetaLabel l) where	PROVED	False	no
795	1	S795OrderSemanticsActual.lean	2527	True	theorem qVFamily_order_eq_valuation :	theorem qVFamily_order_coprime_actual :	PROVED	False	no
797	2	S797PaperHullFirstAuditActual.lean	4039	True	noncomputable def paperHullFirstCarrier : Set (qVFamTensorBlock T b) :=	theorem paperHullFirstCarrier_eq_paperRootThetaHull :	AUDIT	False	no
798	1	S798OtRootStackSectionActual.lean	4883	True	theorem stackQSection_divisor_order :	theorem stackRootSection_divisor_order :	PROVED	False	no
799	1	S799LeastLambdaOPaperTargetActual.lean	4089	True	noncomputable def paperQPilotRegionLeast : Set (qVFamTensorBlock T b) :=	theorem paperQPilotRegionLeast_eq_least :	PROVED	False	no
800	1	S800LeastLambdaOHullActual.lean	5590	True	noncomputable def lambdaORegion (c : qVFamTensorV → Real) :	def candidateHulls (P : Set (qVFamTensorBlock T b)) :	PROVED	False	no
801	1	S801PaperHullLogActual.lean	4439	True	theorem paperLeastLambdaOHull_eq_paperQPilotRegion :	noncomputable def paperHullLog	PROVED	False	no
802	2	S802QVFamBlockMapsLatticeActualAdapted.lean	3597	False	theorem pureTensor_mem_fractionalLattice	theorem qVFamBlockMapsFractionalLattice_actual :	INVALID	False	yes
803	1	S803RootNormCarrierDecisionActual.lean	3404	True	theorem rootNormCarrier_norm_eq_actual	def RootNormTensorFractionalLattice : Set (RootNormQVBlock (T := T) b) :=	PROVED	False	no
804	1	S804FinalCor312NonzeroActual.lean	3495	True	def S804CorrectedHullLog (P : PaperSignedHull X label) : Prop :=	noncomputable def s804SourceLink	PROVED	False	no
805	1	S805NonzeroHullReplacementActual.lean	4137	True	noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=	theorem qPilotPaperRegion_eq_rootThetaRegion_one :	PROVED	False	no
806	1	S806PaperRootHullNonzeroGapsActual.lean	4700	True	theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :	noncomputable def paperRootMinimalRegion : Set (qVFamTensorBlock T b) :=	PROVED	False	no
807	3	S807CancellationNoGoActual.lean	6663	False	theorem norm_add_eq_left_of_norm_lt {x y : K} (h : ‖y‖ < ‖x‖) :	theorem norm_sum_eq_of_unique_max {ι : Type*} (s : Finset ι) (f : ι → K) (i0 : ι)	GAP	True	yes
809	1	S809PaperLeastHullRootStackBridgeActual.lean	4324	True	def PaperLeastHullLogFormulaTarget : Prop :=	structure PaperLeastHullCompletionData where	PROVED	False	no
810	1	S810LeastHullPaperCarrierActual.lean	3444	True	noncomputable def paperHullFirstCarrierCorrected : Set (qVFamTensorBlock T b) :=	theorem paperHullFirstCarrierCorrected_eq_lambdaORegion :	PROVED	False	no
811	1	S811StackMuPermActionActual.lean	2583	True	abbrev StackMuGroup : Type := rootsOfUnity (2 * l.value) (rootStackExtension T b)	noncomputable def stackMuPerm (ζ : StackMuGroup T b) :	PROVED	False	no
812	1	S812LeastLambdaOFiniteLStackActual.lean	4073	True	theorem paperLeastLambdaOHullLog_formula	theorem paperQPilotLogLeast_le_paperLeastHullLog	PROVED	False	no
813	1	S813PaperInterfaceHub.lean	4311	True	structure PaperHullLogInterface (X : Type*) where	structure StackyHullLogInterface (X : Type*) extends PaperHullLogInterface X where	PROVED	False	no
814	2	S814SkeletonQuantizedLeastHullActual.lean	18533	True	noncomputable def valueGroupSkeletonLength (c : Real) : Real :=	noncomputable def paperQPilotExponentFamily : qVFamTensorV -> Real :=	GAP	True	no
815	1	S815PaperScalingDataFiniteLActual.lean	3732	True	theorem paperScalingData_nonempty_iff_localGenerator :	structure FiniteLScalingGenerator where	PROVED	False	no
816	1	S816StackyHullInterfaceActual.lean	5508	True	noncomputable def hull : Set (qVFamTensorBlock T b) :=	noncomputable def qPilotRegion : Set (qVFamTensorBlock T b) :=	PROVED	False	no
817	1	S817StackRootUnitNormActual.lean	5048	True	theorem stackRootUnit_norm_eq_rootNormedElementNorm :	theorem stackRootUnit_norm_eq_p_rpow :	PROVED	False	no
818	1	S818StackHaarNormalizationAuditActual.lean	3154	True	noncomputable def stackHaarBallLog : Real :=	theorem stackHaarNormalizationBridge_iff :	AUDIT	False	no
819	1	S819PaperRootCompletionGeneratorActual.lean	4174	True	noncomputable def paperCRoot : Real :=	theorem paperCRoot_eq_order_div :	PROVED	False	no
82	3	S82ProbeAdapted.lean	161	False			AUDIT	False	no
820	1	S820FiniteLScalingGeneratorActual.lean	5216	True	noncomputable def stackRootUnit : (rootStackExtension T b)ˣ :=	theorem stackRootUnit_ne_zero :	PROVED	False	no
821	1	S821StackHaarScalingAuditActual.lean	3226	True	noncomputable def stackHaarUnitBallLog : Real :=	noncomputable def stackHaarBallScalingFactor : Real :=	AUDIT	False	no
822	3	S822StackyCardActualAdapted.lean	3093	False	theorem stackMuUnit_isPrimitiveRoot :	theorem stackMuGroup_card :	INVALID	False	yes
823	1	S823StackHaarNormalizedActual.lean	3816	True	noncomputable def normalizedRootStackHaar : Measure (rootStackExtension (l := l) T b) :=	noncomputable def normalizedRootStackUnitBallLog : Real :=	PROVED	False	no
824	1	S824RootStackyHaarVolumeActual.lean	20475	True	noncomputable def stackMuElem : rootStackExtension T b :=	theorem stackMuElem_pow :	GAP	True	no
825	1	S825StackFactorCNormEquivActual.lean	4684	True	theorem stackRootUnitFactor_eq_one_iff_norm_eq_paperNorm (i : qVFamTensorV) :	theorem stackRootUnitFactorOne_iff_norm_eq_paperNorm :	PROVED	False	no
826	1	S826CNormOrderRamificationActual.lean	5514	True	def QVFamNormalizedNormCompatibility : Prop :=	theorem qVFamNormalizedCoefficient_eq_order_div_e	PROVED	False	no
827	1	S827PaperValueGroupNormCardActual.lean	3129	True	abbrev paperValueGroupPlace : NumberField.FinitePlace T.arithmetic.F :=	def PaperNormValuationCard : Prop :=	GAP	False	no
828	2	S828PaperRootValueGroupActualAdapted.lean	3210	False	def PaperRootValueGroupDivisibility : Prop :=	theorem paperRootInValueGroup_iff_divisibility :	INVALID	False	yes
829	1	S829PaperNormValuationSpectralActual.lean	3482	False	theorem paperGeneralNormalizedNormFormula	theorem paperGeneralNormalizedLogFormula	INVALID	False	yes
830	1	S830ValueGroupNormChainActual.lean	2432	True	structure PaperValueGroupNormChain where	theorem valueGroupNormCharacterization_of_chain	PROVED	False	no
831	1	S831StackHaarDimensionActual.lean	3844	True	noncomputable def d : Nat :=	noncomputable def dK : Nat :=	PROVED	False	no
832	1	S832DFactorAbsorptionAuditActual.lean	1767	True	theorem dFactor_eq_iff (d L : Real) :	theorem weighted_dFactor_iff (w d L : Real) (hw : w ≠ 0) :	AUDIT	False	no
833	1	S833PaperNormalizedStackHaarActual.lean	4964	True	noncomputable def paperNormalizedRootStackHaar (d : Nat) :	noncomputable def paperNormalizedRootStackRootBallLog (d : Nat) : Real :=	PROVED	False	no
835	1	S835PaperRootValueGroupIffActual.lean	3381	True	def PaperRootValueGroupDivisibility : Prop :=	theorem paperRootInValueGroup_iff_divisibility :	PROVED	False	no
836	1	S836NormFormulaFixAuditActual.lean	1668	True	structure NormFormulaFixSpec where	def AnalyticFormulaSource : String :=	AUDIT	False	no
837	1	S837PaperRootMinimalCompactActual.lean	3140	True	def S837MinimalCompactRequired : Prop :=	def S837MinimalOpenRequired : Prop :=	PROVED	False	no
838	1	S838QVFamilyDivisibilityActual.lean	2925	True	theorem l_not_dvd_order :	theorem not_twoL_dvd_of_e_one	PROVED	False	no
839	1	S839PaperRootMinimalProductCompactActual.lean	5079	True	noncomputable def s839FractionalLattice : Submodule ℤ_[(qVFamTensorP T b)]	noncomputable def s839HolomorphicLattice : Submodule ℤ_[(qVFamTensorP T b)]	PROVED	False	no
840	1	S840QVFamRamificationAuditActual.lean	2936	True	def QVFamRamificationExponentOne : Prop :=	theorem qVFamRamificationExponent_pos :	AUDIT	False	no
841	1	S841FractionalCompactAbsorptionActual.lean	4088	True	theorem s841FractionalCompact :	def S841PointwiseAbsorption : Prop :=	PROVED	False	no
850	1	S850LocalQParameterNormalizationActual.lean	1734	True	noncomputable def paperRamificationIndex : Nat :=	noncomputable def paperOrderPi (q : FinitePlaceQCandidate place) : Int :=	PROVED	False	no
851	1	S851PointwiseAbsorptionAuditActual.lean	3603	True	def S851FractionalMulLe : Prop :=	theorem s851Pointwise_iff_mulLe :	AUDIT	False	no
853	2	S853PaperOrderNoEActual.lean	3657	True	theorem paperRootCoefficientFamily_eq_order_div :	theorem paperRootCoefficientFamily_no_e (i : qVFamTensorV) :	PROVED	False	no
854	1	S854ProductCompactRouteActual.lean	4145	True	theorem s854HolomorphicCompact :	def S854ProductCompact : Prop :=	PROVED	False	no
855	1	S855OtriLogVolumeInterfaceActual.lean	3089	True	noncomputable def stackQDivisorOrder : Real :=	noncomputable def stackRootDivisorOrder : Real :=	PROVED	False	no
856	1	S856LogShellIntrinsicVolumeAuditActual.lean	5437	True	structure SourceLogShellIntrinsicVolume	def SourceLogShellIntrinsicVolumeSpec (D : SourceLogShellDatum.{u}) : Prop :=	AUDIT	False	no
857	1	S857OtriLogVolumeInterfaceActual.lean	4055	True	structure OtriLogVolumeInterface (X : Type*) where	noncomputable def otriLogVolumeInterface	PROVED	False	no
858	1	S858PaperGapConditionalCor312Actual.lean	7604	True	structure PaperGapIntrinsicVolume where	structure PaperGap (P : PaperSignedHull X label) where	PROVED	False	no
859	1	S859PaperIntrinsicLogVolumeActual.lean	2417	True	noncomputable def paperIntrinsicLogVolume (u : StackSectionCarrier (l := l) T b) : Real :=	theorem paperIntrinsicLogVolume_root :	PROVED	False	no
860	1	S860GlobalCor312AuditActual.lean	3856	True	noncomputable def weightedQPilot : Real :=	noncomputable def thetaHullScalar : Real :=	AUDIT	False	no
861	1	S861RootCharacterNormComparisonActual.lean	2892	True	def RootNormedCharacterNormComparison (n : Nat) : Prop :=	def RootHaarFactorNormPow (n : Nat) : Prop :=	PROVED	False	no
862	1	S862OtriLogVolumeInterfacePaperActual.lean	5528	True	noncomputable def paperOtriPlace : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=	noncomputable def otriQDivisorOrder : Real :=	PROVED	False	no
863	1	S863ProductImageCompactActual.lean	4366	True	def s863MulImage : Set (qVFamTensorBlock T b) :=	theorem s863MulImageCompact : IsCompact (s863MulImage (l := l) T b) := by	PROVED	False	no
864	1	S864PaperLambdaOLogVolumeActual.lean	3317	True	noncomputable def paperLambdaOLogVolume (lam : qVFamTensorV → Real) : Real :=	theorem paperLambdaOLogVolume_cRoot :	PROVED	False	no
865	1	S865RootHaarFactorNormPowActual.lean	4192	True	noncomputable def rootHaarFactorNormPowExactGoal : Prop :=	theorem rootHaarFactor_normPow_actual :	PROVED	False	no
866	1	S866RootStackCharacterNormLiftActual.lean	3804	True	noncomputable def rootStackAlgebraMapUnits :	def RootStackHaarCharRestrictionBridge (n : Nat) : Prop :=	PROVED	False	no
867	1	S867OtriPaperIntegrationActual.lean	4581	True	theorem s867_intrinsicRoot_eq_neg_lambdaO :	noncomputable def s867OtriInterface	PROVED	False	no
868	1	S868GlobalPaperTargetInterfaceActual.lean	3929	True	theorem leastHullPaperRegion_actual (b : Bad (nativePlaceSelection T)) :	def PaperHullLogFormulaGap (b : Bad (nativePlaceSelection T)) : Prop :=	PROVED	False	no
869	1	S869OtriGapsFilledActual.lean	4206	True	noncomputable def otriNonunitLogMeasure : StackSectionCarrier (l := l) T b → Real :=	theorem otriNonunitLogMeasure_root :	PROVED	False	no
87	1	S87OBoundaryDecompositionActual.lean	5156	True	noncomputable def dvrUniformizer : Integers (CommonPrimeCompletion place) := by	theorem dvrUniformizer_irreducible :	GAP	True	no
870	1	S870RootStackRestrictionBridgeActual.lean	3179	True	theorem rootStack_scalar_det (u : rootNormedExtension T b) :	def RootStackGeneralNormFormula : Prop :=	PROVED	False	no
872	1	S872OtriLogVolumeInterfaceActual.lean	3144	True	structure OtriLogVolumeInterface (X : Type) where	noncomputable def paperLogVolumeOnHull :	PROVED	False	no
873	1	S873PaperGapIntrinsicVolumeActual.lean	5251	True	noncomputable def stackDivisorLogMap :	noncomputable def gapLogShellDatum : SourceLogShellDatum where	PROVED	False	no
874	1	S874GlobalInterfaceFillActual.lean	4467	True	def leastHullPaperRegionGlobal : Prop :=	theorem leastHullPaperRegionGlobal_actual :	PROVED	False	no
875	1	S875PaperGapHullLogActual.lean	3379	True	def S875HullLogDatum : Prop :=	theorem paperLeastLambdaOHullLog_eq_neg_order_div	PROVED	False	no
876	1	S876CorrectedGlobalTargetActual.lean	3378	True	abbrev PaperLeastHullData (b : Bad (nativePlaceSelection T)) : Type :=	noncomputable def paperQPilotWeightedLeast : Real :=	PROVED	False	no
877	1	S877WeightedIdentificationActual.lean	4694	True	def HqCorrected : Prop :=	def HthetaCorrected : Prop :=	PROVED	False	no
878	1	S878RootStackCharacterNormDirectActual.lean	3298	True	noncomputable def rootStackHaarFactor (u : (rootStackExtension T b)ˣ) : ENNReal :=	def RootStackHaarFactorNormPow (n : Nat) : Prop :=	PROVED	False	no
879	1	S879RootStackNormFormulaInputsActual.lean	3692	True	theorem rootStack_scalar_det_actual (u : rootNormedExtension T b) :	def ENormExtensionFormula : Prop :=	PROVED	False	no
880	1	S880S867ExactFillActual.lean	3101	True	theorem s880PaperLeastHullLogDatumQVFam :	noncomputable def s880CarrierVolume :	PROVED	False	no
881	1	S881PaperGapIntrinsicVolumeS869Actual.lean	3618	True	def S881HullLogExactGap : Prop :=	theorem S881HullLogExactGap_eq_S873 :	PROVED	False	no
882	1	S882PerBCorrectedActual.lean	3911	True	theorem rootThetaHull_eq_canonicalUnitReference :	theorem perBThetaHullLog_eq_zero :	PROVED	False	no
883	1	S883HullLogSingleFieldActual.lean	4783	True	theorem lambdaOLogVolume_eq_gapVolumeLog :	theorem s883HullLogExactGap_iff_lambdaO :	PROVED	False	no
884	1	S884PaperGapIntrinsicVolumeRebuildActual.lean	4410	True	noncomputable def stackDivisorLogMap :	noncomputable def gapLogShellDatum : SourceLogShellDatum where	PROVED	False	no
885	1	S885RootStackUniformizerNormActual.lean	3962	True	def S885UnitFactorOne : Prop :=	def S885UnitDecomposition (pi : (rootStackExtension T b)ˣ) : Prop :=	PROVED	False	no
886	1	S886ENormExtensionFormulaActual.lean	1443	True	theorem eNormExtensionFormula_actual :	theorem rootStackNormFormulaInputs_actual :	PROVED	False	no
887	1	S887RootStackHaarDetViaS861EActual.lean	3440	True	def RootStackCharacterNormComparisonAt (n : Nat) : Prop :=	def RootStackCharacterNormComparisonAtDQp : Prop :=	PROVED	False	no
888	1	S888HqHthetaActual.lean	2926	True	def HthetaNoTwoL : Prop :=	theorem s877_htheta_iff_extra (hno : HthetaNoTwoL T) :	PROVED	False	no
889	1	S889CompatibilityScalingGroupoid.lean	2681	True	structure ScalingGraph where	inductive Path : G.Obj → G.Obj → Type	PROVED	False	no
890	1	S890CompatibilityScalingInstanceActual.lean	4756	True	noncomputable def qClassicalLog : Real :=	noncomputable def qRootLog : Real :=	PROVED	False	no
891	1	S891IndScaleOneEdgesActual.lean	3143	True	structure IndInvarianceData (α : Type) where	inductive IndEdge (D : IndInvarianceData α) (a b : α) : Type	PROVED	False	no
892	2	S892RootStackGeneralNormFormulaActualAdapted.lean	3060	False	theorem rootStackNormExtensionFormula_actual :	theorem finrankL_eq_dK_mul_dLK :	INVALID	False	yes
893	1	S893RootStackDVRInstanceActual.lean	3071	True	def S893AmbientUltrametricRequired : Prop :=	def S893NormedAlgebraQpLRequired : Prop :=	PROVED	False	no
894	1	S894HqPositiveActual.lean	3303	True	theorem hqWeightedCNormOrder_of_cNorm_eq_order	theorem hq_weighted_term_eq_zero_of_cNorm_eq_order	PROVED	False	no
895	1	S895HthetaPositiveActual.lean	4155	True	theorem perBThetaHullLog_eq_leastHullLog_of_bridges	theorem thetaHullScalar_eq_leastHullWeighted_of_bridges	PROVED	False	no
896	2	S896NonzeroPerBCorrectedActualAdapted.lean	5094	False	def ClosedInput (b : Bad (nativePlaceSelection T)) : Prop :=	theorem paperRootThetaHullNonzero_eq_qPilotPaperRegion	INVALID	False	yes
897	1	S897ECharacterNormViaUniformizerActual.lean	3222	True	theorem rootStackCharacterNormComparisonAtDQp_of_factorNormPow	theorem rootStackCharacterNormComparisonAtDQp_of_uniformizerData	PROVED	False	no
898	1	S898PaperGapFromScalingActual.lean	3593	True	theorem thetaHullLog_eq_neg_paperRoot :	theorem thetaHullLog_eq_gapVolumeLog :	PROVED	False	no
899	1	S899CNormOrderRamificationActual.lean	4122	True	def S899NormCompatibility : Prop :=	def S899RamificationOne : Prop :=	PROVED	False	no
900	2	S900PerBThetaHullLogNonzeroActualAdapted.lean	4642	False	theorem rootMinimalRegion_closed :	theorem paperRootThetaHullNonzero_eq_qPilotPaperRegion :	INVALID	False	yes
901	19	S901ProbeAdapted.lean	173	False			AUDIT	False	no
902	1	S902RootStackDVRInstancesActual.lean	3075	True	def S902NormedAlgebraLERequired : Prop :=	def S902NormedAlgebraQpERequired : Prop :=	PROVED	False	no
903	1	S903ECharacterNormLightActual.lean	2545	True	def S903ECharacterNormExactInput : Prop :=	theorem s903_hchar_of_exactInput	PROVED	False	no
904	2	S904PaperCor312ScalingActualAdapted.lean	4239	False	noncomputable def s904PaperGap	theorem paperCor312_of_scaling	INVALID	False	yes
907	1	S907LVExToyActual.lean	5050	True	abbrev V : Type := ℝ × ℝ	def sigma (v : V) : V := (-v.1, v.2)	PROVED	False	no
908	1	S908ORExpansionContainmentActual.lean	4718	True	structure ORExpansionData (X : Type u) (ι : Type v) where	theorem orExpansion_comparison	PROVED	False	no
909	1	S909PaperSVsLeastHullActual.lean	2481	True	noncomputable def modelHull : Set (qVFamTensorBlock T b) :=	theorem modelHull_eq_qPilotPaperRegion :	PROVED	False	no
910	2	S910ProbeAdapted.lean	157	False			AUDIT	False	no
911	1	S911PaperQPilotHullCorollaryActual.lean	6829	True	theorem paperRootCoefficientFamily_sum_eq :	theorem paperSkeletonQPilotLog_le_hull :	PROVED	False	no
912	2	S912RootStackNormedAlgebraActualAdapted.lean	1668	False			STATEMENT	False	yes
913	1	S913PaperMonodromyActual.lean	4331	True	noncomputable def paperQPilotScalar : Real :=	noncomputable def paperThetaScalar : Real :=	PROVED	False	no
914	1	S914PaperLVExInstantiationActual.lean	3182	True	noncomputable def s914R : Set (qVFamTensorBlock T b) :=	noncomputable def s914S : Set (qVFamTensorBlock T b) :=	PROVED	False	no
915	2	S915MultiradialHullCompareActualAdapted.lean	3863	False	noncomputable def paperMultiradialPossibleImageUnion : Set (qVFamTensorBlock T b) :=	noncomputable def paperMultiradialHull : Set (qVFamTensorBlock T b) :=	INVALID	False	yes
916	1	S916PaperMultiradialSActual.lean	4001	True	structure PaperIndImageData where	noncomputable def paperSImageUnion (D : PaperIndImageData (l := l) T b) :	PROVED	False	no
917	1	S917IndImageUnionActual.lean	4122	True	theorem currentMultiradialImageUnion_eq_theta :	theorem qPilotPaperRegion_subset_thetaImageNZ :	PROVED	False	no
918	3	S918InequalityMeasureActual.lean	3165	True	theorem s914S_measure_lt_top : mu (s914S (l := l) T b) < ⊤ :=	theorem s918RPos_actual : S918RMeasurePosRequired (l := l) T b mu := by	PROVED	False	no
919	1	S919GlobalWeightedInequalityActual.lean	3432	True	noncomputable def weightedPaperV	theorem weightedPaperV_mono	PROVED	False	no
92	1	S92NormRatioUnifiedActual.lean	4561	True	theorem qVFamNormRatio_eq_normalized_div_default	theorem qVFamDefaultNorm_pos (b : Bad (nativePlaceSelection T)) :	PROVED	False	no
920	1	S920SHullFinitenessActual.lean	4651	True	abbrev s920O : Set (qVFamTensorBlock T b) :=	theorem s920PaperRegion_subset_O (j : SignedLabel l.value) :	PROVED	False	no
921	1	S921RQpilotPaperRegionPositivityActual.lean	3747	True	theorem s921R_zero_mem : (0 : qVFamTensorBlock T b) ∈ s914R (l := l) T b := by	theorem s921R_nonempty : (s914R (l := l) T b).Nonempty :=	PROVED	False	no
922	1	S922ModelHullPaperSHullInequalityActual.lean	5312	True	abbrev S922O : Set (qVFamTensorBlock T b) :=	theorem S922O_closed : IsClosed (S922O (l := l) T b) :=	PROVED	False	no
923	4	S923CheckAdapted.lean	223	False			AUDIT	False	no
924	1	S924S918InequalityFixedActual.lean	3174	True	theorem s924R_measure_pos_of_interior	def S924SHullFinite : Prop :=	PROVED	False	no
925	1	S925HullFinitenessActual.lean	2774	True	theorem s914S_measure_lt_top_actual :	theorem paperRootThetaHullNonzero_measure_lt_top :	PROVED	False	no
926	1	S926GlobalIntegrationActual.lean	4104	True	noncomputable def perBModelLog (b : Bad (nativePlaceSelection T)) : Real :=	noncomputable def perBPaperSLog (b : Bad (nativePlaceSelection T)) : Real :=	PROVED	False	no
927	1	S927FinalWeightedInequalityActual.lean	3231	True	noncomputable def perBVRGlobal (b : Bad (nativePlaceSelection T)) : Real :=	noncomputable def perBVSGlobal (b : Bad (nativePlaceSelection T)) : Real :=	PROVED	False	no
928	2	S928ActualIndImageGapActual.lean	3204	True	structure ActualIndImageData where	noncomputable def actualIndImage (D : ActualIndImageData (l := l) T b) :	PROVED	False	no
929	1	S929RQpilotPaperSHullFinalActual.lean	3354	True	theorem s914R_eq_modelHull :	theorem S918RMeasurePosRequired_actual :	PROVED	False	no
93	1	S93BoundaryLogCompatibilityActual.lean	4072	True	theorem boundaryLogWith_unit	structure UniformizerChangeData	GAP	True	no
930	2	S930GlobalWeightedPaperInequalityActualAdapted.lean	2963	False	def S930IndImageBounded	noncomputable def s930VR (b : Bad (nativePlaceSelection T)) : Real :=	INVALID	False	yes
931	1	S931IndImageBoundedActual.lean	3008	True	theorem indImageBounded_iff :	def S931IndImageBoundGap : Prop :=	PROVED	False	no
932	1	S932S918ActualPositivityActual.lean	3005	True	theorem s914R_measure_pos_actual :	theorem s932V_R_le_V_S :	PROVED	False	no
934	3	S934PaperIndImageExactGapActualAdapted.lean	2157	False	structure PaperIndImageExactGap where	def PaperIndImageExactGapRequired : Prop :=	INVALID	False	yes
936	1	S936IndImageTransferActual.lean	2986	True	structure S936IndImageTransferData where	def S936IndImageTransferRequired : Prop :=	PROVED	False	no
937	1	S937IndImageActual.lean	2481	True	theorem s937Ind1Image_nonempty	theorem s937Ind2Image_nonempty	PROVED	False	no
939	2	S939PaperSCarrierAuditActualAdapted.lean	3943	False	abbrev PaperSCarrier (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type uR :=	abbrev ModelSCarrier (T : SourceNativeInitialThetaData.{0} l)	AUDIT	False	no
940	1	S940Ind3ImageActual.lean	4819	True	noncomputable def ind1ImageOfSet	theorem ind1ImageOfSet_nonempty	PROVED	False	no
941	1	S941PaperCor312FaithfulContractActual.lean	4643	True	def PaperCor312FaithfulObject : Prop :=	theorem paperCor312_object_actual : PaperCor312FaithfulObject (l := l) T D :=	PROVED	False	no
942	1	S942ActualPaperSInterfaceActual.lean	4180	True	structure ActualPaperIndImage (D : PaperIndImageData (l := l) T b) where	structure ActualPaperSInterface where	PROVED	False	no
943	1	S943ActualIndImageTransferActual.lean	3316	True	structure ActualIndImageTransfer where	def ActualIndImageTransferRequired : Prop :=	PROVED	False	no
944	1	S944PaperSHullFiniteActual.lean	3434	True	theorem paperSHull_measure_lt_top_perB	theorem s934PaperSHullFinite_of_bounded	PROVED	False	no
945	4	S945CheckAdapted.lean	451	False			AUDIT	False	no
946	2	S946TensorPaperSContainmentActual.lean	3082	True	def S946TensorPointwiseImageCondition : Prop :=	theorem s946QPilotContainment_iff_pointwise :	PROVED	False	no
949	1	S949PaperQPilotCarrierBridgeActual.lean	3674	True	structure PaperCarrierAssembly where	noncomputable def bridgeOfAssembly (A : PaperCarrierAssembly (T := T) b) :	PROVED	False	no
950	1	S950PaperFaithfulFinalInequalityActual.lean	3406	True	structure PaperFaithfulFinalData where	def PaperFaithfulFinalInequality	PROVED	False	no
951	1	S951ActualIndImageTransferActual.lean	5201	True	abbrev S951Ind1Carrier (j : Fin (capsuleLevels l)) (vQ : C.VQ)	abbrev S951Ind2Carrier (j : Fin (capsuleLevels l)) (vQ : C.VQ) : Type :=	PROVED	False	no
952	1	S952IndImageSubsetOActual.lean	2638	True	def S952IndImageSubsetO : Prop :=	theorem s952IndImageSubsetO_iff_bounded :	PROVED	False	no
956	3	S956ClosureContainmentActual.lean	2696	True	noncomputable def paperTensorSClosure : Set (FinalLValuedCarrier T b) :=	def S956ClosureContainment : Prop :=	PROVED	False	no
957	1	S957TensorClosureContainmentActual.lean	3075	True	noncomputable def paperTensorHull : Set (FinalLValuedCarrier T b) := by	def S957ThetaImageDenseInQPilot : Prop :=	PROVED	False	no
958	1	S958ThetaDensityExactActual.lean	3484	True	theorem s958_density_iff_approximation :	def S958DensityExactInput : Prop :=	PROVED	False	no
959	1	S959FinalLValuedTopologyExactActual.lean	3462	True	def S959FiniteProductTopologyModel : Prop :=	def S959FinalLLocallyCompactRequired : Prop :=	PROVED	False	no
960	1	S960PointwiseApproxActual.lean	3669	True	theorem qPilotPaperRegion_eq_rootThetaRegion_one :	theorem qPilotImage_eq_thetaJ1Image :	PROVED	False	no
961	1	S961FinalLTensorLogVolumeFromCarrierTopologyActual.lean	3698	True	noncomputable def finalLTensorLogVolumeDataOfCarrierTopology	noncomputable def carrierTopologyDataOfFinalLTensor	PROVED	False	no
962	1	S962TensorPacketPaperInequalityActual.lean	4658	True	noncomputable def tensorNormalizedLogVolume	theorem tensorNormalizedLogVolume_mono	PROVED	False	no
963	1	S963ActualToBlockProjectionActual.lean	4772	True	structure S963IndProjectionTriple	noncomputable def s963TransferOfProjections	PROVED	False	no
964	1	S964TensorPacketIndBoundedExactActual.lean	2246	True	structure S964TensorIndBoundedData where	def S964TensorIndBoundedRequired : Prop :=	PROVED	False	no
965	1	S965FinalLCarrierTopologyActual.lean	3265	True	structure S965CarrierLinearization where	def S965CarrierLinearizationRequired : Prop :=	PROVED	False	no
966	1	S966ActualToBlockActual.lean	4691	True	structure S966ToQVFamActual	def S966ToQVFamRequired : Prop :=	PROVED	False	no
967	1	S967FinalLIndBoundedActual.lean	3266	True	noncomputable def finalLUnitRegion : Set (FinalLValuedCarrier T b) :=	noncomputable def finalLImageOfQVam (E : Set (qVFamTensorBlock T b)) :	PROVED	False	no
968	1	S968FinalTensorInequalityCor312Actual.lean	4606	True	noncomputable def s968Inclusion	theorem paperCor312_of_tensorInequality	PROVED	False	no
969	1	S969IndCarrierEmbeddingActual.lean	4948	True	structure S969IndCarrierEmbeddingData	noncomputable def s969ProjectionTriple_of_embeddings	PROVED	False	no
970	1	S970FiniteLogShellCarrierActual.lean	2481	True	abbrev FiniteLogShellCarrier (p : Nat) [Fact p.Prime] (d : Nat) : Type :=	structure FiniteLogShellHaarData (d : Nat) where	PROVED	False	no
971	1	S971TensorRegionImageActual.lean	3711	True	noncomputable def tensorThetaRegionImage : Set (FinalLValuedCarrier T b) :=	noncomputable def tensorThetaRegionIndUnion : Set (FinalLValuedCarrier T b) :=	PROVED	False	no
972	1	S972IndAdditiveEmbeddingConditionsActual.lean	5216	True	structure S972IndAdditiveEmbeddingConditions	noncomputable def s972EmbeddingData_of_conditions	PROVED	False	no
973	1	S973QPilotTensorImagePositivityActual.lean	4936	True	def S973QPilotImageInteriorNonempty : Prop :=	theorem s973QPilotImage_measure_pos_of_interior	PROVED	False	no
974	1	S974TensorHullFiniteActual.lean	2351	True	def S974HullSubsetUnitRegion : Prop :=	theorem paperTensorHull_measure_lt_top_of_subset	PROVED	False	no
975	1	S975DensityRegionImageActual.lean	3416	True	noncomputable def rootThetaRegionImageInLValued	noncomputable def paperPossibleRegionImageUnion	PROVED	False	no
976	1	S976FiniteLogShellHaarActual.lean	3166	True	noncomputable def finiteLogShellHaarData (d : Nat) :	theorem finiteLogShellHaarRequired (d : Nat) :	PROVED	False	no
977	1	S977ActualIndImageDataFromEmbeddingsActual.lean	2793	True	theorem s928ActualIndImageData_nonempty_of_embeddings	def S977ExactRequirement : Prop :=	PROVED	False	no
978	1	S978FiniteCarrierHullActual.lean	3743	True	noncomputable def finitePossibleRegionImageUnion :	noncomputable def finitePaperTensorHull :	PROVED	False	no
979	1	S979TensorRegionHullInequalityActual.lean	6263	True	noncomputable def tensorRegionHullLog	theorem qPilotTensorLog_le_tensorRegionHullLog	PROVED	False	no
980	1	S980QPilotImagePositivityActual.lean	3673	True	theorem s980QPilotRegion_measure_pos_of_open	theorem s980FiniteLogShell_unit_pos (p d : Nat) [Fact p.Prime] :	PROVED	False	no
981	1	S981TensorRegionHullFiniteActual.lean	3889	True	def S981TensorRegionHullSubsetUnitRegion : Prop :=	theorem tensorRegionHull_measure_lt_top_of_subset	PROVED	False	no
982	1	S982FinalLTensorFromFiniteQuotientActual.lean	3240	True	structure S982FiniteQuotientBridge where	def S982FiniteQuotientBridgeRequired : Prop :=	PROVED	False	no
983	1	S983PaperXiFSourceLinkConstructionActual.lean	4249	True	noncomputable def paperXiFSourceLinkOfActualTheta	theorem paperXiFSourceLinkOfActualTheta_link_identification	PROVED	False	no
984	1	S984FiniteQuotientBridgeActual.lean	2781	True	def S984FiniteFreeCondition : Prop :=	abbrev S984FiniteQuotientBridge : Type :=	PROVED	False	no
985	1	S985FinalExactAssemblyActual.lean	3329	True	structure S985FinalExactInputs where	theorem s979Hypotheses_of_finalInputs	PROVED	False	no
986	1	S986FiniteQuotientTransportActual.lean	3125	True	structure S986TransportObligations where	def S986TransportObligationsRequired : Prop :=	PROVED	False	no
987	1	S987FiniteQuotientTransportActual.lean	5238	False	noncomputable def carrierTopologyDataOfLinearization	noncomputable def finalLTensorLogVolumeDataOfLinearization	INVALID	False	yes
988	11	S988ExactProbeAdapted.lean	1539	False	structure Data where		AUDIT	False	no
989	1	S989FiniteCarrierDirectActual.lean	4659	True	noncomputable def finitePaperTensorData (d : Nat) :	noncomputable def finiteQPilotImage	PROVED	False	no
990	1	S990FiniteCarrierPositivityFinitenessActual.lean	4974	True	noncomputable def finiteCarrierUnitRegion (d : Nat) :	theorem finiteCarrierUnitRegion_pos (d : Nat) :	PROVED	False	no
991	1	S991S983LinkInputsActual.lean	4110	True	theorem s991SourceIdentifications :	theorem s991SignedQIdentification	PROVED	False	no
992	1	S992FinalIntegrationActual.lean	6199	True	theorem s992S979Hypotheses	noncomputable def s992ConcreteLink	PROVED	False	no
994	1	S994FiniteCarrierCor312Actual.lean	5606	True	structure S994FiniteLinearization where	noncomputable def s994ActualLinearization : S994FiniteLinearization T b where	PROVED	False	no
995	1	S995FiniteCarrierCor312ConclusionActual.lean	5318	True	theorem s995FiniteCarrierCor312Conclusion	theorem s995Cor312Conclusion	PROVED	False	no
996	1	S996FiniteQuotientLinearizationActual.lean	3410	True	noncomputable def s996QVFamLinearization :	def S996FinalLValuedFiniteModuleRequired : Prop :=	PROVED	False	no
997	1	S997FiniteQPilotPositivityActual.lean	3768	True	def S997UnitRegionSubsetQPilot	theorem s997QPilotImage_measure_pos_of_unitRegion_subset	PROVED	False	no
998	1	S998FinitePaperHullFinitenessActual.lean	4077	True	def S998FiniteHullSubsetUnitRegion : Prop :=	theorem finitePaperHull_measure_lt_top_of_subset	PROVED	False	no
999	1	S999HQHC3Actual.lean	3152	True	def S999LineC3Identification : Prop :=	def S999QPilotLogVolumeIdentification : Prop :=	PROVED	False	no
```