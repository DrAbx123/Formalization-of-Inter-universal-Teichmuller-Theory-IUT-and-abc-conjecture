# A477 资产 → DAG 映射（shehdd 区域，只读核对）

日期: 2026-11-11。方法: 只读读取 dag/declaration-dag.json (节点 declarations/files) 与 dag/generated/declarations-index.json；把 99 个关键已有 olean 资产映射到 DAG 节点。未新建/修改任何 Lean 文件、fragment、extra-targets。

## 1. 总览（一行统计）

- 关键资产 99 个：**直接映射 41**；**文件已被 DAG 节点引用但声明名未登记 22**；**文件未被任何 DAG 节点引用 36**。
- DAG 状态：nodes 1311 / edges 2637 / conflicts 0 / validate problems 0；引用我区域文件的 DAG 节点 166 个；`shehdd:*` 节点 72 个（未改）。

| 区域 | 直接映射 | 文件已覆盖 | 未引用 | 合计 |
|---|---|---|---|---|
| IUT III Cor 3.12 tree | 7 | 3 | 6 | 16 |
| IUT III Thm 3.11 tree | 0 | 5 | 2 | 7 |
| IUT II Kummer/log-shell | 10 | 2 | 2 | 14 |
| IUT I Hodge theater / Theta | 12 | 5 | 0 | 17 |
| ABC bridge / Frey / Tate / Fnd | 12 | 7 | 22 | 41 |
| paper 层 | 0 | 0 | 4 | 4 |

## 2. 直接映射（资产 -> DAG 节点）

Cor 3.12: StepXIContract -> iutiii:IUTIII.COR312.TARGET, iutiii:IUTIII.STEPXI.CONTRACT, iutiv-abc:StepXI; Cor312Conclusion -> iutiii:IUTIII.COR312.TARGET; q_positive_of_constructed_stepXI -> iutiii:IUTIII.COR312.WIRING; cor312Conclusion_of_contract -> iuti-ii:IUTIII.Interface.Cor312, iutiii:IUTIII.COR312.WIRING; HullDeterminantLogVolumeFrozenSpec+hullDeterminantLogVolumeFrozenSpec_holds -> iutiii:IUTIII.HULL.DET_LOG_VOLUME; sourceHullVolume_eq_imageVolume_iff -> iutiii:IUTIII.HULL.CARD_GEOMETRY。

Kummer: SourceLogShellDatum -> iuti-ii:IUTII.Kummer.LogShellCarrier, theta-etth:L1; logShell_eq_invScaledPreLogShell/IQSpan -> theta-etth:L1; SourceLogShellInvariantImageIdentification -> e-deep:E1.logShellBridge, iuti-ii:IUTII.Kummer.LogShellAbsTopIII, theta-etth:L2; sourceLocalLogShellDatum -> theta-etth:L8; absoluteKummerMap_eq_one_iff -> iuti-ii:IUTII.Kummer.Absolute.trio, theta-etth:L4; nthPowerSubgroup/absoluteKummerMapQuotient_injective -> theta-etth:L6; possibleImage_subset_of_generator_mem/sourceThetaPilotIQPacket -> iuti-ii:IUTII.Kummer.SourceThetaPilot, theta-etth:L7。

Hodge/Theta: FrobeniusPictureGraphAut/chainTranslation -> iuti-ii:IUTI.HodgeTheater.ThetaLinkGraph; graphAut_eq_translation -> theta-etth:G1; oddTheta -> theta-etth:T1; oddTheta_shift/oddThetaFraction_eval_unconditional/oddTheta_ne_zero_at_i -> theta-etth:T4; gaussExponent/realThetaValue/gaussianSquareSum_formula/toFiniteLabel/representative_toFl -> theta-etth:T5。

ABC: ABCFrontier/bridgeInterface_of_frontier -> iutiv-abc:G3, mainline:abc-frontier, routes:abcfrontier; abcConjecture_of_frontier -> T3-abc-frontier 等; abcFrontier_iff_abcConjecture -> T3-abc-frontier; Cor312ToABCBridgeInterface -> iutiv-abc:G2, legacy-dag:legacy:cor312-bridge-definition; cor312ToABCBridge_abcConjecture -> T1-cor312-abc-bridge, iutiv-abc:G1; cor312ToABCBridge_heightBound -> T1-cor312-abc-bridge, iutiv-abc:G2.b; abcConjecture_iff_freyJProductHeightCriterion -> mainline:abc-freyj-criteria; not_FrontierHeightWeightClause -> mainline:abc-frontier-heightweight-refutation; ABCHeightWeightAdditiveBoundV2 及其 iff -> iutiv-abc:HW.add, mainline:abc-height-weight-additive; ABCLogConjecture -> iutiv-abc:G0.log, mainline:abc-log-equivalence。

## 3. 文件已被 DAG 节点引用、但声明名未登记（22 条）

这些资产所在文件已有节点引用（节点 files 字段覆盖），只是具体声明名未写进节点的 declarations。逐条：

- Cor3.12: cor312_of_constructed_stepXI (Contract.lean) 覆盖节点 hull:HULL.STEPXI.CONTRACT.TREE.CONSUMER,iut-skeleton:StepXI; Cor312Route (Routes.lean) 覆盖 iutiii:IUTIII.COR312.TARGET,iutiii:IUTIII.COR312.WIRING; packetLogVolume_tensorPower (HullDetLogVolumeReduction.lean) 覆盖 hull:X.CONSUMER.DET.TENSOR,iutiii:IUTIII.HULL.DET_LOG_VOLUME。
- Thm3.11: ind1QuotientLift (Ind1Reduction.lean) -> iutiii:IUTIII.IND1; PossibleImage/lowerClosure (Ind3Reduction.lean) -> iutiii:IUTIII.IND3; logShellRayPresentation_univ_iff/k1BoundaryOf_negLogVolumeRayPresentation (SourceK1K2CardReduction.lean) -> hull:X.CONSUMER.KUMMER.ID.HULL.COMPACT,iut-skeleton:K1K2。
- Kummer: kummerRatioHom/kummerMap_eq_one_iff (KummerGaloisClass.lean) -> iuti-ii:IUTII.Kummer.Classes。
- Hodge/Theta: ThetaQDisplacement/hodgeTheaterLink_displacement -> iuti-ii:IUTI.HodgeTheater.ThetaLinkGraph; thetaPacket_eq -> iut-pre-abc:HodgeTheater.familyTransport,iuti-ii:IUTI.HodgeTheater.Family; SourcePlacePartition/sectionMap_injective -> iuti-ii:IUTI.InitialTheta.Definition31。
- ABC: ABCFreyJProductHeightCriterion -> mainline:abc-freyj-criteria; not_ABCFrontierGapReduced -> mainline:abc-frontier-heightweight-refutation,routes:abcfrontier; abcLogBound_exists_iff_rpow_exists/radical_eq_natRadical -> iutiv-abc:G0.log,mainline:abc-log-equivalence; abcInvariantPolynomial_coprime_left/abcInvariantCancellation_le_256 -> mainline:abc-invariant-coprimality; abcJInvariant_den_radical_bounds -> mainline:abc-invariant-radical-bridge。

## 4. 未被任何 DAG 节点引用的已有资产（36 条，登记用）

全部为 olean-新鲜、已编译对象；未挂任何 DAG 节点（文件级也无引用）。

Cor3.12 (6): TateQPilotJComparison.lean: qPilotLogVolume, tateJInvariantLogVolume, qPilotLogVolume_eq_log_prime, qPilotLogVolume_pos, tateJInvariant_norm_mul_q_norm_one; Volume.lean: StepXIFiniteCertificate。
Thm3.11 (2): SourceLabelWeightedDiagonal.lean: labelWeight; SourceSharedBoundary.lean: NonzeroFiniteLabel。
Kummer (2): AlgebraicClosureKummerRoots.lean: exists_root_algebraicClosure, fixed_by_absoluteGalois_mem_base。
ABC/Fnd (22): ABCNonemptyOddBadSupport.lean: abcOddBadPrimeSupport, mem_abcOddBadPrimeSupport_iff; FreyTateAnalyticInput.lean: freyAbcTateCandidateQ_norm_lt_one, _norm_le_invNine, _arithmeticCertificate; FreyWeierstrassCurve.lean: freyWeierstrassCurve_discriminant; ABCModelHeightComparison.lean: rationalFreyWeierstrassCurve_j_height_bounds; TateCurveArithmetic.lean: canonical_equation_coefficients; TateJInvariantNorm.lean: tateJInvariant_norm; TateUniformizationContract.lean: tateParameterUnit, tateParameterUnit_ne_one, CurveIndexedTateUniformization; EllipticTorsion.lean: AllNTorsionRational, galoisActionOnPoint, galoisActionOnLTorsionLinearEquivHom; IntegralUnitLogarithm.lean: unitLog, unitLog_mul; LogarithmLocalInverse.lean: exists_log1p_preimage, integers_subset_integralLogShell; Radical.lean: natRadical_pos; NormLog.lean: unitNormLogDegree; LocalQParameter.lean: FinitePlaceQCandidate。
paper 层 (4): AbcStatementAlignmentActual.lean: abcConjecture_iff_tauCeti; Mzk1GeomCorePreciseToOldActual.lean: toOldWitness, genEll15GeometricCoreStatement_of_precise; Mzk1GeometricCorePreciseActual.lean: Mzk1GeometricCoreWitnessPrecise。

## 5. 真缺失（逐字命名层，语义等价实现均存在；只登记不造文件）

1. IUT III Cor 3.12 顶层陈述逐字命名：索引 IUT312|iut312 命中 0（StepXIContract/Cor312Conclusion/三路线等价实现已有）。
2. IUT II Cor 4.10 逐字命名：cor4[._]?10 命中 0（SignedLabel/Fl 字典、SourceLogShellInvariantImageIdentification、NonzeroFiniteLabel 已有）。
3. IUT III Def 3.8(i) Theta-pilot 对象层逐字命名：命中 0（SourceThetaPilotIQContainment one-place、FinitePlaceThetaPilotScaledRegion 已有）。
4. IUT I Def 3.1(b) 独立 q-parameter 对象逐字命名：命中 0（FinitePlaceQCandidate + ArithmeticQPilot{LogVolume,BaseChange,GlobalNormalization} 已有）。

结论：本区域已有资产充足（99 个关键资产全部存在且 olean 新鲜）；41 个已直接映射 DAG，22 个文件已被节点引用仅缺声明名登记，36 个未引用为可补登记项；逐字命名真缺失 4 条。按 A477 不再新建 Lean 文件。
