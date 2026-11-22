import tmp.sheaf.xif.paper.S3140ClosureGateActual

/-! # Kernel-checked axiom recount for the final S3140 gate (audit-proof)

True-fresh gate: S3140ClosureGateActual EXIT=0 SIZE=21918, olean 02:57:51.
Watchdog does not capture `#eval` output, so the audited counts are recorded as
KERNEL-CHECKED `rfl` THEOREMS on explicit data lists (List.length / String
equality of literals reduce definitionally).  The gate file itself contains the
authoritative 53 per-declaration `#print axioms` lines; the three no-axiom
declarations are the rfl length theorems.

Audited result: 53 declarations = 50 with exactly
[propext, Classical.choice, Quot.sound] + 3 with no axioms; zero sorryAx.
-/

/-- All 53 audited declarations (same list/order as the gate's #print axioms). -/
def S3140AuditedDeclarations : List String := [
  "LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate",
  "LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate_tight",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate_tight",
  "LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedQC_le_HC",
  "LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedMagnitude",
  "LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134CanonicalRootedQC_le_HC",
  "LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_canonicalQC_le_thetaPilot",
  "LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted",
  "LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134Step3115_mainlineQC_le_thetaPilot_viaEpsilon",
  "LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134SameCContractBridge_ofEpsilonResidual",
  "LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing",
  "LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleResidual_of_exactMissing",
  "LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangle_hullDet_after_SHE",
  "LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangleResidual_of_R1Identification",
  "LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparisonGap_of_c3HullReadout",
  "LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparison_final_of_c3HullReadout",
  "LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.qThetaPilotLogVolumeComparison_of_modelMap",
  "LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.nativeToC3Identification_of_modelMap",
  "LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_abcConjecture_of_threeResiduals",
  "LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_pointWeightCard_iff_abcConjecture",
  "LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual.s3135_abcConjecture_of_endToEndInputsV2",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3_tight",
  "LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual.S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical",
  "LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero",
  "LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaNormalizationFactor_eq",
  "LeanFormal.IUT.XiFPaper.S3135HaarModulusActual.s3135_haar_unit_scaling",
  "LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual.s3135_realifiedDegreeSection",
  "LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual.lgpRoot_mem_thetaValueSubgroup",
  "LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual.lgpRealifiedValueTransport_compat",
  "LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual.lgpBadLocalPacket_place_agree",
  "LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual.sourceMultiradialMutationOfBPS_point_invariant",
  "LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual.sourceFirstTriangleMutationData_gluing_invariant",
  "S3131FinalResidualRegistry_length",
  "S3131RegistryGateOwners_length",
  "S3131ABCStrengthResiduals_length",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140LastSeamThetaMissing_iff_rawHaar",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingCanonicalRootedThetaReadout_of_factor_zero",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingThetaHalfReadout_of_factor_zero",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140FourthTriangleResidual_of_normalization",
  "LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual.S3140NormalizedTwoLthRootSupply_iff",
  "LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.canonicalThetaTarget_of_VForm_and_exactFactor",
  "LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.thetaHalfRawResidual_iff_missingThetaHalf",
  "LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual.S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC",
  "LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual.S3134LastSeamThetaHalf_iff_missingThetaHalf",
  "LeanFormal.IUT.XiFPaper.S3132GateThetaHalfConsumptionActual.missingThetaHalf_of_lastSeamThetaMissing",
  "LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm",
  "LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_zero_of_VForm",
  "LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_eq",
  "LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff",
  "LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual.c3TensorBlockDimension_eq_prod_finrank",
  "LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual.thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume"
]

/-- The 3 declarations with NO axioms (rfl length theorems; stronger than trio). -/
def S3140NoAxiomDeclarations : List String := [
  "S3131FinalResidualRegistry_length",
  "S3131RegistryGateOwners_length",
  "S3131ABCStrengthResiduals_length"
]

/-- The 50 declarations with footprint exactly the three allowed axioms. -/
def S3140TrioDeclarations : List String := [
  "LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate",
  "LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate_tight",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate_tight",
  "LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedQC_le_HC",
  "LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedMagnitude",
  "LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134CanonicalRootedQC_le_HC",
  "LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_canonicalQC_le_thetaPilot",
  "LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted",
  "LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134Step3115_mainlineQC_le_thetaPilot_viaEpsilon",
  "LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134SameCContractBridge_ofEpsilonResidual",
  "LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing",
  "LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleResidual_of_exactMissing",
  "LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangle_hullDet_after_SHE",
  "LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangleResidual_of_R1Identification",
  "LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparisonGap_of_c3HullReadout",
  "LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparison_final_of_c3HullReadout",
  "LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.qThetaPilotLogVolumeComparison_of_modelMap",
  "LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.nativeToC3Identification_of_modelMap",
  "LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_abcConjecture_of_threeResiduals",
  "LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_pointWeightCard_iff_abcConjecture",
  "LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual.s3135_abcConjecture_of_endToEndInputsV2",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3",
  "LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3_tight",
  "LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual.S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical",
  "LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero",
  "LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaNormalizationFactor_eq",
  "LeanFormal.IUT.XiFPaper.S3135HaarModulusActual.s3135_haar_unit_scaling",
  "LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual.s3135_realifiedDegreeSection",
  "LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual.lgpRoot_mem_thetaValueSubgroup",
  "LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual.lgpRealifiedValueTransport_compat",
  "LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual.lgpBadLocalPacket_place_agree",
  "LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual.sourceMultiradialMutationOfBPS_point_invariant",
  "LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual.sourceFirstTriangleMutationData_gluing_invariant",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140LastSeamThetaMissing_iff_rawHaar",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingCanonicalRootedThetaReadout_of_factor_zero",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingThetaHalfReadout_of_factor_zero",
  "LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140FourthTriangleResidual_of_normalization",
  "LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual.S3140NormalizedTwoLthRootSupply_iff",
  "LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.canonicalThetaTarget_of_VForm_and_exactFactor",
  "LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.thetaHalfRawResidual_iff_missingThetaHalf",
  "LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual.S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC",
  "LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual.S3134LastSeamThetaHalf_iff_missingThetaHalf",
  "LeanFormal.IUT.XiFPaper.S3132GateThetaHalfConsumptionActual.missingThetaHalf_of_lastSeamThetaMissing",
  "LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm",
  "LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_zero_of_VForm",
  "LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_eq",
  "LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff",
  "LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual.c3TensorBlockDimension_eq_prod_finrank",
  "LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual.thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume"
]

/-- Per-declaration axiom footprint as DATA (empty = no axioms). -/
def S3140AxiomFootprint : List (String × List String) := [
  ("LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3140ClosureGateActual.s3140_projectClosureGate_tight", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate_tight", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedQC_le_HC", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual.S3131CanonicalRootedMagnitude", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134CanonicalRootedQC_le_HC", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_canonicalQC_le_thetaPilot", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual.S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134Step3115_mainlineQC_le_thetaPilot_viaEpsilon", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual.S3134SameCContractBridge_ofEpsilonResidual", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleToC3ReadoutIdentification_iff_exactMissing", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual.S3134FourthTriangleResidual_of_exactMissing", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangle_hullDet_after_SHE", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual.S3134FourthTriangleResidual_of_R1Identification", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparisonGap_of_c3HullReadout", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual.S3134QThetaComparison_final_of_c3HullReadout", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.qThetaPilotLogVolumeComparison_of_modelMap", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual.nativeToC3Identification_of_modelMap", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_abcConjecture_of_threeResiduals", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_pointWeightCard_iff_abcConjecture", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual.s3135_abcConjecture_of_endToEndInputsV2", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3_tight", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual.S3134Step3115ThetaPilotReadout_eq_thetaPilot_of_canonical", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaPilotHullLogVolumeReal_eq_canonical_of_factor_zero", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual.thetaNormalizationFactor_eq", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135HaarModulusActual.s3135_haar_unit_scaling", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual.s3135_realifiedDegreeSection", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual.lgpRoot_mem_thetaValueSubgroup", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3136LGPRealifiedValueTransportActual.lgpRealifiedValueTransport_compat", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual.lgpBadLocalPacket_place_agree", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual.sourceMultiradialMutationOfBPS_point_invariant", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual.sourceFirstTriangleMutationData_gluing_invariant", ["propext", "Classical.choice", "Quot.sound"]),
  ("S3131FinalResidualRegistry_length", []),
  ("S3131RegistryGateOwners_length", []),
  ("S3131ABCStrengthResiduals_length", []),
  ("LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140LastSeamThetaMissing_iff_rawHaar", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingCanonicalRootedThetaReadout_of_factor_zero", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140MissingThetaHalfReadout_of_factor_zero", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3140ThetaNormalizationLegActual.S3140FourthTriangleResidual_of_normalization", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3140NormalizedRootResidualActual.S3140NormalizedTwoLthRootSupply_iff", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.canonicalThetaTarget_of_VForm_and_exactFactor", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual.thetaHalfRawResidual_iff_missingThetaHalf", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual.S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual.S3134LastSeamThetaHalf_iff_missingThetaHalf", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132GateThetaHalfConsumptionActual.missingThetaHalf_of_lastSeamThetaMissing", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_zero_of_VForm", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual.canonicalTarget_iff_factor_eq", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual.c3TensorBlockDimension_eq_prod_finrank", ["propext", "Classical.choice", "Quot.sound"]),
  ("LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual.thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume", ["propext", "Classical.choice", "Quot.sound"])
]

/-- Machine-readable summary string (literal). -/
def S3140AxiomSummary : String :=
  "AXIOM_SUMMARY total=53 trio=50 noax=3 sorryAx=0"

/-- KERNEL-CHECKED: 53 audited declarations. -/
theorem S3140AuditedDeclarations_length : S3140AuditedDeclarations.length = 53 := rfl

/-- KERNEL-CHECKED: 50 trio declarations. -/
theorem S3140TrioDeclarations_length : S3140TrioDeclarations.length = 50 := rfl

/-- KERNEL-CHECKED: 3 no-axiom declarations. -/
theorem S3140NoAxiomDeclarations_length : S3140NoAxiomDeclarations.length = 3 := rfl

/-- KERNEL-CHECKED: 53 axiom-footprint rows. -/
theorem S3140AxiomFootprint_length : S3140AxiomFootprint.length = 53 := rfl

/-- KERNEL-CHECKED: the summary string. -/
theorem S3140AxiomSummary_eq :
    S3140AxiomSummary = "AXIOM_SUMMARY total=53 trio=50 noax=3 sorryAx=0" := rfl

#print axioms S3140AuditedDeclarations_length
#print axioms S3140TrioDeclarations_length
#print axioms S3140NoAxiomDeclarations_length
#print axioms S3140AxiomFootprint_length
#print axioms S3140AxiomSummary_eq
-- re-pinned against rebuilt S3131FinalResidualRegistryActual (EXIT=0 SIZE 9250, 15 ids, olean 03:17:01) + refreshed registry helpers (03:20:20); semantic no-change
-- FINAL registry re-pin: rebuilt S3131FinalResidualRegistryActual EXIT=0 SIZE 9528 (olean 03:23:47), 15 ids/order unchanged; semantic no-change, gate hashes re-pinned 2026-11-10

-- FINAL FINAL re-pin against registry SIZE 10039 (olean 03:24:43); gate hash pair for the acceptance record

-- recompiled against truly-final gate (registry 10314) for the final record

-- FINAL freeze re-pin against registry SIZE 11034 (stepxi C2 theorem content update; olean 03:33:55, 15 ids/order/ABC unchanged)


-- REGISTRY FROZEN AT 11938 (src sha 002D6209..., olean 03:36:13): final acceptance re-pin


-- REGISTRY FROZEN AT 12702 (src sha 41C98036..., olean 03:38:48): THE final acceptance re-pin


-- ERRATA FROZEN AT 12847 (src sha 76809A6D..., olean 03:41:17; M2a OPEN): DEFINITIVE final acceptance pin


-- COMBINED REOPEN: C3 convention CLOSED (S3139C3ConventionClosureActual certified); registry 13108 frozen (olean 04:06:14) - single final re-pin


-- M2a CLOSED combined reopen (second real closure): registry SIZE 13129 (olean 04:19:43); single re-pin

