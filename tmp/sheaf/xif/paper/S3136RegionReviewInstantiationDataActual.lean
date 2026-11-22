/-! # Stage-4 host: (c) review rows instantiated from prior-art supplies (data)

PRIOR ART (checked first, §7.9):
* HunitEpsilonTransferReduction.lean:90/103/118 (epsilon<->sharp hunit transfer on
  SourceUnitRegionHaarData); :166 frozen refutation of nondegenerate source datum.
* CardAMPLThetaBoundSupply.lean:78/94/116 (Theta-constant upper bound supply + real form).
* IUTIV/Estimates/StepVProcessionAverage.lean:35/68/100/190/217 (weighted-average and
  (R4) exceptional-term supplies).

CONSUMER: mainline/lattice (c) assembly. This data file maps each row of
S3136RegionVolumeEstimateReviewActual to the prior-art supply that instantiates it,
with the exact residual obstruction (no claim).

LABEL: instantiation mapping (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136RegionReviewInstantiationDataActual

structure LGPReviewInstantiationRow where
  reviewRow : String
  priorArtSupply : String
  instantiationStatus : String

def lgpReviewInstantiation : List LGPReviewInstantiationRow :=
  [ ⟨"nature additive Haar family", "our own S3136NativeHaarFamilyActual.lgpNativeHaarFamily (checker CITABLE)", "INSTANTIATED (constructive, no prior-art needed)"⟩,
    ⟨"compact tensor region volume finiteness", "our own S3136ModelThetaTensorVolumeFiniteActual + Mathlib IsCompact.measure_lt_top", "INSTANTIATED (class A)"⟩,
    ⟨"theta tensor scaled regions / hulls", "our own ThetaTensorScaledImageActual + prior-art sourceHaarActualUnitRegion (SourceUnitRegionHaarDataActual:407)", "INSTANTIATED at region level (both carriers available)"⟩,
    ⟨"normalized log-volume readout", "prior-art iqHullRealVolume/logVolume interface + our theta log-scale sums", "INSTANTIATED at shape level"⟩,
    ⟨"unit-region bound", "HunitEpsilonTransferReduction:90 cor312GapSupply_hunit_of_epsilon_hullBound + :118 sourceInterface variant; degenerate instantiation via sourceHaarActualData (degreeBound = 0) proved in S3136SourceUnitRegionInstantiationAttemptActual", "INSTANTIATED ONLY DEGENERATE (degreeBound=0; frozen refutation :166 forbids claiming nondegenerate source datum)"⟩,
    ⟨"normalized-weight / Theta upper bound side", "CardAMPLThetaBoundSupply:78 fields (theta, theta_nonneg, hull_logVolume_le) + realVolume_le:94; reuse adapters in S3136CardAMPLSupplyReuseActual", "SUPPLIED as interface data (theta identification with our model packet OPEN)"⟩,
    ⟨"split point bound ((R1)-(R3))", "partial: StepVProcessionAverage:100 exceptionalSum_le_r4 ((R4)); (R1)-(R3) prime-splitting/rounding estimates NOT in prior art", "PARTIAL (R4 only); (R1)-(R3) missing classB"⟩,
    ⟨"weighted-average side (Prop 1.7 / Step V)", "StepVProcessionAverage:35 collectionBound, :54 processionAverage_eq, :68 processionAverage_le, :190 weightedAverage_le_collectionBound, :217 processionNormalized_le_of_collectionBounds; reuse in S3136WeightedAveragePriorArtReuseActual", "SUPPLIED (class A reuse; needs our theta label-weight identification rows)"⟩,
    ⟨"regionVolume <= normalizedWeight (the (c) inequality itself)", "composition of Hunit comparison shape (log-volume) + CardAMPL theta bound + StepV average; carrier bridge between native Haar measure and the IQ/log-volume carrier MISSING", "NOT INSTANTIATED: exact obstruction = carrier bridge + nondegenerate source-haar datum (degree-faithful refutation)"⟩ ]

theorem lgpReviewInstantiation_length : lgpReviewInstantiation.length = 9 := rfl

#check lgpReviewInstantiation
#check lgpReviewInstantiation_length

end LeanFormal.IUT.XiFPaper.S3136RegionReviewInstantiationDataActual