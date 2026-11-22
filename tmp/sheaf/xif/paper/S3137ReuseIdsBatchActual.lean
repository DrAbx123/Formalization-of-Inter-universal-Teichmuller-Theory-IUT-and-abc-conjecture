import LeanFormal.IUT.Audit.Status

/-! # S3137: INDEX.REUSE ids batch (prior-art reuse registry note; frozen 14041 (third combined reopen: Option-B model-route closure))

stepxi-provided (S3139PriorArtReuseIdsActual.priorArtReuseIds, EXIT0 157943,
checker CITABLE, probe _S3139PriorArtCheckProbe 158996) plus lattice's own
prior-art reuse entries.  Index note only; no registry edit.
-/

namespace LeanFormal.IUT.XiFPaper.S3137ReuseIdsBatchActual

/-- INDEX.REUSE ids (data). -/
def S3137ReuseIds : List (String × String) :=
  [ ("INDEX.REUSE.theater-family", "SourceUnitRegionHaarDataActual.lean:122-353 (prime strip/theater/equiv/link/laws/injective/family/OriginalInput)"),
    ("INDEX.REUSE.fact-prime-instance", "FinitePlacePadicScalarStructure.lean:28 completionRationalPrime_fact"),
    ("INDEX.REUSE.height-weight-theorem", "ThetaBoundToHeightWeight.lean:67 heightWeightBound_of_normalizedVolumeComparison"),
    ("INDEX.REUSE.v2-interface", "Cor312ComparisonRegionV2Actual.lean:9/26/32 Cor312EpsilonArithmeticComparisonV2 / bridge / heightBoundV2"),
    ("INDEX.REUSE.qpilot-M1-names", "S3133M1InjectionReductionActual:55/79 + S3133M1ContractObstructionActual:56/67"),
    ("INDEX.REUSE.stage4-unit-map", "S3136LGPGlobalUnitsToLocalUnitsActual:48/54"),
    ("INDEX.REUSE.iq-carrier-concrete-model", "IQCarrierConcreteModel.lean:193/303/315/346/358/373/386/413/431 (interface + hunit/hsplit/hptfin/hweightvol/hpoint + epsilonComparison/Additive)"),
    ("INDEX.REUSE.haar-unit-region", "IQCarrierHaarData.lean:181/207/215/225/265/353; SourceContractedSupplyRealization.lean:219/239/253/273"),
    ("INDEX.REUSE.f4-clause-chain", "HunitEpsilonTransferReduction.lean:90/103/118/141/166/188; HullVertexConvexityAssembly.lean:119/136/155/217/277"),
    ("INDEX.REUSE.card-hull-real", "CardHullReal* .lean + HullDeterminantLogVolumeReduction.lean:501/536/560/569 + CardAMPLThetaBoundSupply.lean:193"),
    ("INDEX.REUSE.cor312-comparison", "Cor312ToABCBridgeInterface.lean:200-284; Cor312ComparisonGapReduction.lean:128-478; Cor312GapDictionaryLayer.lean:176-372"),
    ("INDEX.REUSE.v2-consumer-names", "S3139V2ConsumerPathNamesActual.v2ConsumerPathNames (comparisonRegion, membership lemmas, regionVolume/dictionary->invariance mapping, invariance residual names)") ]

theorem S3137ReuseIds_length : S3137ReuseIds.length = 12 := rfl

end LeanFormal.IUT.XiFPaper.S3137ReuseIdsBatchActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: prior-art reuse ids. -/
def S3137ReuseIdsRecord : Obligation :=
  { id := "S3137.index.reuse-ids"
    source := "stepxi S3139PriorArtReuseIdsActual.priorArtReuseIds (EXIT0 157943, checker CITABLE, probe 158996); lattice prior-art sweep S3137PriorArt*Actual"
    status := VerificationStatus.interface
    note := "INDEX.REUSE ids recorded (next re-pin input; registry frozen 14041 (third combined reopen: Option-B model-route closure)): theater-family, fact-prime-instance, height-weight theorem, V2 interface, qpilot M1 names, stage4 unit map, IQCarrierConcreteModel, Haar/unit-region, F4 clause chain, Card/CTheta/hull real, Cor312 comparison/gap/dictionary, V2 consumer names. All prior art is REUSE, not new residuals. This re-plans the 3rd-reopen scope (model theater-family CLOSED BY REUSE; remaining paper inputs as classified)."
    dependsOn := ["S3137ReuseIdsBatchActual"] }

end LeanFormal.IUT.Audit