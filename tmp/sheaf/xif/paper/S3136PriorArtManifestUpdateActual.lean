/-! # Stage-4 host: prior-art manifest update (§7.9 batches)

Data manifest of the prior-art-check / reuse / instantiation artifacts delivered in
the last two batches, with checker status and the exact prior art each reuses.

LABEL: manifest (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136PriorArtManifestUpdateActual

structure LGPPriorArtArtifactRow where
  file : String
  checkerVerdict : String
  priorArtReused : String

def lgpPriorArtManifest : List LGPPriorArtArtifactRow :=
  [ ⟨"S3136PriorArtCheckActual", "CITABLE (3 decls)", "SourceUnitRegionHaarDataActual, IQCarrierHaarData, SourceImageHull, SourceOriginalInput, FinitePlacePadicScalarStructure, tmp/local-cft-port"⟩,
    ⟨"S3136ModelOriginalInputReuseActual", "CITABLE (3 decls)", "SourceUnitRegionHaarDataActual:346 sourceHaarActualOriginalInput; :357 sourceHaarActual_primeStripAt"⟩,
    ⟨"S3136ModelUnitRegionHaarDataReuseActual", "CITABLE (6 decls)", "SourceUnitRegionHaarDataActual:407/416/433/441/447"⟩,
    ⟨"S3136FactPrimeReuseActual", "CITABLE (2 decls)", "FinitePlacePadicScalarStructure.lean:28 completionRationalPrime_fact"⟩,
    ⟨"S3136ClassABDClassConcreteInstancesActual", "CITABLE (4 decls)", "own S3136BDClassChainToolActual (class A)"⟩,
    ⟨"S3136PriorArtCor312SuppliesActual", "CITABLE (3 decls)", "HunitEpsilonTransferReduction.lean:62/70/90/103/118/141/166; CardAMPLThetaBoundSupply.lean:78/94/101/109/116/125; StepVProcessionAverage.lean:35/39/54/68/100/125/162/190/217"⟩,
    ⟨"S3136SourceUnitRegionInstantiationAttemptActual", "CITABLE (4 decls)", "HunitEpsilonTransferReduction.lean:90/103 + SourceUnitRegionHaarDataActual:416 (degenerate datum)"⟩,
    ⟨"S3136CardAMPLSupplyReuseActual", "CITABLE (5 decls)", "CardAMPLThetaBoundSupply.lean:78/94/116/125"⟩,
    ⟨"S3136WeightedAveragePriorArtReuseActual", "CITABLE (4 decls)", "StepVProcessionAverage.lean:35/54/68/:190/:217"⟩,
    ⟨"S3136RegionReviewInstantiationDataActual", "CITABLE (3 decls)", "all three prior-art supplies (mapping table, 9 rows)"⟩,
    ⟨"S3136CarrierBridgeAttemptActual", "CITABLE (4 decls)", "IQHullLogVolumeInterface (SourceHullCompactnessReduction.lean:52); sourceSetVolume (:188)"⟩,
    ⟨"S3136ThetaConstantIdentificationAttemptActual", "CITABLE (4 decls)", "CardAMPLThetaBoundSupply.lean:78/94/116 + model Theta log-volume"⟩,
    ⟨"S3136SplitPointStatementShapesActual", "CITABLE (4 decls)", "IUT IV Thm 1.10 (R1)-(R3) p.1523-1545 + StepV (R4):100"⟩,
    ⟨"S3136WeightedAverageLabelMappingActual", "CITABLE (4 decls)", "StepVProcessionAverage.lean:35/68"⟩ ]

theorem lgpPriorArtManifest_length : lgpPriorArtManifest.length = 14 := rfl

#check lgpPriorArtManifest
#check lgpPriorArtManifest_length

end LeanFormal.IUT.XiFPaper.S3136PriorArtManifestUpdateActual