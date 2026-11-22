/-!
# S3139: repo-first prior-art audit (data only; policy §7.9)

Audit performed before the route endgame batch.  For each asset: file:line ->
reuse / adapt / none.  (No new definitions were needed for the reused items.)

Lead-listed theater-family / Haar assets (REUSE where the model route needs them):
* LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean
  - sourceHaarActualPrimeStrip : 122-136 -> REUSE (actual F-prime-strip of the model theater family)
  - Theater : 143-147 -> REUSE
  - sourceHaarActualPrimeStripEquiv : 151-166 (+ laws :224-284) -> REUSE
  - TheaterLink : 213-221 -> REUSE
  - Theater_injective : 288-319 -> REUSE
  - Family : 322-341 -> REUSE
  - OriginalInput : 346-353 -> REUSE
  My first-triangle route work uses the production CapsuleTheaterAssignment / OriginalInput
  objects (already existing) and does not re-prove any theater-family construction.
* LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:25/28-29
  completionRationalPrime / instance completionRationalPrime_fact :
  Fact (completionRationalPrime place).val.Prime -> REUSE when a concrete
  completion-prime Fact instance is needed (my S3139 C2/Brauer layer takes the
  prime/n as abstract parameters, so no new instance is defined).

Model Haar / IQ carrier / hull interface assets (REUSE):
* LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean (IQHullLogVolumeInterface,
  Cor312EpsilonArithmeticComparison, Additive variant) -> REUSE via the paper-route
  streams; my V2 consumer path is generic over the region/volume readout.
* LeanFormal/IUT/ABCBridge/Bridge/ThetaBoundToHeightWeight.lean:67
  heightWeightBound_of_normalizedVolumeComparison -> REUSE (paper-route height/weight
  theorem; my route conclusion only feeds the q/Theta side).
* tmp/sheaf/xif/paper/Cor312ComparisonRegionV2Actual.lean
  Cor312EpsilonArithmeticComparisonV2 :9, Cor312ToABCBridgeInterfaceV2 :26,
  cor312ToABCBridge_heightBoundV2 :32 -> REUSE by mainline/abc; my V2 consumer
  (SourceV2ComparisonRegionConsumer.membership_and_volume) supplies the C3
  convention-transfer + invariance entry, not a duplicate bridge.

Referenced cross-stream names VERIFIED to exist:
* tmp/sheaf/xif/paper/S3133M1InjectionReductionActual.lean:55
  S3133BadToAllPlaceIndexInjection_of_bijections; :79 S3133M1Remaining.
* tmp/sheaf/xif/paper/S3133M1ContractObstructionActual.lean:56
  S3133M1ContractSeparatedMissing; :67 S3133M1ContractSeparatedMissing_to_M1Remaining.
* tmp/sheaf/xif/paper/S3136LGPGlobalUnitsToLocalUnitsActual.lean:48
  lgpGlobalUnitsToLocalUnits; :54 lgpGlobalUnitsToLocalUnits_apply.
* Production PrcAutomorphismTensorAction (Ind1AutomorphismTensorActionActual.lean:44) and
  polyIsoOfPerm (S3139C3Ind1BridgeActual) already verified by the certified C3 closure.

DECISION: no re-proving of the listed existing results; reuse via imports/adaptation.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139PriorArtAuditActual

/-- Prior-art audit entry: (asset file:line, name, decision). -/
structure PriorArtEntry where
  location : String
  name : String
  decision : String

/-- The prior-art audit for the route endgame batch. -/
def priorArtAudit : List PriorArtEntry :=
  [ { location := "LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:122",
      name := "sourceHaarActualPrimeStrip (+ Theater :143, PrimeStripEquiv :151, TheaterLink :213, laws :224, Theater_injective :288, Family :322, OriginalInput :346)",
      decision := "REUSE (existing fully proven model theater family)" },
    { location := "LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:28",
      name := "completionRationalPrime_fact : Fact (completionRationalPrime place).val.Prime",
      decision := "REUSE (existing Fact-prime instance)" },
    { location := "LeanFormal/IUT/ABCBridge/Bridge/ThetaBoundToHeightWeight.lean:67",
      name := "heightWeightBound_of_normalizedVolumeComparison",
      decision := "REUSE (paper-route height/weight theorem)" },
    { location := "tmp/sheaf/xif/paper/Cor312ComparisonRegionV2Actual.lean:9/26/32",
      name := "Cor312EpsilonArithmeticComparisonV2 / Cor312ToABCBridgeInterfaceV2 / cor312ToABCBridge_heightBoundV2",
      decision := "REUSE (mainline/abc V2 interface; my consumer supplies C3 transfer entry)" },
    { location := "tmp/sheaf/xif/paper/S3133M1InjectionReductionActual.lean:55/79",
      name := "S3133BadToAllPlaceIndexInjection_of_bijections / S3133M1Remaining",
      decision := "REUSE (qpilot M1 residual names; verified)" },
    { location := "tmp/sheaf/xif/paper/S3133M1ContractObstructionActual.lean:56/67",
      name := "S3133M1ContractSeparatedMissing / _to_M1Remaining",
      decision := "REUSE (qpilot contract-separated M1 datum; verified)" },
    { location := "tmp/sheaf/xif/paper/S3136LGPGlobalUnitsToLocalUnitsActual.lean:48/54",
      name := "lgpGlobalUnitsToLocalUnits / _apply",
      decision := "REUSE (stage4 canonical unit map; verified)" } ]

end LeanFormal.IUT.XiFPaper.S3139PriorArtAuditActual
