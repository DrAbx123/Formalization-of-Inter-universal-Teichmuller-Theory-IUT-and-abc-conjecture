/-!
# S3139: prior-art reuse ids (data only; registry frozen 13129)

Id mapping for the reuse decisions recorded in S3139PriorArtAuditActual
(policy §7.9 repo-first).  These are NOT new nodes in my stream; they point the
INDEX at already-existing proven assets and record where my route consumers
rely on them.

* INDEX.REUSE.theater-family -> LeanFormal/IUT/IUTIII/Corollary312/StepXI/
  HolomorphicHull/SourceUnitRegionHaarDataActual.lean (sourceHaarActualPrimeStrip
  :122, Theater :143, sourceHaarActualPrimeStripEquiv :151, TheaterLink :213,
  laws :224-284, Theater_injective :288-319, Family :322-341, OriginalInput :346-353).
  Decision: REUSE (model theater family fully proven there; no re-proof in S3139).
* INDEX.REUSE.fact-prime-instance -> LeanFormal/IUT/ABCBridge/Geometry/
  FinitePlacePadicScalarStructure.lean:28 completionRationalPrime_fact.
  Decision: REUSE when a concrete completion-prime Fact instance is needed.
* INDEX.REUSE.height-weight-theorem -> LeanFormal/IUT/ABCBridge/Bridge/
  ThetaBoundToHeightWeight.lean:67 heightWeightBound_of_normalizedVolumeComparison.
  Decision: REUSE (paper-route height/weight theorem).
* INDEX.REUSE.v2-interface -> tmp/sheaf/xif/paper/Cor312ComparisonRegionV2Actual.lean
  Cor312EpsilonArithmeticComparisonV2 :9, Cor312ToABCBridgeInterfaceV2 :26,
  cor312ToABCBridge_heightBoundV2 :32.  Decision: REUSE; my S3139 semantics
  (V2ComparisonRegionConsumer) supplies the C3 convention-transfer entry only.
* INDEX.REUSE.qpilot-M1-names -> S3133M1InjectionReductionActual:55/79,
  S3133M1ContractObstructionActual:56/67 (verified).
* INDEX.REUSE.stage4-unit-map -> S3136LGPGlobalUnitsToLocalUnitsActual:48/54 (verified).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3139PriorArtReuseIdsActual

/-- Reuse-id entry: (index id, existing location, decision). -/
def priorArtReuseIds : List (String × String × String) :=
  [ ("INDEX.REUSE.theater-family",
      "LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:122-353",
      "REUSE (model theater family)"),
    ("INDEX.REUSE.fact-prime-instance",
      "LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:28",
      "REUSE (completionRationalPrime_fact)"),
    ("INDEX.REUSE.height-weight-theorem",
      "LeanFormal/IUT/ABCBridge/Bridge/ThetaBoundToHeightWeight.lean:67",
      "REUSE (heightWeightBound_of_normalizedVolumeComparison)"),
    ("INDEX.REUSE.v2-interface",
      "tmp/sheaf/xif/paper/Cor312ComparisonRegionV2Actual.lean:9/26/32",
      "REUSE (V2 interface; S3139 supplies C3 transfer entry)"),
    ("INDEX.REUSE.qpilot-M1-names",
      "tmp/sheaf/xif/paper/S3133M1InjectionReductionActual.lean:55/79 + S3133M1ContractObstructionActual.lean:56/67",
      "REUSE (verified)"),
    ("INDEX.REUSE.stage4-unit-map",
      "tmp/sheaf/xif/paper/S3136LGPGlobalUnitsToLocalUnitsActual.lean:48/54",
      "REUSE (verified)") ]

end LeanFormal.IUT.XiFPaper.S3139PriorArtReuseIdsActual
