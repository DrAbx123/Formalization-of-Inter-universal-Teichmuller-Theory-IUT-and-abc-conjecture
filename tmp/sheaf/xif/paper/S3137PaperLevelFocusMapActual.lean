import LeanFormal.IUT.Audit.Status

/-! # S3137: paper-level focus map (STEP 0 prior-art checked)

STEP 0 prior-art: GenEll|Compactly Bounded|Cor312EpsilonArithmeticComparison|WeightedRootedIdentity|logShellPoint|RegionRelativeToHullAndWeight|heightWeightBound_of_normalizedVolumeComparison|Cor312ComparisonData|SourceCor312 -> 47 LeanFormal / 403 paper / 30 corpus hits -> reuse+adapt (see S3137PriorArt* and coord/PRIOR-ART-INDEX.md).

Paper-level focus (per Lead 7.10 directive):
(c) remaining weight <= theta (hull half free via CardAMPL) + hpoint/dictionary;
(b) two families (height <= volume; volume <= weight + thetaBound + D);
GenEll Theorem 2.1 statement formalization (corpus text present; LeanFormal 0 refs);
route bridges sameC / capsule-label / stage4-unit-map / invariance;
Theta side sharp residual = R2 exactly (R1 free) + hc DATA + H1 LGPModelSourceClauseMissing + H4 hull<=theta + H5 q-side + H6 GenEll.
Registry frozen 14041; no intermediate reopen.
-/

namespace LeanFormal.IUT.XiFPaper.S3137PaperLevelFocusMapActual

/-- Paper-level focus -> prior-art pointers + status/class. -/
def S3137PaperLevelFocusMap : List (String × String × String) :=
  [ ("(c) weight <= theta (remaining)", "CertificateHullWiring.lean:99/106/155/204/272/347; CardAMPLThetaBoundSupply.lean:78/94/116/125/193 (hull half free); S3135RegionRelativeIQActual/S3135RegionRelativeObligationActual; Cor312ComparisonGapReduction:306", "ADAPT: hull half free; remaining weight<=theta + hpoint/dictionary (class B)"),
    ("(b) height <= volume family", "ThetaBoundToHeightWeight.lean:67 heightWeightBound_of_normalizedVolumeComparison; S3131PaperRouteHeightReductionActual; S3131HeightVolumeDictionaryAttemptActual; S3135HeightWeightAtPaperActual", "ADAPT: reduction exists; actual logShellPoint/dictionary class B"),
    ("(b) volume <= weight + thetaBound + D family", "Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight (Cor312ToABCBridgeInterface:248); Cor312ComparisonGapReduction:306; IQCarrierConcreteModel:413/431", "ADAPT: shape + concrete model; paper general instance class B"),
    ("GenEll Theorem 2.1 statement form", "corpus papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt lines 615-687; S3132IVGenEllShadowAdapterActual.genEll_transfer; S3137GenEllCorpusAssetActual", "ADAPT: statement form recorded in S3137GenEllStatementFormActual; no LeanFormal 0-ref proof (class B paper input)"),
    ("route sameC bridge", "S3137QThetaComparisonBridgeActual.SameCQThetaReadoutBridge / qThetaPilotLogVolumeComparison_of_sameC; S3131PaperNormalizedComparisonActual.S3131PaperRegionalQ_le_Hull", "REUSE: conditional on named sameC readout bridge"),
    ("route capsule-label link", "S3139RouteCapsuleLabelResidualActual.SourceCapsuleLabelLinkResidual (stepxi)", "REUSE: named residual; open"),
    ("route stage4 unit map", "S3136LGPGlobalUnitsToLocalUnitsActual:48/54; S3137Stage4UnitMapReuseActual", "REUSE"),
    ("route comparison/measure invariance", "S3139RouteComparisonInvarianceActual / S3139ComparisonMeasureInvarianceResidualActual (stepxi); S3131RouteComparisonInvarianceActual", "REUSE: named residuals"),
    ("Theta sharp residual = R2 (R1 free)", "S3132RootedScalingDataTrivialActual 159097; S3132ThetaSideSharpResidualReducedActual 159585; S3132RootedScalingDataFormulaActual 160816", "REUSE: R1 free; R2 sharp; hc DATA (not unconditional)"),
    ("H1 LGPModelSourceClauseMissing", "hull S3132ThetaSideClauseResidualActual.ClauseSideVFormResidual; S3132ThetaSideModelClauseResidualActual.ModelSideVFormResidual", "ADAPT: named hull-side residuals"),
    ("H4 hull <= theta", "CertificateHullWiring.lean:99/106/155; CardAMPLThetaBoundSupply.lean:78-193", "ADAPT: certificate slot + Ampl supply"),
    ("H5 q-side", "SourceQSideComparison.lean:88/96/108/125/140/170/184", "REUSE"),
    ("H6 GenEll", "S3132IVGenEllShadowAdapterActual.genEll_transfer; corpus GenEll Thm 2.1", "ADAPT: shadow adapter + paper statement form") ]

theorem S3137PaperLevelFocusMap_length : S3137PaperLevelFocusMap.length = 13 := rfl

end LeanFormal.IUT.XiFPaper.S3137PaperLevelFocusMapActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: paper-level focus map. -/
def S3137PaperLevelFocusMapRecord : Obligation :=
  { id := "S3137.index.paper-level-focus-map"
    source := "Lead 7.10 focus list; coord/PRIOR-ART-INDEX.md A-F; S3137PriorArt*Actual; hull/stepxi ids"
    status := VerificationStatus.interface
    note := "PAPER-LEVEL FOCUS MAP (STEP 0 done: 47 LeanFormal / 403 paper / 30 corpus hits; reuse+adapt): (c) weight<=theta remaining with hull half free (CertificateHullWiring + CardAMPLThetaBoundSupply) + hpoint/dictionary; (b) two families height<=volume (ThetaBoundToHeightWeight:67 + S3131 reductions) and volume<=weight+thetaBound+D (regionVolume_le_normalizedWeight shape + concrete model); GenEll Thm 2.1 statement form (corpus 615-687; formal shape S3137GenEllStatementFormActual); route bridges sameC/capsule-label/stage4-unit-map/invariance with exact named residuals; Theta sharp residual = R2 exactly (R1 free) + hc DATA + H1 LGPModelSourceClauseMissing + H4 hull<=theta + H5 q-side + H6 GenEll. Registry frozen 14041; no intermediate reopen. Classes: paper inputs class B; no D found."
    dependsOn := ["S3137PaperLevelFocusMapActual", "S3137PriorArtPaperRouteActual", "S3137ThetaSideRootedScalingNotesActual"] }

end LeanFormal.IUT.Audit
