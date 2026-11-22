set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Repo treasure survey record: Theta-side readout analogues (vendor promachina)

Machine-checkable record of the survey done for the paper-route Theta side.
Source locations are cited for attribution; nothing from the vendor snapshot is
imported (separate lake project, source reference only).

Findings and reuse decisions:
1. vendor Iut/Stage1/PilotComparison.lean:21-56 — PilotSide/PilotLogVolume/
   Corollary312Inequality/Stage1Comparison.  USED (adapted) in
   S3132SourceAdaptedPilotComparisonActual.
2. vendor Iut/Stage1/CorollarySchema.lean:28-92 — signedPilotLogVolume,
   Corollary312ComparisonData, thetaPilot/qPilot/thetaPilot_side/qPilot_side/
   qPilot_positive/corollary312/stage1Comparison.  USED (adapted) in
   S3132SourceAdaptedCorollary312DataActual.
3. vendor Iut/Stage1/IUTStage1IUTIVAlgebra.lean:9887-9928 — IV Corollary 2.3
   Diophantine shadow with exact GenEll transfer field.  USED (adapted) in
   S3132IVGenEllShadowAdapterActual.
4. vendor Iut/SourceTrace/Corollary312SourceGraph.lean:66-167 — CorridorAcceptance
   /CorridorNode acceptance graph (data-only labels: initial-theta, hull,
   log-volume, determinant, ...).  NOT used as evidence; recorded here as the
   source-side node naming (labels are not proofs).
5. vendor Iut/Stage1/IUTStage1FrobenioidShift.lean:36-124 — MultiradialThetaHull
   Endpoint / PlaceAuditedMultiradialThetaHullEndpoint interfaces.  NOT imported;
   our concrete endpoint object is the canonical rooted readout with the residual
   identity (hull stream files), so the vendor endpoint interface is not needed.
6. vendor Iut/Stage1/IUTStage1EndpointAudit.lean — PlaceAuditedMultiradialTheta
   HullEndpoint audit namespace; label-only for our purposes.
7. tmp/local-cft-port (importable) + Iut/ (importable): used earlier for
   completion tools (commonPrimeCompletionActualRingEquiv,
   Iut.ThetaFinitePlace.completionRingHom); no native/initial-theta hull readout
   analogues found (grep Native/InitialTheta/thetaHull/readout/qVFam/Haar).
-/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideSurveyRecordActual

/-- A source-survey entry. -/
structure SurveyEntry where
  source : String
  declarations : List String
  decision : String

/-- The survey entries for the paper-route Theta side. -/
def thetaSideSurvey : List SurveyEntry :=
  [ { source := "vendor/.../Iut/Stage1/PilotComparison.lean:21-56"
      declarations := ["PilotSide", "PilotLogVolume", "Corollary312Inequality",
        "Stage1Comparison"]
      decision := "adapted in S3132SourceAdaptedPilotComparisonActual" }
  , { source := "vendor/.../Iut/Stage1/CorollarySchema.lean:28-92"
      declarations := ["signedPilotLogVolume", "Corollary312ComparisonData",
        "thetaPilot", "qPilot", "corollary312", "stage1Comparison"]
      decision := "adapted in S3132SourceAdaptedCorollary312DataActual" }
  , { source := "vendor/.../Iut/Stage1/IUTStage1IUTIVAlgebra.lean:9887-9928"
      declarations := ["IUTStage1IUTIVCorollary23DiophantineInequalityShadow",
        "genEll_transfer", "discrepancy", "lowerBound"]
      decision := "adapted in S3132IVGenEllShadowAdapterActual" }
  , { source := "vendor/.../Iut/SourceTrace/Corollary312SourceGraph.lean:66-167"
      declarations := ["CorridorAcceptance", "CorridorNode"]
      decision := "label-only source graph; not evidence" }
  , { source := "vendor/.../Iut/Stage1/IUTStage1FrobenioidShift.lean:36-124"
      declarations := ["MultiradialThetaHullEndpoint",
        "PlaceAuditedMultiradialThetaHullEndpoint"]
      decision := "not needed: concrete endpoint = canonical readout + residual" }
  , { source := "tmp/local-cft-port + Iut (importable)"
      declarations := ["PadicField.Norm/Uniformizer", "Iut.ThetaFinitePlace.completionRingHom"]
      decision := "used for completion tools; no native readout analogue" } ]

/-- The survey lists the six recorded treasure entries. -/
theorem thetaSideSurvey_length : thetaSideSurvey.length = 6 := rfl

#check SurveyEntry
#check thetaSideSurvey
#check thetaSideSurvey_length

end LeanFormal.IUT.XiFPaper.S3132ThetaSideSurveyRecordActual
