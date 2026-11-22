set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Paper-route Theta side: source attribution and audit record

Machine-checkable attribution/audit record for the adapted source materials used
by this stream.  Data record only; no argument.  Pins at write time: registry
13129 frozen, gate 23066, acceptance record 15501.

SOURCES AND USE:
1. vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/
   Iut/Stage1/PilotComparison.lean:21-56 -> adapted in
   S3132SourceAdaptedPilotComparisonActual (PilotSide/PilotLogVolume/
   Corollary312Inequality/Stage1Comparison).
2. same vendor Iut/Stage1/CorollarySchema.lean:28-92 -> adapted in
   S3132SourceAdaptedCorollary312DataActual (signedPilotLogVolume,
   Corollary312ComparisonData, thetaPilot/qPilot/corollary312/stage1Comparison).
3. same vendor Iut/Stage1/IUTStage1IUTIVAlgebra.lean:9887-9928 -> adapted in
   S3132IVGenEllShadowAdapterActual (IV Cor. 2.3 Diophantine-inequality shadow,
   exact genEll_transfer field, discrepancy/lowerBound).
4. same vendor Iut/SourceTrace/Corollary312SourceGraph.lean:66-167 -> NOT used as
   evidence; CorridorAcceptance/CorridorNode are labels only.
5. same vendor Iut/Stage1/IUTStage1FrobenioidShift.lean:36-124 -> NOT needed;
   MultiradialThetaHullEndpoint interface superseded by the concrete canonical
   rooted readout + residual.
6. [GenEll] paper: papers/motizuki_corpus/text/Arithmetic Elliptic Curves in
   General Position.txt, Theorem 2.1 - the exact GenEll transfer field of the IV
   interface: compactly bounded subsets + general ABC are EQUIVALENT; it is a
   reduction theorem, NOT a proof of ABC.  Used only as the source citation for
   the AdaptedIVGenEllShadow.genEll_transfer field shape.
7. tmp/local-cft-port (importable) + Iut/ (importable): completion tools
   (commonPrimeCompletionActualRingEquiv, normalizedCompletionRingEquiv,
   Iut.ThetaFinitePlace.completionRingHom); no native/initial-theta hull readout
   analogue (grep Native/InitialTheta/thetaHull/readout/qVFam/Haar).
8. stage4 adapters consumed: S3136NativeHaarFamilyActual
   (lgpNativeHaarFamily), S3136ModelClauseWitnessAdapterActual
   (LGPConcreteClauseData/lgpConcreteClauseData_toNativeData),
   S3136ModelSourceClauseActual (LGPModelSourceClauseMissing/lgpModelNativeData),
   S3136ModelNativeDataWithHaarActual (LGPModelNativeDataWithHaar).

CIRCULARITY AUDIT (Theta-half chain, repeated after adaptations):
- residual props are packet/readout data equalities; no field references
  ABCConjecture/Cor312Conclusion/gate/registry;
- final composition proofs use only residual props as hypotheses (concrete hTie
  is declared-but-unused, so no hidden use);
- 0 forbidden imports across hull S3132 files (ABCBridge = LeanFormal geometry
  dir, not the ABC statement); gate imports hull files one way only;
- no scaling:=1 dependence: hull lambda ranges over ALL nonzero scalings; the
  unit-reference mass 1 in the normalization closure is a Haar NORMALIZATION,
  categorically different from the S3135 concrete scaling:=1.
- FLAGS (from stage4): (i) Omega-root != normalized local root supply (local-root
  missing); (ii) Gap/Missing opaque-Prop records are LABELS, not evidence.
-/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideAuditRecordActual

/-- An adapted-source attribution entry. -/
structure AdaptedSource where
  source : String
  declarations : List String
  consumer : String

/-- Sources adapted or consulted by the paper-route Theta side. -/
def thetaSideAdaptedSources : List AdaptedSource :=
  [ { source := "vendor/.../Iut/Stage1/PilotComparison.lean:21-56"
      declarations := ["PilotSide", "PilotLogVolume", "Corollary312Inequality",
        "Stage1Comparison"]
      consumer := "S3132SourceAdaptedPilotComparisonActual" }
  , { source := "vendor/.../Iut/Stage1/CorollarySchema.lean:28-92"
      declarations := ["signedPilotLogVolume", "Corollary312ComparisonData",
        "thetaPilot", "qPilot", "corollary312", "stage1Comparison"]
      consumer := "S3132SourceAdaptedCorollary312DataActual" }
  , { source := "vendor/.../Iut/Stage1/IUTStage1IUTIVAlgebra.lean:9887-9928"
      declarations := ["IUTStage1IUTIVCorollary23DiophantineInequalityShadow",
        "genEll_transfer", "discrepancy", "lowerBound"]
      consumer := "S3132IVGenEllShadowAdapterActual" }
  , { source := "papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt (Theorem 2.1)"
      declarations := ["GenEll reduction equivalence: compactly bounded subsets + general ABC"]
      consumer := "source anchor for AdaptedIVGenEllShadow.genEll_transfer (not a proof of ABC)" }
  , { source := "vendor/.../Iut/SourceTrace/Corollary312SourceGraph.lean:66-167"
      declarations := ["CorridorAcceptance", "CorridorNode"]
      consumer := "label-only; NOT evidence" }
  , { source := "vendor/.../Iut/Stage1/IUTStage1FrobenioidShift.lean:36-124"
      declarations := ["MultiradialThetaHullEndpoint",
        "PlaceAuditedMultiradialThetaHullEndpoint"]
      consumer := "not needed; concrete canonical readout + residual supersedes" }
  , { source := "stage4 S3136* adapters (NativeHaarFamily / ModelClauseWitnessAdapter / ModelSourceClause / ModelNativeDataWithHaar)"
      declarations := ["lgpNativeHaarFamily", "LGPConcreteClauseData",
        "LGPModelSourceClauseMissing", "LGPModelNativeDataWithHaar"]
      consumer := "S3132ThetaSideClauseResidualActual / S3132ThetaSideModelClauseResidualActual" } ]

/-- Audit verdict record. -/
structure ThetaSideAuditVerdict where
  circularity : String
  scaling : String
  flags : List String
  registryPin : Nat

/-- The audit verdict for the paper-route Theta side. -/
def thetaSideAuditVerdict : ThetaSideAuditVerdict :=
  { circularity := "no proof circularity: residuals are data equalities, proofs use only residuals as hypotheses, 0 forbidden imports, no reversed gate dependency"
    scaling := "no scaling:=1 dependence (lambda over all nonzero scalings; unit-mass-1 is Haar normalization)"
    flags := ["Omega-root != normalized local root supply (local-root missing)",
      "Gap/Missing opaque-Prop records are labels, not evidence"]
    registryPin := 13129 }

/-- The catalog lists the seven adapted/consulted source entries. -/
theorem thetaSideAdaptedSources_length : thetaSideAdaptedSources.length = 7 := rfl

/-- The audit verdict records the frozen registry pin. -/
theorem thetaSideAuditVerdict_registryPin :
    thetaSideAuditVerdict.registryPin = 13129 := rfl

#check AdaptedSource
#check thetaSideAdaptedSources
#check ThetaSideAuditVerdict
#check thetaSideAuditVerdict
#check thetaSideAdaptedSources_length
#check thetaSideAuditVerdict_registryPin

end LeanFormal.IUT.XiFPaper.S3132ThetaSideAuditRecordActual