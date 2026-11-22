import LeanFormal.IUT.Audit.Status

/-! # AbsTopIII11: INDEX.ABSIII ids (citation rows + classification)

Registry frozen 14041; no registry edits.  IDs only; statements in
AbsTopIII10StatementLedgerActual; citation rows in GenEll12CitationRowsActual
([AbsTopIII] Prop 5.8(ii) row) and AbsTopIII12CitationRowsActual.
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII11IndexIdsActual

/-- INDEX.ABSIII ids with class (data). -/
def AbsTopIIIIndexIds : List (String × String) :=
  [ ("INDEX.ABSIII.sec0-notations-graph", "C concrete-combinatorial-formalizable; corpus 1269; tree SourceThetaLinkGraphAutomorphismReduction:11"),
    ("INDEX.ABSIII.sec1-galois-reconstruction", "D anabelian-deep-input; corpus 1442"),
    ("INDEX.ABSIII.sec2-archimedean", "B formalizable-partial; corpus 2523"),
    ("INDEX.ABSIII.sec3-log-frobenius", "C concrete-p-adic-formalizable; corpus 3280; Def 3.1(iv) 3424-3520; tree MonoAnalyticLogShell* + SourceLogShell* + bridge"),
    ("INDEX.ABSIII.sec4-archimedean", "B formalizable-partial; corpus 5284"),
    ("INDEX.ABSIII.sec5-global", "D anabelian-deep-input; corpus 6044"),
    ("INDEX.ABSIII.cor5.2", "D anabelian-deep-input; corpus 6538"),
    ("INDEX.ABSIII.cor5.5", "D anabelian-deep-input; corpus 7347"),
    ("INDEX.ABSIII.def5.6-log-shells", "C concrete-p-adic-formalizable; tree SourceLogShellAbsTopIIIBridge:6/10/15"),
    ("INDEX.ABSIII.prop5.7-local-volumes", "C concrete-p-adic-formalizable; corpus 7915-7941; tree SourceEWeightedLogVolumeData:54/244 + HaarTranslateRealLineLogCompatibility:6/10 + CardHullReal* normalizations"),
    ("INDEX.ABSIII.prop5.8-monoanalytic-reconstruction", "D anabelian-deep-input with C p-adic shadow (MonoAnalyticLogShellArchPsiCnsCalibration); corpus 8059"),
    ("INDEX.ABSIII.cor5.10-fundamental-properties", "C concrete-p-adic-formalizable; corpus 8494; tree HaarTranslateRealLineLogCompatibility:6/10 + LogFrobeniusCompatibility:6 + HaarTranslateRealLineInstance:57/182"),
    ("INDEX.ABSIII.hull.01-logshell", "C concrete-p-adic-formalizable; AbsTopIII01LogShellActual (hull, CITABLE): Def 5.6 / Prop 5.8(v) elementary reuse"),
    ("INDEX.ABSIII.hull.03-cor510", "C concrete-p-adic-formalizable; AbsTopIII03Cor510Actual (hull, CITABLE): Cor 5.10(i) concrete finite log-volume PROVED"),
    ("INDEX.ABSIII.hull.04-logfrobenius", "C concrete-p-adic-formalizable; AbsTopIII04LogFrobeniusActual (hull, CITABLE): Def 3.1(iv) dictionary"),
    ("INDEX.ABSIII.hull.05-deep-inputs", "D anabelian-deep-input (named, none proved); AbsTopIII05ReconstructionInputsActual (hull, CITABLE)"),
    ("INDEX.ABSIII.hull.07-volume-bridge", "C concrete-p-adic-formalizable; AbsTopIII07VolumeLogShellBridgeActual (hull, CITABLE 163739); prior art S3137LogShellHaarLogVolumeScalingActual:61/85/109"),
    ("INDEX.ABSIII.hull.08-pv-scaling", "C concrete-p-adic-formalizable; AbsTopIII08PvAdicScalingActual (hull, CITABLE 164324); prior art S3137ThetaHullVolumeScalingActual:59/70; stage4 AbsTopIII02/06"),
    ("INDEX.ABSIII.hull.09-theta-hull-scaling", "C concrete-p-adic-formalizable; AbsTopIII09ThetaHullScalingActual (hull, CITABLE 164106)") ]

theorem AbsTopIIIIndexIds_length : AbsTopIIIIndexIds.length = 19 := rfl

end LeanFormal.IUT.XiFPaper.AbsTopIII11IndexIdsActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: AbsTopIII ids. -/
def AbsTopIIIIndexIdsRecord : Obligation :=
  { id := "INDEX.ABSIII.ids"
    source := "corpus Topics in Absolute Anabelian Geometry III; tree citation files; coord/PRIOR-ART-INDEX.md section E"
    status := VerificationStatus.interface
    note := "INDEX.ABSIII ids (19, incl. hull execution assets): section 0 graph (C), section 1 Galois reconstruction (D), section 2/4 archimedean (B partial), section 3 Log-Frobenius + Def 3.1(iv) (C; tree MonoAnalyticLogShell/SourceLogShell machinery), section 5 global (D), Cor 5.2/5.5 (D), Def 5.6 log-shells (C), Prop 5.7 Local Volumes (C; tree normalized log-volume/Haar), Prop 5.8 Mono-analytic Reconstruction (D with C p-adic shadow), Cor 5.10 Fundamental Properties (C; tree log-Frobenius compatibility), plus hull execution assets absiii.hull.01-logshell / .03-cor510 / .04-logfrobenius (C) and .05-deep-inputs (D named, none proved), all CITABLE. Registry frozen 14041."
    dependsOn := ["AbsTopIII11IndexIdsActual", "INDEX.GENELL.citation-rows"] }

end LeanFormal.IUT.Audit