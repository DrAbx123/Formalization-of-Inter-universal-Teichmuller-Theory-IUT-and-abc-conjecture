import LeanFormal.IUT.Audit.Status

/-! # IUTExternal21: INDEX.EXT.<ref>.<nn> alias rows (per landed files; mainline protocol)

Mainline protocol: exact landed file names + decl head + status after each batch;
lattice maps them to INDEX.EXT.<ref>.<nn> and keeps alias rows; planned-but-not-
landed files keep INDEX.EXT.<ref>.PLANNED until checker green.  STEP 0 prior-art:
deep search GenEll05bChainWiring|GenEll01dHeightWiring|S3171IUTIVSection1|
S3171UniformHeightConsumer|EtTh0[1-4]|Frd0[1-2]|ExpEst0[0-2]|flt_rr_serre|belyi_pair
-> 128 paper hits (anchors exist).  No registry edits (frozen 14041).
-/

namespace LeanFormal.IUT.XiFPaper.IUTExternal21ExtAliasesActual

/-- Alias rows: (INDEX.EXT id, landed file/decl head, status, class). -/
def IUTExternalExtAliases : List (String × String × String × String) :=
  [ ("INDEX.EXT.GenEll.01", "GenEll00NamingActual", "LANDED + checker CITABLE", "A/statement"),
    ("INDEX.EXT.GenEll.02", "GenEll01BasicActual (PaperHeight/BDClassOn/CompactlyBoundedSubset; IsBDLe reuse)", "LANDED", "A"),
    ("INDEX.EXT.GenEll.03", "GenEll01dHeightWiringActual", "LANDED (mainline)", "A"),
    ("INDEX.EXT.GenEll.04", "GenEll05Theorem21Actual (theorem21_i_implies_ii PROVED; Theorem21_ii_implies_i_required named)", "LANDED + checker CITABLE", "A + B"),
    ("INDEX.EXT.GenEll.05", "GenEll05bChainWiringActual", "LANDED (mainline; consumed by GenEll14P3Wiring)", "A wiring"),
    ("INDEX.EXT.GenEll.06", "GenEll08MainReductionActual (GenEllMainReductionStatement/genEll_mainReduction_shape/GenEllIUTIVSection2Consumer)", "LANDED", "A shape"),
    ("INDEX.EXT.GenEll.07", "GenEll09IUTIVSection2ConsumerActual", "LANDED + checker CITABLE (stepxi)", "P3 interface"),
    ("INDEX.EXT.GenEll.08", "GenEll10H6ClosureActual (interface level)", "LANDED + checker CITABLE (stepxi)", "P3 interface"),
    ("INDEX.EXT.GenEll.09", "GenEll11RouteInterfaceActual", "LANDED + checker CITABLE (stepxi)", "P3 interface"),
    ("INDEX.EXT.GenEll.10", "GenEll12Step0RecordActual; GenEll13IdsActual.genEllP3Ids (SHA 64A8BD8A)", "LANDED + checker CITABLE", "P3 ids"),
    ("INDEX.EXT.GenEll.11", "GenEll14P3WiringActual (consumes GenEll05bWiringMap)", "LANDED + checker CITABLE (stepxi); lattice ledger = GenEll10/11/12/13", "P3"),
    ("INDEX.EXT.NCBel.01", "noncritical Belyi statement layer (stage4 Mzk1 statement; hook into GenEll05 Theorem21ReductionInputs)", "PLANNED until checker green", "B + D"),
    ("INDEX.EXT.NCBel.02", "ported belyi_pair (abc; 276 files under tmp/external/ported/belyi_pair)", "PORTED source; olean/probe pending", "adapt (Apache-2.0)"),
    ("INDEX.EXT.pGC.01", "IUTExternalPGC01StatementActual", "PLANNED", "B"),
    ("INDEX.EXT.GeoAn.01", "IUTExternalGeoAn01BasicActual", "PLANNED", "B"),
    ("INDEX.EXT.AbsAnb.01", "IUTExternalAbsAnb01StatementActual", "PLANNED", "B"),
    ("INDEX.EXT.AbSc.01", "IUTExternalAbSc01StatementActual", "PLANNED", "B"),
    ("INDEX.EXT.SemiAn.01", "IUTExternalSemiAn01BasicActual", "PLANNED", "B"),
    ("INDEX.EXT.QuCnf.01", "IUTExternalQuCnf01StatementActual", "PLANNED", "B"),
    ("INDEX.EXT.CbGC.01", "IUTExternalCbGC01StatementActual", "PLANNED", "B"),
    ("INDEX.EXT.Config.01", "IUTExternalConfig01BasicActual", "PLANNED", "B"),
    ("INDEX.EXT.FrdI-II.01", "Frd01StatementActual (statement layer)", "LANDED; checker pending (universe annotation fix per shehdd)", "B statement"),
    ("INDEX.EXT.FrdI-II.02", "Frd02ReuseActual (reuse audit)", "LANDED (stepxi batch)", "B"),
    ("INDEX.EXT.EtTh.01", "EtTh01StatementActual (EtaleThetaKummerClass etc.)", "LANDED + checker CITABLE (probe trio)", "B statement"),
    ("INDEX.EXT.EtTh.02", "EtTh02DeepInputsActual (EtThDeepInput, etThDeepInputs; proved := false)", "LANDED; DEEP NAMED only", "D named"),
    ("INDEX.EXT.EtTh.03", "EtTh03TreeReuseActual.etThTreeReuse", "LANDED", "reuse"),
    ("INDEX.EXT.EtTh.04", "EtTh04RouteWiringActual (H1-H6/A35/P3 wiring)", "LANDED", "wiring"),
    ("INDEX.EXT.EtTh.05", "EtTh05 boundary reuse (per AG07MathlibCoverage); EtTh01OddThetaSeries/EtTh02ShiftLaw/EtTh03EtaleThetaGroup/EtTh04QPilotData sub-assets", "LANDED sub-assets; EtTh05 boundary pending", "A/B mixed"),
    ("INDEX.EXT.AbsTopIII.01", "AbsTopIII01LogShellActual (Def5.6/Prop5.8(v) elementary reuse)", "LANDED + checker CITABLE", "A"),
    ("INDEX.EXT.AbsTopIII.03", "AbsTopIII03Cor510Actual (Cor5.10(i) concrete finite log-volume PROVED)", "LANDED + checker CITABLE", "A"),
    ("INDEX.EXT.AbsTopIII.04", "AbsTopIII04LogFrobeniusActual (Def3.1(iv) dictionary)", "LANDED + checker CITABLE", "A"),
    ("INDEX.EXT.AbsTopIII.05", "AbsTopIII05ReconstructionInputsActual (DEEP named, none proved)", "LANDED + checker CITABLE; D named only", "D named"),
    ("INDEX.EXT.AbsTopIII.07", "AbsTopIII07VolumeLogShellBridgeActual", "LANDED + checker CITABLE", "A"),
    ("INDEX.EXT.AbsTopIII.08", "AbsTopIII08PvAdicScalingActual", "LANDED + checker CITABLE", "A"),
    ("INDEX.EXT.AbsTopIII.09", "AbsTopIII09ThetaHullScalingActual", "LANDED + checker CITABLE", "A"),
    ("INDEX.EXT.ExpEst.00", "ExpEst00NamingActual", "LANDED", "A naming"),
    ("INDEX.EXT.ExpEst.01", "ExpEst01StatementLedgerActual", "LANDED; ledger", "B/A mix"),
    ("INDEX.EXT.ExpEst.02", "ExpEst02 (7 decls; honest PNT paper-inputs)", "LANDED + checker CITABLE (3BB83606)", "A partial/B"),
    ("INDEX.EXT.IUTIV.01", "S3171IUTIVSection1Statement", "LANDED + checker CITABLE (probe _S3171BatchProbe 164512)", "statement"),
    ("INDEX.EXT.IUTIV.02", "S3171IUTIVSection1Estimates", "LANDED + checker CITABLE", "statement"),
    ("INDEX.EXT.IUTIV.03", "S3171IUTIVSection1Display", "LANDED + checker CITABLE", "statement"),
    ("INDEX.EXT.IUTIV.04", "S3171IUTIVSection1Inputs", "LANDED + checker CITABLE", "inputs"),
    ("INDEX.EXT.IUTIV.05", "S3171UniformHeightConsumer", "LANDED + checker CITABLE", "consumer"),
    ("INDEX.EXT.AG.01", "AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (CPA: 72 decls CITABLE) + Repartitions + AdelicIndex + CoherentBaseChange + TwoChartCech + CechSectionsOfDivisor (flat adapted)", "AG_FLT_* checker CITABLE (qpilot); Cech pending compile", "complete-proof citable first layer"),
    ("INDEX.EXT.AG.02", "ported flt_rr_serre (RR/Serde closure)", "PORTED; olean-path retry pending", "adapt pending"),
    ("INDEX.EXT.AG.03", "TauCeti (tmp/TauCeti) WeilDivisor/LineBundle/RR/Serde/Pencil/Belyi + ported tauceti2/belyi_poly (quickport batches)", "QUICKPORT in progress (queue saturated); source Apache-2.0", "adapt pending"),
    ("planned-placeholder", "INDEX.EXT.<ref>.PLANNED rows for pGC/GeoAn/AbsAnb/AbSc/SemiAn/QuCnf/CbGC/Config/NCBel-statement until checker green per mainline protocol", "PLACEHOLDER", "-") ]

end LeanFormal.IUT.XiFPaper.IUTExternal21ExtAliasesActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: INDEX.EXT alias rows. -/
def IUTExternalExtAliasesRecord : Obligation :=
  { id := "INDEX.IUTEXTERNAL.ext-alias-rows"
    source := "mainline protocol + landed anchors (GenEll00-14*, S3171*, EtTh01-04, Frd01-02, ExpEst00-02, AbsTopIII01/03/05/07/08/09, AG_FLT_*, ported flt_rr_serre/belyi_pair, TauCeti quickports)"
    status := VerificationStatus.interface
    note := "INDEX.EXT.<ref>.<nn> ALIAS ROWS (45): landed anchors mapped with status LANDED/PLANNED/PORTED/QUICKPORT-in-progress; GenEll00-14*, GenEll05bChainWiring/GenEll01dHeightWiring, S3171IUTIVSection1{Statement,Estimates,Display,Inputs}+UniformHeightConsumer, EtTh01-05 sub-assets (deep inputs D named only), Frd01-02, ExpEst00-02, AbsTopIII01/03/04/05/07/08/09 (05 D named only), AG_FLT_* citable first layer, ported flt_rr_serre (olean retry), ported belyi_pair (276 files), TauCeti quickports, planned placeholders for pGC/GeoAn/AbsAnb/AbSc/SemiAn/QuCnf/CbGC/Config/NCBel-statement. Alias rows updated per mainline protocol; no registry edits (frozen 14041)."
    dependsOn := ["IUTExternal21ExtAliasesActual", "IUTExternal10IndexIdsActual", "IUTExternal20ProofStatusActual"] }

end LeanFormal.IUT.Audit